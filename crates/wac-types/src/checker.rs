use crate::{
    CoreExtern, CoreFuncType, DefinedType, DefinedTypeId, Enum, Flags, FuncResult, FuncTypeId,
    InterfaceId, ItemKind, ModuleTypeId, PrimitiveType, Record, ResourceId, Type, Types, ValueType,
    Variant, WorldId,
};
use anyhow::{bail, Context, Result};
use indexmap::IndexMap;
use std::collections::HashSet;

/// Represents the kind of subtyping check to perform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubtypeCheck {
    /// The type is a covariant check.
    Covariant,
    /// The type is a contravariant check.
    Contravariant,
}

/// Implements a subtype checker.
///
/// Subtype checking is used to type check instantiation arguments.
pub struct SubtypeChecker<'a> {
    kinds: Vec<SubtypeCheck>,
    cache: &'a mut HashSet<(ItemKind, ItemKind)>,
}

impl<'a> SubtypeChecker<'a> {
    /// Creates a new subtype checker with the given cache.
    pub fn new(cache: &'a mut HashSet<(ItemKind, ItemKind)>) -> Self {
        Self {
            kinds: Default::default(),
            cache,
        }
    }

    /// Checks if `a` is a subtype of `b`.
    pub fn is_subtype(
        &mut self,
        a: ItemKind,
        at: &Types,
        b: ItemKind,
        bt: &Types,
        kind: SubtypeCheck,
    ) -> Result<()> {
        if self.cache.contains(&(a, b)) {
            return Ok(());
        }

        self.kinds.push(kind);
        let result = self.is_subtype_(a, at, b, bt);
        self.kinds.pop();

        if result.is_ok() {
            self.cache.insert((a, b));
        }

        result
    }

    fn is_subtype_(&mut self, a: ItemKind, at: &Types, b: ItemKind, bt: &Types) -> Result<()> {
        match (a, b) {
            (ItemKind::Type(a), ItemKind::Type(b)) => self.ty(a, at, b, bt),
            (ItemKind::Func(a), ItemKind::Func(b)) => self.func(a, at, b, bt),
            (ItemKind::Instance(a), ItemKind::Instance(b)) => self.interface(a, at, b, bt),
            (ItemKind::Component(a), ItemKind::Component(b)) => self.world(a, at, b, bt),
            (ItemKind::Module(a), ItemKind::Module(b)) => self.module(a, at, b, bt),
            (ItemKind::Value(a), ItemKind::Value(b)) => self.value_type(a, at, b, bt),
            _ => {
                let (expected, expected_types, found, found_types) =
                    self.expected_found(&a, at, &b, bt);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.desc(expected_types),
                    found = found.desc(found_types)
                )
            }
        }
    }

    fn expected_found<'b, T>(
        &self,
        a: &'b T,
        at: &'b Types,
        b: &'b T,
        bt: &'b Types,
    ) -> (&'b T, &'b Types, &'b T, &'b Types) {
        match self.kind() {
            // For covariant checks, the supertype is the expected type
            SubtypeCheck::Covariant => (b, bt, a, at),
            // For contravariant checks, the subtype is the expected type
            SubtypeCheck::Contravariant => (a, at, b, bt),
        }
    }

    /// Gets the current check kind.
    fn kind(&self) -> SubtypeCheck {
        self.kinds.last().copied().unwrap()
    }

    fn resource(&self, a: ResourceId, at: &Types, b: ResourceId, bt: &Types) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &at[at.resolve_resource(a)];
        let b = &bt[bt.resolve_resource(b)];
        if a.name != b.name {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);

            bail!(
                "expected resource `{expected}`, found resource `{found}`",
                expected = expected.name,
                found = found.name
            );
        }

        Ok(())
    }

    fn ty(&mut self, a: Type, at: &Types, b: Type, bt: &Types) -> Result<()> {
        match (a, b) {
            (Type::Resource(a), Type::Resource(b)) => return self.resource(a, at, b, bt),
            (Type::Func(a), Type::Func(b)) => return self.func(a, at, b, bt),
            (Type::Value(a), Type::Value(b)) => return self.value_type(a, at, b, bt),
            (Type::Interface(a), Type::Interface(b)) => return self.interface(a, at, b, bt),
            (Type::World(a), Type::World(b)) => return self.world(a, at, b, bt),
            (Type::Module(a), Type::Module(b)) => return self.module(a, at, b, bt),
            _ => {}
        }

        let (expected, expected_types, found, found_types) = self.expected_found(&a, at, &b, bt);

        bail!(
            "expected {expected}, found {found}",
            expected = expected.desc(expected_types),
            found = found.desc(found_types)
        )
    }

    fn func(&self, a: FuncTypeId, at: &Types, b: FuncTypeId, bt: &Types) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &at[a];
        let b = &bt[b];

        // Note: currently subtyping for functions is done in terms of equality
        // rather than actual subtyping; the reason for this is that implementing
        // runtimes don't yet support more complex subtyping rules.

        if a.params.len() != b.params.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected function with parameter count {expected}, found parameter count {found}",
                expected = expected.params.len(),
                found = found.params.len(),
            );
        }

        for (i, ((an, a), (bn, b))) in a.params.iter().zip(b.params.iter()).enumerate() {
            if an != bn {
                let (expected, _, found, _) = self.expected_found(an, at, bn, bt);
                bail!("expected function parameter {i} to be named `{expected}`, found name `{found}`");
            }

            self.value_type(*a, at, *b, bt)
                .with_context(|| format!("mismatched type for function parameter `{bn}`"))?;
        }

        match (&a.results, &b.results) {
            (None, None) => return Ok(()),
            (Some(FuncResult::Scalar(a)), Some(FuncResult::Scalar(b))) => {
                return self
                    .value_type(*a, at, *b, bt)
                    .context("mismatched type for function result");
            }
            (Some(FuncResult::List(a)), Some(FuncResult::List(b))) => {
                for (i, ((an, a), (bn, b))) in a.iter().zip(b.iter()).enumerate() {
                    if an != bn {
                        let (expected, _, found, _) = self.expected_found(an, at, bn, bt);
                        bail!("expected function result {i} to be named `{expected}`, found name `{found}`");
                    }

                    self.value_type(*a, at, *b, bt)
                        .with_context(|| format!("mismatched type for function result `{bn}`"))?;
                }

                return Ok(());
            }
            (Some(FuncResult::List(_)), Some(FuncResult::Scalar(_)))
            | (Some(FuncResult::Scalar(_)), Some(FuncResult::List(_)))
            | (Some(_), None)
            | (None, Some(_)) => {
                // Handle the mismatch below
            }
        }

        let (expected, _, found, _) = self.expected_found(a, at, b, bt);
        match (&expected.results, &found.results) {
            (Some(FuncResult::List(_)), Some(FuncResult::Scalar(_))) => {
                bail!("expected function that returns a named result, found function with a single result type")
            }
            (Some(FuncResult::Scalar(_)), Some(FuncResult::List(_))) => {
                bail!("expected function that returns a single result type, found function that returns a named result")
            }
            (Some(_), None) => {
                bail!("expected function with a result, found function without a result")
            }
            (None, Some(_)) => {
                bail!("expected function without a result, found function with a result")
            }
            (Some(FuncResult::Scalar(_)), Some(FuncResult::Scalar(_)))
            | (Some(FuncResult::List(_)), Some(FuncResult::List(_)))
            | (None, None) => unreachable!(),
        }
    }

    fn instance_exports(
        &mut self,
        a: &IndexMap<String, ItemKind>,
        at: &Types,
        b: &IndexMap<String, ItemKind>,
        bt: &Types,
    ) -> Result<()> {
        // For instance type subtyping, all exports in the other
        // instance type must be present in this instance type's
        // exports (i.e. it can export *more* than what this instance
        // type needs).
        for (k, b) in b.iter() {
            match a.get(k) {
                Some(a) => {
                    self.is_subtype(*a, at, *b, bt, SubtypeCheck::Covariant)
                        .with_context(|| format!("mismatched type for export `{k}`"))?;
                }
                None => match self.kind() {
                    SubtypeCheck::Covariant => {
                        bail!(
                            "instance is missing expected {kind} export `{k}`",
                            kind = b.desc(bt)
                        )
                    }
                    SubtypeCheck::Contravariant => {
                        bail!(
                            "instance has unexpected {kind} export `{k}`",
                            kind = b.desc(bt)
                        )
                    }
                },
            }
        }

        Ok(())
    }

    fn interface(&mut self, a: InterfaceId, at: &Types, b: InterfaceId, bt: &Types) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &at[a];
        let b = &bt[b];
        self.instance_exports(&a.exports, at, &b.exports, bt)
    }

    fn world(&mut self, a: WorldId, at: &Types, b: WorldId, bt: &Types) -> Result<()> {
        let a = &at[a];
        let b = &bt[b];

        // For component type subtyping, all exports in the other component
        // type must be present in this component type's exports (i.e. it
        // can export *more* than what this component type needs).
        // However, for imports, the check is reversed (i.e. it is okay
        // to import *less* than what this component type needs).
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => {
                    self.is_subtype(*b, bt, *a, at, SubtypeCheck::Contravariant)
                        .with_context(|| format!("mismatched type for import `{k}`"))?;
                }
                None => match self.kind() {
                    SubtypeCheck::Covariant => {
                        bail!(
                            "component is missing expected {kind} import `{k}`",
                            kind = a.desc(at)
                        )
                    }
                    SubtypeCheck::Contravariant => {
                        bail!(
                            "component has unexpected import {kind} `{k}`",
                            kind = a.desc(at)
                        )
                    }
                },
            }
        }

        for (k, b) in b.exports.iter() {
            match a.exports.get(k) {
                Some(a) => {
                    self.is_subtype(*a, at, *b, bt, SubtypeCheck::Covariant)
                        .with_context(|| format!("mismatched type for export `{k}`"))?;
                }
                None => match self.kind() {
                    SubtypeCheck::Covariant => {
                        bail!(
                            "component is missing expected {kind} export `{k}`",
                            kind = b.desc(bt)
                        )
                    }
                    SubtypeCheck::Contravariant => {
                        bail!(
                            "component has unexpected {kind} export `{k}`",
                            kind = b.desc(bt)
                        )
                    }
                },
            }
        }

        Ok(())
    }

    fn module(&mut self, a: ModuleTypeId, at: &Types, b: ModuleTypeId, bt: &Types) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &at[a];
        let b = &bt[b];

        // For module type subtyping, all exports in the other module
        // type must be present in expected module type's exports (i.e. it
        // can export *more* than what is expected module type needs).
        // However, for imports, the check is reversed (i.e. it is okay
        // to import *less* than what this module type needs).
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => {
                    self.kinds.push(SubtypeCheck::Contravariant);
                    let r = self.core_extern(b, bt, a, at).with_context(|| {
                        format!("mismatched type for import `{m}::{n}`", m = k.0, n = k.1)
                    });
                    self.kinds.pop();
                    r?;
                }
                None => match self.kind() {
                    SubtypeCheck::Covariant => bail!(
                        "module is missing expected {a} import `{m}::{n}`",
                        m = k.0,
                        n = k.1
                    ),
                    SubtypeCheck::Contravariant => {
                        bail!(
                            "module has unexpected {a} import `{m}::{n}`",
                            m = k.0,
                            n = k.1
                        )
                    }
                },
            }
        }

        for (k, b) in b.exports.iter() {
            match a.exports.get(k) {
                Some(a) => {
                    self.kinds.push(SubtypeCheck::Covariant);
                    let r = self
                        .core_extern(a, at, b, bt)
                        .with_context(|| format!("mismatched type for export `{k}`"));
                    self.kinds.pop();
                    r?;
                }
                None => match self.kind() {
                    SubtypeCheck::Covariant => {
                        bail!("module is missing expected {b} export `{k}`")
                    }
                    SubtypeCheck::Contravariant => {
                        bail!("module has unexpected {b} export `{k}`")
                    }
                },
            }
        }

        Ok(())
    }

    fn core_extern(&self, a: &CoreExtern, at: &Types, b: &CoreExtern, bt: &Types) -> Result<()> {
        macro_rules! limits_match {
            ($ai:expr, $am:expr, $bi:expr, $bm:expr) => {{
                $ai >= $bi
                    && match ($am, $bm) {
                        (Some(am), Some(bm)) => am <= bm,
                        (None, Some(_)) => false,
                        _ => true,
                    }
            }};
        }

        match (a, b) {
            (CoreExtern::Func(a), CoreExtern::Func(b)) => return self.core_func(a, at, b, bt),
            (
                CoreExtern::Table {
                    element_type: ae,
                    initial: ai,
                    maximum: am,
                },
                CoreExtern::Table {
                    element_type: be,
                    initial: bi,
                    maximum: bm,
                },
            ) => {
                if ae != be {
                    let (expected, _, found, _) = self.expected_found(ae, at, be, bt);
                    bail!("expected table element type {expected}, found {found}");
                }

                if !limits_match!(ai, am, bi, bm) {
                    bail!("mismatched table limits");
                }

                return Ok(());
            }
            (
                CoreExtern::Memory {
                    memory64: a64,
                    shared: ashared,
                    initial: ai,
                    maximum: am,
                },
                CoreExtern::Memory {
                    memory64: b64,
                    shared: bshared,
                    initial: bi,
                    maximum: bm,
                },
            ) => {
                if ashared != bshared {
                    bail!("mismatched shared flag for memories");
                }

                if a64 != b64 {
                    bail!("mismatched memory64 flag for memories");
                }

                if !limits_match!(ai, am, bi, bm) {
                    bail!("mismatched memory limits");
                }

                return Ok(());
            }
            (
                CoreExtern::Global {
                    val_type: avt,
                    mutable: am,
                },
                CoreExtern::Global {
                    val_type: bvt,
                    mutable: bm,
                },
            ) => {
                if am != bm {
                    bail!("mismatched mutable flag for globals");
                }

                if avt != bvt {
                    let (expected, _, found, _) = self.expected_found(avt, at, bvt, bt);
                    bail!("expected global type {expected}, found {found}");
                }

                return Ok(());
            }
            (CoreExtern::Tag(a), CoreExtern::Tag(b)) => return self.core_func(a, at, b, bt),
            _ => {}
        }

        let (expected, _, found, _) = self.expected_found(a, at, b, bt);
        bail!("expected {expected}, found {found}");
    }

    fn core_func(&self, a: &CoreFuncType, at: &Types, b: &CoreFuncType, bt: &Types) -> Result<()> {
        if a != b {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!("expected {expected}, found {found}");
        }

        Ok(())
    }

    fn value_type(&self, a: ValueType, at: &Types, b: ValueType, bt: &Types) -> Result<()> {
        let a = at.resolve_value_type(a);
        let b = bt.resolve_value_type(b);

        match (a, b) {
            (ValueType::Primitive(a), ValueType::Primitive(b)) => self.primitive(a, at, b, bt),
            (ValueType::Defined { id: a, .. }, ValueType::Defined { id: b, .. }) => {
                self.defined_type(a, at, b, bt)
            }
            (ValueType::Borrow(a), ValueType::Borrow(b))
            | (ValueType::Own(a), ValueType::Own(b)) => self.resource(a, at, b, bt),
            _ => {
                let (expected, expected_types, found, found_types) =
                    self.expected_found(&a, at, &b, bt);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.desc(expected_types),
                    found = found.desc(found_types)
                )
            }
        }
    }

    fn defined_type(
        &self,
        a: DefinedTypeId,
        at: &Types,
        b: DefinedTypeId,
        bt: &Types,
    ) -> std::result::Result<(), anyhow::Error> {
        if a == b {
            return Ok(());
        }

        let a = &at[a];
        let b = &bt[b];
        match (a, b) {
            (DefinedType::Tuple(a), DefinedType::Tuple(b)) => self.tuple(a, at, b, bt),
            (DefinedType::List(a), DefinedType::List(b)) => self
                .value_type(*a, at, *b, bt)
                .context("mismatched type for list element"),
            (DefinedType::Option(a), DefinedType::Option(b)) => self
                .value_type(*a, at, *b, bt)
                .context("mismatched type for option"),
            (
                DefinedType::Result {
                    ok: a_ok,
                    err: a_err,
                },
                DefinedType::Result {
                    ok: b_ok,
                    err: b_err,
                },
            ) => {
                self.result("ok", a_ok, at, b_ok, bt)?;
                self.result("err", a_err, at, b_err, bt)
            }
            (DefinedType::Variant(a), DefinedType::Variant(b)) => self.variant(a, at, b, bt),
            (DefinedType::Record(a), DefinedType::Record(b)) => self.record(a, at, b, bt),
            (DefinedType::Flags(a), DefinedType::Flags(b)) => self.flags(a, at, b, bt),
            (DefinedType::Enum(a), DefinedType::Enum(b)) => self.enum_type(a, at, b, bt),
            (DefinedType::Alias(_), _) | (_, DefinedType::Alias(_)) => {
                unreachable!("aliases should have been resolved")
            }
            _ => {
                let (expected, expected_types, found, found_types) =
                    self.expected_found(a, at, b, bt);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.desc(expected_types),
                    found = found.desc(found_types)
                )
            }
        }
    }

    fn result(
        &self,
        desc: &str,
        a: &Option<ValueType>,
        at: &Types,
        b: &Option<ValueType>,
        bt: &Types,
    ) -> Result<()> {
        match (a, b) {
            (None, None) => return Ok(()),
            (Some(a), Some(b)) => {
                return self
                    .value_type(*a, at, *b, bt)
                    .with_context(|| format!("mismatched type for result `{desc}`"))
            }
            (Some(_), None) | (None, Some(_)) => {
                // Handle mismatch below
            }
        }

        let (expected, _, found, _) = self.expected_found(a, at, b, bt);
        match (expected, found) {
            (None, None) | (Some(_), Some(_)) => unreachable!(),
            (Some(_), None) => bail!("expected an `{desc}` for result type"),
            (None, Some(_)) => bail!("expected no `{desc}` for result type"),
        }
    }

    fn enum_type(&self, a: &Enum, at: &Types, b: &Enum, bt: &Types) -> Result<()> {
        if a.0.len() != b.0.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected an enum type case count of {expected}, found a count of {found}",
                expected = expected.0.len(),
                found = found.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!("expected enum case {index} to be named `{expected}`, found an enum case named `{found}`");
        }

        Ok(())
    }

    fn flags(&self, a: &Flags, at: &Types, b: &Flags, bt: &Types) -> Result<()> {
        if a.0.len() != b.0.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected a flags type flag count of {expected}, found a count of {found}",
                expected = expected.0.len(),
                found = found.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!("expected flag {index} to be named `{expected}`, found a flag named `{found}`");
        }

        Ok(())
    }

    fn record(&self, a: &Record, at: &Types, b: &Record, bt: &Types) -> Result<()> {
        if a.fields.len() != b.fields.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected a record field count of {expected}, found a count of {found}",
                expected = expected.fields.len(),
                found = found.fields.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.fields.iter().zip(b.fields.iter()).enumerate() {
            if an != bn {
                let (expected, _, found, _) = self.expected_found(an, at, bn, bt);
                bail!("expected record field {i} to be named `{expected}`, found a field named `{found}`");
            }

            self.value_type(*a, at, *b, bt)
                .with_context(|| format!("mismatched type for record field `{bn}`"))?;
        }

        Ok(())
    }

    fn variant(&self, a: &Variant, at: &Types, b: &Variant, bt: &Types) -> Result<()> {
        if a.cases.len() != b.cases.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected a variant case count of {expected}, found a count of {found}",
                expected = expected.cases.len(),
                found = found.cases.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.cases.iter().zip(b.cases.iter()).enumerate() {
            if an != bn {
                let (expected, _, found, _) = self.expected_found(an, at, bn, bt);
                bail!("expected variant case {i} to be named `{expected}`, found a case named `{found}`");
            }

            match (a, b) {
                (None, None) => {}
                (Some(a), Some(b)) => self
                    .value_type(*a, at, *b, bt)
                    .with_context(|| format!("mismatched type for variant case `{bn}`"))?,
                _ => {
                    let (expected, _, found, _) = self.expected_found(a, at, b, bt);
                    match (expected, found) {
                        (None, None) | (Some(_), Some(_)) => unreachable!(),
                        (None, Some(_)) => {
                            bail!("expected variant case `{bn}` to be untyped, found a typed case")
                        }
                        (Some(_), None) => {
                            bail!("expected variant case `{bn}` to be typed, found an untyped case")
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn tuple(&self, a: &Vec<ValueType>, at: &Types, b: &Vec<ValueType>, bt: &Types) -> Result<()> {
        if a.len() != b.len() {
            let (expected, _, found, _) = self.expected_found(a, at, b, bt);
            bail!(
                "expected a tuple of size {expected}, found a tuple of size {found}",
                expected = expected.len(),
                found = found.len()
            );
        }

        for (i, (a, b)) in a.iter().zip(b.iter()).enumerate() {
            self.value_type(*a, at, *b, bt)
                .with_context(|| format!("mismatched type for tuple item {i}"))?;
        }

        Ok(())
    }

    fn primitive(&self, a: PrimitiveType, at: &Types, b: PrimitiveType, bt: &Types) -> Result<()> {
        // Note: currently subtyping for primitive types is done in terms of equality
        // rather than actual subtyping; the reason for this is that implementing
        // runtimes don't yet support more complex subtyping rules.
        if a != b {
            let (expected, _, found, _) = self.expected_found(&a, at, &b, bt);
            bail!(
                "expected {expected}, found {found}",
                expected = expected.desc(),
                found = found.desc()
            );
        }

        Ok(())
    }
}
