use std::collections::HashMap;

use indexmap::IndexMap;
use wac_types::{
    CoreExtern, DefinedType, DefinedTypeId, Enum, Flags, FuncResult, FuncTypeId, InterfaceId,
    ItemKind, ModuleTypeId, PrimitiveType, Record, ResourceId, Type, Types, UsedType, ValueType,
    Variant, WorldId,
};
use wasm_encoder::{
    Alias, ComponentBuilder, ComponentExportKind, ComponentOuterAliasKind, ComponentType,
    ComponentTypeEncoder, ComponentTypeRef, ComponentValType, CoreTypeEncoder, EntityType,
    GlobalType, InstanceType, MemoryType, ModuleType, TableType, TagKind, TagType, TypeBounds,
};

use crate::{NodeId, PackageId};

enum Encodable {
    Builder(ComponentBuilder),
    Instance(InstanceType),
    Component(ComponentType),
}

impl Encodable {
    fn type_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.type_count(),
            Encodable::Component(t) => t.type_count(),
            Encodable::Instance(t) => t.type_count(),
        }
    }

    fn instance_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.instance_count(),
            Encodable::Component(t) => t.instance_count(),
            Encodable::Instance(t) => t.instance_count(),
        }
    }

    fn core_type_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.core_type_count(),
            Encodable::Component(t) => t.core_type_count(),
            Encodable::Instance(t) => t.core_type_count(),
        }
    }

    fn ty(&mut self) -> ComponentTypeEncoder {
        match self {
            Encodable::Builder(t) => t.ty().1,
            Encodable::Instance(t) => t.ty(),
            Encodable::Component(t) => t.ty(),
        }
    }

    fn core_type(&mut self) -> CoreTypeEncoder {
        match self {
            Encodable::Builder(t) => t.core_type().1,
            Encodable::Instance(t) => t.core_type(),
            Encodable::Component(t) => t.core_type(),
        }
    }

    fn import_type(&mut self, name: &str, ty: ComponentTypeRef) {
        match self {
            Encodable::Component(t) => {
                t.import(name, ty);
            }
            Encodable::Builder(b) => {
                b.import(name, ty);
            }
            _ => unreachable!("expected a component type"),
        }
    }

    fn alias(&mut self, alias: Alias) {
        match self {
            Encodable::Builder(t) => {
                t.alias(alias);
            }
            Encodable::Instance(t) => {
                t.alias(alias);
            }
            Encodable::Component(t) => {
                t.alias(alias);
            }
        }
    }
}

impl Default for Encodable {
    fn default() -> Self {
        Self::Builder(Default::default())
    }
}

#[derive(Default)]
pub struct Scope<'a> {
    /// The map of types to their encoded indexes.
    pub type_indexes: IndexMap<Type, u32>,
    /// The map of imported instances in this scope.
    pub instances: IndexMap<InterfaceId, u32>,
    /// The map of import/export name to their alias indexes.
    type_aliases: IndexMap<&'a str, u32>,
    /// The map of resource names to their encoded indexes.
    resources: IndexMap<&'a str, u32>,
    encodable: Encodable,
}

#[derive(Default)]
pub struct State<'a> {
    scopes: Vec<Scope<'a>>,
    pub current: Scope<'a>,
    pub node_indexes: HashMap<NodeId, u32>,
    pub packages: HashMap<PackageId, u32>,
}

impl<'a> State<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn builder(&mut self) -> &mut ComponentBuilder {
        assert!(self.scopes.is_empty());
        match &mut self.current.encodable {
            Encodable::Builder(builder) => builder,
            _ => unreachable!("expected a builder"),
        }
    }

    fn push(&mut self, encodable: Encodable) {
        log::debug!("pushing new type scope");
        let prev = std::mem::replace(
            &mut self.current,
            Scope {
                encodable,
                ..Default::default()
            },
        );

        self.scopes.push(prev);
    }

    fn pop(&mut self) -> Encodable {
        log::debug!("popping type scope");
        let prev = std::mem::replace(&mut self.current, self.scopes.pop().unwrap());
        prev.encodable
    }

    fn used_type_index(&mut self, name: &str) -> Option<u32> {
        if let Some(index) = self.current.type_aliases.get(name) {
            return Some(*index);
        }

        if let Some(parent) = self.scopes.last() {
            if let Some(outer) = parent.type_aliases.get(name) {
                let index = self.current.encodable.type_count();
                log::debug!("encoding outer alias for `{name}` to type index {index}");
                self.current.encodable.alias(Alias::Outer {
                    kind: ComponentOuterAliasKind::Type,
                    count: 1,
                    index: *outer,
                });
                return Some(index);
            }
        }

        None
    }
}

pub struct TypeEncoder<'a>(&'a Types);

impl<'a> TypeEncoder<'a> {
    pub fn new(types: &'a Types) -> Self {
        Self(types)
    }

    pub fn ty(&self, state: &mut State<'a>, ty: Type, name: Option<&str>) -> u32 {
        if let Some(index) = state.current.type_indexes.get(&ty) {
            return *index;
        }

        if let Some(name) = name {
            if let Some(index) = state.used_type_index(name) {
                state.current.type_indexes.insert(ty, index);
                return index;
            }
        }

        let index = match ty {
            Type::Resource(_) => unreachable!(),
            Type::Func(id) => self.func_type(state, id),
            Type::Value(ValueType::Primitive(ty)) => Self::primitive(state, ty),
            Type::Value(ValueType::Borrow(id)) => self.borrow(state, id),
            Type::Value(ValueType::Own(id)) => self.own(state, id),
            Type::Value(ValueType::Defined { id, .. }) => self.defined(state, id),
            Type::Interface(id) => self.instance(state, id, false),
            Type::World(id) => self.component(state, id),
            Type::Module(id) => self.module(state, id),
        };

        state.current.type_indexes.insert(ty, index);
        index
    }

    fn func_type(&self, state: &mut State<'a>, id: FuncTypeId) -> u32 {
        log::debug!("encoding function {id}");
        let ty = &self.0[id];

        let params = ty
            .params
            .iter()
            .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
            .collect::<Vec<_>>();

        let results = match &ty.results {
            Some(FuncResult::Scalar(ty)) => vec![("", self.value_type(state, *ty))],
            Some(FuncResult::List(results)) => results
                .iter()
                .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
                .collect(),
            None => Vec::new(),
        };

        let index = state.current.encodable.type_count();
        let mut encoder = state.current.encodable.ty().function();
        encoder.params(params);

        match &ty.results {
            Some(FuncResult::Scalar(_)) => {
                encoder.result(results[0].1);
            }
            _ => {
                encoder.results(results);
            }
        }

        log::debug!("function {id} encoded to type index {index}");
        index
    }

    fn defined(&self, state: &mut State<'a>, id: DefinedTypeId) -> u32 {
        log::debug!("encoding defined type {id}");
        let ty = &self.0[id];
        let index = match ty {
            DefinedType::Tuple(types) => self.tuple(state, types),
            DefinedType::List(ty) => self.list(state, *ty),
            DefinedType::Option(ty) => self.option(state, *ty),
            DefinedType::Result { ok, err } => self.result(state, *ok, *err),
            DefinedType::Variant(v) => self.variant(state, v),
            DefinedType::Record(r) => self.record(state, r),
            DefinedType::Flags(f) => self.flags(state, f),
            DefinedType::Enum(e) => self.enum_type(state, e),
            DefinedType::Alias(ValueType::Primitive(ty)) => Self::primitive(state, *ty),
            DefinedType::Alias(ValueType::Borrow(id)) => self.borrow(state, *id),
            DefinedType::Alias(ValueType::Own(id)) => self.own(state, *id),
            DefinedType::Alias(ValueType::Defined { id, .. }) => self.defined(state, *id),
        };

        log::debug!("defined type {id} encoded to type index {index}");
        index
    }

    fn use_aliases(&self, state: &mut State<'a>, uses: &'a IndexMap<String, UsedType>) {
        state.current.type_aliases.clear();

        for (name, used) in uses {
            let interface = &self.0[used.interface];
            let instance = state.current.instances[&used.interface];
            let index = state.current.encodable.type_count();
            let export: &String = used.name.as_ref().unwrap_or(name);
            let kind = interface.exports.get(export).unwrap();
            state.current.encodable.alias(Alias::InstanceExport {
                instance,
                kind: ComponentExportKind::Type,
                name: export,
            });

            log::debug!(
                "aliased export `{export}` ({kind:?}) of instance {instance} to type index {index}"
            );

            state.current.type_aliases.insert(name, index);
        }
    }

    fn instance(&self, state: &mut State<'a>, id: InterfaceId, types_only: bool) -> u32 {
        log::debug!("encoding instance type for interface {id}");
        let interface = &self.0[id];
        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        // Encode any required aliases
        self.use_aliases(state, &interface.uses);
        state.push(Encodable::Instance(InstanceType::default()));

        // Otherwise, export all exports
        for (name, kind) in &interface.exports {
            match kind {
                ItemKind::Type(Type::Resource(_)) => {
                    self.export(state, name, *kind);
                }
                ItemKind::Type(ty) => {
                    let index = self.export(state, name, *kind);

                    // Map the encoded type index to any remapped types.
                    // if let Some(prev) = interface.remapped_types.get(ty) {
                    //     for ty in prev {
                    //         state.current.type_indexes.insert(*ty, index);
                    //     }
                    // }
                }
                _ => {
                    if !types_only {
                        self.export(state, name, *kind);
                    }
                }
            }
        }

        match state.pop() {
            Encodable::Instance(ty) => {
                let index = state.current.encodable.type_count();
                state.current.encodable.ty().instance(&ty);
                log::debug!("instance {id} encoded to type index {index}");
                index
            }
            _ => unreachable!(),
        }
    }

    pub fn component(&self, state: &mut State<'a>, id: WorldId) -> u32 {
        log::debug!("encoding component type for world {id}");
        let world = &self.0[id];

        state.push(Encodable::Component(ComponentType::default()));

        for used in world.uses.values() {
            self.import_deps(state, used.interface);
        }

        self.use_aliases(state, &world.uses);

        for (name, kind) in &world.imports {
            self.import(state, name, *kind);
        }

        for (name, kind) in &world.exports {
            self.export(state, name, *kind);
        }

        match state.pop() {
            Encodable::Component(ty) => {
                let index = state.current.encodable.type_count();
                state.current.encodable.ty().component(&ty);
                log::debug!("world {id} encoded to type index {index}");
                index
            }
            _ => unreachable!(),
        }
    }

    fn import_deps(&self, state: &mut State<'a>, id: InterfaceId) {
        if state.current.instances.contains_key(&id) {
            return;
        }

        let interface = &self.0[id];

        // Depth-first recurse on the dependencies of this interface
        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        let name = self.0[id]
            .id
            .as_deref()
            .expect("interface should have an id");

        log::debug!("encoding dependency on interface {id}");

        let index = self.instance(state, id, !state.scopes.is_empty());
        let import_index = state.current.encodable.instance_count();

        state
            .current
            .encodable
            .import_type(name, ComponentTypeRef::Instance(index));

        log::debug!("interface {id} is available for aliasing as instance {import_index}");

        state.current.instances.insert(id, import_index);
    }

    fn interface(&self, state: &mut State<'a>, id: InterfaceId) -> u32 {
        let interface = &self.0[id];
        log::debug!(
            "encoding interface definition of `{name}` ({id})",
            name = interface.id.as_deref().unwrap_or("")
        );
        assert!(state.scopes.is_empty());
        state.push(Encodable::Component(ComponentType::default()));

        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        let index = self.instance(state, id, false);

        Self::export_type(
            state,
            interface.id.as_deref().expect("interface must have an id"),
            ComponentTypeRef::Instance(index),
        );

        match state.pop() {
            Encodable::Component(ty) => {
                let (index, encoder) = state.builder().ty();
                encoder.component(&ty);
                log::debug!(
                    "encoded interface definition of `{id}` to type index {index}",
                    id = interface.id.as_deref().unwrap_or("")
                );
                index
            }
            _ => unreachable!(),
        }
    }

    fn world(&self, state: &mut State<'a>, id: WorldId) -> u32 {
        let world = &self.0[id];
        let world_id = world.id.as_deref().expect("world must have an id");

        log::debug!("encoding world definition of `{world_id}`");

        assert!(state.scopes.is_empty());
        state.push(Encodable::Component(ComponentType::default()));
        let index = self.component(state, id);
        Self::export_type(state, world_id, ComponentTypeRef::Component(index));

        match state.pop() {
            Encodable::Component(ty) => {
                let (index, encoder) = state.builder().ty();
                encoder.component(&ty);
                log::debug!("encoded world definition of `{world_id}` to type index {index}");
                index
            }
            _ => unreachable!(),
        }
    }

    fn module(&self, state: &mut State<'a>, id: ModuleTypeId) -> u32 {
        log::debug!("encoding module definition");
        let ty = &self.0[id];
        let mut encoded = ModuleType::new();

        for ((module, name), ext) in &ty.imports {
            let ty = self.entity_type(&mut encoded, ext);
            encoded.import(module, name, ty);
        }

        for (name, ext) in &ty.exports {
            let ty = self.entity_type(&mut encoded, ext);
            encoded.export(name, ty);
        }

        let index = state.current.encodable.core_type_count();
        state.current.encodable.core_type().module(&encoded);
        log::debug!("encoded module definition to type index {index}");
        index
    }

    fn entity_type(&self, encodable: &mut ModuleType, ext: &CoreExtern) -> EntityType {
        match ext {
            CoreExtern::Func(func) => {
                let index = encodable.type_count();
                encodable.ty().function(
                    func.params.iter().copied().map(Into::into),
                    func.results.iter().copied().map(Into::into),
                );
                EntityType::Function(index)
            }
            CoreExtern::Table {
                element_type,
                initial,
                maximum,
            } => EntityType::Table(TableType {
                element_type: (*element_type).into(),
                minimum: *initial,
                maximum: *maximum,
            }),
            CoreExtern::Memory {
                memory64,
                shared,
                initial,
                maximum,
            } => EntityType::Memory(MemoryType {
                minimum: *initial,
                maximum: *maximum,
                memory64: *memory64,
                shared: *shared,
            }),
            CoreExtern::Global { val_type, mutable } => EntityType::Global(GlobalType {
                val_type: (*val_type).into(),
                mutable: *mutable,
            }),
            CoreExtern::Tag(func) => {
                let index = encodable.type_count();
                encodable.ty().function(
                    func.params.iter().copied().map(Into::into),
                    func.results.iter().copied().map(Into::into),
                );
                EntityType::Tag(TagType {
                    kind: TagKind::Exception,
                    func_type_idx: index,
                })
            }
        }
    }

    pub fn value_type(&self, state: &mut State<'a>, ty: ValueType) -> ComponentValType {
        if let Some(index) = state.current.type_indexes.get(&Type::Value(ty)) {
            return ComponentValType::Type(*index);
        }

        let index = match ty {
            ValueType::Primitive(ty) => return ComponentValType::Primitive(ty.into()),
            ValueType::Borrow(id) => self.borrow(state, id),
            ValueType::Own(id) => self.own(state, id),
            ValueType::Defined { id, .. } => self.defined(state, id),
        };

        state.current.type_indexes.insert(Type::Value(ty), index);
        ComponentValType::Type(index)
    }

    fn primitive(state: &mut State<'a>, ty: PrimitiveType) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .primitive(ty.into());
        index
    }

    fn tuple(&self, state: &mut State<'a>, types: &[ValueType]) -> u32 {
        let types = types
            .iter()
            .map(|ty| self.value_type(state, *ty))
            .collect::<Vec<_>>();
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().tuple(types);
        index
    }

    fn list(&self, state: &mut State<'a>, ty: ValueType) -> u32 {
        let ty = self.value_type(state, ty);
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().list(ty);
        index
    }

    fn option(&self, state: &mut State<'a>, ty: ValueType) -> u32 {
        let ty = self.value_type(state, ty);
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().option(ty);
        index
    }

    fn result(&self, state: &mut State<'a>, ok: Option<ValueType>, err: Option<ValueType>) -> u32 {
        let ok = ok.map(|ty| self.value_type(state, ty));
        let err = err.map(|ty| self.value_type(state, ty));
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().result(ok, err);
        index
    }

    fn borrow(&self, state: &mut State<'a>, res: ResourceId) -> u32 {
        assert!(!state.scopes.is_empty());
        let res = state.current.resources[self.0[res].name.as_str()];
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().borrow(res);
        index
    }

    fn own(&self, state: &mut State<'a>, res: ResourceId) -> u32 {
        assert!(!state.scopes.is_empty());
        let res = state.current.resources[self.0[res].name.as_str()];
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().own(res);
        index
    }

    fn variant(&self, state: &mut State<'a>, variant: &Variant) -> u32 {
        let cases = variant
            .cases
            .iter()
            .map(|(n, ty)| (n.as_str(), ty.map(|ty| self.value_type(state, ty)), None))
            .collect::<Vec<_>>();

        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().variant(cases);
        index
    }

    fn record(&self, state: &mut State<'a>, record: &Record) -> u32 {
        let fields = record
            .fields
            .iter()
            .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
            .collect::<Vec<_>>();
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().record(fields);
        index
    }

    fn flags(&self, state: &mut State<'a>, flags: &Flags) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .flags(flags.0.iter().map(String::as_str));
        index
    }

    fn enum_type(&self, state: &mut State<'a>, e: &Enum) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .enum_type(e.0.iter().map(String::as_str));
        index
    }

    fn import(&self, state: &mut State<'a>, name: &str, kind: ItemKind) {
        if let ItemKind::Type(Type::Resource(id)) = kind {
            return self.import_resource(state, name, id);
        }

        let ty = kind.ty();
        log::debug!(
            "encoding import of `{name}` ({kind})",
            name = name,
            kind = kind.desc(self.0)
        );

        let index = self.ty(state, ty, Some(name));

        match kind {
            ItemKind::Type(_) => {
                let import_index = state.current.encodable.type_count();
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(index)));

                // Remap the type to the index of the imported item
                state.current.type_indexes.insert(ty, import_index);
            }
            ItemKind::Func(_) => {
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Func(index));
            }
            ItemKind::Instance(id) => {
                let import_index = state.current.encodable.instance_count();
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Instance(index));
                log::debug!("instance {import_index} is available for aliasing as interface {id}");
                state.current.instances.insert(id, import_index);
            }
            _ => unreachable!("expected only types, functions, and instance types"),
        }
    }

    fn import_resource(&self, state: &mut State<'a>, name: &str, id: ResourceId) {
        if state.current.resources.contains_key(name) {
            return;
        }

        log::debug!("encoding import of resource `{name}` ({id})");

        let resource = &self.0[id];
        let index = if let Some(outer) = state.used_type_index(name) {
            // This is an alias to an outer resource type
            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(outer)));

            log::debug!("encoded outer alias for resource `{name}` ({id}) to type index {index}");
            index
        } else if let Some(alias_of) = resource.alias_of {
            // This is an alias to another resource at the same scope
            let orig =
                state.current.resources[self.0[self.0.resolve_resource(alias_of)].name.as_str()];
            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(orig)));

            log::debug!("encoded import for resource `{name}` as type index {index} (alias of type index {orig})");
            index
        } else {
            // Otherwise, this is a new resource type, import with a subtype bounds
            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::SubResource));

            log::debug!("encoded import for resource `{name}` to type index {index}");
            index
        };

        state.current.resources.insert(&resource.name, index);
    }

    fn export(&self, state: &mut State<'a>, name: &str, kind: ItemKind) -> u32 {
        if let ItemKind::Type(Type::Resource(id)) = kind {
            return self.export_resource(state, name, id);
        }

        let ty = kind.ty();
        log::debug!(
            "encoding export of `{name}` ({kind})",
            name = name,
            kind = kind.desc(self.0)
        );

        let index = self.ty(state, ty, Some(name));
        let index = Self::export_type(
            state,
            name,
            match kind {
                ItemKind::Type(_) => ComponentTypeRef::Type(TypeBounds::Eq(index)),
                ItemKind::Func(_) => ComponentTypeRef::Func(index),
                ItemKind::Instance(_) => ComponentTypeRef::Instance(index),
                _ => unreachable!("expected only types, functions, and instance types"),
            },
        );

        // For types, remap to the index of the exported item
        if let ItemKind::Type(ty) = kind {
            state.current.type_indexes.insert(ty, index);
        }

        index
    }

    fn export_resource(&self, state: &mut State<'a>, name: &str, id: ResourceId) -> u32 {
        log::debug!("encoding export of resource `{name}` ({id})");

        if let Some(existing) = state.current.resources.get(name) {
            return *existing;
        }

        let resource = &self.0[id];
        let index = if let Some(outer) = state.used_type_index(name) {
            // This is an alias to an outer resource type
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::Eq(outer)));
            log::debug!("encoded outer alias for resource `{name}` ({id}) as type index {index}");
            index
        } else if let Some(alias_of) = resource.alias_of {
            // This is an alias to another resource at the same scope
            let index =
                state.current.resources[self.0[self.0.resolve_resource(alias_of)].name.as_str()];
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::Eq(index)));
            log::debug!("encoded alias for resource `{name}` ({id}) as type index {index}");
            index
        } else {
            // Otherwise, this is a new resource type, export with a subtype bounds
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::SubResource));
            log::debug!("encoded export of resource `{name}` ({id}) as type index {index}");
            index
        };

        state.current.resources.insert(&resource.name, index);
        index
    }

    fn export_type(state: &mut State<'a>, name: &str, ty: ComponentTypeRef) -> u32 {
        match &mut state.current.encodable {
            Encodable::Component(t) => {
                let index = t.type_count();
                t.export(name, ty);
                index
            }
            Encodable::Instance(t) => {
                let index = t.type_count();
                t.export(name, ty);
                index
            }
            Encodable::Builder(_) => unreachable!("expected a component or instance type"),
        }
    }
}
