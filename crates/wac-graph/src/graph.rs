use crate::encoding::{State, TypeEncoder};
use indexmap::IndexSet;
use petgraph::{algo::toposort, graphmap::DiGraphMap, Direction};
use semver::Version;
use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    ops::Index,
    str::FromStr,
};
use thiserror::Error;
use wac_types::{
    BorrowedKey, BorrowedPackageKey, ExternKind, ItemKind, Package, PackageKey, SubtypeCheck,
    SubtypeChecker, Type, Types,
};
use wasm_encoder::{ComponentTypeRef, TypeBounds};
use wasmparser::{
    names::{ComponentName, ComponentNameKind},
    BinaryReaderError, Validator, WasmFeatures,
};

struct PackagePath<'a> {
    package: &'a str,
    version: Option<Version>,
    segments: &'a str,
}

impl<'a> PackagePath<'a> {
    fn new(path: &'a str) -> GraphResult<Self> {
        let (package, segments) =
            path.split_once('/')
                .ok_or_else(|| Error::UnqualifiedPackagePath {
                    path: path.to_string(),
                })?;

        let (package, version) = package
            .split_once('@')
            .map(|(n, v)| (n, Version::from_str(v).map(Some).map_err(|e| (v, e))))
            .unwrap_or((package, Ok(None)));

        let version = version.map_err(|(version, error)| Error::InvalidPackageVersion {
            version: version.to_string(),
            error,
        })?;

        Ok(Self {
            package,
            version,
            segments,
        })
    }
}

/// Represents an error that can occur when working with a composition graph.
#[derive(Debug, Error)]
pub enum Error {
    /// The specified package path is not fully-qualified.
    #[error("package path `{path}` is not a fully-qualified package path")]
    UnqualifiedPackagePath {
        /// The path that was invalid.
        path: String,
    },
    /// The specified package version is invalid.
    #[error("package version `{version}` is not a valid: {error}")]
    InvalidPackageVersion {
        /// The version that was invalid.
        version: String,
        /// The error that occurred while parsing the package version.
        #[source]
        error: semver::Error,
    },
    /// The specified package has not been registered.
    #[error("package `{package}` has not been registered with the graph", package = BorrowedPackageKey::from_name_and_version(.package, .version.as_ref()))]
    UnknownPackage {
        /// The name of the unknown package.
        package: String,
        /// The version of the unknown package.
        version: Option<Version>,
    },
    /// The package does not export an item for the specified path.
    #[error("package `{package}` does not export an item for path `{path}`")]
    PackageMissingExport {
        /// The package with the missing export.
        package: String,
        /// The path that was missing.
        path: String,
    },
    /// The specified package identifier is invalid.
    #[error("the specified package identifier is invalid")]
    InvalidPackageId,
    /// The specified node identifier is invalid.
    #[error("the specified node identifier is invalid")]
    InvalidNodeId,
    /// The package is already registered in the graph.
    #[error("package `{key}` has already been registered in the graph")]
    PackageAlreadyRegistered {
        /// The key representing the already registered package
        key: PackageKey,
    },
    /// An extern name already exists in the graph.
    #[error("{kind} name `{name}` already exists in the graph")]
    ExternAlreadyExists {
        /// The kind of extern.
        kind: ExternKind,
        /// The name of the existing extern.
        name: String,
    },
    /// An invalid extern name was given.
    #[error("{kind} name `{name}` is not a valid extern name")]
    InvalidExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern.
        kind: ExternKind,
        /// The underlying validation error.
        #[source]
        source: anyhow::Error,
    },
    /// The node is not an instance.
    #[error("expected node to be an instance, but it is a {kind}")]
    NodeIsNotAnInstance {
        /// The node that is not an instance.
        node: NodeId,
        /// The kind of the node.
        kind: String,
    },
    /// The node is not an instantiation.
    #[error("the specified node is not an instantiation")]
    NodeIsNotAnInstantiation {
        /// The node that is not an instantiation.
        node: NodeId,
    },
    /// The instance does not export an item with the given name.
    #[error("instance does not have an export `{export}`")]
    InstanceMissingExport {
        /// The instance node that is missing the export.
        node: NodeId,
        /// The export that was missing.
        export: String,
    },
    /// The provided argument name is invalid.
    #[error("argument name `{name}` is not an import of package `{package}`")]
    InvalidArgumentName {
        /// The instantiation node that does not have the provided argument name.
        node: NodeId,
        /// The name of the invalid argument.
        name: String,
        /// The name of the package that does not have the argument.
        package: String,
    },
    /// The source type does not match the target argument type.
    #[error("mismatched instantiation argument `{name}`")]
    ArgumentTypeMismatch {
        /// The name of the argument.
        name: String,
        /// The source of the error.
        #[source]
        source: anyhow::Error,
    },
    /// The argument has already satisfied.
    #[error("argument `{name}` has already satisfied")]
    ArgumentAlreadySatisfied {
        /// The target node that already has the satisfied argument.
        node: NodeId,
        /// The name of the argument that is already satisfied.
        name: String,
    },
    /// The graph contains a cycle.
    #[error("the graph contains a cycle and cannot be encoded")]
    GraphContainsCycle {
        /// The node where the cycle was detected.
        node: NodeId,
    },
    /// The encoding of the graph failed validation.
    #[error("the encoding of the graph failed validation")]
    EncodingValidationFailure {
        /// The source of the validation error.
        #[source]
        source: BinaryReaderError,
    },
}

/// An alias for the result type used by the composition graph.
pub type GraphResult<T> = std::result::Result<T, Error>;

/// An identifier for a package in a composition graph.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct PackageId {
    /// The index into the graph's packages list.
    index: usize,
    /// The generation of the package.
    ///
    /// This is used to invalidate identifiers on package removal.
    generation: usize,
}

/// An identifier for a node in a composition graph.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeId {
    /// The index into the graph's node list.
    index: usize,
    /// The generation of the node.
    ///
    /// This is used to invalidate identifiers on node removal.
    generation: usize,
}

#[derive(Debug, Clone)]
enum NodeKind {
    /// The node is an import of an item.
    Import(String),
    /// The node is an instantiation of a package.
    Instantiation,
    /// The node is an alias of an export of an instance.
    Alias,
}

/// Represents a package registered with a composition graph.
#[derive(Debug, Clone)]
struct RegisteredPackage {
    /// The underlying package.
    package: Option<Package>,
    /// The nodes associated with the package.
    nodes: HashSet<NodeId>,
    /// The generation of the package.
    ///
    /// The generation is incremented each time a package is removed from the graph.
    ///
    /// This ensures referring package identifiers are invalidated when a package is removed.
    generation: usize,
}

impl RegisteredPackage {
    fn new(generation: usize) -> Self {
        Self {
            package: None,
            nodes: Default::default(),
            generation,
        }
    }
}

#[derive(Debug, Clone)]
struct NodeData<C> {
    /// The node kind.
    kind: NodeKind,
    /// The package associated with the node, if any.
    package: Option<PackageId>,
    /// The item kind of the node.
    item_kind: ItemKind,
    /// The optional name to associate with the node.
    ///
    /// When the graph is encoded, node names are recorded in a `names` custom section.
    name: Option<String>,
    /// The name to use for exporting the node.
    export: Option<String>,
    /// The aliased nodes from this node.
    aliases: HashMap<String, NodeId>,
    /// The context associated with the node.
    context: C,
}

impl<C> NodeData<C> {
    fn new(kind: NodeKind, item_kind: ItemKind, package: Option<PackageId>, context: C) -> Self {
        Self {
            kind,
            item_kind,
            package,
            name: None,
            export: None,
            aliases: Default::default(),
            context,
        }
    }
}

/// Represents a node in a composition graph.
#[derive(Debug, Clone)]
struct Node<C> {
    /// The data associated with the node.
    data: Option<NodeData<C>>,
    /// The generation of the node.
    ///
    /// The generation is incremented each time the node is removed from the graph.
    ///
    /// This ensures referring node identifiers are invalidated when a node is removed.
    generation: usize,
}

impl<C> Node<C> {
    fn new(generation: usize) -> Self {
        Self {
            data: None,
            generation,
        }
    }
}

/// Represents an edge in a composition graph.
#[derive(Debug, Clone)]
enum Edge {
    /// The edge is from an instance to an aliased exported item.
    ///
    /// The data is the index of the export on the source node.
    Alias(usize),
    /// The edge is from any node to an instantiation node.
    ///
    /// The set is import indexes on the target node that are satisfied by
    /// the source node.
    Argument(IndexSet<usize>),
}

/// Represents the type of an import.
#[derive(Debug, Copy, Clone)]
pub enum ImportType<'a> {
    /// The type is specified via a package path string.
    Path(&'a str),
    /// The type is specified as a type defined in the graph.
    GraphDefined(ItemKind),
    /// The type is specified as a type defined in a package.
    PackageDefined(PackageId, ItemKind),
}

/// Represents information about a node in a composition graph.
pub struct NodeInfo<'a, C> {
    /// The types collection for the node's item kind.
    pub types: &'a Types,
    /// The item kind of the node.
    pub kind: ItemKind,
    /// The context of the node.
    pub context: &'a C,
    /// The optional name of the node.
    pub name: Option<&'a str>,
    /// The aliases from this node.
    pub aliases: &'a HashMap<String, NodeId>,
    /// The export name of the node.
    ///
    /// If the node is not exported, this field will be `None`.
    pub export: Option<&'a str>,
}

/// Represents a composition graph.
///
/// A composition graph is a directed acyclic graph (DAG) that represents a WebAssembly composition.
///
/// Types may be defined directly in a composition graph or referenced from packages registered with
/// the graph.
///
/// There are three node types in the graph:
///
/// * an *import node* representing an imported item.
/// * an *instantiation node* representing an instantiation of a package.
/// * an *alias node* representing an alias of an exported item from an instance.
///
/// There are two edge types in the graph:
///
/// * an *alias edge* from an any node that is an instance to an alias node; alias edges are
///   implicitly added to the graph when an alias node is added.
/// * an *instantiation argument edge* from any node to an instantiation node; instantiation
///   argument edges contain a set of instantiation arguments satisfied on the target node
///   from the source node.
///
/// The type parameter `C` represents the context type to associate with each node in the graph.
///
/// A node's context may be retrieved by indexing the graph with a node identifier.
#[derive(Clone)]
pub struct CompositionGraph<C = ()> {
    /// The underlying graph data structure.
    graph: DiGraphMap<NodeId, Edge>,
    /// The import nodes of the graph.
    imports: HashMap<String, NodeId>,
    /// The set of used export names.
    exports: HashSet<String>,
    /// The map of package keys to package ids.
    package_map: HashMap<PackageKey, PackageId>,
    /// The registered packages.
    packages: Vec<RegisteredPackage>,
    /// The list of free entries in the packages list.
    free_packages: Vec<usize>,
    /// The nodes in the graph.
    nodes: Vec<Node<C>>,
    /// The list of free entries in the nodes list.
    free_nodes: Vec<usize>,
    /// The types that are directly defined by the graph.
    types: Types,
    /// The cache used for subtype checks.
    type_check_cache: HashSet<(ItemKind, ItemKind)>,
}

impl<C> CompositionGraph<C> {
    /// Creates a new composition graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Gets a reference to the type collection of the graph.
    pub fn types(&self) -> &Types {
        &self.types
    }

    /// Gets a mutable reference to the type collection of the graph.
    ///
    /// This type collection is used to define types directly in the graph.
    pub fn types_mut(&mut self) -> &mut Types {
        &mut self.types
    }

    /// Registers a package with the graph.
    ///
    /// A package can be used to create instantiations, but are not
    /// directly part of the graph.
    pub fn register_package(&mut self, package: wac_types::Package) -> GraphResult<PackageId> {
        let key = PackageKey::new(&package);
        if self.package_map.contains_key(&key) {
            return Err(Error::PackageAlreadyRegistered { key });
        }

        let id = self.alloc_package(package);
        let prev = self.package_map.insert(key, id);
        assert!(prev.is_none());
        Ok(id)
    }

    /// Unregisters a package from the graph.
    ///
    /// Any edges and nodes associated with the package are also removed.
    pub fn unregister_package(&mut self, id: PackageId) -> GraphResult<()> {
        if self.get_package(id).is_none() {
            return Err(Error::InvalidPackageId);
        }

        self.free_package(id);
        Ok(())
    }

    /// Gets a package that was registered with the graph.
    pub fn get_package(&self, id: PackageId) -> Option<&Package> {
        let PackageId { index, generation } = id;
        let entry = &self.packages[index];
        if entry.generation != generation {
            return None;
        }

        entry.package.as_ref()
    }

    /// Gets the registered package of the given package name and version.
    pub fn get_package_by_name(
        &self,
        name: &str,
        version: Option<&Version>,
    ) -> Option<(PackageId, &wac_types::Package)> {
        let key: BorrowedPackageKey<'_> = BorrowedPackageKey::from_name_and_version(name, version);
        let id = self.package_map.get(&key as &dyn BorrowedKey)?;
        Some((*id, self.packages[id.index].package.as_ref().unwrap()))
    }

    /// Adds an *import node* to the graph.
    ///
    /// If an import with the same name already exists, an error is returned.
    pub fn add_import_node(
        &mut self,
        name: impl Into<String>,
        ty: ImportType,
        context: C,
    ) -> GraphResult<NodeId> {
        let name = name.into();
        if self.imports.contains_key(&name) {
            return Err(Error::ExternAlreadyExists {
                kind: ExternKind::Import,
                name,
            });
        }

        // Ensure that the given import name is a valid extern name
        ComponentName::new(&name, 0).map_err(|e| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Import,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        })?;

        let (package, item_kind) = match ty {
            ImportType::Path(path) => {
                let path = PackagePath::new(path)?;

                let (id, package) = self
                    .get_package_by_name(path.package, path.version.as_ref())
                    .ok_or_else(|| Error::UnknownPackage {
                        package: path.package.to_string(),
                        version: path.version,
                    })?;

                let mut kind = None;
                for segment in path.segments.split('/') {
                    kind = match kind {
                        Some(ItemKind::Instance(id)) => {
                            package.types()[id].exports.get(segment).copied()
                        }
                        None => package.export(segment),
                        _ => None,
                    };

                    if kind.is_none() {
                        break;
                    }
                }

                let kind = kind.ok_or_else(|| Error::PackageMissingExport {
                    package: path.package.to_string(),
                    path: path.segments.to_string(),
                })?;

                (Some(id), kind)
            }
            ImportType::GraphDefined(kind) => (None, kind),
            ImportType::PackageDefined(package, kind) => (Some(package), kind),
        };

        let id = self.alloc_node(NodeData::new(
            NodeKind::Import(name.clone()),
            item_kind,
            package,
            context,
        ));
        self.graph.add_node(id);

        let prev = self.imports.insert(name, id);
        assert!(prev.is_none());

        Ok(id)
    }

    /// Adds an *instantiation node* to the graph.
    ///
    /// Initially the instantiation will have no connected arguments.
    ///
    /// Use `add_argument_edge` to add an edge between an argument and the
    /// instantiation.
    pub fn add_instantiation_node(&mut self, id: PackageId, context: C) -> GraphResult<NodeId> {
        let package = self.get_package(id).ok_or(Error::InvalidPackageId)?;
        let node = self.alloc_node(NodeData::new(
            NodeKind::Instantiation,
            ItemKind::Instance(package.instance_type()),
            Some(id),
            context,
        ));
        Ok(self.graph.add_node(node))
    }

    /// Adds an *alias node* to the graph.
    ///
    /// The provided node must be an instance and the export name must match an export
    /// of the instance.
    ///
    /// If an alias already exists for the export, the existing alias node will be returned.
    ///
    /// An implicit *alias edge* will be added from the instance to the alias node.
    pub fn add_alias_node(
        &mut self,
        source: NodeId,
        export: &str,
        context: C,
    ) -> GraphResult<NodeId> {
        let source_data = self
            .get_node(source)
            .ok_or(Error::InvalidNodeId)?
            .data
            .as_ref()
            .unwrap();

        if let Some(id) = source_data.aliases.get(export) {
            return Ok(*id);
        }

        // Ensure the source is an instance
        let types = self.node_types(source_data);
        let exports = match source_data.item_kind {
            ItemKind::Instance(id) => &types[id].exports,
            _ => {
                return Err(Error::NodeIsNotAnInstance {
                    node: source,
                    kind: source_data.item_kind.desc(types).to_string(),
                });
            }
        };

        // Ensure the export exists
        let (index, _, kind) =
            exports
                .get_full(export)
                .ok_or_else(|| Error::InstanceMissingExport {
                    node: source,
                    export: export.to_string(),
                })?;

        // Allocate the alias node
        let aliased = self.alloc_node(NodeData::new(
            NodeKind::Alias,
            *kind,
            source_data.package,
            context,
        ));

        let prev = self.nodes[source.index]
            .data
            .as_mut()
            .unwrap()
            .aliases
            .insert(export.to_string(), aliased);
        assert!(prev.is_none());

        self.graph.add_node(aliased);
        let prev = self.graph.add_edge(source, aliased, Edge::Alias(index));
        assert!(prev.is_none());
        Ok(aliased)
    }

    /// Gets the source node and export name of an alias node.
    ///
    /// Returns `None` if the given id is invalid or if the node is not an alias.
    pub fn get_alias_source(&self, node: NodeId) -> Option<(NodeId, &str)> {
        for (s, t, edge) in self.graph.edges_directed(node, Direction::Incoming) {
            assert_eq!(t, node);

            if let Edge::Alias(index) = edge {
                let data = self.get_node_data(s)?;
                match data.item_kind {
                    ItemKind::Instance(id) => {
                        let types = self.node_types(data);
                        let export = types[id].exports.get_index(*index).unwrap().0;
                        return Some((s, export));
                    }
                    _ => unreachable!("alias source should be an instance"),
                }
            }
        }

        None
    }

    // pub fn get_arguments(&self, node)

    /// Gets information about a node in the graph.
    ///
    /// Returns `None` if the specified node identifier is invalid.
    pub fn get_node_info(&self, id: NodeId) -> Option<NodeInfo<C>> {
        let data = self.get_node_data(id)?;

        Some(NodeInfo {
            types: self.node_types(data),
            kind: data.item_kind,
            context: &data.context,
            name: data.name.as_deref(),
            aliases: &data.aliases,
            export: data.export.as_deref(),
        })
    }

    /// Sets the name of a node in the graph.
    ///
    /// Node names are recorded in a `names` custom section when the graph is encoded.
    pub fn set_node_name(&mut self, id: NodeId, name: impl Into<String>) -> GraphResult<()> {
        let node = self.get_node_mut(id).ok_or(Error::InvalidPackageId)?;
        node.data.as_mut().unwrap().name = Some(name.into());
        Ok(())
    }

    /// Sets a node's export mark.
    ///
    /// Nodes marked for export will be exported from the encoded WebAssembly component.
    pub fn export_node(&mut self, id: NodeId, name: impl Into<String>) -> GraphResult<()> {
        let name = name.into();
        if self.exports.contains(&name) {
            return Err(Error::ExternAlreadyExists {
                kind: ExternKind::Export,
                name,
            });
        }

        let map_reader_err = |e: BinaryReaderError| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Export,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        };

        // Ensure that the given export name is a valid extern name
        match ComponentName::new(&name, 0).map_err(map_reader_err)?.kind() {
            ComponentNameKind::Hash(_)
            | ComponentNameKind::Url(_)
            | ComponentNameKind::Dependency(_) => {
                return Err(Error::InvalidExternName {
                    name: name.to_string(),
                    kind: ExternKind::Export,
                    source: anyhow::anyhow!("export name cannot be a hash, url, or dependency"),
                });
            }
            _ => {}
        };

        let node = self.get_node_mut(id).ok_or(Error::InvalidPackageId)?;
        node.data.as_mut().unwrap().export = Some(name.clone());

        let inserted = self.exports.insert(name);
        assert!(inserted);
        Ok(())
    }

    /// Clears a node's export mark.
    pub fn unexport_node(&mut self, id: NodeId) -> GraphResult<()> {
        let node = self.get_node_mut(id).ok_or(Error::InvalidPackageId)?;
        node.data.as_mut().unwrap().export = None;
        Ok(())
    }

    /// Removes a node from the graph.
    ///
    /// All incoming and outgoing edges of the node are also removed.
    ///
    /// If the node has aliases, the aliased nodes are also removed.
    ///
    /// Returns `true` if the node was removed, otherwise returns `false`.
    pub fn remove_node(&mut self, node: NodeId) -> bool {
        if !self.graph.remove_node(node) {
            return false;
        }

        self.free_node(node, false);
        true
    }

    /// Adds an *instantiation argument edge* to the graph.
    ///
    /// The target node must be an instantiation node.
    ///
    /// The source node must be type-compatible with the argument of the target node.
    ///
    /// The argument must be a valid import on the target and not already have an
    /// incoming edge from a different source node.
    pub fn add_argument_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        argument: &str,
    ) -> GraphResult<()> {
        fn add_edge<C>(
            graph: &mut CompositionGraph<C>,
            source: NodeId,
            target: NodeId,
            argument: &str,
            cache: &mut HashSet<(ItemKind, ItemKind)>,
        ) -> GraphResult<()> {
            // Ensure the target is an instantiation node
            let target_data = graph
                .get_node(target)
                .ok_or(Error::InvalidNodeId)?
                .data
                .as_ref()
                .unwrap();

            if let NodeKind::Instantiation = target_data.kind {
                return Err(Error::NodeIsNotAnInstantiation { node: target });
            }

            // Ensure the argument is a valid import of the target package
            let target_types = graph.node_types(target_data);
            let package = graph.packages[target_data.package.unwrap().index]
                .package
                .as_ref()
                .unwrap();
            let package_type = &package.types()[package.ty()];

            // Ensure the argument isn't already satisfied
            let argument_index =
                package_type
                    .imports
                    .get_index_of(argument)
                    .ok_or(Error::InvalidArgumentName {
                        node: target,
                        name: argument.to_string(),
                        package: package.name().to_string(),
                    })?;

            for (s, t, edge) in graph.graph.edges_directed(target, Direction::Incoming) {
                assert_eq!(t, target);
                match edge {
                    Edge::Alias(_) => {
                        unreachable!(
                            "incoming alias edges should not exist for instantiation nodes"
                        )
                    }
                    Edge::Argument(set) => {
                        if set.contains(&argument_index) {
                            if s == source {
                                return Ok(());
                            }

                            return Err(Error::ArgumentAlreadySatisfied {
                                node: target,
                                name: argument.to_string(),
                            });
                        }
                    }
                }
            }

            // Perform a subtype check on the source and target
            let source_data = graph.get_node_data(source).ok_or(Error::InvalidNodeId)?;
            let source_types = graph.node_types(source_data);

            let mut checker = SubtypeChecker::new(cache);
            checker
                .is_subtype(
                    source_data.item_kind,
                    source_types,
                    target_data.item_kind,
                    target_types,
                    SubtypeCheck::Covariant,
                )
                .map_err(|e| Error::ArgumentTypeMismatch {
                    name: argument.to_string(),
                    source: e,
                })?;

            // Finally, insert the argument edge
            if let Some(edge) = graph.graph.edge_weight_mut(source, target) {
                match edge {
                    Edge::Alias(_) => {
                        unreachable!("alias edges should not exist for instantiation nodes")
                    }
                    Edge::Argument(set) => {
                        let inserted = set.insert(argument_index);
                        assert!(inserted);
                    }
                }
            } else {
                let mut set = IndexSet::new();
                set.insert(argument_index);
                graph.graph.add_edge(source, target, Edge::Argument(set));
            }

            Ok(())
        }

        // Temporarily take ownership of the cache to avoid borrowing issues
        let mut cache = std::mem::take(&mut self.type_check_cache);
        let result = add_edge(self, source, target, argument, &mut cache);
        self.type_check_cache = cache;
        result
    }

    /// Removes an *instantiation argument edge* from the graph.
    ///
    /// The target node must be an instantiation.
    ///
    /// The argument must be a valid import on the target.
    ///
    /// If the argument is not connected to the source, then this function
    /// will be a no-op.
    pub fn remove_argument_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        argument: &str,
    ) -> GraphResult<()> {
        // Ensure the target is an instantiation node
        let target_data = self.get_node_data(target).ok_or(Error::InvalidNodeId)?;
        if let NodeKind::Instantiation = target_data.kind {
            return Err(Error::NodeIsNotAnInstantiation { node: target });
        }

        // Ensure the argument is a valid import of the target package
        let package = self.packages[target_data.package.unwrap().index]
            .package
            .as_ref()
            .unwrap();
        let package_type = &package.types()[package.ty()];

        let argument_index =
            package_type
                .imports
                .get_index_of(argument)
                .ok_or(Error::InvalidArgumentName {
                    node: target,
                    name: argument.to_string(),
                    package: package.name().to_string(),
                })?;

        // Finally remove the argument edge if a connection exists
        let remove_edge = if let Some(edge) = self.graph.edge_weight_mut(source, target) {
            match edge {
                Edge::Alias(_) => {
                    unreachable!("alias edges should not exist for instantiation nodes")
                }
                Edge::Argument(set) => {
                    set.swap_remove(&argument_index);
                    set.is_empty()
                }
            }
        } else {
            false
        };

        if remove_edge {
            self.graph.remove_edge(source, target);
        }

        Ok(())
    }

    /// Encodes the composition graph as a new WebAssembly component.
    ///
    /// An error will be returned if the graph contains a dependency cycle.
    pub fn encode(&self, options: EncodeOptions) -> GraphResult<Vec<u8>> {
        let bytes = CompositionGraphEncoder::new(self).encode(options)?;

        if options.validate {
            Validator::new_with_features(WasmFeatures {
                component_model: true,
                ..Default::default()
            })
            .validate_all(&bytes)
            .map_err(|e| Error::EncodingValidationFailure { source: e })?;
        }

        Ok(bytes)
    }

    /// Decodes a composition graph from the bytes of a WebAssembly component.
    pub fn decode(_data: &[u8]) -> GraphResult<CompositionGraph<()>> {
        todo!("decoding of composition graphs is not yet implemented")
    }

    fn alloc_package(&mut self, package: wac_types::Package) -> PackageId {
        let (index, entry) = if let Some(index) = self.free_packages.pop() {
            let entry = &mut self.packages[index];
            assert!(entry.package.is_none());
            (index, entry)
        } else {
            let index = self.packages.len();
            self.packages.push(RegisteredPackage::new(0));
            (index, &mut self.packages[index])
        };

        entry.package = Some(package);

        PackageId {
            index,
            generation: entry.generation,
        }
    }

    fn free_package(&mut self, id: PackageId) {
        debug_assert_eq!(
            self.packages[id.index].generation, id.generation,
            "invalid package identifier"
        );

        // Free all nodes associated with the package
        let nodes = std::mem::take(&mut self.packages[id.index].nodes);
        for node in nodes {
            let removed = self.graph.remove_node(node);
            assert!(removed);
            self.free_node(node, true);
        }

        // Remove the package from the package map
        let entry = &mut self.packages[id.index];
        let prev = self
            .package_map
            .remove(&BorrowedPackageKey::new(entry.package.as_ref().unwrap()) as &dyn BorrowedKey);
        assert!(prev.is_some());

        // Finally free the package
        *entry = RegisteredPackage::new(entry.generation.wrapping_add(1));
        self.free_packages.push(id.index);
    }

    fn alloc_node(&mut self, data: NodeData<C>) -> NodeId {
        let (index, node) = if let Some(index) = self.free_nodes.pop() {
            let node = &mut self.nodes[index];
            assert!(node.data.is_none());
            (index, node)
        } else {
            let index = self.nodes.len();
            self.nodes.push(Node::new(0));
            (index, &mut self.nodes[index])
        };

        let id = NodeId {
            index,
            generation: node.generation,
        };

        if let Some(package) = data.package {
            debug_assert_eq!(
                self.packages[package.index].generation, package.generation,
                "invalid package identifier"
            );

            let added = self.packages[package.index].nodes.insert(id);
            assert!(added);
        }

        node.data = Some(data);
        id
    }

    fn get_node(&self, id: NodeId) -> Option<&Node<C>> {
        let NodeId { index, generation } = id;
        let node = self.nodes.get(index)?;
        if node.generation != generation {
            return None;
        }

        assert!(node.data.is_some());
        Some(node)
    }

    fn get_node_mut(&mut self, id: NodeId) -> Option<&mut Node<C>> {
        let NodeId { index, generation } = id;
        let node = self.nodes.get_mut(index)?;
        if node.generation != generation {
            return None;
        }

        assert!(node.data.is_some());
        Some(node)
    }

    fn free_node(&mut self, id: NodeId, package_removed: bool) {
        debug_assert_eq!(
            self.nodes[id.index].generation, id.generation,
            "invalid node identifier"
        );

        // Free the node
        let next = self.nodes[id.index].generation.wrapping_add(1);
        let node = std::mem::replace(&mut self.nodes[id.index], Node::new(next));
        let data = node.data.unwrap();

        // If we're not freeing the node as a result of removing a package,
        // then remove it from the package and also recurse on any aliases.
        if !package_removed {
            // Remove the node from the package
            if let Some(pkg) = data.package {
                debug_assert_eq!(
                    self.packages[pkg.index].generation, pkg.generation,
                    "invalid package identifier"
                );

                let removed = self.packages[pkg.index].nodes.remove(&id);
                assert!(removed);
            }

            // Recursively remove any alias nodes from the graph
            for alias in data.aliases.values() {
                self.remove_node(*alias);
            }
        }

        // Remove any import entries
        if let NodeKind::Import(name) = data.kind {
            let removed = self.imports.remove(&name);
            assert!(removed.is_some());
        }

        // Finally, add the node to the free list
        self.free_nodes.push(id.index);
    }

    fn get_node_data(&self, id: NodeId) -> Option<&NodeData<C>> {
        self.get_node(id)?.data.as_ref()
    }

    fn node_types(&self, data: &NodeData<C>) -> &Types {
        data.package
            .and_then(|id| self.get_package(id))
            .map(|p| p.types())
            .unwrap_or(&self.types)
    }
}

// This is implemented *without* a `C: Default` constraint.
impl<C> Default for CompositionGraph<C> {
    fn default() -> Self {
        Self {
            graph: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
            package_map: Default::default(),
            packages: Default::default(),
            free_packages: Default::default(),
            nodes: Default::default(),
            free_nodes: Default::default(),
            types: Default::default(),
            type_check_cache: Default::default(),
        }
    }
}

impl<C> Index<PackageId> for CompositionGraph<C> {
    type Output = wac_types::Package;

    fn index(&self, id: PackageId) -> &Self::Output {
        self.get_package(id).expect("invalid package identifier")
    }
}

impl<C> Index<NodeId> for CompositionGraph<C> {
    type Output = C;

    fn index(&self, id: NodeId) -> &Self::Output {
        &self
            .get_node(id)
            .expect("node identifier is invalid")
            .data
            .as_ref()
            .unwrap()
            .context
    }
}

/// The options for encoding a composition graph.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
pub struct EncodeOptions {
    /// Whether or not to define instantiated components.
    ///
    /// If `false`, components will be imported instead.
    pub define_components: bool,

    /// Whether or not to validate the encoded output.
    pub validate: bool,
}

/// Used to encode a composition graph as a new WebAssembly component.
struct CompositionGraphEncoder<'a, C>(&'a CompositionGraph<C>);

impl<'a, C> CompositionGraphEncoder<'a, C> {
    fn new(graph: &'a CompositionGraph<C>) -> Self {
        Self(graph)
    }

    fn encode(self, options: EncodeOptions) -> GraphResult<Vec<u8>> {
        // TODO: do a pass on all of the instantiation nodes and merge auto imports

        // First toposort the graph
        let nodes = toposort(&self.0.graph, None)
            .map_err(|e| Error::GraphContainsCycle { node: e.node_id() })?;

        // Then encode each node in topological order
        let mut state = State::new();
        for node in nodes {
            let data = self.0.get_node_data(node).unwrap();
            let index = match &data.kind {
                NodeKind::Import(name) => self.import(&mut state, name, data),
                NodeKind::Instantiation => self.instantiation(&mut state, node, data, options),
                NodeKind::Alias => todo!(),
            };

            let prev = state.node_indexes.insert(node, index);
            assert!(prev.is_none());
        }

        Ok(std::mem::take(state.builder()).finish())
    }

    fn import(&self, state: &mut State<'a>, name: &str, data: &NodeData<C>) -> u32 {
        let types = self.0.node_types(data);

        log::debug!(
            "encoding import `{name}` ({kind})",
            kind = data.item_kind.desc(self.0.node_types(data))
        );

        let encoder = TypeEncoder::new(types);
        let ty = match data.item_kind {
            ItemKind::Type(ty) => {
                ComponentTypeRef::Type(TypeBounds::Eq(encoder.ty(state, ty, None)))
            }
            ItemKind::Func(id) => ComponentTypeRef::Func(encoder.ty(state, Type::Func(id), None)),
            ItemKind::Instance(id) => {
                // Check to see if the instance has already been imported
                // This may occur when an interface uses another
                if let Some(index) = state.current.instances.get(&id) {
                    log::debug!("skipping import of interface {id} as it was already imported with instance index {index}");
                    return *index;
                }

                ComponentTypeRef::Instance(encoder.ty(state, Type::Interface(id), None))
            }
            ItemKind::Component(id) => {
                ComponentTypeRef::Component(encoder.ty(state, Type::World(id), None))
            }
            ItemKind::Module(id) => {
                ComponentTypeRef::Module(encoder.ty(state, Type::Module(id), None))
            }
            ItemKind::Value(ty) => ComponentTypeRef::Value(encoder.value_type(state, ty)),
        };

        let index = state.builder().import(name, ty);
        log::debug!("import `{name}` encoded to {ty:?}");

        match data.item_kind {
            ItemKind::Type(ty) => {
                // Remap to the imported index
                state.current.type_indexes.insert(ty, index);
            }
            ItemKind::Instance(id) => {
                log::debug!("interface {id} is available for aliasing as instance index {index}");
                state.current.instances.insert(id, index);
            }
            _ => {}
        }

        index
    }

    fn instantiation(
        &self,
        state: &mut State<'a>,
        node: NodeId,
        data: &NodeData<C>,
        options: EncodeOptions,
    ) -> u32 {
        let package_id = data.package.expect("instantiation requires a package");
        let package = self.0.packages[package_id.index].package.as_ref().unwrap();

        log::debug!(
            "encoding instantiation of package `{package}`",
            package = package.name()
        );

        let component_index = if let Some(index) = state.packages.get(&package_id) {
            *index
        } else {
            let index = if options.define_components {
                state.builder().component_raw(package.bytes())
            } else {
                let encoder = TypeEncoder::new(package.types());
                let ty = encoder.component(state, package.ty());
                state.builder().import(
                    &Self::package_import_name(package),
                    ComponentTypeRef::Component(ty),
                )
            };

            state.packages.insert(package_id, index);
            index
        };

        let arguments = self
            .0
            .graph
            .edges_directed(node, Direction::Incoming)
            .flat_map(|(s, _, e)| match e {
                Edge::Alias(_) => unreachable!(),
                Edge::Argument(i) => i.iter().map(|i| {
                    let (name, _) = package.types()[package.ty()].imports.get_index(*i).unwrap();
                    (
                        name.as_str(),
                        self.0.get_node_data(s).unwrap().item_kind.into(),
                        state.node_indexes[&s],
                    )
                }),
            })
            .collect::<Vec<_>>();

        let index = state
            .builder()
            .instantiate(component_index, arguments.iter().copied());

        log::debug!(
            "instantiation of package `{package}` ({arguments:?}) encoded to instance index {index}",
            package = package.name(),
        );

        index
    }

    fn package_import_name(package: &Package) -> String {
        let mut name = String::new();

        write!(&mut name, "unlocked-dep=<{name}", name = package.name()).unwrap();
        if let Some(version) = package.version() {
            write!(&mut name, "@{{>={version}}}", version = version).unwrap();
        }

        write!(&mut name, ">").unwrap();
        name
    }
}
