//! Context environment: locating context source files, parsing them,
//! instantiating parameterized contexts, and building symbol tables.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use sal_syntax::ast::*;
use sal_syntax::parse_context;
use sal_syntax::printer;
use sal_syntax::span::Span;

use crate::error::SalError;
use crate::prelude;
use crate::types::{SemType, TypeId};

/// A binding for a context parameter in an instance.
#[derive(Debug, Clone)]
pub enum Binding {
    /// Type actual: semantic type plus the defining (instance, AST) pair —
    /// the flattener needs the syntax to recover concrete bounds.
    Type(SemType, Option<(Rc<Instance>, Type)>),
    /// Expression actual: kept as a closure (defining instance + AST) so
    /// it can be typed and, later, evaluated.
    Expr(Rc<Instance>, Expr, SemType),
}

/// What a name refers to inside a context instance.
#[derive(Debug, Clone)]
pub enum Entry {
    /// Declared or parameter type. `def` carries the definition for
    /// type-aliases so instantiation can look through them.
    Type {
        sem: SemType,
        /// For scalars: the element names in declaration order.
        scalar_elems: Option<Vec<String>>,
        /// For datatypes: constructors (name, accessor list).
        datatype: Option<Vec<(String, Vec<(String, SemType)>)>>,
        /// Syntactic definition (unresolved AST), used by the flattener.
        def: Option<TypeDef>,
    },
    /// Constant (including scalar elements, constructors, accessors,
    /// recognizers, context expression parameters). `value` is the
    /// defining AST if any.
    Const {
        sem: SemType,
        value: Option<Expr>,
    },
    Module {
        params: Vec<(String, SemType)>,
        /// (name, class, semtype) for every state variable of the module.
        state: Vec<(String, VarClass, SemType)>,
        def: Module,
        param_decls: Vec<VarDecl>,
    },
    Assertion {
        form: AssertionForm,
        body: AssertionExpr,
    },
    /// `c : CONTEXT = ctx{...}` alias.
    Ctx(Rc<Instance>),
}

/// An instantiated context: parsed definition + parameter bindings +
/// symbol table.
pub struct Instance {
    /// Context name (unqualified).
    pub name: String,
    /// Canonical instance key, e.g. `bakery{5, 15}`.
    pub key: String,
    pub def: Rc<SalContext>,
    pub bindings: HashMap<String, Binding>,
    /// Symbol table, filled lazily in declaration order.
    pub symbols: RefCell<HashMap<String, Entry>>,
    /// Declaration order (for scoping checks).
    pub order: RefCell<Vec<String>>,
}

impl std::fmt::Debug for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Instance({})", self.key)
    }
}

pub struct SalEnv {
    pub search_path: Vec<PathBuf>,
    parsed: RefCell<HashMap<String, Rc<SalContext>>>,
    instances: RefCell<HashMap<String, Rc<Instance>>>,
    pub prelude: Rc<Instance>,
}

impl SalEnv {
    pub fn new() -> Self {
        let mut search_path = vec![PathBuf::from(".")];
        if let Ok(p) = std::env::var("SALCONTEXTPATH") {
            for part in p.split(':').filter(|s| !s.is_empty()) {
                search_path.push(PathBuf::from(part));
            }
        }
        // library contexts shipped with the tools (e.g. ltllib), located
        // relative to the executable: <exe>/../lib (installed) or
        // <repo>/lib when running from target/{debug,release}
        if let Ok(exe) = std::env::current_exe() {
            for up in [1usize, 2, 3] {
                let mut d = exe.clone();
                for _ in 0..up {
                    d.pop();
                }
                let lib = d.join("lib");
                if lib.join("ltllib.sal").exists() {
                    search_path.push(lib);
                    break;
                }
            }
        }
        SalEnv {
            search_path,
            parsed: RefCell::new(HashMap::new()),
            instances: RefCell::new(HashMap::new()),
            prelude: prelude::build(),
        }
    }

    /// Parse a context from an explicit file path, checking the declared
    /// name against the file name (as the oracle does).
    pub fn parse_file(&self, path: &std::path::Path) -> Result<Rc<SalContext>, SalError> {
        let src = std::fs::read_to_string(path)
            .map_err(|_| SalError::global(format!("Cannot open file \"{}\".", path.display())))?;
        let file_label = path
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| path.display().to_string());
        let ast = parse_context(&src).map_err(|e| SalError::Parse {
            file: file_label,
            span: Span::new(e.pos, e.pos),
            msg: e.msg,
        })?;
        let stem = path
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_default();
        if ast.name.name != stem {
            return Err(SalError::semantic(
                &ast.name.name,
                ast.span,
                format!(
                    "Invalid context name \"{}\". The context declared name and the file name \
                     must be the same.",
                    stem
                ),
            ));
        }
        let rc = Rc::new(ast);
        self.parsed
            .borrow_mut()
            .insert(rc.name.name.clone(), rc.clone());
        Ok(rc)
    }

    /// Locate and parse a context by name via the search path.
    pub fn load_context(&self, name: &str) -> Result<Rc<SalContext>, SalError> {
        if let Some(c) = self.parsed.borrow().get(name) {
            return Ok(c.clone());
        }
        for dir in &self.search_path {
            let p = dir.join(format!("{}.sal", name));
            if p.exists() {
                return self.parse_file(&p);
            }
        }
        Err(SalError::global(format!(
            "Source file for the context \"{}\" was not found.",
            name
        )))
    }

    /// Get (or create) the instance of a context with the given bindings.
    pub fn instance(
        &self,
        def: Rc<SalContext>,
        bindings: HashMap<String, Binding>,
        key: String,
    ) -> Rc<Instance> {
        if let Some(i) = self.instances.borrow().get(&key) {
            return i.clone();
        }
        let inst = Rc::new(Instance {
            name: def.name.name.clone(),
            key: key.clone(),
            def,
            bindings,
            symbols: RefCell::new(HashMap::new()),
            order: RefCell::new(Vec::new()),
        });
        self.instances.borrow_mut().insert(key, inst.clone());
        inst
    }

    /// Instance for an unparameterized reference to a context (or one whose
    /// actuals have already been bound).
    pub fn plain_instance(&self, def: Rc<SalContext>) -> Rc<Instance> {
        let key = def.name.name.clone();
        self.instance(def, HashMap::new(), key)
    }
}

impl Default for SalEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// Canonical key for an instance given resolved actual bindings, e.g.
/// `bakery{5, 15}` — used only for caching/identity.
pub fn instance_key(name: &str, def: &SalContext, bindings: &HashMap<String, Binding>) -> String {
    if bindings.is_empty() {
        return name.to_string();
    }
    let mut parts = Vec::new();
    for p in &def.params {
        match p {
            CtxParam::Types(ids) => {
                for id in ids {
                    if let Some(Binding::Type(t, _)) = bindings.get(&id.name) {
                        parts.push(format!("{}", t));
                    }
                }
            }
            CtxParam::Vars(ids, _) => {
                for id in ids {
                    if let Some(Binding::Expr(_, e, _)) = bindings.get(&id.name) {
                        parts.push(printer::print_expr(e));
                    }
                }
            }
        }
    }
    format!("{}{{{}}}", name, parts.join(", "))
}

/// Nominal id for a type declared in an instance.
pub fn type_id(inst: &Instance, name: &str) -> TypeId {
    TypeId {
        ctx: inst.key.clone(),
        name: name.to_string(),
    }
}
