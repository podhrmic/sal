//! The built-in `prelude` context (a Rust rendering of the oracle's
//! `sal-prelude.scm`). Only names expressible in SAL concrete syntax are
//! included (the Scheme prelude also defines hyphenated names reachable
//! only from the lsal syntax).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use sal_syntax::ast::{Ident, SalContext};
use sal_syntax::span::Span;

use crate::env::{Entry, Instance};
use crate::types::SemType;

fn fun1(a: SemType, r: SemType) -> SemType {
    SemType::Fun(Box::new(a), Box::new(r))
}

fn fun2(a: SemType, b: SemType, r: SemType) -> SemType {
    SemType::Fun(Box::new(SemType::Tuple(vec![a, b])), Box::new(r))
}

pub fn build() -> Rc<Instance> {
    use SemType::*;
    let mut sym: HashMap<String, Entry> = HashMap::new();
    let mut order: Vec<String> = Vec::new();

    let add_type = |sym: &mut HashMap<String, Entry>,
                        order: &mut Vec<String>,
                        name: &str,
                        sem: SemType| {
        sym.insert(
            name.to_string(),
            Entry::Type {
                sem,
                scalar_elems: None,
                datatype: None,
                def: None,
            },
        );
        order.push(name.to_string());
    };
    let add_const = |sym: &mut HashMap<String, Entry>,
                         order: &mut Vec<String>,
                         name: &str,
                         sem: SemType| {
        sym.insert(name.to_string(), Entry::Const { sem, value: None });
        order.push(name.to_string());
    };

    // types
    for t in ["bool", "boolean", "BOOLEAN"] {
        add_type(&mut sym, &mut order, t, Bool);
    }
    add_type(&mut sym, &mut order, "any", Any);
    for t in [
        "number", "real", "REAL", "int", "integer", "INTEGER", "nat", "natural", "NATURAL",
        "nzint", "NZINTEGER", "nzreal", "NZREAL", "nznat", "char", "CHAR", "character",
    ] {
        add_type(&mut sym, &mut order, t, Number);
    }
    let string_ty = Tuple(vec![Number, Array(Box::new(Number), Box::new(Number))]);
    add_type(&mut sym, &mut order, "string", string_ty.clone());
    add_type(&mut sym, &mut order, "STRING", string_ty);

    // boolean constants (scalar elements of bool)
    for c in ["true", "false", "TRUE", "FALSE"] {
        add_const(&mut sym, &mut order, c, Bool);
    }

    // numeric operations reachable as identifiers
    add_const(&mut sym, &mut order, "max", fun2(Number, Number, Number));
    add_const(&mut sym, &mut order, "min", fun2(Number, Number, Number));
    add_const(&mut sym, &mut order, "exp", fun2(Number, Number, Number));
    add_const(&mut sym, &mut order, "nor", fun2(Bool, Bool, Bool));
    add_const(&mut sym, &mut order, "nand", fun2(Bool, Bool, Bool));
    add_const(&mut sym, &mut order, "xnor", fun2(Bool, Bool, Bool));
    add_const(&mut sym, &mut order, "real_pred?", fun1(Number, Bool));
    add_const(&mut sym, &mut order, "int_pred?", fun1(Number, Bool));
    add_const(&mut sym, &mut order, "nat_pred?", fun1(Number, Bool));
    add_const(
        &mut sym,
        &mut order,
        "up_to",
        fun1(Number, fun1(Number, Bool)),
    );
    add_const(
        &mut sym,
        &mut order,
        "below",
        fun1(Number, fun1(Number, Bool)),
    );
    add_const(
        &mut sym,
        &mut order,
        "above",
        fun1(Number, fun1(Number, Bool)),
    );

    // LTL operators
    for op in ["X", "G", "F"] {
        add_const(&mut sym, &mut order, op, fun1(Bool, Bool));
    }
    for op in ["W", "M", "R", "U"] {
        add_const(&mut sym, &mut order, op, fun2(Bool, Bool, Bool));
    }
    // CTL operators
    for op in ["EX", "AX", "EG", "AG", "EF", "AF"] {
        add_const(&mut sym, &mut order, op, fun1(Bool, Bool));
    }
    for op in ["EU", "AU", "ER", "AR"] {
        add_const(&mut sym, &mut order, op, fun2(Bool, Bool, Bool));
    }
    add_const(&mut sym, &mut order, "accepting", fun1(Bool, Bool));
    // ringset support + debugging
    for op in ["rpred", "rsucc", "dbg_print", "dbg_expr"] {
        add_const(&mut sym, &mut order, op, fun1(Any, Any));
    }

    let def = SalContext {
        name: Ident {
            name: "prelude".into(),
            span: Span::dummy(),
        },
        params: vec![],
        decls: vec![],
        span: Span::dummy(),
    };
    Rc::new(Instance {
        name: "prelude".into(),
        key: "prelude".into(),
        def: Rc::new(def),
        bindings: HashMap::new(),
        symbols: RefCell::new(sym),
        order: RefCell::new(order),
    })
}

