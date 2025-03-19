use crate::conds::{
    AndCondition, ConditionEqualWrap, FalseCondition, TrueCondition, to_condition_equal,
};
use crate::{ACDC, ACDCDim, ACDCZX, Hyp, ZXOrDim, simple_var};
use egg::{Analysis, ConditionalApplier, Language, Pattern, Rewrite, Symbol};
use serde_derive::{Deserialize, Serialize};
use std::any::Any;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::ops::Deref;
use std::slice::Iter;
use std::sync::Arc;

pub const REVERSE_LEMMA_SUFFIX: &str = "-**rev**";

fn find_all_symbols_in_expr_helper(dim: &ACDCDim, discovered_symbols: &mut HashSet<String>) {
    match dim {
        ACDCDim::Lit { lit: _ } => {}
        ACDCDim::Symbol { symbol: s } => {
            discovered_symbols.insert(s.clone());
        }
        ACDCDim::Add { a, b } => {
            find_all_symbols_in_expr_helper(a, discovered_symbols);
            find_all_symbols_in_expr_helper(b, discovered_symbols);
        }
        ACDCDim::Mul { a, b } => {
            find_all_symbols_in_expr_helper(a, discovered_symbols);
            find_all_symbols_in_expr_helper(b, discovered_symbols);
        }
        ACDCDim::Sub { a, b } => {
            find_all_symbols_in_expr_helper(a, discovered_symbols);
            find_all_symbols_in_expr_helper(b, discovered_symbols);
        }
        ACDCDim::Fn { fn_name: _, args } => {
            for arg in args {
                find_all_symbols_in_expr_helper(arg, discovered_symbols);
            }
        }
        _ => {}
    }
}
fn find_all_symbols_in_expr(dim: &ACDCDim) -> HashSet<String> {
    let mut discovered_symbols = HashSet::new();
    find_all_symbols_in_expr_helper(dim, &mut discovered_symbols);
    discovered_symbols
}
fn common_vars(a: &ACDCDim, b: &ACDCDim) -> HashSet<String> {
    let a_vars = find_all_symbols_in_expr(a);
    let b_vars = find_all_symbols_in_expr(b);
    a_vars.intersection(&b_vars).cloned().collect()
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct ACDCDimConstraintParam {
    param: ZXParam,
    pos: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ACDCDimConstraint {
    s: Symbol,

    l: ACDCDim,
    r: ACDCDim,
    pos: [ACDCDimConstraintParam; 2], // Position of the dep type constraints, in = 0, out =1 or None if its a direct value
    unsat: bool,
}

pub fn to_acdc_expr(dim: &ACDCDim) -> String {
    match dim {
        ACDCDim::Lit { lit } => lit.to_string(),
        ACDCDim::Symbol { symbol: s } => {
            // FIXME: Some symbols should not start with ?
            format!("?{}", s.to_string())
        }
        ACDCDim::Add { a, b } => format!("(+ {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Mul { a, b } => format!("(* {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Sub { a, b } => format!("(- {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Fn { fn_name, args } => format!(
            "(Fn {} {})",
            fn_name,
            args.iter()
                .map(to_acdc_expr)
                .collect::<Vec<String>>()
                .join(" ")
        ),
        ACDCDim::Dep1 { zx } => {
            format!("(dep1 {})", acdczx_to_pattern(&*zx))
        }
        ACDCDim::Dep2 { zx } => {
            format!("(dep2 {})", acdczx_to_pattern(&*zx))
        }
    }
}

fn replace_dim_subtree(dim: &ACDCDim, replace: &ACDCDim, with: &ACDCDim) -> ACDCDim {
    if (dim == replace) {
        return with.clone();
    }
    match dim {
        ACDCDim::Add { a, b } => {
            let a = replace_dim_subtree(a, replace, with);
            let b = replace_dim_subtree(b, replace, with);
            ACDCDim::Add {
                a: Box::new(a),
                b: Box::new(b),
            }
        }
        ACDCDim::Mul { a, b } => {
            let a = replace_dim_subtree(a, replace, with);
            let b = replace_dim_subtree(b, replace, with);
            ACDCDim::Mul {
                a: Box::new(a),
                b: Box::new(b),
            }
        }
        ACDCDim::Sub { a, b } => {
            let a = replace_dim_subtree(a, replace, with);
            let b = replace_dim_subtree(b, replace, with);
            ACDCDim::Sub {
                a: Box::new(a),
                b: Box::new(b),
            }
        }
        ACDCDim::Fn { fn_name, args } => {
            let args = args
                .iter()
                .map(|a| replace_dim_subtree(a, replace, with))
                .collect();
            ACDCDim::Fn {
                fn_name: fn_name.clone(),
                args,
            }
        }
        _ => dim.clone(),
    }
}

fn replace_dims_in_zx(zx: &ACDCZX, replace: &ACDCDim, with: &ACDCDim) -> ACDCZX {
    match zx {
        ACDCZX::Cast { n, m, zx } => {
            let n = replace_dim_subtree(n, replace, with);
            let m = replace_dim_subtree(m, replace, with);
            ACDCZX::Cast {
                n,
                m,
                zx: zx.clone(),
            }
        }
        ACDCZX::Val { n, m, val } => {
            let n = n.clone().map(|n| replace_dim_subtree(&n, replace, with));
            let m = m.clone().map(|m| replace_dim_subtree(&m, replace, with));
            ACDCZX::Val {
                n,
                m,
                val: val.clone(),
            }
        }
        ACDCZX::Z { n, m, alpha } => {
            let n = replace_dim_subtree(n, replace, with);
            let m = replace_dim_subtree(m, replace, with);
            ACDCZX::Z {
                n,
                m,
                alpha: alpha.clone(),
            }
        }
        ACDCZX::X { n, m, alpha } => {
            let n = replace_dim_subtree(n, replace, with);
            let m = replace_dim_subtree(m, replace, with);
            ACDCZX::X {
                n,
                m,
                alpha: alpha.clone(),
            }
        }
        ACDCZX::Stack { a, b } => {
            let a = replace_dims_in_zx(a, replace, with);
            let b = replace_dims_in_zx(b, replace, with);
            ACDCZX::Stack {
                a: Box::new(a),
                b: Box::new(b),
            }
        }
        ACDCZX::Compose { a, b } => {
            let a = replace_dims_in_zx(a, replace, with);
            let b = replace_dims_in_zx(b, replace, with);
            ACDCZX::Compose {
                a: Box::new(a),
                b: Box::new(b),
            }
        }
        ACDCZX::NWire { n } => {
            let n = replace_dim_subtree(n, replace, with);
            ACDCZX::NWire { n }
        }
        ACDCZX::Fn { fn_name, args } => {
            let args = args
                .iter()
                .map(|a| match a {
                    ZXOrDim::ZX(zx) => ZXOrDim::ZX(replace_dims_in_zx(zx, replace, with)),
                    ZXOrDim::Dim(dim) => ZXOrDim::Dim(replace_dim_subtree(dim, replace, with)),
                })
                .collect();
            ACDCZX::Fn {
                fn_name: fn_name.clone(),
                args,
            }
        }
    }
}

fn replace_param_with_dep(dim: &ACDCDim, param: &ZXParam) -> ACDCDim {
    let replaced_dim1 = replace_dim_subtree(
        dim,
        &param.n,
        &ACDCDim::Dep1 {
            zx: Box::new(simple_var(param.name.as_str())),
        },
    );
    replace_dim_subtree(
        &replaced_dim1,
        &param.m,
        &ACDCDim::Dep2 {
            zx: Box::new(simple_var(param.name.as_str())),
        },
    )
}

fn replace_param_with_dep_zx(zx: &ACDCZX, param: &ZXParam) -> ACDCZX {
    let replaced_dim_1 = replace_dims_in_zx(
        zx,
        &param.n,
        &ACDCDim::Dep1 {
            zx: Box::new(simple_var(param.name.as_str())),
        },
    );
    replace_dims_in_zx(
        &replaced_dim_1,
        &param.m,
        &ACDCDim::Dep2 {
            zx: Box::new(simple_var(param.name.as_str())),
        },
    )
}

const PLACEHOLDER: &str = "#####PLACEHOLDER######";
fn to_acdc_exprs_with_placeholders(constr: &ACDCDimConstraint) -> (String, String) {
    let constr_rep = format!("?{}", constr.s.as_str());
    (
        to_acdc_expr(&constr.l).replace(constr_rep.as_str(), PLACEHOLDER),
        to_acdc_expr(&constr.r).replace(constr_rep.as_str(), PLACEHOLDER), // TODO, this is super hacky but should work
    )
}

fn contains_symbol(dim: &ACDCDim, s: &String) -> bool {
    contains_any_symbol(dim, &HashSet::from([s.clone()]))
}

fn contains_any_symbol(dim: &ACDCDim, s: &HashSet<String>) -> bool {
    match dim {
        ACDCDim::Symbol { symbol } => s.contains(symbol),
        ACDCDim::Add { a, b } => contains_any_symbol(a, s) || contains_any_symbol(b, s),
        ACDCDim::Mul { a, b } => contains_any_symbol(a, s) || contains_any_symbol(b, s),
        ACDCDim::Sub { a, b } => contains_any_symbol(a, s) || contains_any_symbol(b, s),
        ACDCDim::Fn { fn_name: _, args } => args.iter().any(|a| contains_any_symbol(a, s)),
        _ => false, // Lit, Dep{1,2}
    }
}

fn invert(dim: &ACDCDim, s: &Symbol) -> ACDCDim {
    unimplemented!("invert");
    // solve for s in dim, where n can exists multiple times
}

fn contains_sub(dim: &ACDCDim) -> bool {
    match dim {
        ACDCDim::Add { a, b } => contains_sub(a) || contains_sub(b),
        ACDCDim::Mul { a, b } => contains_sub(a) || contains_sub(b),
        ACDCDim::Fn { fn_name: _, args } => args.iter().any(|a| contains_sub(a)),
        ACDCDim::Sub { a, b } => true,
        _ => false,
    }
}

// This function considers each acdc dim as a function of the common variables
// then it isolates the common variables and checks if that isolation is unsatisfiable
// The latter occurs, when a function, such as sub, doesn't have an inverse
// To solve this we would need much bigger reasoning machinery
fn gen_common_var_constraint(
    l: (ACDCDim, Option<u32>),
    r: (ACDCDim, Option<u32>),
    lp: &ZXParam,
    rp: &ZXParam,
) -> Vec<ACDCDimConstraint> {
    let l_dim = l.0;
    let r_dim = r.0;
    let l_idx = l.1;
    let r_idx = r.1;
    let common_vars = common_vars(&l_dim, &r_dim);
    if common_vars.is_empty() {
        return vec![];
    }

    let mut ret = Vec::new();
    for common_var in common_vars {
        ret.push(ACDCDimConstraint {
            s: Symbol::from(common_var.clone()),
            l: l_dim.clone(),
            r: r_dim.clone(),
            pos: [
                ACDCDimConstraintParam {
                    param: lp.clone(),
                    pos: l_idx,
                },
                ACDCDimConstraintParam {
                    param: rp.clone(),
                    pos: r_idx,
                },
            ],
            unsat: !(&l_dim == &r_dim
                && &l_dim
                    == &ACDCDim::Symbol {
                        symbol: common_var.clone(),
                    }), // Right now only allow when both are the same variable not in exprs
        });
    }
    ret
}

fn gen_common_var_constraints(zxparam1: &ZXParam, zxparam2: &ZXParam) -> Vec<ACDCDimConstraint> {
    let dim_pairs = get_all_dim_pairs(zxparam1, zxparam2);
    let mut constraints = Vec::new();
    for (l, r) in dim_pairs {
        constraints.append(
            gen_common_var_constraint((l.0, Some(l.1)), (r.0, Some(r.1)), zxparam1, zxparam2)
                .as_mut(),
        );
    }
    constraints
}

fn get_all_combinations<T>(a: &Vec<T>, b: &Vec<T>) -> Vec<(T, T)>
where
    T: Eq + Clone,
{
    let mut ret: Vec<(T, T)> = Vec::new();
    for i in a.iter() {
        for j in b.iter() {
            ret.push((i.clone(), j.clone()));
        }
    }
    ret
}

#[inline]
fn get_all_dim_pairs(
    zxparams1: &ZXParam,
    zxparams2: &ZXParam,
) -> Vec<((ACDCDim, u32), (ACDCDim, u32))> {
    vec![
        ((zxparams1.n.clone(), 0), (zxparams2.n.clone(), 0)),
        ((zxparams1.n.clone(), 0), (zxparams2.m.clone(), 1)),
        ((zxparams1.m.clone(), 1), (zxparams2.m.clone(), 1)),
    ]
}

fn get_all_combinations_zx_params(params: &Vec<ZXParam>) -> Vec<(ZXParam, ZXParam)> {
    let all_combs = get_all_combinations(&params, &params);
    all_combs
        .into_iter()
        .filter(|(a, b)| a.name != b.name)
        .collect()
}

fn is_symbol_from(dim: &ACDCDim, s: &HashSet<String>) -> Option<String> {
    match dim {
        ACDCDim::Symbol { symbol } => {
            if (s.contains(symbol)) {
                Some(symbol.to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

// TODO : Cleanup
fn get_param_to_symbol_constraints(
    params: &Vec<ZXParam>,
    discovered_symbols: &HashSet<String>,
) -> Vec<Constr> {
    let mut ret = Vec::new();
    for param in params {
        // TODO: generalize from eq to symbol

        let s = is_symbol_from(&param.n, discovered_symbols);
        if s.is_some() {
            let symbol = ACDCDim::Symbol {
                symbol: s.clone().unwrap(),
            };
            ret.extend(
                gen_common_var_constraint(
                    (symbol.clone(), None),
                    (param.n.clone(), Some(0)),
                    &ZXParam {
                        n: symbol.clone(),
                        m: symbol.clone(),
                        name: s.clone().unwrap(),
                    },
                    &param,
                )
                .iter()
                .map(|x| dim_constr_to_cond_eq(s.clone().unwrap().as_str(), &param.name, x)),
            );
        }
        let s = is_symbol_from(&param.m, discovered_symbols);
        if s.is_some() {
            let symbol = ACDCDim::Symbol {
                symbol: s.clone().unwrap(),
            };
            ret.extend(
                gen_common_var_constraint(
                    (symbol.clone(), None),
                    (param.m.clone(), Some(1)),
                    &ZXParam {
                        n: symbol.clone(),
                        m: symbol.clone(),
                        name: s.clone().unwrap(),
                    },
                    &param,
                )
                .iter()
                .map(|x| dim_constr_to_cond_eq(s.clone().unwrap().as_str(), &param.name, x)),
            );
        }
    }
    ret
}

fn get_all_conditions(params: &Vec<ZXParam>) -> Vec<Constr> {
    let all_combs = get_all_combinations_zx_params(params);
    let mut ret = Vec::new();
    for (zxparam1, zxparam2) in all_combs {
        let constraints = gen_common_var_constraints(&zxparam1, &zxparam2);
        for constr in constraints {
            let cond = dim_constr_to_cond_eq(
                zxparam1.name.as_str(),
                zxparam2.name.as_str(),
                &constr.clone(),
            );
            ret.push(cond);
        }
    }
    ret
}

#[derive(Debug, Clone)]
enum Constr {
    Eq(ConditionEqualWrap<ACDC>),
    False(FalseCondition),
}
#[inline(always)]
fn dep_type_str(idx: u32, name: &str) -> String {
    format!("(dep{} ?{})", idx, name)
}
fn dim_constr_to_cond_eq(l_name: &str, r_name: &str, constr: &ACDCDimConstraint) -> Constr {
    if constr.unsat {
        return Constr::False(FalseCondition {});
    }
    let exprs = to_acdc_exprs_with_placeholders(constr);

    let mut e0 = exprs.0;
    let mut e1 = exprs.1;
    // println!("{}", e0.as_str());
    // println!("{}", e1.as_str());
    if constr.pos[0].pos.is_some() {
        let dep_arg_l = dep_type_str(
            constr.pos[0].pos.unwrap() + 1,
            constr.pos[0].param.name.as_str(),
        );
        e0 = e0.replace(PLACEHOLDER, dep_arg_l.as_str());
    } else {
        e0 = e0.replace(PLACEHOLDER, format!("?{}", l_name).as_str());
    }
    if constr.pos[1].pos.is_some() {
        let dep_arg_r = dep_type_str(
            constr.pos[1].pos.unwrap() + 1,
            constr.pos[1].param.name.as_str(),
        );
        e1 = e1.replace(PLACEHOLDER, dep_arg_r.as_str());
    } else {
        e1 = e1.replace(PLACEHOLDER, format!("?{}", r_name).as_str());
    }
    // println!("{} {}", l_name, r_name);
    // println!("{}", e0.as_str());
    // println!("{}", e1.as_str());
    // println!(
    //     "{:?}",
    //     ConditionEqualWrap::<ACDC>::new(e0.as_str().parse().unwrap(), e1.as_str().parse().unwrap(), )
    // );
    Constr::Eq(ConditionEqualWrap::new(
        e0.as_str().parse().unwrap(),
        e1.as_str().parse().unwrap(),
    ))
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZXParam {
    n: ACDCDim,
    m: ACDCDim,
    name: String,
}
impl ZXParam {
    pub fn new(n: ACDCDim, m: ACDCDim, name: &str) -> Self {
        ZXParam {
            n,
            m,
            name: name.to_string(),
        }
    }
    pub fn from_dep_hyp(h: Hyp) -> Self {
        match h {
            Hyp::DepHyp { name, n, m } => ZXParam {
                n: n.clone(),
                m: m.clone(),
                name: name.clone(),
            },
            _ => panic!("Only dep hyp supported"),
        }
    }
}

pub fn zx_or_dim_pattern(zd: &ZXOrDim) -> String {
    match zd {
        ZXOrDim::ZX(zx) => acdczx_to_pattern(zx),
        ZXOrDim::Dim(dim) => to_acdc_expr(dim),
    }
}

pub fn acdczx_to_pattern(zx: &ACDCZX) -> String {
    match zx {
        ACDCZX::Val { val: s, n, m } => {
            if n.is_none() && m.is_none() {
                format!("?{}", s)
            } else {
                format!(
                    "(val {} {} {})",
                    s,
                    to_acdc_expr(&n.clone().unwrap()),
                    to_acdc_expr(&m.clone().unwrap())
                )
            }
        }
        ACDCZX::Cast { n, m, zx } => format!(
            "(cast {} {} {})",
            to_acdc_expr(n),
            to_acdc_expr(m),
            acdczx_to_pattern(zx)
        ),
        ACDCZX::Compose { a, b } => format!(
            "(compose {} {})",
            acdczx_to_pattern(a),
            acdczx_to_pattern(b)
        ),
        ACDCZX::NWire { n } => format!("(n_wire {})", to_acdc_expr(n)),
        ACDCZX::Stack { a, b } => {
            format!("(stack {} {})", acdczx_to_pattern(a), acdczx_to_pattern(b))
        }
        ACDCZX::X { n, m, alpha: a } => format!(
            "(X {} {} {})",
            to_acdc_expr(n),
            to_acdc_expr(m),
            to_acdc_expr(a)
        ),
        ACDCZX::Z { n, m, alpha: a } => format!(
            "(Z {} {} {})",
            to_acdc_expr(n),
            to_acdc_expr(m),
            to_acdc_expr(a)
        ),
        ACDCZX::Fn { fn_name, args } => format!(
            "(fn {} {})",
            fn_name,
            args.iter()
                .map(zx_or_dim_pattern)
                .collect::<Vec<String>>()
                .join(" ")
        ),
    }
}

pub fn collect_dim_symbols(zx: &ACDCZX) -> HashSet<String> {
    match zx {
        ACDCZX::Cast { n, m, zx } => {
            let mut ret = collect_dim_symbols(zx);
            ret.extend(find_all_symbols_in_expr(n));
            ret.extend(find_all_symbols_in_expr(m));
            ret
        }
        ACDCZX::Val { n, m, val } => {
            let mut ret = HashSet::new();
            if n.is_some() {
                ret.extend(find_all_symbols_in_expr(&n.clone().unwrap()));
            }
            if m.is_some() {
                ret.extend(find_all_symbols_in_expr(&m.clone().unwrap()));
            }
            ret
        }
        ACDCZX::Z { n, m, alpha } => {
            let mut ret = find_all_symbols_in_expr(n);
            ret.extend(find_all_symbols_in_expr(m));
            ret
        }
        ACDCZX::X { n, m, alpha } => {
            let mut ret = find_all_symbols_in_expr(n);
            ret.extend(find_all_symbols_in_expr(m));
            ret
        }
        ACDCZX::Stack { a, b } => {
            let mut ret = collect_dim_symbols(a);
            ret.extend(collect_dim_symbols(b));
            ret
        }
        ACDCZX::Compose { a, b } => {
            let mut ret = collect_dim_symbols(a);
            ret.extend(collect_dim_symbols(b));
            ret
        }
        ACDCZX::NWire { n } => find_all_symbols_in_expr(n),
        ACDCZX::Fn { fn_name, args } => {
            let mut ret = HashSet::new();
            for arg in args {
                match arg {
                    ZXOrDim::ZX(zx) => {
                        ret.extend(collect_dim_symbols(zx));
                    }
                    ZXOrDim::Dim(dim) => {
                        ret.extend(find_all_symbols_in_expr(dim));
                    }
                }
            }
            ret
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchedZXParam {
    matched: ACDCZX,
    name: String,
}
#[derive(Debug, Clone)]
pub struct Lemma<T>
where
    T: Analysis<ACDC> + Clone + 'static + Debug,
{
    name: String,
    lhs: Box<ACDCZX>,
    rhs: Box<ACDCZX>,
    params: Vec<ZXParam>,
    bidirectional: bool,
    rewrites: Vec<Rewrite<ACDC, T>>,
}

fn get_params_from_lemma(
    lemma_zx: &ACDCZX,
    matched: &ACDCZX,
    params: &Vec<ZXParam>,
) -> Vec<MatchedZXParam> {
    let mut param_names = HashSet::new();
    params.iter().for_each(|param| {
        param_names.insert(param.name.clone());
    });
    match (lemma_zx, matched) {
        (ACDCZX::Val { val, n, m }, r) => {
            if param_names.contains(val) {
                vec![MatchedZXParam {
                    matched: r.clone(),
                    name: val.clone(),
                }]
            } else {
                vec![]
            }
        }
        (ACDCZX::Stack { a: a1, b: b1 }, ACDCZX::Stack { a: a2, b: b2 }) => {
            let mut ret = Vec::new();
            ret.extend(get_params_from_lemma(a1, a2, params));
            ret.extend(get_params_from_lemma(b1, b2, params));
            ret
        }
        (ACDCZX::Compose { a: a1, b: b1 }, ACDCZX::Compose { a: a2, b: b2 }) => {
            let mut ret = Vec::new();
            ret.extend(get_params_from_lemma(a1, a2, params));
            ret.extend(get_params_from_lemma(b1, b2, params));
            ret
        }
        (
            ACDCZX::Cast {
                n: n1,
                m: m1,
                zx: zx1,
            },
            ACDCZX::Cast {
                n: n2,
                m: m2,
                zx: zx2,
            },
        ) => {
            if n1 != n2 || m1 != m2 {
                panic!("Cast arg mismatch");
            }
            get_params_from_lemma(zx1, zx2, params)
        }
        (
            ACDCZX::Fn {
                fn_name: fn_name1,
                args: args1,
            },
            ACDCZX::Fn {
                fn_name: fn_name2,
                args: args2,
            },
        ) => {
            if fn_name1 != fn_name2 {
                panic!("Fn name mismatch");
            }
            if args1.len() != args2.len() {
                panic!("Fn arg mismatch");
            }
            let mut ret = Vec::new();
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                match (a1, a2) {
                    (ZXOrDim::ZX(zx1), ZXOrDim::ZX(zx2)) => {
                        ret.extend(get_params_from_lemma(zx1, zx2, params));
                    }
                    (ZXOrDim::Dim(dim1), ZXOrDim::Dim(dim2)) => {
                        if dim1 != dim2 {
                            panic!("Fn arg mismatch");
                        }
                    }
                    _ => panic!("Fn arg type mismatch"),
                }
            }
            ret
        }

        (l, r) => {
            if std::mem::discriminant(l) == std::mem::discriminant(r) {
                vec![]
            } else {
                panic!("Found mismatch. Why did this match?")
            }
        }
    }
}

impl<T> Lemma<T>
where
    T: Analysis<ACDC> + Clone + 'static + Debug,
{
    pub fn get_rewrites(&self) -> Vec<Rewrite<ACDC, T>> {
        self.rewrites.clone()
    }
    pub fn get_rewrites_ref(&self) -> &Vec<Rewrite<ACDC, T>> {
        &self.rewrites
    }

    pub fn get_params(&self, node: &ACDCZX, rhs: bool) -> Vec<MatchedZXParam> {
        if (rhs && !self.bidirectional) {
            panic!("Can only use rhs get_params on bidirectional lemmas");
        }
        let base = if rhs {
            self.rhs.clone()
        } else {
            self.lhs.clone()
        };
        get_params_from_lemma(node, base.deref(), &self.params)
    }
}

pub fn generate_rw<T>(
    name: &str,
    lhs: &ACDCZX,
    rhs: &ACDCZX,
    params: Vec<ZXParam>,
    bidirectional: bool,
) -> Lemma<T>
where
    T: Analysis<ACDC> + Clone + 'static + Debug,
{
    let replaced_lhs = &params.iter().fold(lhs.clone(), |acc, param| {
        replace_param_with_dep_zx(&acc, &param)
    });
    let replaced_rhs = &params.iter().fold(rhs.clone(), |acc, param| {
        replace_param_with_dep_zx(&acc, &param)
    });
    // println!("------");
    // println!("{}", name);
    // println!("{:?} - {:?}", lhs, replaced_lhs);
    // println!("{:?} - {:?}", rhs, replaced_rhs);
    // println!("------");
    let mut all_symbols_in_exprs = collect_dim_symbols(replaced_lhs);
    all_symbols_in_exprs.extend(collect_dim_symbols(replaced_rhs));
    let l_pattern: Pattern<ACDC> = acdczx_to_pattern(replaced_lhs).as_str().parse().unwrap();
    let r_pattern: Pattern<ACDC> = acdczx_to_pattern(replaced_rhs).as_str().parse().unwrap();
    let mut conditions = get_all_conditions(&params);
    conditions.extend(get_param_to_symbol_constraints(
        &params,
        &all_symbols_in_exprs,
    ));
    let mut eq_conditions = Vec::new();
    // println!(
    //     "For {} generated {} conditions: {:?}",
    //     name,
    //     conditions.len(),
    //     conditions
    // );
    for cond in conditions {
        match cond {
            Constr::Eq(c) => eq_conditions.push(c),
            Constr::False(_) => {
                return Lemma {
                    name: name.to_string(),
                    lhs: Box::new(lhs.clone()),
                    rhs: Box::new(rhs.clone()),
                    params,
                    bidirectional,
                    rewrites: vec![],
                };
            } // If there is an unsatisfiable condition, we can't generate rewrites
        }
    }
    // let mut cond_r: ConditionalApplier<&ConditionEqual<ACDC>, _>;
    let cond: AndCondition<_, T> = eq_conditions.into_iter().fold(
        AndCondition {
            c1: Arc::new(TrueCondition {}),
            c2: Arc::new(TrueCondition {}),
        },
        |acc, c| AndCondition {
            c1: Arc::new(acc),
            c2: Arc::new(to_condition_equal(&c)),
        },
    );

    let r_cond: ConditionalApplier<AndCondition<ACDC, T>, Pattern<ACDC>> = ConditionalApplier {
        condition: cond.clone(),
        applier: r_pattern.clone(),
    };
    let rw = Rewrite::new(name, l_pattern.clone(), r_cond).unwrap();
    let rws;
    if !bidirectional {
        rws = vec![rw];
    } else {
        let l_cond: ConditionalApplier<AndCondition<ACDC, T>, Pattern<ACDC>> = ConditionalApplier {
            condition: cond,
            applier: l_pattern.clone(),
        };
        let rw_back = Rewrite::new(
            format!("{}{}", name, REVERSE_LEMMA_SUFFIX),
            r_pattern.clone(),
            l_cond,
        )
        .unwrap();
        rws = vec![rw, rw_back];
    }
    Lemma {
        name: name.to_string(),
        lhs: Box::new(lhs.clone()),
        rhs: Box::new(rhs.clone()),
        params,
        bidirectional,
        rewrites: rws,
    }
}

#[derive(Debug, Clone)]
pub struct LemmaContainer<T>
where
    T: Analysis<ACDC> + Clone + Debug + 'static,
{
    lemmas: HashMap<String, Box<Lemma<T>>>,
}

impl<T> LemmaContainer<T>
where
    T: Analysis<ACDC> + Clone + Debug + 'static,
{
    pub fn new(lemmas: Vec<Lemma<T>>) -> Self {
        let mut lemma_map = HashMap::new();
        for lemma in lemmas {
            lemma_map.insert(lemma.name.clone(), Box::new(lemma));
        }
        LemmaContainer { lemmas: lemma_map }
    }

    pub fn get(&self, name: &String) -> Option<Box<Lemma<T>>> {
        if name.ends_with(REVERSE_LEMMA_SUFFIX) {
            let lemma = self
                .lemmas
                .get(name.strip_suffix(REVERSE_LEMMA_SUFFIX).unwrap())
                .cloned();
            if (&lemma).is_none() {
                return None;
            }
            let lemma = lemma.unwrap();
            if (&lemma).bidirectional {
                // Only return if bidirectional and reverse
                return Some(lemma);
            }
            return None;
        }
        self.lemmas.get(name).cloned()
    }

    pub fn get_match_args(&self, name: String, candidate: &ACDCZX) -> Option<Vec<MatchedZXParam>> {
        let lemma = self.get(&name);
        if (&lemma).is_none() {
            return None;
        }
        let lemma = lemma.unwrap();
        let params = lemma.get_params(candidate, name.ends_with(REVERSE_LEMMA_SUFFIX));
        Some(params)
    }
}
