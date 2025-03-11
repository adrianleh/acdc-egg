use crate::conds::{
    AndCondition, ConditionEqualWrap, FalseCondition, TrueCondition, to_condition_equal,
};
use crate::{ACDC, ACDCDim, ACDCZX, Hyp};
use egg::{Analysis, ConditionalApplier, Language, Pattern, Rewrite, Symbol};
use serde_derive::{Deserialize, Serialize};
use std::cmp::PartialEq;
use std::collections::HashSet;
use std::sync::Arc;

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
struct ACDCDimConstraintParam<'a> {
    param: ZXParam<'a>,
    pos: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ACDCDimConstraint<'a> {
    s: Symbol,

    l: ACDCDim,
    r: ACDCDim,
    pos: [ACDCDimConstraintParam<'a>; 2], // Position of the dep type constraints, in = 0, out =1
    unsat: bool,
}

fn to_acdc_expr(dim: &ACDCDim) -> String {
    match dim {
        ACDCDim::Lit { lit } => lit.to_string(),
        ACDCDim::Symbol { symbol: s } => s.to_string(),
        ACDCDim::Add { a, b } => format!("(+ {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Mul { a, b } => format!("(* {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Sub { a, b } => format!("(- {} {})", to_acdc_expr(a), to_acdc_expr(b)),
        ACDCDim::Fn { fn_name, args } => unimplemented!("Can't serialize fn, yet"),
    }
}

const PLACEHOLDER: &str = "#####PLACEHOLDER######";
fn to_acdc_exprs_with_placeholders(constr: &ACDCDimConstraint) -> (String, String) {
    (
        to_acdc_expr(&constr.l).replace(constr.s.as_str(), PLACEHOLDER),
        to_acdc_expr(&constr.r).replace(constr.s.as_str(), PLACEHOLDER), // TODO, this is super hacky but should work
    )
}

fn contains_symbol(dim: &ACDCDim, s: &String) -> bool {
    match dim {
        ACDCDim::Lit { lit: _ } => false,
        ACDCDim::Symbol { symbol } => symbol == s,
        ACDCDim::Add { a, b } => contains_symbol(a, s) || contains_symbol(b, s),
        ACDCDim::Mul { a, b } => contains_symbol(a, s) || contains_symbol(b, s),
        ACDCDim::Sub { a, b } => contains_symbol(a, s) || contains_symbol(b, s),
        ACDCDim::Fn { fn_name: _, args } => args.iter().any(|a| contains_symbol(a, s)),
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
fn gen_common_var_constraint<'a>(
    l: (ACDCDim, u32),
    r: (ACDCDim, u32),
    lp: &'a ZXParam<'a>,
    rp: &'a ZXParam<'a>,
) -> Vec<ACDCDimConstraint<'a>> {
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

fn gen_common_var_constraints<'a>(
    zxparam1: &'a ZXParam<'a>,
    zxparam2: &'a ZXParam<'a>,
) -> Vec<ACDCDimConstraint<'a>> {
    let dim_pairs = get_all_dim_pairs(zxparam1, zxparam2);
    let mut constraints = Vec::new();
    for (l, r) in dim_pairs {
        constraints.append(gen_common_var_constraint(l, r, zxparam1, zxparam2).as_mut());
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

fn get_all_combinations_zx_params(params: Vec<ZXParam>) -> Vec<(ZXParam, ZXParam)> {
    let all_combs = get_all_combinations(&params, &params);
    all_combs
        .into_iter()
        .filter(|(a, b)| a.name != b.name)
        .collect()
}

fn get_all_conditions(params: Vec<ZXParam>) -> Vec<Constr> {
    let all_combs = get_all_combinations_zx_params(params);
    let mut ret = Vec::new();
    for (zxparam1, zxparam2) in all_combs {
        let constraints = gen_common_var_constraints(&zxparam1, &zxparam2);
        for constr in constraints {
            let cond = dim_constr_to_cond_eq(zxparam1.name, zxparam2.name, &constr.clone());
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

    let dep_arg_l = dep_type_str(constr.pos[0].pos + 1, constr.pos[0].param.name);
    let dep_arg_r = dep_type_str(constr.pos[1].pos + 1, constr.pos[1].param.name);
    println!("{} - {}", dep_arg_l.as_str(), dep_arg_r.as_str());

    let e0 = exprs.0.replace(PLACEHOLDER, dep_arg_l.as_str());
    let e1 = exprs.1.replace(PLACEHOLDER, dep_arg_r.as_str());
    Constr::Eq(ConditionEqualWrap::new(
        e0.as_str().parse().unwrap(),
        e1.as_str().parse().unwrap(),
    ))
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZXParam<'a> {
    n: ACDCDim,
    m: ACDCDim,
    name: &'a str,
}
impl<'a> ZXParam<'a> {
    pub fn new(n: ACDCDim, m: ACDCDim, name: &'a str) -> Self {
        ZXParam { n, m, name }
    }
    pub fn from_dep_hyp(h: Hyp) -> Self {
        match h {
            Hyp::DepHyp { name, n, m } => ZXParam {
                n: n.clone(),
                m: m.clone(),
                name: name.as_str(),
            },
            _ => panic!("Only dep hyp supported"),
        }
    }
}

fn acdczx_to_pattern(zx: &ACDCZX) -> String {
    match zx {
        ACDCZX::Val { val: s, n: _, m: _ } => format!("?{}", s),
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
        ACDCZX::Fn {
            fn_name: _,
            args: _,
        } => unimplemented!("Functions on ZX diagrams not yet supported"),
    }
}

pub fn generate_rw<T>(
    name: &str,
    lhs: &ACDCZX,
    rhs: &ACDCZX,
    params: Vec<ZXParam>,
    bidirectional: bool,
) -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    let l_pattern: Pattern<ACDC> = acdczx_to_pattern(lhs).as_str().parse().unwrap();
    let r_pattern: Pattern<ACDC> = acdczx_to_pattern(rhs).as_str().parse().unwrap();
    let conditions = get_all_conditions(params);
    let mut eq_conditions = Vec::new();
    println!(
        "For {} generated {} conditions: {:?}",
        name,
        conditions.len(),
        conditions
    );
    for cond in conditions {
        match cond {
            Constr::Eq(c) => eq_conditions.push(c),
            Constr::False(_) => return vec![], // If there is an unsatisfiable condition, we can't generate rewrites
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
    if !bidirectional {
        return vec![rw];
    }
    let l_cond: ConditionalApplier<AndCondition<ACDC, T>, Pattern<ACDC>> = ConditionalApplier {
        condition: cond,
        applier: l_pattern.clone(),
    };
    let rw_back = Rewrite::new(format!("{}{}", name, "-rev"), r_pattern.clone(), l_cond).unwrap();
    vec![rw, rw_back]
}
