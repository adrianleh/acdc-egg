mod conditioneqwrapper;
mod conds;
mod vyzxlemma;

use crate::vyzxlemma::{ZXParam, generate_rw};
use egg::*;
use serde_derive::{Deserialize, Serialize};
use std::cmp::max;
use std::fmt::format;
use std::process::exit;

fn main() {
    let val_a = "(val n1 m1 a)";
    let val_b = "(val m1 o1 b)";
    let val_c = "(val n2 m2 c)";
    let val_d = "(val m2 o2 d)";
    let expr_str = format!("(stack (compose {} {}) (compose {} {}))", val_a, val_b, val_c, val_d);
    let goal = format!("(compose (stack {} {}) (stack {} {}))", val_a, val_c, val_b, val_d);
    let expr = expr_str.parse().unwrap();
    let mut rules =vyzx_rules();
    rules.extend(dim_rules());
    println!("{:?}", vyzx_rules::<ConstantFolding>());
    rules.extend(dep_rules());
    let mut runner = Runner::<ACDC, ConstantFolding, ()>::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&rules);
    for (i, node) in runner.egraph.nodes().iter().enumerate() {
        println!(
            "{}: {:?} -> {:?}",
            i,
            node,
            runner.egraph.id_to_node(runner.egraph.find(Id::from(i)))
        );
    }
    let expr_id = runner.egraph.add_expr(&expr);
    let res = runner.egraph.add_expr(&goal.parse().unwrap());
    println!(
        "{}",
        runner.explain_equivalence(&expr, &goal.parse().unwrap(),)
    );
    assert_eq!(runner.egraph.find(expr_id), runner.egraph.find(res),);
}

fn dim_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC>,
{
    vec![
        rewrite!("add-0"; "(+ 0 ?a)" => "?a"),
        rewrite!("mul-0"; "(* 0 ?a)" => "0"),
        rewrite!("mul-1"; "(* 1 ?a)" => "?a"),
        rewrite!("neg-0"; "(- 0)" => "0"),
    ]
}

fn dep_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC>,
{
    vec![
        rewrite!("deps"; "?a"=> {ForceDepArgs{}}),
        rewrite!("n-val"; "(dep1 (val ?a ?b ?c))" => "?a"),
        rewrite!("m-val"; "(dep2 (val ?a ?b ?c))" => "?b"),
        rewrite!("n-nwire"; "(dep1 (n_wire ?a))" => "?a"),
        rewrite!("m-nwire"; "(dep2 (n_wire ?a))" => "?a"),
        rewrite!("n-z"; "(dep1 (Z ?a ?b ?c))" => "?a"),
        rewrite!("m-z"; "(dep2 (Z ?a ?b ?c))" => "?b"),
        rewrite!("n-x"; "(dep1 (X ?a ?b ?c))" => "?a"),
        rewrite!("m-x"; "(dep2 (X ?a ?b ?c))" => "?b"),
        rewrite!("n-stack"; "(dep1 (stack ?a ?b))" => "(+ (dep1 ?a) (dep1 ?b))"),
        rewrite!("m-stack"; "(dep2 (stack ?a ?b))" => "(+ (dep2 ?a) (dep2 ?b))"),
        rewrite!("n-compose"; "(dep1 (compose ?a ?b))" => "(dep1 ?a)" if {
            ConditionEqual::new(
        "(dep2 ?a)".parse().unwrap(),
        "(dep1 ?b)".parse().unwrap())
        } if  {
            ConditionEqual::new(
        "(dep2 ?a)".parse().unwrap(),
        "(dep1 ?b)".parse().unwrap()) }
        ),
        rewrite!("m-compose"; "(dep2 (compose ?a ?b))" => "(dep2 ?b)" if {
            ConditionEqual::new(
        "(dep2 ?a)".parse().unwrap(),
        "(dep1 ?b)".parse().unwrap())
        }),
        rewrite!("n-cast"; "(dep1 (cast ?a ?b ?c))" => "(dep1 ?a)"),
        rewrite!("m-cast"; "(dep2 (cast ?a ?b ?c))" => "(dep2 ?c)"),
    ]
}
fn vyzx_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    let rws = vec![
        generate_rw(
        "stack-assoc",
        &ACDCZX::Stack(
            Box::from(ACDCZX::Stack(
                Box::from(ACDCZX::Var("a".to_string())),
                Box::from(ACDCZX::Var("b".to_string())),
            )),
            Box::from(ACDCZX::Var("c".to_string())),
        ),
        &ACDCZX::Stack(
            Box::from(ACDCZX::Var("a".to_string())),
            Box::from(ACDCZX::Stack(
                Box::from(ACDCZX::Var("b".to_string())),
                Box::from(ACDCZX::Var("c".to_string())),
            )),
        ),
        vec![
            ZXParam::new(
                ACDCDim::Var("n1".to_string()),
                ACDCDim::Var("m1".to_string()),
                "a",
            ),
            ZXParam::new(
                ACDCDim::Var("n2".to_string()),
                ACDCDim::Var("m2".to_string()),
                "b",
            ),
            ZXParam::new(
                ACDCDim::Var("n3".to_string()),
                ACDCDim::Var("m3".to_string()),
                "c",
            ),
        ],
        true,
    ),
        generate_rw(
            "stack-compose-dist",
            &ACDCZX::Stack(
                Box::from(ACDCZX::Compose(
                    Box::from(ACDCZX::Var("a".to_string())),
                    Box::from(ACDCZX::Var("b".to_string())),
                )),
                Box::from(ACDCZX::Compose(
                    Box::from(ACDCZX::Var("c".to_string())),
                    Box::from(ACDCZX::Var("d".to_string())),
                )),
            ),
            &ACDCZX::Compose(
                Box::from(ACDCZX::Stack(
                    Box::from(ACDCZX::Var("a".to_string())),
                    Box::from(ACDCZX::Var("c".to_string())),
                )),
                Box::from(ACDCZX::Stack(
                    Box::from(ACDCZX::Var("b".to_string())),
                    Box::from(ACDCZX::Var("d".to_string())),
                )),
            ),
            vec![
                ZXParam::new(
                    ACDCDim::Var("n1".to_string()),
                    ACDCDim::Var("m1".to_string()),
                    "a",
                ),
                ZXParam::new(
                    ACDCDim::Var("m1".to_string()),
                    ACDCDim::Var("o1".to_string()),
                    "b",
                ),
                ZXParam::new(
                    ACDCDim::Var("n2".to_string()),
                    ACDCDim::Var("m2".to_string()),
                    "c",
                ),
                ZXParam::new(
                    ACDCDim::Var("m2".to_string()),
                    ACDCDim::Var("o4".to_string()),
                    "d",
                ),
            ],
            true
        )
    ];
   rws.into_iter().flatten().collect()

}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ForceDepArgs {}
impl<T> Applier<ACDC, T> for ForceDepArgs
where
    T: Analysis<ACDC>,
{
    fn apply_one(
        &self,
        egraph: &mut EGraph<ACDC, T>,
        matched_id: Id,
        _: &Subst,
        _: Option<&PatternAst<ACDC>>,
        _: Symbol,
    ) -> Vec<Id> {
        let node = egraph.id_to_node(matched_id);
        if !is_zx_term(node, egraph) {
            return vec![];
        }
        let d1 = egraph.add(ACDC::Dep1(matched_id));
        let d2 = egraph.add(ACDC::Dep2(matched_id));
        vec![d1, d2]
    }
}

// (datatype ZX (Cast ZX Dim Dim) (Stack ZX ZX) (Compose ZX ZX) (Val String Dim Dim) (Z Dim Dim Dim) (nWire Dim))
define_language! {
    enum ACDC {
        Lit(i32),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "dep1" = Dep1(Id),
        "dep2" = Dep2(Id),
        Var(Symbol),
        "cast" = Cast([Id; 3]),
        "stack" = Stack([Id; 2]),
        "compose" = Compose([Id; 2]),
        "val" = Val([Id; 3]),
        "Z" = Z([Id; 3]),
        "X" = X([Id; 3]),
        "n_wire" = NWire(Id),
        Fn(Symbol, Vec<Id>),
    }
}

fn is_dim_term<T>(acdc: &ACDC, egraph: &EGraph<ACDC, T>) -> bool
where
    T: Analysis<ACDC>,
{
    match acdc {
        ACDC::Lit(_) => true,
        ACDC::Var(_) => true,
        ACDC::Add(_) => true,
        ACDC::Mul(_) => true,
        ACDC::Sub(_) => true,
        ACDC::Fn(_, ids) => ids
            .iter()
            .all(|id| is_dim_term(egraph.id_to_node(*id), egraph)),
        _ => false,
    }
}

fn is_zx_term<T>(acdc: &ACDC, egraph: &EGraph<ACDC, T>) -> bool
where
    T: Analysis<ACDC>,
{
    match acdc {
        ACDC::Cast(_) => true,
        ACDC::Stack(_) => true,
        ACDC::Compose(_) => true,
        ACDC::Val(_) => true,
        ACDC::Z(_) => true,
        ACDC::X(_) => true,
        ACDC::NWire(_) => true,
        ACDC::Fn(_, ids) => ids
            .iter()
            .all(|id| is_zx_term(egraph.id_to_node(*id), egraph)),
        _ => false,
    }
}

#[derive(Default, Clone)]
struct ConstantFolding;
impl Analysis<ACDC> for ConstantFolding {
    type Data = Option<i32>;

    fn make(egraph: &mut EGraph<ACDC, Self>, enode: &ACDC) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            ACDC::Lit(n) => Some(*n),
            ACDC::Add([a, b]) => Some(x(a)? + x(b)?),
            ACDC::Mul([a, b]) => Some(x(a)? * x(b)?),
            ACDC::Sub([a, b]) => Some(max(x(a)? - x(b)?, 0)),
            _ => None,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn modify(egraph: &mut EGraph<ACDC, Self>, id: Id) {
        if let Some(i) = egraph[id].data {
            let added = egraph.add(ACDC::Lit(i));
            egraph.union_trusted(id, added, "constant-folding");
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone, Serialize, Deserialize)]
pub enum ACDCDim {
    Lit(i32),
    Var(String),
    Add(Box<ACDCDim>, Box<ACDCDim>),
    Mul(Box<ACDCDim>, Box<ACDCDim>),
    Sub(Box<ACDCDim>, Box<ACDCDim>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ACDCZX {
    Var(String),
    Cast(ACDCDim, ACDCDim, Box<ACDCZX>),
    Val(ACDCDim, ACDCDim, String),
    Z(ACDCDim, ACDCDim, ACDCDim),
    X(ACDCDim, ACDCDim, ACDCDim),
    Stack(Box<ACDCZX>, Box<ACDCZX>),
    Compose(Box<ACDCZX>, Box<ACDCZX>),
    NWire(ACDCDim),
    Fn(String, Vec<ACDCZX>),
}

fn dim_to_acdc_dim_id<T>(dim_id: &Id, egraph: &EGraph<ACDC, T>) -> Option<ACDCDim>
where
    T: Analysis<ACDC>,
{
    let dim = egraph.id_to_node(*dim_id);
    match dim {
        ACDC::Lit(n) => Some(ACDCDim::Lit(*n)),
        ACDC::Var(s) => Some(ACDCDim::Var(s.to_string())),
        ACDC::Add([a, b]) => Some(ACDCDim::Add(
            Box::from(dim_to_acdc_dim_id(a, egraph)?),
            Box::from(dim_to_acdc_dim_id(b, egraph)?),
        )),
        ACDC::Mul([a, b]) => Some(ACDCDim::Mul(
            Box::from(dim_to_acdc_dim_id(a, egraph)?),
            Box::from(dim_to_acdc_dim_id(b, egraph)?),
        )),
        ACDC::Sub([a, b]) => Some(ACDCDim::Sub(
            Box::from(dim_to_acdc_dim_id(a, egraph)?),
            Box::from(dim_to_acdc_dim_id(b, egraph)?),
        )),
        _ => None,
    }
}

fn dim_to_acdc_insert_rec<T>(acdcdim: &ACDCDim, egraph: &mut EGraph<ACDC, T>) -> Id
where
    T: Analysis<ACDC>,
{
    match acdcdim {
        ACDCDim::Lit(n) => egraph.add(ACDC::Lit(*n)),
        ACDCDim::Var(s) => egraph.add(ACDC::Var(Symbol::from(s.clone()))),
        ACDCDim::Add(a, b) => {
            let a_id = dim_to_acdc_insert_rec(a, egraph);
            let b_id = dim_to_acdc_insert_rec(b, egraph);
            egraph.add(ACDC::Add([a_id, b_id]))
        }
        ACDCDim::Mul(a, b) => {
            let a_id = dim_to_acdc_insert_rec(a, egraph);
            let b_id = dim_to_acdc_insert_rec(b, egraph);
            egraph.add(ACDC::Mul([a_id, b_id]))
        }
        ACDCDim::Sub(a, b) => {
            let a_id = dim_to_acdc_insert_rec(a, egraph);
            let b_id = dim_to_acdc_insert_rec(b, egraph);
            egraph.add(ACDC::Sub([a_id, b_id]))
        }
    }
}
