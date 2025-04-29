extern crate alloc;
extern crate core;

mod conditioneqwrapper;
mod conds;
mod conv;
mod diff;
mod problems;
mod recexpr;
mod serialize;
mod subtrees;
mod vyzxlemma;
mod vyzxrules;

use crate::serialize::{ACDCResult, SerFlatTermWrap};
use crate::vyzxlemma::{acdczx_to_pattern, LemmaContainer};
use crate::vyzxrules::{vyzx_rules, vyzx_rws};
use alloc::string::String;
use core::fmt::Debug;
use egg::*;
use serde_derive::{Deserialize, Serialize};
use std::cmp::max;
use std::io;
use std::io::Read;

fn main() {
    let mut json = String::new();
    io::stdin().read_to_string(&mut json).unwrap_or_else(|_| panic!("Failed to read input json")); // Read from stdin until EOF
    run_with_problem(json.as_str());
}

fn run_with_problem(json: &str) {
    let zx: Lemma = serde_json::from_str(json).expect("Failed to parse JSON");
    // let val_a = "(val n1 (* 1 m1) a)";
    // let val_b = "(val (+ 0 m1) o1 b)";
    // let val_c = "(val n2 m2 c)";
    // let val_d = "(val m2 o2 d)";
    // let n_wire_c = "(n_wire n2)";
    // let expr_str = format!(
    //     "(stack (compose {} {}) (compose {} {}))",
    //     val_a, val_b, val_c, val_d
    // );
    // let goal_str = format!(
    //     "(compose (stack {} (compose {} {})) (stack {} {}))",
    //     val_a, n_wire_c, val_c, val_b, val_d
    // );
    let expr = acdczx_to_pattern(&zx.prop.l).parse().unwrap();
    let goal = acdczx_to_pattern(&zx.prop.r).parse().unwrap();
    let lemmas = LemmaContainer::new(vyzx_rules());
    let mut rules = vyzx_rws();
    rules.extend(dim_rules());
    // println!("{:?}", vyzx_rules::<ConstantFolding>());
    rules.extend(dep_rules());
    let start_time = std::time::Instant::now();
    let mut runner = Runner::<ACDC, ConstantFolding, ()>::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .with_expr(&goal)
        // .with_iter_limit(15)
        .run(&rules);
    let end_time = std::time::Instant::now();
    eprintln!(
        "Run time: {}ms",
        end_time.duration_since(start_time).as_millis()
    );
    let expr_id = runner.egraph.add_expr(&expr);
    let res = runner.egraph.add_expr(&goal);
    assert_eq!(runner.egraph.find(expr_id), runner.egraph.find(res),);
    // for (i, node) in runner.egraph.nodes().iter().enumerate() {
    //     println!(
    //         "{}: {:?} -> {:?}",
    //         i,
    //         node,
    //         runner.egraph.id_to_node(runner.egraph.find(Id::from(i)))
    //     );
    // }

    eprintln!("Explaining...");
    let start_expl_time = std::time::Instant::now();
    let mut expl = runner.explain_equivalence(&expr, &goal);
    eprintln!("size {}", expl.get_tree_size());
    // eprintln!("Flattening...");
    let flat_explanations: Vec<_> = expl.make_flat_explanation().to_vec();
    let egraph = &runner.egraph;
    // eprintln!("Converting...");
    let mut wrap_exprs = vec![];
    let get_first_enode = |id| egraph[id].nodes[0].clone();
    let mut prev = runner
        .egraph
        .id_to_node(expr_id)
        .build_recexpr(get_first_enode);
    for ft in flat_explanations {
        let curr = ft.clone().get_recexpr();
        eprintln!("{:?}", curr.clone());
        wrap_exprs.push(SerFlatTermWrap::from(
            prev.clone(),
            curr.clone(),
            ft.clone(),
            egraph,
            &lemmas,
        ));
        prev = curr.clone();
    }
    let end_expl_time = std::time::Instant::now();
    let result = ACDCResult::new(
        wrap_exprs.clone(),
        end_expl_time.duration_since(start_expl_time).as_millis() as u64,
        end_time.duration_since(start_time).as_millis() as u64,
    );
    println!("{}", serde_json::to_string_pretty(&result).unwrap());

    eprintln!(
        "Run time: {}ms",
        end_time.duration_since(start_time).as_millis()
    );
    eprintln!(
        "Explain time: {}ms",
        end_expl_time.duration_since(start_expl_time).as_millis()
    );
}

fn dim_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC>,
{
    vec![
        rewrite!("simpl-add-0"; "(+ 0 ?a)" => "?a"),
        rewrite!("simpl-mul-0"; "(* 0 ?a)" => "0"),
        rewrite!("simpl-mul-1"; "(* 1 ?a)" => "?a"),
        rewrite!("simpl-neg-0"; "(- ?a 0)" => "?a"),
        // rewrite!("IZR"; "(fn IZR ?a)" => "?a"),
        // rewrite!("Rplus"; "(fn Rplus ?a ?b)" => "(+ ?a ?b)"),
    ]
}

fn dep_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC>,
{
    vec![
        rewrite!("deps"; "?a"=> {ForceDepArgs{}}), // Forces a Dep1 and Dep2 for all ZX terms
        rewrite!("dep-n-val"; "(dep1 (val ?a ?b ?c))" => "?a"),
        rewrite!("dep-m-val"; "(dep2 (val ?a ?b ?c))" => "?b"),
        rewrite!("dep-n-nwire"; "(dep1 (n_wire ?a))" => "?a"),
        rewrite!("dep-m-nwire"; "(dep2 (n_wire ?a))" => "?a"),
        rewrite!("dep-n-z"; "(dep1 (Z ?a ?b ?c))" => "?a"),
        rewrite!("dep-m-z"; "(dep2 (Z ?a ?b ?c))" => "?b"),
        rewrite!("dep-n-x"; "(dep1 (X ?a ?b ?c))" => "?a"),
        rewrite!("dep-m-x"; "(dep2 (X ?a ?b ?c))" => "?b"),
        rewrite!("dep-n-stack"; "(dep1 (stack ?a ?b))" => "(+ (dep1 ?a) (dep1 ?b))"),
        rewrite!("dep-m-stack"; "(dep2 (stack ?a ?b))" => "(+ (dep2 ?a) (dep2 ?b))"),
        rewrite!("dep-n-compose"; "(dep1 (compose ?a ?b))" => "(dep1 ?a)"),
        rewrite!("dep-m-compose"; "(dep2 (compose ?a ?b))" => "(dep2 ?b)"),
        rewrite!("dep-n-cast"; "(dep1 (cast ?a ?b ?c))" => "(dep1 ?a)"),
        rewrite!("dep-m-cast"; "(dep2 (cast ?a ?b ?c))" => "(dep2 ?b)"),
    ]
}
// if {
//             ConditionEqual::new(
//         "(dep2 ?a)".parse().unwrap(),
//         "(dep1 ?b)".parse().unwrap())
//         }
#[inline(always)]
fn simple_var(s: &str) -> ACDCZX {
    ACDCZX::Val {
        n: None,
        m: None,
        val: s.to_string(),
    }
}

#[inline(always)]
fn simple_symbol(s: &str) -> ACDCDim {
    ACDCDim::Symbol {
        symbol: s.to_string(),
    }
}

#[inline(always)]
fn simple_lit(lit: i32) -> ACDCDim {
    ACDCDim::Lit { lit }
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
        // nats
        Lit(i32),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        // dep args
        "dep1" = Dep1(Id),
        "dep2" = Dep2(Id),
        // nat or zx
        Var(Symbol),
        // zx
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

#[derive(Default, Debug, Clone)]
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
        merge_min(to, from)
    }

    fn modify(egraph: &mut EGraph<ACDC, Self>, id: Id) {
        if let Some(i) = egraph[id].data {
            let added = egraph.add(ACDC::Lit(i));
            egraph.union_trusted(id, added, "simpl");
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ACDCDim {
    #[serde(rename = "const")]
    Lit {
        lit: i32,
    },
    #[serde(rename = "symbol")]
    Symbol {
        symbol: String,
    },
    #[serde(rename = "+")]
    Add {
        a: Box<ACDCDim>,
        b: Box<ACDCDim>,
    },
    #[serde(rename = "*")]
    Mul {
        a: Box<ACDCDim>,
        b: Box<ACDCDim>,
    },
    #[serde(rename = "-")]
    Sub {
        a: Box<ACDCDim>,
        b: Box<ACDCDim>,
    },
    #[serde(rename = "fn")]
    Fn {
        #[serde(rename = "fn")]
        fn_name: String,
        args: Vec<ACDCDim>,
    },
    Dep1 {
        zx: Box<ACDCZX>,
    }, // TODO: Implement translation when dealing with ingestion from serialized strings
    Dep2 {
        zx: Box<ACDCZX>,
    },
}
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(untagged)]
pub enum ZXOrDim {
    ZX(ACDCZX),
    Dim(ACDCDim),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ACDCZX {
    #[serde(rename = "cast")]
    Cast {
        n: ACDCDim,
        m: ACDCDim,
        zx: Box<ACDCZX>,
    },
    #[serde(rename = "symbol")]
    Val {
        n: Option<ACDCDim>,
        m: Option<ACDCDim>,
        #[serde(rename = "symbol")]
        val: String,
    },
    #[serde(rename = "z")]
    Z {
        n: ACDCDim,
        m: ACDCDim,
        alpha: ACDCDim,
    },
    #[serde(rename = "x")]
    X {
        n: ACDCDim,
        m: ACDCDim,
        alpha: ACDCDim,
    },
    #[serde(rename = "stack")]
    Stack { a: Box<ACDCZX>, b: Box<ACDCZX> },
    #[serde(rename = "compose")]
    Compose { a: Box<ACDCZX>, b: Box<ACDCZX> },
    #[serde(rename = "n_wire")]
    NWire { n: ACDCDim },
    #[serde(rename = "fn")]
    Fn {
        #[serde(rename = "fn")]
        fn_name: String,
        args: Vec<ZXOrDim>,
    },
}

fn dim_to_acdc_dim_id<T>(dim_id: &Id, egraph: &EGraph<ACDC, T>) -> Option<ACDCDim>
where
    T: Analysis<ACDC>,
{
    let dim = egraph.id_to_node(*dim_id);
    match dim {
        ACDC::Lit(n) => Some(ACDCDim::Lit { lit: *n }),
        ACDC::Var(s) => Some(ACDCDim::Symbol {
            symbol: s.to_string(),
        }),
        ACDC::Add([a, b]) => Some(ACDCDim::Add {
            a: Box::from(dim_to_acdc_dim_id(a, egraph)?),
            b: Box::from(dim_to_acdc_dim_id(b, egraph)?),
        }),
        ACDC::Mul([a, b]) => Some(ACDCDim::Mul {
            a: Box::from(dim_to_acdc_dim_id(a, egraph)?),
            b: Box::from(dim_to_acdc_dim_id(b, egraph)?),
        }),
        ACDC::Sub([a, b]) => Some(ACDCDim::Sub {
            a: Box::from(dim_to_acdc_dim_id(a, egraph)?),
            b: Box::from(dim_to_acdc_dim_id(b, egraph)?),
        }),
        _ => None,
    }
}

// fn dim_to_acdc_insert_rec<T>(acdcdim: &ACDCDim, egraph: &mut EGraph<ACDC, T>) -> Id
// where
//     T: Analysis<ACDC>,
// {
//     match acdcdim {
//         ACDCDim::Lit(n) => egraph.add(ACDC::Lit(*n)),
//         ACDCDim::Var(s) => egraph.add(ACDC::Var(Symbol::from(s.clone()))),
//         ACDCDim::Add(a, b) => {
//             let a_id = dim_to_acdc_insert_rec(a, egraph);
//             let b_id = dim_to_acdc_insert_rec(b, egraph);
//             egraph.add(ACDC::Add([a_id, b_id]))
//         }
//         ACDCDim::Mul(a, b) => {
//             let a_id = dim_to_acdc_insert_rec(a, egraph);
//             let b_id = dim_to_acdc_insert_rec(b, egraph);
//             egraph.add(ACDC::Mul([a_id, b_id]))
//         }
//         ACDCDim::Sub(a, b) => {
//             let a_id = dim_to_acdc_insert_rec(a, egraph);
//             let b_id = dim_to_acdc_insert_rec(b, egraph);
//             egraph.add(ACDC::Sub([a_id, b_id]))
//         }
//     }
// }

#[derive(Serialize, Deserialize, Debug)]
pub struct Proportional {
    l: ACDCZX,
    r: ACDCZX,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "type")]
pub enum Hyp {
    #[serde(rename = "dephyp")]
    DepHyp {
        name: String,
        n: ACDCDim,
        m: ACDCDim,
    },
    #[serde(rename = "hypprop")]
    HypProp { prop: Proportional, hyps: Vec<Hyp> },
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "type")]
pub struct Lemma {
    prop: Proportional,
    name: Option<String>,
    hyps: Vec<Hyp>,
}

// fn main() {
//     let json_data = r#"{"type":"Lemma","prop":{"type":"prop","r":{"type":"cast","n":{"type":"symbol","symbol":"n'"},"m":{"type":"symbol","symbol":"m'"},"zx":{"type":"fn","fn":"f","args":[{"type":"symbol","symbol":"zx1"}]}},"l":{"type":"cast","n":{"type":"symbol","symbol":"n'"},"m":{"type":"symbol","symbol":"m'"},"zx":{"type":"symbol","symbol":"zx0"}}},"hyps":[{"type":"dephyp","name":"zx0","n":{"type":"-","a":{"type":"+","a":{"type":"symbol","symbol":"n"},"b":{"type":"const","lit":16}},"b":{"type":"const","lit":3}},"m":{"type":"symbol","symbol":"m"}},{"type":"dephyp","name":"zx1","n":{"type":"-","a":{"type":"+","a":{"type":"symbol","symbol":"n"},"b":{"type":"const","lit":16}},"b":{"type":"const","lit":3}},"m":{"type":"symbol","symbol":"m"}},{"type":"hypprop","prop":{"type":"prop","r":{"type":"symbol","symbol":"zx1"},"l":{"type":"symbol","symbol":"zx0"}},"hyps":[]}]}
// "#;
//
//     let zx: Lemma = serde_json::from_str(json_data).expect("Failed to parse JSON");
//     println!("{:#?}", zx);
// }
