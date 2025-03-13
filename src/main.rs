mod conditioneqwrapper;
mod conds;
mod vyzxlemma;

use crate::vyzxlemma::{generate_rw, ZXParam};
use egg::*;
use serde::ser::SerializeStruct;
use serde::Serialize as Ser;
use serde::Serializer;
use serde_derive::{Deserialize, Serialize};
use std::cmp::max;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.contains(&"--version".to_string()) {
        println!("0.0.1");
        return;
    }
    let val_a = "(val n1 (* 1 m1) a)";
    let val_b = "(val (+ 0 m1) o1 b)";
    let val_c = "(val n2 m2 c)";
    let val_d = "(val m2 o2 d)";
    let expr_str = format!(
        "(stack (compose {} {}) (compose {} {}))",
        val_a, val_b, val_c, val_d
    );
    let goal = format!(
        "(compose (stack {} {}) (stack {} {}))",
        val_a, val_c, val_b, val_d
    );
    let expr = expr_str.parse().unwrap();
    let mut rules = vyzx_rules();
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
    let mut expl = runner.explain_equivalence(&expr, &goal.parse().unwrap());
    let flat_explanations: Vec<_> = expl.make_flat_explanation().to_vec();
    let egraph = &runner.egraph;
    for ft in flat_explanations {
        let ftw = SerFlatTermWrap::from(ft, egraph);
        let json = serde_json::to_string_pretty(&ftw).unwrap();
        println!("{}", json);
    }

    assert_eq!(runner.egraph.find(expr_id), runner.egraph.find(res),);
}

#[derive(Debug, Clone)]
struct SerFlatTermWrap<'a, L: Language + 'static, A: Analysis<L> + 'static>(
    FlatTerm<L>,
    &'a EGraph<L, A>,
);

struct SerADCDWrap<'a, A: Analysis<ACDC> + 'static>(ACDC, &'a EGraph<ACDC, A>);

impl<'a, A: Analysis<ACDC> + 'static> ToSer<'a, SerADCDWrap<'a, A>, ACDC, A> for ACDC {
    fn to_ser(&self, egraph: &'a EGraph<ACDC, A>) -> SerADCDWrap<'a, A> {
        SerADCDWrap(self.clone(), egraph)
    }
}
impl <'a, A : Analysis<ACDC>> Ser for SerADCDWrap<'a, A> {


    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[inline(always)]
        fn id_to_ser_acdc_warp<A: Analysis<ACDC>>(egraph: &egg::EGraph<ACDC, A>, id : Id) -> SerADCDWrap<A> {
            egraph.id_to_node(id).to_ser(egraph)
        }
        let mut state: <S as Serializer>::SerializeStruct;
        match &self.0 {
            ACDC::Lit(lit) => {
                state = serializer.serialize_struct("ACDC", 2)?;
                state.serialize_field("type", "const")?;
                state.serialize_field("lit", &lit)?;
            }
            ACDC::Add(ids) => {
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "+")?;
                state.serialize_field("a", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("b", &id_to_ser_acdc_warp(self.1, ids[0]))?;
            }
            ACDC::Sub(ids) => {
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "-")?;
                state.serialize_field("a", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("b", &id_to_ser_acdc_warp(self.1, ids[0]))?;
            }
            ACDC::Mul(ids) => {
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "*")?;
                state.serialize_field("a", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("b", &id_to_ser_acdc_warp(self.1, ids[0]))?;
            }
            ACDC::Dep1(id) => {
                state = serializer.serialize_struct("ACDC", 2)?;
                state.serialize_field("type", "dep1")?;
                state.serialize_field("id", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Dep2(id) => {
                state = serializer.serialize_struct("ACDC", 2)?;
                state.serialize_field("type", "dep1")?;
                state.serialize_field("id", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Var(s) => {
                state = serializer.serialize_struct("ACDC", 2)?;
                state.serialize_field("type", "var")?;
                state.serialize_field("s", s.as_str())?;
            }
            ACDC::Cast(ids) => {
                state = serializer.serialize_struct("ACDC", 4)?;
                state.serialize_field("type", "cast")?;
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
                state.serialize_field("zx", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::Stack(ids) => {
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "stack")?;
                state.serialize_field("a", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("b", &id_to_ser_acdc_warp(self.1, ids[1]))?;
            }
            ACDC::Compose(ids) => {
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "compose")?;
                state.serialize_field("a", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("b", &id_to_ser_acdc_warp(self.1, ids[1]))?;
            }
            ACDC::Val(ids) => {
                state = serializer.serialize_struct("ACDC", 4)?;
                state.serialize_field("type", "val")?;
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
                state.serialize_field("val", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::Z(ids) => {
                state = serializer.serialize_struct("ACDC", 4)?;
                state.serialize_field("type", "Z")?;
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
                state.serialize_field("alpha", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::X(ids) => {
                state = serializer.serialize_struct("ACDC", 4)?;
                state.serialize_field("type", "X")?;
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, ids[0]))?;
                state.serialize_field("m", &id_to_ser_acdc_warp(self.1, ids[1]))?;
                state.serialize_field("alpha", &id_to_ser_acdc_warp(self.1, ids[2]))?;
            }
            ACDC::NWire(id) => {
                state = serializer.serialize_struct("ACDC", 2)?;
                state.serialize_field("type", "n_wire")?;
                state.serialize_field("n", &id_to_ser_acdc_warp(self.1, *id))?;
            }
            ACDC::Fn(fn_name, ids) => {
                let args : Vec<SerADCDWrap<'a, A>> = ids
                    .iter()
                    .map(|id| id_to_ser_acdc_warp(self.1, *id))
                    .collect();
                state = serializer.serialize_struct("ACDC", 3)?;
                state.serialize_field("type", "fn")?;
                state.serialize_field("fn_name", fn_name.as_str())?;
                state.serialize_field("args", &args)?;
            }
        }
        state.end()
    }
}

trait ToSer<'a, S, L: Language, A: Analysis<L>>
where
    S: Ser,
{
    fn to_ser(&self, egraph: &'a EGraph<L, A>) -> S;
}

impl<'a, L: Language + 'static, A: Analysis<L>> SerFlatTermWrap<'a, L, A> {
    fn from(flat_term: FlatTerm<L>, egraph: &'a EGraph<L, A>) -> Self {
        SerFlatTermWrap(flat_term, egraph)
    }

    fn children(&self) -> Vec<SerFlatTermWrap<L, A>> {
        self.0
            .children
            .iter()
            .map(|ft| SerFlatTermWrap::from(ft.clone(), self.1))
            .collect()
    }
}

// impl<L: Language + 'static + ToSer<T, L, A>, A: Analysis<L>, T: Ser> Ser
//     for SerFlatTermWrap<L, A> - Weird rust typing reasons make this not work
impl<'a, A: Analysis<ACDC>> Ser for SerFlatTermWrap<'a, ACDC, A>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let fwd_rule = &self.0.forward_rule.map(|x| x.to_string());
        let bwd_rule = &self.0.backward_rule.map(|x| x.to_string());
        let mut state = serializer.serialize_struct("SerFlatTermWrap", 4)?;
        state.serialize_field("node", &self.0.node.to_ser(self.1))?;
        state.serialize_field("backward_rule", bwd_rule)?;
        state.serialize_field("forward_rule", fwd_rule)?;
        state.serialize_field("children", &self.children())?;
        state.end()
    }
}

fn dim_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC>,
{
    vec![
        rewrite!("add-0"; "(+ 0 ?a)" => "?a"),
        rewrite!("mul-0"; "(* 0 ?a)" => "0"),
        rewrite!("mul-1"; "(* 1 ?a)" => "?a"),
        rewrite!("neg-0"; "(- ?a 0)" => "?a"),
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

fn vyzx_rules<T>() -> Vec<Rewrite<ACDC, T>>
where
    T: Analysis<ACDC> + Clone + 'static,
{
    let rws = vec![
        generate_rw(
            "stack-assoc",
            &ACDCZX::Stack {
                a: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("a")),
                    b: Box::from(simple_var("b")),
                }),
                b: Box::from(simple_var("c")),
            },
            &ACDCZX::Stack {
                a: Box::from(simple_var("a")),
                b: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("b")),
                    b: Box::from(simple_var("c")),
                }),
            },
            vec![
                ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
                ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "b"),
                ZXParam::new(simple_symbol("n3"), simple_symbol("m3"), "c"),
            ],
            true,
        ),
        generate_rw(
            "stack-compose-dist",
            &ACDCZX::Stack {
                a: Box::from(ACDCZX::Compose {
                    a: Box::from(simple_var("a")),
                    b: Box::from(simple_var("b")),
                }),
                b: Box::from(ACDCZX::Compose {
                    a: Box::from(simple_var("c")),
                    b: Box::from(simple_var("d")),
                }),
            },
            &ACDCZX::Compose {
                a: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("a")),
                    b: Box::from(simple_var("c")),
                }),
                b: Box::from(ACDCZX::Stack {
                    a: Box::from(simple_var("b")),
                    b: Box::from(simple_var("d")),
                }),
            },
            vec![
                ZXParam::new(simple_symbol("n1"), simple_symbol("m1"), "a"),
                ZXParam::new(simple_symbol("m1"), simple_symbol("o1"), "b"),
                ZXParam::new(simple_symbol("n2"), simple_symbol("m2"), "c"),
                ZXParam::new(simple_symbol("m2"), simple_symbol("o2"), "d"),
            ],
            true,
        ),
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
#[serde(tag = "type")]
pub enum ACDCDim {
    #[serde(rename = "const")]
    Lit { lit: i32 },
    #[serde(rename = "symbol")]
    Symbol { symbol: String },
    #[serde(rename = "+")]
    Add { a: Box<ACDCDim>, b: Box<ACDCDim> },
    #[serde(rename = "*")]
    Mul { a: Box<ACDCDim>, b: Box<ACDCDim> },
    #[serde(rename = "-")]
    Sub { a: Box<ACDCDim>, b: Box<ACDCDim> },
    #[serde(rename = "fn")]
    Fn {
        #[serde(rename = "fn")]
        fn_name: String,
        args: Vec<ACDCDim>,
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
    Z {
        n: ACDCDim,
        m: ACDCDim,
        alpha: ACDCDim,
    },
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
    hyps: Vec<Hyp>,
}

// fn main() {
//     let json_data = r#"{"type":"Lemma","prop":{"type":"prop","r":{"type":"cast","n":{"type":"symbol","symbol":"n'"},"m":{"type":"symbol","symbol":"m'"},"zx":{"type":"fn","fn":"f","args":[{"type":"symbol","symbol":"zx1"}]}},"l":{"type":"cast","n":{"type":"symbol","symbol":"n'"},"m":{"type":"symbol","symbol":"m'"},"zx":{"type":"symbol","symbol":"zx0"}}},"hyps":[{"type":"dephyp","name":"zx0","n":{"type":"-","a":{"type":"+","a":{"type":"symbol","symbol":"n"},"b":{"type":"const","lit":16}},"b":{"type":"const","lit":3}},"m":{"type":"symbol","symbol":"m"}},{"type":"dephyp","name":"zx1","n":{"type":"-","a":{"type":"+","a":{"type":"symbol","symbol":"n"},"b":{"type":"const","lit":16}},"b":{"type":"const","lit":3}},"m":{"type":"symbol","symbol":"m"}},{"type":"hypprop","prop":{"type":"prop","r":{"type":"symbol","symbol":"zx1"},"l":{"type":"symbol","symbol":"zx0"}},"hyps":[]}]}
// "#;
//
//     let zx: Lemma = serde_json::from_str(json_data).expect("Failed to parse JSON");
//     println!("{:#?}", zx);
// }
