use crate::vyzxlemma::acdczx_to_pattern;
use crate::vyzxrules::{compose_assoc, stack_assoc};
use crate::{
    dep_rules, dim_rules, simple_lit, ConstantFolding, Lemma, Proportional, ACDC,
    ACDCZX,
};
use egg::Runner;

fn build_l_assoc(base: &ACDCZX, n: u32) -> ACDCZX {
    if n == 0 {
        return base.clone();
    }
    ACDCZX::Compose {
        a: Box::new(build_l_assoc(base, n - 1)),
        b: Box::new(base.clone()),
    }
}

fn build_r_assoc(base: &ACDCZX, n: u32) -> ACDCZX {
    if n == 0 {
        return base.clone();
    }
    ACDCZX::Compose {
        a: Box::new(base.clone()),
        b: Box::new(build_r_assoc(base, n - 1)),
    }
}

fn benchmark_assoc(n: u32) {
    let base = ACDCZX::NWire { n: simple_lit(1) };
    let l = build_l_assoc(&base, n);
    let r = build_r_assoc(&base, n);
    let prop = Proportional { l, r };
    let lemma = Lemma {
        name: Some(format!("assoc_{}", n).to_string()),
        prop,
        hyps: vec![],
    };
    let rules = compose_assoc().get_rewrites();
    let expr = acdczx_to_pattern(&lemma.prop.l).parse().unwrap();
    let goal = acdczx_to_pattern(&lemma.prop.r).parse().unwrap();

    let start_time = std::time::Instant::now();
    let mut runner = Runner::<ACDC, ConstantFolding, ()>::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .with_expr(&goal)
        .with_iter_limit(usize::MAX)
        .run(&rules);
    let end_time = std::time::Instant::now();
    println!(
        "{},{}",
        n,
        end_time.duration_since(start_time).as_millis()
    );
    let expr_id = runner.egraph.add_expr(&expr);
    let res = runner.egraph.add_expr(&goal);
    if runner.egraph.find(expr_id) != runner.egraph.find(res) {
        panic!(
            "Failed to find equality for assoc_{}.  ",
            n,
        );
    }
}

pub fn benchmark(benchmark_name: &str, n: u32) {
    match benchmark_name {
        "assoc" => benchmark_assoc(n),
        _ => panic!("Unknown benchmark: {}", benchmark_name),
    }
}
