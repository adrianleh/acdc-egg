use crate::serialize::{SerFlatTermWrap};
use crate::vyzxlemma::{LemmaContainer, acdczx_to_pattern};
use crate::vyzxrules::compose_assoc;
use crate::{
    ACDC, ACDCTiming, ACDCZX, ConstantFolding, Lemma, Proportional, simple_lit, simple_var_sized,
};
use egg::{Language, RecExpr, Runner};
use rand::Rng;
use std::collections::HashMap;
use std::time::Duration;
use serde_derive::{Deserialize, Serialize};

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

fn run_benchmark(l: ACDCZX, r: ACDCZX, name: &str) -> ACDCTiming {
    let prop = Proportional { l, r };
    let lemma = Lemma {
        name: Some(name.to_string()),
        prop,
        hyps: vec![],
        total_arguments: 0,
        inferred_arguments: vec![],
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
    eprintln!(
        "{},{}",
        name,
        end_time.duration_since(start_time).as_millis()
    );
    let expr_id = runner.egraph.add_expr(&expr);
    let res = runner.egraph.add_expr(&goal);
    if runner.egraph.find(expr_id) != runner.egraph.find(res) {
        panic!("Failed to find equality for {}.  ", name);
    }
    // TODO: Try getting the explanation for the rewrite
    // Count time for explanation
    // Then serialize explanation and print length
    // Count serialization time
    if let Some((expl_time, conv_time)) = get_expl(&mut runner, expr, goal, expr_id, res) {
        ACDCTiming {
            name: Some(name.to_string()),
            run_time: end_time.duration_since(start_time).as_millis(),
            conversion_time: conv_time.as_millis(),
            explain_time: expl_time.as_millis(),
        }
    } else {
        panic!("Failed to get explanation for {}", name);
    }
}

fn get_expl(
    runner: &mut Runner<ACDC, ConstantFolding, ()>,
    expr: RecExpr<ACDC>,
    goal: RecExpr<ACDC>,
    expr_id: egg::Id,
    res: egg::Id,
) -> Option<(Duration, Duration)> {
    let lemmas = LemmaContainer::new(vec![compose_assoc()]);
    eprintln!("Explaining...");
    let start_expl_time = std::time::Instant::now();
    let mut expl = runner.explain_equivalence(&expr, &goal);
    eprintln!("size {}", expl.get_tree_size());
    // eprintln!("Flattening...");
    // eprintln!("Converting...");
    let mut wrap_exprs = vec![];
    let get_first_enode = |id| (&runner).egraph.id_to_node(id).clone();

    let flat_explanations: Vec<_> = expl.make_flat_explanation().to_vec();
    let end_expl_time = std::time::Instant::now();
    let expl_time = end_expl_time.duration_since(start_expl_time);
    let start_conv_time = std::time::Instant::now();
    eprintln!("flat_explanations size: {:}", flat_explanations.len());
    let mut prev = runner
        .egraph
        .id_to_node(expr_id)
        .build_recexpr(get_first_enode);
    for ft in flat_explanations {
        let curr = ft.clone().get_recexpr();
        wrap_exprs.push(SerFlatTermWrap::from(
            prev.clone(),
            curr.clone(),
            ft.clone(),
            &runner.egraph,
            &lemmas,
        ));
        prev = curr.clone();
    }
    let end_conv_time = std::time::Instant::now();
    let conversion_time = end_conv_time.duration_since(start_conv_time);
    Some((expl_time, conversion_time))
}

fn benchmark_assoc(n: u32) -> ACDCTiming {
    let base = ACDCZX::NWire { n: simple_lit(1) };
    let l = build_l_assoc(&base, n);
    let r = build_r_assoc(&base, n);
    run_benchmark(l, r, &format!("assoc_{}", n))
}

fn benchmark_rnd_assoc(n: u32)  -> ACDCTiming {
    if let Some(base) = generate_random_stack(n as usize) {
        let l = build_l_assoc(&base, n);
        let r = build_r_assoc(&base, n);
        run_benchmark(l, r, &format!("rnd_assoc_{}", n))
    } else {
        panic!("n must be greater than 0 for random assoc benchmark");
    }
}

#[derive(Debug, Clone,Serialize, Deserialize)]
struct ACDCTimingStats {
    avg_run_time: f64,
    avg_explain_time: f64,
    avg_conversion_time: f64,
    std_dev_run_time: f64,
    std_dev_explain_time: f64,
    std_dev_conversion_time: f64,
}
fn get_stats(results: Vec<ACDCTiming>) -> HashMap<String, ACDCTimingStats> {
    let mut buckets: HashMap<String, Vec<ACDCTiming>> = HashMap::new();
    for res in results {
        let curr_name = res.clone().name.unwrap_or_else(|| "unknown".to_string());
        if buckets.contains_key(&curr_name) {
            buckets.get_mut(&curr_name).unwrap().push(res);
        } else {
            buckets.insert(curr_name.clone(), vec![res]);
        }
    }
    let mut stats: HashMap<String, ACDCTimingStats> = HashMap::new();
    fn get_avg(times: &Vec<ACDCTiming>, f: fn(&ACDCTiming) -> u128) -> f64 {
        let count = times.len() as f64;
        times.iter().map(|t| f(t) as f64 / count).sum()
    }
    fn get_std_dev(times: &Vec<ACDCTiming>, f: fn(&ACDCTiming) -> u128, avg: f64) -> f64 {
        let count = times.len() as f64;
        (times
            .iter()
            .map(|t| (f(t) as f64 - avg).powi(2))
            .sum::<f64>()
            / count)
            .sqrt()
    }

    for (name, times) in buckets {
        let avg_run_time: f64 = get_avg(&times, |t| t.run_time);
        let avg_explain_time: f64 = get_avg(&times, |t| t.explain_time);
        let avg_conversion_time: f64 = get_avg(&times, |t| t.conversion_time);
        let std_dev_run_time = get_std_dev(&times, |t| t.run_time, avg_run_time);
        let std_dev_explain_time = get_std_dev(&times, |t| t.explain_time, avg_explain_time);
        let std_dev_conversion_time =
            get_std_dev(&times, |t| t.conversion_time, avg_conversion_time);
        stats.insert(
            name,
            ACDCTimingStats {
                avg_run_time,
                avg_explain_time,
                avg_conversion_time,
                std_dev_run_time,
                std_dev_explain_time,
                std_dev_conversion_time,
            },
        );
    }
    stats
}

fn generate_random_stack(n: usize) -> Option<ACDCZX> {
    if n == 0 {
        return None;
    }

    // Create the initial list of 'n' ordered variables, e.g., v0, v1, v2, ...
    let expressions: Vec<ACDCZX> = (0..n)
        .map(|i| simple_var_sized(format!("x{}", i).as_str(), 1, 1))
        .collect();

    // Call the recursive helper function to build the expression tree.
    Some(build_random_tree_recursive(&expressions))
}

fn build_random_tree_recursive(expressions: &[ACDCZX]) -> ACDCZX {
    // Base case: if there's only one expression, return it.
    // It needs to be cloned because the function returns an owned Math value.
    if expressions.len() == 1 {
        return expressions[0].clone();
    }

    let mut rng = rand::rng();

    // Recursive step:
    // 1. Pick a random split point. The split point `k` will divide the slice
    //    into `[0..k]` and `[k..]`. `k` must be between 1 and len-1.
    //    `gen_range` is exclusive on the upper bound, so we use `1..expressions.len()`.
    let k = rng.random_range(1..expressions.len());

    // 2. Split the slice into two parts.
    let (left_slice, right_slice) = expressions.split_at(k);

    // 3. Recursively build the sub-trees for the left and right parts.
    let left_expr = build_random_tree_recursive(left_slice);
    let right_expr = build_random_tree_recursive(right_slice);

    // 4. Combine them into a new `Add` expression.
    ACDCZX::Compose {
        a: Box::new(left_expr),
        b: Box::new(right_expr),
    }
}

pub fn benchmark(benchmark_name: &str, n_from: u32, n_to: u32, iterations: u32) {
    let mut results: Vec<ACDCTiming> = vec![];
    for n in n_from..=n_to {
        for _ in 0..iterations {
            let res = match benchmark_name {
                "assoc" => benchmark_assoc(n),
                "rnd_assoc" => benchmark_rnd_assoc(n),
                _ => panic!("Unknown benchmark: {}", benchmark_name),
            };
            results.push(res);
        }
    }
    let stats = get_stats(results);
    let json_stats = serde_json::to_string_pretty(&stats).unwrap();
    println!("{}", json_stats);
}
