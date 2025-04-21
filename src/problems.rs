macro_rules! create_problem_fn {
    ($name:ident, $file:expr) => {
        pub fn $name() -> &'static str {
            include_str!($file)
        }
    };
}

create_problem_fn!(prob_3, "problem3.json");
create_problem_fn!(prob_4, "problem4.json");
create_problem_fn!(prob_5, "problem5.json");
create_problem_fn!(prob_6, "problem6.json");
create_problem_fn!(prob_7, "problem7.json");
create_problem_fn!(prob_10, "problem10.json");
create_problem_fn!(prob_11, "problem11.json");
create_problem_fn!(prob_12, "problem12.json");
create_problem_fn!(prob_13, "problem13.json");
create_problem_fn!(prob_14, "problem14.json");
create_problem_fn!(prob_15, "problem15.json");
create_problem_fn!(prob_16, "problem16.json");
create_problem_fn!(prob_17, "problem17.json");
create_problem_fn!(prob_18, "problem18.json");
create_problem_fn!(prob_19, "problem19.json");
create_problem_fn!(prob_dom, "probdom.json");
create_problem_fn!(attest, "attest.json");

pub  fn  all_problems<'a>() -> Vec<&'a str> {
    vec![prob_3(), prob_4(), prob_5(), prob_6(), prob_7(), prob_10(), prob_11(), prob_12(), prob_13(), prob_14(), prob_15(), prob_16(), prob_17(), prob_18(), prob_19()]
}

