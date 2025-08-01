use crate::vyzxlemma::{Lemma, LemmaContainer, generate_rw_from_lemma};
use crate::vyzxrules::{vyzx_rules, vyzx_rws};
use crate::{ACDC, ConstantFolding, DirectionalLemma, dep_rules, dim_rules, run_with_problem};
use egg::Rewrite;
use jsonrpc_v2::{Data, Error, Params, ResponseObjects, Server};
use std::ops::DerefMut;
use std::sync::{Arc, Mutex};
use tokio::io::{self, AsyncBufReadExt, stdin};

// This struct will hold the state that we want to share across methods.
struct SharedState {
    rules: Vec<Rewrite<ACDC, ConstantFolding>>,
    lemma_container: Box<LemmaContainer<ConstantFolding>>,
}

impl SharedState {
    fn new() -> Self {
        SharedState {
            rules: vec![],
            lemma_container: Box::new(LemmaContainer::new(vec![])),
        }
    }

    fn add_lemmas(&mut self, lemmas: Vec<DirectionalLemma>) -> i64 {
        let new_lemmas: Vec<Lemma<ConstantFolding>> = lemmas
            .into_iter()
            .map(|l| generate_rw_from_lemma(l))
            .collect();
        new_lemmas
            .clone()
            .into_iter()
            .for_each(|l| self.lemma_container.deref_mut().add(l));
        let new_rules: Vec<_> = new_lemmas
            .into_iter()
            .flat_map(|l| l.get_rewrites())
            .collect();
        self.rules.extend(new_rules);
        self.rules.len() as i64
    }

    fn clear_lemmas(&mut self) -> i64 {
        self.rules.clear();
        self.lemma_container.deref_mut().clear();
        self.rules.len() as i64
    }

    fn default_lemmas(&mut self) -> i64 {
        self.lemma_container = Box::new(LemmaContainer::new(vyzx_rules()));
        let mut rules = vyzx_rws();
        rules.extend(dim_rules());
        rules.extend(dep_rules());
        self.rules = rules;
        self.rules.len() as i64
    }
}

async fn add(
    data: Data<Arc<Mutex<SharedState>>>,
    Params(params): Params<Vec<DirectionalLemma>>,
) -> Result<i64, Error> {
    let mut state = data.lock().unwrap();
    Ok(state.add_lemmas(params))
}

async fn clear(data: Data<Arc<Mutex<SharedState>>>) -> Result<i64, Error> {
    // Lock the mutex to get mutable access to the state.
    let mut state = data.lock().unwrap();
    Ok(state.clear_lemmas())
}

async fn default_lemmas(data: Data<Arc<Mutex<SharedState>>>) -> Result<i64, Error> {
    // Lock the mutex to get mutable access to the state.
    let mut state = data.lock().unwrap();
    Ok(state.default_lemmas())
}

/// A simple "ping" method that takes no parameters and doesn't need the state.
async fn ping() -> Result<&'static str, Error> {
    Ok("pong")
}
/// A new method to retrieve a value from the shared state.
async fn run(
    data: Data<Arc<Mutex<SharedState>>>,
    params: Params<crate::Lemma>,
) -> Result<String, Error> {
    // Lock the mutex to get read-only access.
    let state = data.lock().unwrap();
    let result = run_with_problem(&params.0, &state.rules);
    Ok(result)
}

pub async fn tokio_main() {
    let state = Arc::new(Mutex::new(SharedState::new()));
    let data = Data::new(state);
    let rpc = Server::new()
        .with_data(data)
        .with_method("add_lemmas", add)
        .with_method("default_lemmas", default_lemmas)
        .with_method("clear_lemmas", clear)
        .with_method("ping", ping)
        .with_method("run_problem", run)
        .finish();
    eprintln!("JSON-RPC server started. Reading from stdin...");

    let mut reader = io::BufReader::new(stdin());

    let mut line_buf = String::new();
    while let Ok(len) = reader.read_line(&mut line_buf).await {
        if len == 0 {
            break; // EOF reached
        }
        
        let response_objects = rpc.handle(line_buf.as_bytes()).await;
        match response_objects {
            ResponseObjects::One(res) => {
                println!("{}", serde_json::to_string_pretty(&res).unwrap());
            }
            ResponseObjects::Many(res_vec) => {
                for res in res_vec {
                    println!("{}", serde_json::to_string_pretty(&res).unwrap());
                }
            }
            ResponseObjects::Empty => {
                eprintln!("No response generated for the request.");
            }
        }

        // Clear the buffer for the next request.
        line_buf.clear();
    }

    eprintln!("Server shutting down.");
}
