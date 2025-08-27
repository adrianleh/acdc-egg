use crate::vyzxlemma::{Lemma, LemmaContainer, generate_rw_from_lemma};
use crate::vyzxrules::{vyzx_rules, vyzx_rws};
use crate::{ACDC, ConstantFolding, Directional, dep_rules, dim_rules, run_with_problem};
use actix_web::{App, HttpServer, guard, web};
use egg::Rewrite;
use jsonrpc_v2::{Data, Error, Params, ResponseObjects, Server};
use serde_derive::Deserialize;
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};
use tokio::io::{self, AsyncBufReadExt, AsyncReadExt, stdin};

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

    fn add_lemmas(&mut self, lemmas: Vec<Directional>) -> Result<i64, String> {
        let new_lemmas: Vec<_> = lemmas
            .into_iter()
            .map(|l| generate_rw_from_lemma(l))
            .collect();
        let errs = new_lemmas
            .clone()
            .into_iter()
            .filter(|l| l.is_err())
            .map(|e| e.err().unwrap())
            .collect::<Vec<_>>();
        if !errs.is_empty() {
            return Err(errs.join(","));
        }
        new_lemmas
            .clone()
            .into_iter()
            .for_each(|l| self.lemma_container.deref_mut().add(l.unwrap()));
        let new_rules: Vec<_> = new_lemmas
            .into_iter()
            .flat_map(|l| l.unwrap().get_rewrites())
            .collect();
        self.rules.extend(new_rules);
        Ok(self.rules.len() as i64)
    }

    fn clear_lemmas(&mut self) -> i64 {
        self.rules.clear();
        self.lemma_container.deref_mut().clear();
        self.rules.len() as i64
    }

    fn default_lemmas(&mut self) -> i64 {
        self.lemma_container = Box::new(LemmaContainer::new(vyzx_rules()));
        self.rules = vyzx_rws();
        self.rules.len() as i64
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
enum DirectionalParam {
    Single(Vec<Directional>),
    Nested(Vec<Vec<Directional>>),
}

async fn add(
    data: Data<Arc<Mutex<SharedState>>>,
    Params(params): Params<DirectionalParam>,
) -> Result<i64, Error> {
    let mut state = data.lock().unwrap();
    let params = match params {
        DirectionalParam::Single(v) => v,
        DirectionalParam::Nested(vv) => vv.into_iter().flatten().collect(),
    };
    let res = state.add_lemmas(params);
    if res.is_ok() {
        return Ok(res.unwrap());
    }
    Err(Error::internal(res.err().unwrap()))
}

// async fn add(
//     data: Data<Arc<Mutex<SharedState>>>,
//     Params(params): Params<Vec<Directional>>,
// ) -> Result<i64, Error> {
//     let mut state = data.lock().unwrap();
//     let res = state.add_lemmas(params);
//     if res.is_ok() {
//         return Ok(res.unwrap());
//     }
//     Err(Error::internal(res.err().unwrap()))
// }

async fn clear(data: Data<Arc<Mutex<SharedState>>>) -> Result<i64, Error> {
    // Lock the mutex to get mutable access to the state.
    let mut state = data.lock().unwrap();
    Ok(state.clear_lemmas())
}

async fn default_lemmas(data: Data<Arc<Mutex<SharedState>>>) -> Result<i64, Error> {
    let mut state = data.lock().unwrap();
    Ok(state.default_lemmas())
}

async fn ping() -> Result<&'static str, Error> {
    Ok("pong")
}

async fn run(
    data: Data<Arc<Mutex<SharedState>>>,
    params: Params<crate::Lemma>,
) -> Result<String, Error> {
    let state = data.lock().unwrap();
    let mut rules = state.rules.clone();
    rules.extend(dim_rules());
    rules.extend(dep_rules());
    let result = run_with_problem(&params.0, &rules, state.lemma_container.deref());
    if result.is_err() {
        return Err(Error::internal(result.err().unwrap()));
    }
    Ok(result.unwrap())
}

pub async fn tokio_main(http: bool) {
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
    if http {
        const address: &str = "0.0.0.0:8080";
        eprintln!("Starting JSON-RPC server on {}", address);
        let _ = HttpServer::new(move || {
            let rpc = rpc.clone();
            App::new().service(
                web::service("/api")
                    .guard(guard::Post())
                    .finish(rpc.into_web_service()),
            )
        })
        .bind(address)
        .unwrap()
        .run()
        .await;
        return;
    }
    eprintln!("JSON-RPC server started. Reading from stdin...");

    let mut reader = io::BufReader::new(stdin());

    let mut buffer = String::new();
    loop {
        let mut content_length = 0;

        // Read headers until we find Content-Length or EOF
        // Make sure to remember the content length
        loop {
            buffer.clear(); // Clear the buffer for the next header line
            if reader.read_line(&mut buffer).await.unwrap_or(0) == 0 {
                // EOF, connection closed
                eprintln!("Connection closed.");
                return;
            }

            // Check for the Content-Length header
            if let Some(len_str) = buffer.strip_prefix("Content-Length: ") {
                content_length = len_str.trim().parse().unwrap_or(0);
            }

            // An empty line (`\r\n`) indicates the end of headers
            if buffer.trim().is_empty() {
                break;
            }
        }

        // Likely not to cause issues but guarding any way
        if content_length == 0 {
            eprintln!("Warning: Received message with Content-Length of 0 or missing header.");
            continue;
        }

        // Read the body into a buffer
        let mut body_buf = vec![0; content_length];
        if reader.read_exact(&mut body_buf).await.is_err() {
            eprintln!("Error reading message body.");
            break;
        }

        // Handle the request
        let response_objects = rpc.handle(body_buf.as_slice()).await;
        match response_objects {
            ResponseObjects::One(res) => {
                let res_str = serde_json::to_string(&res).unwrap();
                println!("Content-Length: {}\r\n\r\n{}", res_str.len(), res_str);
            }
            ResponseObjects::Many(res_vec) => {
                for res in res_vec {
                    let res_str = serde_json::to_string(&res).unwrap();
                    println!("Content-Length: {}\r\n\r\n{}", res_str.len(), res_str);
                }
            }
            ResponseObjects::Empty => {
                // For notifications, no response is sent.
            }
        }
    }
    eprintln!("Server shutting down.");
}
