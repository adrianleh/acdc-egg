use crate::vyzxlemma::{replace_dim_subtree, to_expl_acdc_expr};
use crate::{ACDC, ACDCDim};
use egg::{Pattern, Rewrite};
use serde_derive::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
enum Type {
    #[serde(rename = "zxtype")]
    ZxType { n: ACDCDim, m: ACDCDim },
    #[serde(rename = "nattype")]
    NatType,
    #[serde(rename = "othertype")]
    Other,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct Function {
    name: String,
    args: Vec<(String, Type)>,
    ftype: Type,
}

impl Function {
    pub fn new(name: &str, args: Vec<(String, Type)>, ftype: Type) -> Self {
        Self {
            name: name.to_string(),
            args,
            ftype,
        }
    }

    pub fn is_zx(&self) -> bool {
        match self.ftype {
            Type::ZxType { .. } => true,
            _ => false,
        }
    }

    pub fn is_dim(&self) -> bool {
        match self.ftype {
            Type::NatType => true,
            _ => false,
        }
    }

    pub fn n_args(&self) -> usize {
        self.args.len()
    }

    pub fn arg_map(&self) -> HashMap<String, usize> {
        let mut map = HashMap::new();
        for (i, (arg_name, _)) in self.args.iter().enumerate() {
            map.insert(arg_name.clone(), i);
        }
        map
    }

    pub fn arg_string(&self) -> String {
        self.args
            .iter()
            .map(|arg| arg.0.clone())
            .map(|arg| format!("?{}", arg))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn get_dep_type_rewrites_patterns(&self) -> Vec<(String, String, String)> {
        match &self.ftype {
            Type::ZxType { n, m } => {
                let mut n = n.clone();
                let mut m = m.clone();
                for arg in &self.args {
                    match &arg.1 {
                        Type::NatType {} => {
                            n = replace_dim_subtree(
                                &n,
                                &ACDCDim::Symbol {
                                    symbol: arg.0.clone(),
                                },
                                &ACDCDim::Symbol {
                                    symbol: format!("?{}", arg.0),
                                },
                            );
                            m = replace_dim_subtree(
                                &m,
                                &ACDCDim::Symbol {
                                    symbol: arg.0.clone(),
                                },
                                &ACDCDim::Symbol {
                                    symbol: format!("?{}", arg.0),
                                },
                            );
                        }
                        _ => continue,
                    }
                }
                let dep1 = format!("(dep1 ({} {}))", &self.name, self.arg_string());
                let dep2 = format!("(dep2 ({} {}))", &self.name, self.arg_string());
                let n_pat = to_expl_acdc_expr(&n);
                let m_pat = to_expl_acdc_expr(&m);
                let n_name = format!("dep-{}-n", self.name);
                let m_name = format!("dep-{}-m", self.name);
                vec![(n_name, dep1, n_pat), (m_name, dep2, m_pat)]
            }
            _ => vec![],
        }
    }
    pub fn get_dep_type_rewrites<T>(&self) -> Vec<Rewrite<ACDC, T>>
    where
        T: egg::Analysis<ACDC>,
    {
        let patterns = self.get_dep_type_rewrites_patterns();
        patterns
            .iter()
            .map(|(name, l, r)| {
                eprintln!("Generating fn rewrite: {}: {} -> {}", name, l, r);
                let l_pat: Pattern<ACDC> = l.parse().unwrap();
                let r_pat: Pattern<ACDC> = r.parse().unwrap();
                Rewrite::new(name, l_pat, r_pat).unwrap()
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionContainer {
    functions: HashMap<String, Box<Function>>,
}

impl FunctionContainer {
    pub fn new() -> Self {
        FunctionContainer {
            functions: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.functions.len()
    }
    pub fn add_function(&mut self, f: Function) {
        self.functions.insert(f.name.clone(), Box::new(f));
    }
    pub fn get_function(&self, name: &str) -> Option<&Function> {
        self.functions.get(name).map(|f| f.as_ref())
    }
    pub fn clear(&mut self) {
        self.functions.clear();
    }

    pub fn get_all_rewrites<T>(&self) -> Vec<Rewrite<ACDC, T>>
    where
        T: egg::Analysis<ACDC>,
    {
        let mut rewrites = vec![];
        for f in self.functions.values() {
            let mut f_rewrites = f.get_dep_type_rewrites();
            rewrites.append(&mut f_rewrites);
        }
        rewrites
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transpose_dep_rewrites() {
        let f = Function::new(
            "@ZXCore.transpose",
            vec![
                ("n".to_string(), Type::NatType),
                ("m".to_string(), Type::NatType),
                ("zx".to_string(), Type::Other),
            ],
            Type::ZxType {
                n: ACDCDim::Symbol { symbol: "m".into() },
                m: ACDCDim::Symbol { symbol: "n".into() },
            },
        );

        let rewrites = f.get_dep_type_rewrites_patterns();
        assert_eq!(
            rewrites.len(),
            2,
            "expected 2 rewrites, got: {:?}",
            rewrites.len()
        );
        let exp_dep1 = (
            "(dep1 (@ZXCore.transpose ?n ?m ?zx))".to_string(),
            "?m".to_string(),
        );
        let exp_dep2 = (
            "(dep2 (@ZXCore.transpose ?n ?m ?zx))".to_string(),
            "?n".to_string(),
        );
        let mut rw_patterns: Vec<(String, String)> = rewrites
            .iter()
            .map(|(_, l, r)| (l.to_string(), r.to_string()))
            .collect();
        rw_patterns.sort_by(|a, b| a.0.cmp(&b.0));
        assert_eq!(rw_patterns[0], exp_dep1);
        assert_eq!(rw_patterns[1], exp_dep2);
    }
}
