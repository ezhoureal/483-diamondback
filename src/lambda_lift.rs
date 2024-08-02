use std::collections::{HashMap, HashSet};

use crate::syntax::*;


pub fn uniquify<Span>(e: &Exp<Span>, mapping: &HashMap<String, String>, counter: &mut u32) -> Exp<()> {
    match e {
        Exp::Let {
            bindings,
            body,
            ann,
        } => {
            let mut scoped_mapping = mapping.clone();
            let mut_bind = bindings
                .iter()
                .map(|(var, value)| {
                    *counter += 1;
                    let new_var = format!("{}", counter);
                    let mut_exp = uniquify(value, &scoped_mapping, counter);
                    scoped_mapping.insert(var.to_string(), new_var.clone());
                    return (new_var, mut_exp);
                })
                .collect();
            Exp::Let {
                bindings: mut_bind,
                body: Box::new(uniquify(&body, &scoped_mapping, counter)),
                ann: (),
            }
        }
        Exp::FunDefs { decls, body, ann } => {
            let mut scoped_mapping = mapping.clone();
            for decl in decls {
                *counter += 1;
                scoped_mapping.insert(decl.name.to_string(), format!("{}", counter));
            }
            let mut uniq_decls = vec![];
            for decl in decls {
                let mut func_scope_map = scoped_mapping.clone();
                for param in &decl.parameters {
                    *counter += 1;
                    func_scope_map.insert(param.to_string(), format!("{}", counter));
                }
                uniq_decls.push(FunDecl {
                    name: scoped_mapping[&decl.name].clone(),
                    parameters: decl
                        .parameters
                        .iter()
                        .map(|param| func_scope_map[param].clone())
                        .collect(),
                    body: uniquify(&body, &func_scope_map, counter),
                    ann: (),
                })
            }
            Exp::FunDefs {
                decls: uniq_decls,
                body: Box::new(uniquify(&body, &scoped_mapping, counter)),
                ann: (),
            }
        }
        Exp::Var(v, _) => Exp::Var(mapping[v].clone(), ()),
        Exp::Num(i, _) => Exp::Num(*i, ()),
        Exp::Bool(b, _) => Exp::Bool(*b, ()),
        Exp::Prim(op, subjects, _) => {
            let uniq_sub = subjects
                .iter()
                .map(|s| Box::new(uniquify(s, mapping, counter)))
                .collect();
            Exp::Prim(*op, uniq_sub, ())
        }
        Exp::If {
            cond,
            thn,
            els,
            ann: _,
        } => Exp::If {
            cond: Box::new(uniquify(&cond, mapping, counter)),
            thn: Box::new(uniquify(&thn, mapping, counter)),
            els: Box::new(uniquify(&els, mapping, counter)),
            ann: (),
        },
        Exp::Call(func, params, _) => {
            let uniq_params = params
                .iter()
                .map(|s| uniquify(s, mapping, counter))
                .collect();
            Exp::Call(mapping[func].clone(), uniq_params, ())
        }
        Exp::InternalTailCall(_, _, _) => Exp::InternalTailCall(String::new(), vec![], ()),
        Exp::ExternalCall {
            fun_name: _,
            args: _,
            is_tail,
            ann: _,
        } => Exp::ExternalCall {
            fun_name: String::new(),
            args: vec![],
            is_tail: *is_tail,
            ann: (),
        },
    }
}

// Identify which functions should be lifted to the top level
fn should_lift(p: &Exp<()>) -> HashSet<String> {
    panic!("NYI: should lift")
}

// Lift some functions to global definitions
fn lambda_lift(p: &Exp<()>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {
    match p {
        Exp::Var(_, _) => todo!(),
        Exp::Prim(_, _, _) => todo!(),
        Exp::Let {
            bindings,
            body,
            ann,
        } => todo!(),
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => todo!(),
        Exp::FunDefs { decls, body, ann } => todo!(),
        Exp::Call(_, _, _) => todo!(),
        _ => (vec![], p.clone()),
    }
}