use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};

use crate::syntax::*;

fn uniquify<Span>(e: &Exp<Span>, mapping: &HashMap<String, String>, counter: &mut u32) -> Exp<()> {
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
        Exp::InternalTailCall(_, _, _) => todo!(),
        Exp::ExternalCall {
            fun_name: _,
            args: _,
            is_tail,
            ann: _,
        } => todo!(),
    }
}

// [locals] local variables in the function body
// [captured] returns all unbound variables in the function body
fn search_unbound(e: &Exp<()>, locals: &mut HashSet<String>, unbound: &mut HashSet<String>) {
    match e {
        Exp::Var(s, _) => {
            if !locals.contains(s) {
                unbound.insert(s.clone());
            }
        }
        Exp::Prim(_, exps, _) => {
            for exp in exps {
                search_unbound(exp, locals, unbound);
            }
        }
        Exp::Let {
            bindings,
            body,
            ann,
        } => {
            for bind in bindings {
                locals.insert(bind.0.clone());
                search_unbound(&bind.1, locals, unbound);
            }
            search_unbound(&body, locals, unbound);
        }
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => {
            search_unbound(cond, locals, unbound);
            search_unbound(thn, locals, unbound);
            search_unbound(els, locals, unbound);
        }
        Exp::FunDefs { decls, body, ann } => {
            for decl in decls {
                search_unbound(&decl.body, locals, unbound);
            }
            search_unbound(body, locals, unbound);
        }
        Exp::Call(func, params, _) => {
            for param in params {
                search_unbound(param, locals, unbound);
            }
        }
        _ => {}
    }
}

fn rewrite_params(e: &Exp<()>, globals: &HashMap<String, FunDecl<Exp<()>, ()>>) -> Exp<()> {
    match e {
        Exp::Prim(p, exps, _) => Exp::Prim(
            *p,
            exps.iter()
                .map(|exp| Box::new(rewrite_params(exp, globals)))
                .collect(),
            (),
        ),
        Exp::Let {
            bindings,
            body,
            ann,
        } => Exp::Let {
            bindings: bindings
                .iter()
                .map(|bind| (bind.0.clone(), rewrite_params(&bind.1, globals)))
                .collect(),
            body: Box::new(rewrite_params(body, globals)),
            ann: (),
        },
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => Exp::If {
            cond: Box::new(rewrite_params(cond, globals)),
            thn: Box::new(rewrite_params(thn, globals)),
            els: Box::new(rewrite_params(els, globals)),
            ann: (),
        },
        Exp::FunDefs { decls, body, ann } => Exp::FunDefs {
            decls: decls.iter().map(
                |decl| FunDecl {
                    name: decl.name.clone(),
                    parameters: decl.parameters.clone(),
                    body: rewrite_params(&decl.body, globals),
                    ann: (),
                }
            ).collect(),
            body: Box::new(rewrite_params(body, globals)),
            ann: (),
        },
        Exp::Call(func, params, _) => {
            let mut mod_params = params.clone();
            for p in globals[func].parameters.iter().skip(params.len()) {
                mod_params.push(Exp::Var(p.clone(), ()))
            }
            Exp::Call(func.to_string(), mod_params, ())},
        _ => e.clone(),
    }
}

fn lambda_lift_inner(
    e: &Exp<()>,
    globals: &mut HashMap<String, FunDecl<Exp<()>, ()>>,
    force_global: bool,
) -> Exp<()> {
    match e {
        Exp::Prim(p, exps, _) => {
            let mut new_exps = vec![];
            for exp in exps {
                new_exps.push(Box::new(lambda_lift_inner(&exp, globals, force_global)));
            }
            Exp::Prim(*p, new_exps, ())
        }
        Exp::Let {
            bindings,
            body,
            ann,
        } => {
            let mut new_bindings = vec![];
            for bind in bindings {
                let new_bind = lambda_lift_inner(&bind.1, globals, force_global);
                new_bindings.push((bind.0.clone(), new_bind));
            }
            let new_bod = lambda_lift_inner(&body, globals, force_global);
            Exp::Let {
                bindings: new_bindings,
                body: Box::new(new_bod),
                ann: (),
            }
        }
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => Exp::If {
            cond: Box::new(lambda_lift_inner(&cond, globals, force_global)),
            thn: Box::new(lambda_lift_inner(&thn, globals, force_global)),
            els: Box::new(lambda_lift_inner(&els, globals, force_global)),
            ann: (),
        },
        Exp::FunDefs { decls, body, ann } => {
            let mut new_local_funcs = vec![];
            for decl in decls {
                let mut captured = HashSet::new();
                search_unbound(&decl.body, &mut HashSet::new(), &mut captured);
                if captured.is_empty() && !force_global {
                    new_local_funcs.push(decl.clone());
                    continue;
                }
                globals.insert(
                    decl.name.clone(),
                    FunDecl {
                        name: decl.name.clone(),
                        parameters: [decl.parameters.clone(), Vec::from_iter(captured)].concat(),
                        body: decl.body.clone(),
                        ann: (),
                    },
                );
            }

            let new_body = lambda_lift_inner(&body, globals, force_global);
            if new_local_funcs.is_empty() {
                return new_body;
            }
            Exp::FunDefs {
                decls: new_local_funcs,
                body: Box::new(new_body),
                ann: (),
            }
        }
        Exp::Call(func, params, _) => {
            let new_params = params
                .iter()
                .map(|param| lambda_lift_inner(param, globals, force_global))
                .collect();
            Exp::Call(func.to_string(), new_params, ())
        }
        _ => e.clone(),
    }
}

// Lift some functions to global definitions
pub fn lambda_lift<Ann>(p: &Exp<Ann>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {
    let unique_p = uniquify(&p, &mut HashMap::new(), &mut 0);
    let mut globals = HashMap::new();
    let main = lambda_lift_inner(&unique_p, &mut globals, false);
    (
        globals
            .values()
            .map(|decl| FunDecl {
                name: decl.name.clone(),
                parameters: decl.parameters.clone(),
                body: rewrite_params(&decl.body, &globals),
                ann: (),
            })
            .collect(),
        rewrite_params(&main, &globals),
    )
}
