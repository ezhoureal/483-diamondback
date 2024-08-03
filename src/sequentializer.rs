use crate::syntax::*;

fn try_flatten_prim1(p: &Prim, exp: &SeqExp<()>) -> Option<SeqExp<()>> {
    match exp {
        SeqExp::Imm(i, _) => Some(SeqExp::Prim(*p, vec![i.clone()], ())),
        _ => None,
    }
}

fn try_flatten_prim2(
    p: &Prim,
    exp1: &SeqExp<()>,
    exp2: &SeqExp<()>,
    counter: &mut u32,
) -> Option<SeqExp<()>> {
    if let SeqExp::Imm(i1, _) = exp1 {
        if let SeqExp::Imm(i2, _) = exp2 {
            return Some(SeqExp::Prim(*p, vec![i1.clone(), i2.clone()], ()));
        }
        *counter += 1;
        let name2 = format!("#prim2_2_{}", counter);
        return Some(SeqExp::Let {
            var: name2.clone(),
            bound_exp: Box::new(exp2.clone()),
            body: Box::new(SeqExp::Prim(*p, vec![i1.clone(), ImmExp::Var(name2)], ())),
            ann: (),
        });
    }
    if let SeqExp::Imm(i2, _) = exp2 {
        *counter += 1;
        let name1 = format!("#prim2_1_{}", counter);

        return Some(SeqExp::Let {
            var: name1.clone(),
            bound_exp: Box::new(exp1.clone()),
            body: Box::new(SeqExp::Prim(*p, vec![ImmExp::Var(name1), i2.clone()], ())),
            ann: (),
        });
    }
    None
}

fn parse_param_exps<Span>(
    params: &[Exp<Span>],
    counter: &mut u32,
) -> (Vec<ImmExp>, Vec<(String, SeqExp<()>)>)
where
    Span: Clone,
{
    let mut let_bindings = vec![];
    let imm_params = params
        .iter()
        .map(|param| {
            let seq_param = seq(param, counter);
            if let SeqExp::Imm(i, _) = seq_param {
                return i;
            }
            let var = format!("#var_{}", counter);
            let_bindings.push((var.clone(), seq_param));
            *counter += 1;
            return ImmExp::Var(var);
        })
        .collect();
    (imm_params, let_bindings)
}

fn generate_nested_let(bindings: &[(String, SeqExp<()>)], body: SeqExp<()>) -> SeqExp<()> {
    if bindings.is_empty() {
        return body;
    }
    SeqExp::Let {
        var: bindings[0].0.clone(),
        bound_exp: Box::new(bindings[0].1.clone()),
        body: Box::new(generate_nested_let(&bindings[1..], body)),
        ann: (),
    }
}

pub fn seq<Span>(e: &Exp<Span>, counter: &mut u32) -> SeqExp<()>
where
    Span: Clone,
{
    match e {
        Exp::Bool(b, _) => SeqExp::Imm(ImmExp::Bool(*b), ()),
        Exp::Num(i, _) => SeqExp::Imm(ImmExp::Num(*i), ()),
        Exp::Var(s, _) => SeqExp::Imm(ImmExp::Var(s.clone()), ()),
        Exp::Prim(p, exps, ann) => {
            let params: Vec<Exp<Span>> = exps.iter().map(|exp| (*exp.clone())).collect();
            let (imm_params, let_bindings) = parse_param_exps(&params, counter);
            generate_nested_let(&let_bindings, SeqExp::Prim(*p, imm_params, ()))
        }
        Exp::Let {
            bindings,
            body,
            ann: _,
        } => {
            let mut optionRes: Option<SeqExp<()>> = None;
            for (var, exp) in bindings.iter().rev() {
                optionRes = Some(SeqExp::Let {
                    var: var.clone(),
                    bound_exp: Box::new(seq(&exp, counter)),
                    body: if optionRes.is_some() {
                        Box::new(optionRes.unwrap())
                    } else {
                        Box::new(seq(body, counter))
                    },
                    ann: (),
                })
            }
            optionRes.unwrap()
        }
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => {
            *counter += 1;
            let var_name = format!("#if_{}", counter);
            SeqExp::Let {
                var: var_name.clone(),
                bound_exp: Box::new(seq(cond, counter)),
                body: Box::new(SeqExp::If {
                    cond: ImmExp::Var(var_name),
                    thn: Box::new(seq(thn, counter)),
                    els: Box::new(seq(els, counter)),
                    ann: (),
                }),
                ann: (),
            }
        }
        Exp::FunDefs { decls, body, ann } => {
            let seq_decls = decls
                .iter()
                .map(|decl| SeqFunDecl {
                    name: decl.name.clone(),
                    parameters: decl.parameters.clone(),
                    body: seq(&decl.body, counter),
                    ann: (),
                })
                .collect();
            SeqExp::FunDefs {
                decls: seq_decls,
                body: Box::new(seq(&body, counter)),
                ann: (),
            }
        }
        Exp::Call(_, _, _) => todo!(),
        Exp::InternalTailCall(func, params, _) => {
            let (imm_params, let_bindings) = parse_param_exps(params, counter);
            generate_nested_let(
                &let_bindings,
                SeqExp::InternalTailCall(func.clone(), imm_params, ()),
            )
        }
        Exp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => todo!(),
    }
}

pub fn seq_prog(decls: &[FunDecl<Exp<()>, ()>], p: &Exp<()>) -> SeqProg<()> {
    let mut counter = 0;
    SeqProg {
        funs: decls
            .iter()
            .map(|decl| {
                let seq_body = seq(&decl.body, &mut counter);
                FunDecl {
                    name: decl.name.clone(),
                    parameters: decl.parameters.clone(),
                    body: seq_body,
                    ann: (),
                }
            })
            .collect(),
        main: seq(p, &mut counter),
        ann: (),
    }
}
