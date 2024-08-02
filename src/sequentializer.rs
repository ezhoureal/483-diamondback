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

pub fn seq<Span>(e: &Exp<Span>, counter: &mut u32) -> SeqExp<()> {
    match e {
        Exp::Bool(b, _) => SeqExp::Imm(ImmExp::Bool(*b), ()),
        Exp::Num(i, _) => SeqExp::Imm(ImmExp::Num(*i), ()),
        Exp::Var(s, _) => SeqExp::Imm(ImmExp::Var(s.clone()), ()),
        Exp::Prim(p, exps, ann) => {
            // Prim_1
            if exps.len() == 1 {
                let a = seq(&exps[0], counter);
                if let Some(flattened) = try_flatten_prim1(p, &a) {
                    return flattened;
                }
                *counter += 1;
                let name1 = format!("#prim1_{}", counter);
                SeqExp::Let {
                    var: name1.clone(),
                    bound_exp: Box::new(a),
                    ann: (),
                    body: Box::new(SeqExp::Prim(*p, vec![ImmExp::Var(name1)], ())),
                }
            // Prim_2
            } else {
                let a = seq(&exps[0], counter);
                let b = seq(&exps[1], counter);
                if let Some(flattened) = try_flatten_prim2(p, &a, &b, counter) {
                    return flattened;
                }
                *counter += 1;
                let name1 = format!("#prim2_1_{}", counter);
                let name2 = format!("#prim2_2_{}", counter);
                SeqExp::Let {
                    var: name1.clone(),
                    bound_exp: Box::new(a),
                    ann: (),
                    body: Box::new(SeqExp::Let {
                        var: name2.clone(),
                        bound_exp: Box::new(b),
                        ann: (),
                        body: Box::new(SeqExp::Prim(
                            *p,
                            vec![ImmExp::Var(name1), ImmExp::Var(name2)],
                            (),
                        )),
                    }),
                }
            }
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
        Exp::FunDefs { decls, body, ann } => todo!(),
        Exp::Call(_, _, _) => todo!(),
        Exp::InternalTailCall(_, _, _) => todo!(),
        Exp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => todo!(),
    }
}