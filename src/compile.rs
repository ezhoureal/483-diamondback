use crate::asm::instrs_to_string;
use crate::asm::{Arg32, Arg64, BinArgs, Instr, Loc, MemRef, MovArgs, Reg, Reg32};
use crate::syntax::{Exp, FunDecl, ImmExp, Prim, SeqExp, SeqProg, SurfFunDecl, SurfProg};

use std::collections::{HashMap, HashSet};
use std::convert::{TryFrom, TryInto};
use std::f32::consts::E;
use std::hash::Hash;

#[derive(Debug, PartialEq, Eq)]
pub enum CompileErr<Span> {
    UnboundVariable {
        unbound: String,
        location: Span,
    },
    UndefinedFunction {
        undefined: String,
        location: Span,
    },
    // The Span here is the Span of the let-expression that has the two duplicated bindings
    DuplicateBinding {
        duplicated_name: String,
        location: Span,
    },

    Overflow {
        num: i64,
        location: Span,
    },

    DuplicateFunName {
        duplicated_name: String,
        location: Span, // the location of the 2nd function
    },

    DuplicateArgName {
        duplicated_name: String,
        location: Span,
    },

    FunctionUsedAsValue {
        function_name: String,
        location: Span,
    },

    ValueUsedAsFunction {
        variable_name: String,
        location: Span,
    },

    FunctionCalledWrongArity {
        function_name: String,
        correct_arity: usize,
        arity_used: usize,
        location: Span, // location of the function *call*
    },
}

pub fn check_prog<Span>(p: &SurfProg<Span>) -> Result<(), CompileErr<Span>>
where
    Span: Clone,
{
    let res = check_prog_inner(p, &HashMap::new());
    res
}

static I63_MAX: i64 = 0x3F_FF_FF_FF_FF_FF_FF_FF;
static I63_MIN: i64 = -0x40_00_00_00_00_00_00_00;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Symbol {
    Func(Vec<String>),
    Var,
}

fn check_prog_inner<Span>(
    e: &Exp<Span>,
    symbols: &HashMap<String, Symbol>,
) -> Result<(), CompileErr<Span>>
where
    Span: Clone,
{
    match e {
        Exp::Num(i, ann) => {
            if *i > I63_MAX || *i < I63_MIN {
                return Err(CompileErr::Overflow {
                    num: *i,
                    location: ann.clone(),
                });
            }
            Ok(())
        }
        Exp::Var(name, ann) => {
            if !symbols.contains_key(name) {
                return Err(CompileErr::UnboundVariable {
                    unbound: name.clone(),
                    location: ann.clone(),
                });
            }
            if let Symbol::Func(_) = symbols[name] {
                return Err(CompileErr::FunctionUsedAsValue {
                    function_name: name.clone(),
                    location: ann.clone(),
                });
            }
            Ok(())
        }
        Exp::Prim(_, exps, _) => {
            for e in exps {
                check_prog_inner(e, symbols)?;
            }
            Ok(())
        }
        Exp::Let {
            bindings,
            body,
            ann,
        } => {
            let mut scoped_symbols = symbols.clone();
            let mut appeared = HashSet::new();
            for (name, value) in bindings {
                if appeared.contains(name) {
                    return Err(CompileErr::DuplicateBinding {
                        duplicated_name: name.clone(),
                        location: ann.clone(),
                    });
                }
                appeared.insert(name);
                scoped_symbols.insert(name.clone(), Symbol::Var);
                check_prog_inner(value, &scoped_symbols)?;
            }
            check_prog_inner(body, &scoped_symbols)
        }
        Exp::Bool(_, _) => Ok(()),
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => {
            check_prog_inner(cond, symbols)?;
            check_prog_inner(&thn, symbols)?;
            check_prog_inner(&els, symbols)?;
            Ok(())
        }
        Exp::FunDefs { decls, body, ann } => {
            let mut scoped_symbols = symbols.clone();
            let mut mutual_funcs = HashSet::<String>::new();
            for decl in decls {
                if mutual_funcs.contains(&decl.name) {
                    return Err(CompileErr::DuplicateFunName {
                        duplicated_name: decl.name.clone(),
                        location: ann.clone(),
                    });
                }
                mutual_funcs.insert(decl.name.clone());
                scoped_symbols.insert(decl.name.clone(), Symbol::Func(decl.parameters.clone()));
                check_prog_inner(&decl.body, &scoped_symbols)?;
            }
            check_prog_inner(body, &scoped_symbols)
        }
        Exp::Call(func, params, ann) => {
            if !symbols.contains_key(func) {
                return Err(CompileErr::UndefinedFunction {
                    undefined: func.clone(),
                    location: ann.clone(),
                });
            }
            match &symbols[func] {
                Symbol::Func(decl_params) => {
                    if params.len() != decl_params.len() {
                        return Err(CompileErr::FunctionCalledWrongArity {
                            function_name: func.clone(),
                            correct_arity: decl_params.len(),
                            arity_used: params.len(),
                            location: ann.clone(),
                        });
                    }
                }
                Symbol::Var => {
                    return Err(CompileErr::ValueUsedAsFunction {
                        variable_name: func.clone(),
                        location: ann.clone(),
                    });
                }
            }
            for p in params {
                check_prog_inner(p, &symbols)?;
            }
            Ok(())
        }
        Exp::InternalTailCall(_, _, _) => todo!(),
        Exp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => todo!(),
    }
}

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

fn sequentialize<Span>(e: &Exp<Span>, counter: &mut u32) -> SeqExp<()> {
    match e {
        Exp::Bool(b, _) => SeqExp::Imm(ImmExp::Bool(*b), ()),
        Exp::Num(i, _) => SeqExp::Imm(ImmExp::Num(*i), ()),
        Exp::Var(s, _) => SeqExp::Imm(ImmExp::Var(s.clone()), ()),
        Exp::Prim(p, exps, ann) => {
            // Prim_1
            if exps.len() == 1 {
                let a = sequentialize(&exps[0], counter);
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
                let a = sequentialize(&exps[0], counter);
                let b = sequentialize(&exps[1], counter);
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
                    bound_exp: Box::new(sequentialize(&exp, counter)),
                    body: if optionRes.is_some() {
                        Box::new(optionRes.unwrap())
                    } else {
                        Box::new(sequentialize(body, counter))
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
                bound_exp: Box::new(sequentialize(cond, counter)),
                body: Box::new(SeqExp::If {
                    cond: ImmExp::Var(var_name),
                    thn: Box::new(sequentialize(thn, counter)),
                    els: Box::new(sequentialize(els, counter)),
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

// returns instruction to move imm to Rax
fn imm_to_rax(imm: &ImmExp, stack: &[(&str, i32)]) -> Vec<Instr> {
    vec![Instr::Mov(MovArgs::ToReg(
        Reg::Rax,
        imm_to_arg64(imm, stack),
    ))]
}

/* Encapsulate imm as BinArgs, use case: the second parameter of prim */
fn num_to_bin_args(imm: &ImmExp, stack: &[(&str, i32)]) -> BinArgs {
    match &imm {
        ImmExp::Num(i) => BinArgs::ToReg(Reg::Rax, Arg32::Signed((*i << 1).try_into().unwrap())),
        ImmExp::Var(s) => {
            let offset = get(stack, &s).unwrap();
            BinArgs::ToReg(
                Reg::Rax,
                Arg32::Mem(MemRef {
                    reg: Reg::Rsp,
                    offset: offset,
                }),
            )
        }
        ImmExp::Bool(_) => todo!(), // not supported
    }
}

fn get<T>(env: &[(&str, T)], x: &str) -> Option<T>
where
    T: Copy,
{
    for (y, n) in env.iter().rev() {
        if x == *y {
            return Some(*n);
        }
    }
    None
}

static SNAKE_TRU: u64 = 0xFF_FF_FF_FF_FF_FF_FF_FF;
static SNAKE_FLS: u64 = 0x7F_FF_FF_FF_FF_FF_FF_FF;

static OVERFLOW: &str = "overflow_error";
static ARITH_ERROR: &str = "arith_error";
static CMP_ERROR: &str = "cmp_error";
static IF_ERROR: &str = "if_error";
static LOGIC_ERROR: &str = "logic_error";
static SNAKE_ERROR: &str = "snake_error";

fn imm_to_arg64(imm: &ImmExp, stack: &[(&str, i32)]) -> Arg64 {
    match &imm {
        ImmExp::Num(i) => Arg64::Signed(*i << 1),
        ImmExp::Var(s) => {
            let offset = get(stack, &s).unwrap();
            Arg64::Mem(MemRef {
                reg: Reg::Rsp,
                offset: offset,
            })
        }
        ImmExp::Bool(b) => {
            if *b {
                Arg64::Unsigned(SNAKE_TRU)
            } else {
                Arg64::Unsigned(SNAKE_FLS)
            }
        }
    }
}

fn sub_for_cmp(exps: &Vec<ImmExp>, stack: &Vec<(&str, i32)>, reverse: bool) -> Vec<Instr> {
    let mut res = vec![];
    if reverse {
        // exps[1] - exps[0]
        res.append(&mut vec![
            Instr::Mov(MovArgs::ToReg(Reg::Rdx, imm_to_arg64(&exps[0], stack))),
            Instr::Mov(MovArgs::ToReg(Reg::Rax, imm_to_arg64(&exps[1], stack))),
        ]);
    } else {
        // exps[0] - exps[1]
        res.append(&mut vec![
            Instr::Mov(MovArgs::ToReg(Reg::Rax, imm_to_arg64(&exps[0], stack))),
            Instr::Mov(MovArgs::ToReg(Reg::Rdx, imm_to_arg64(&exps[1], stack))),
        ]);
    }
    res.append(&mut cmp_check(Reg::Rax));
    res.append(&mut cmp_check(Reg::Rdx));

    res.append(&mut vec![
        Instr::Sar(BinArgs::ToReg(Reg::Rax, Arg32::Signed(1))),
        Instr::Sar(BinArgs::ToReg(Reg::Rdx, Arg32::Signed(1))),
        Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
    ]);
    res
}

/// return instructions to convert sign in Rax to boolean value
fn is_neg() -> Vec<Instr> {
    static NEG_MASK: u64 = 0x7F_FF_FF_FF_FF_FF_FF_FF;
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rdx, Arg64::Unsigned(NEG_MASK))),
        Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
    ]
}

fn is_non_neg() -> Vec<Instr> {
    static NON_NEG_MASK: u64 = 0x80_00_00_00_00_00_00_00;
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rdx, Arg64::Unsigned(NON_NEG_MASK))),
        Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
        Instr::Mov(MovArgs::ToReg(Reg::Rdx, Arg64::Unsigned(SNAKE_FLS))),
        Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
    ]
}

fn arith_check(reg: Reg) -> Vec<Instr> {
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rcx, Arg64::Reg(reg))),
        Instr::And(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Cmp(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Je(ARITH_ERROR.to_string()),
    ]
}

fn cmp_check(reg: Reg) -> Vec<Instr> {
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rcx, Arg64::Reg(reg))),
        Instr::And(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Cmp(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Je(CMP_ERROR.to_string()),
    ]
}

fn logic_check(reg: Reg) -> Vec<Instr> {
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rcx, Arg64::Reg(reg))),
        Instr::And(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Cmp(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(0))),
        Instr::Je(LOGIC_ERROR.to_string()),
    ]
}

fn if_check(reg: Reg) -> Vec<Instr> {
    vec![
        Instr::Mov(MovArgs::ToReg(Reg::Rcx, Arg64::Reg(reg))),
        Instr::And(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(1))),
        Instr::Cmp(BinArgs::ToReg(Reg::Rcx, Arg32::Signed(0))),
        Instr::Je(IF_ERROR.to_string()),
    ]
}

fn compile_to_instrs_inner<'a, 'b>(
    e: &'a SeqExp<()>,
    counter: &mut u32,
    max_stack: u32,
    stack: &'b mut Vec<(&'a str, i32)>,
) -> Vec<Instr> {
    match e {
        SeqExp::Imm(exp, _) => imm_to_rax(exp, stack),
        SeqExp::Prim(p, exps, _) => {
            let mut res = imm_to_rax(&exps[0], stack);
            //
            match p {
                Prim::Add => {
                    res.append(&mut arith_check(Reg::Rax));
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    res.append(&mut arith_check(Reg::Rdx));
                    res.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                    res.push(Instr::Jo(OVERFLOW.to_string()));
                }
                Prim::Sub => {
                    res.append(&mut arith_check(Reg::Rax));
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    res.append(&mut arith_check(Reg::Rdx));
                    res.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                    res.push(Instr::Jo(OVERFLOW.to_string()));
                }
                Prim::Mul => {
                    res.append(&mut arith_check(Reg::Rax));
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    res.append(&mut arith_check(Reg::Rdx));
                    res.push(Instr::Sar(BinArgs::ToReg(Reg::Rdx, Arg32::Signed(1))));
                    res.push(Instr::IMul(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                    res.push(Instr::Jo(OVERFLOW.to_string()));
                }
                Prim::Add1 => {
                    res.append(&mut arith_check(Reg::Rax));
                    res.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(0x2))));
                    res.push(Instr::Jo(OVERFLOW.to_string()));
                }
                Prim::Sub1 => {
                    res.append(&mut arith_check(Reg::Rax));
                    res.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(0x2))));
                    res.push(Instr::Jo(OVERFLOW.to_string()));
                }
                Prim::Not => {
                    res.append(&mut logic_check(Reg::Rax));
                    static BOOL_MASK: u64 = 0x80_00_00_00_00_00_00_00;
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        Arg64::Unsigned(BOOL_MASK),
                    )));
                    res.push(Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                }
                Prim::Print => {
                    res = vec![
                        Instr::Mov(MovArgs::ToReg(Reg::Rdi, imm_to_arg64(&exps[0], stack))),
                        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_stack))),
                        Instr::Call("print_snake_val".to_string()),
                        Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_stack))),
                    ];
                }
                Prim::IsBool => {
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        Arg64::Unsigned(SNAKE_FLS),
                    )));
                    res.push(Instr::And(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                    res.push(Instr::Shl(BinArgs::ToReg(Reg::Rax, Arg32::Signed(63))));
                    res.push(Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                }
                Prim::IsNum => {
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        Arg64::Unsigned(SNAKE_FLS),
                    )));
                    res.push(Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                    res.push(Instr::Shl(BinArgs::ToReg(Reg::Rax, Arg32::Signed(63))));
                    res.push(Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                }
                Prim::And => {
                    res.append(&mut logic_check(Reg::Rax));
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    res.append(&mut logic_check(Reg::Rdx));
                    res.push(Instr::And(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                }
                Prim::Or => {
                    res.append(&mut logic_check(Reg::Rax));
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    res.append(&mut logic_check(Reg::Rdx));
                    res.push(Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                }
                Prim::Lt => {
                    res.append(&mut sub_for_cmp(exps, stack, false));
                    res.append(&mut is_neg());
                }
                Prim::Gt => {
                    res.append(&mut sub_for_cmp(exps, stack, true));
                    res.append(&mut is_neg());
                }
                Prim::Le => {
                    res.append(&mut sub_for_cmp(exps, stack, true));
                    res.append(&mut is_non_neg());
                }
                Prim::Ge => {
                    res.append(&mut sub_for_cmp(exps, stack, false));
                    res.append(&mut is_non_neg());
                }
                Prim::Eq => {
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    *counter += 1;
                    let fls_label = format!("false_{}", counter);
                    let done_label = format!("cmp_done_{}", counter);
                    res.append(&mut vec![
                        Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
                        Instr::Jne(fls_label.clone()),
                        Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(SNAKE_TRU))),
                        Instr::Jmp(done_label.clone()),
                        Instr::Label(fls_label),
                        Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(SNAKE_FLS))),
                        Instr::Label(done_label),
                    ]);
                }
                Prim::Neq => {
                    res.push(Instr::Mov(MovArgs::ToReg(
                        Reg::Rdx,
                        imm_to_arg64(&exps[1], stack),
                    )));
                    *counter += 1;
                    let fls_label = format!("false_{}", counter);
                    let done_label = format!("cmp_done_{}", counter);
                    res.append(&mut vec![
                        Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
                        Instr::Je(fls_label.clone()),
                        Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(SNAKE_TRU))),
                        Instr::Jmp(done_label.clone()),
                        Instr::Label(fls_label),
                        Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(SNAKE_FLS))),
                        Instr::Label(done_label),
                    ]);
                }
            }
            res
        }
        SeqExp::Let {
            var,
            bound_exp,
            body,
            ann,
        } => {
            let mut res = compile_to_instrs_inner(&bound_exp, counter, max_stack, stack);
            let offset: i32 = ((stack.len() + 1) * 8).try_into().unwrap();
            res.push(Instr::Mov(MovArgs::ToMem(
                MemRef {
                    reg: Reg::Rsp,
                    offset: offset,
                },
                Reg32::Reg(Reg::Rax),
            )));
            stack.push((var, offset));

            res.append(&mut compile_to_instrs_inner(
                &body, counter, max_stack, stack,
            ));
            res
        }
        SeqExp::If {
            cond,
            thn,
            els,
            ann,
        } => {
            let mut res = imm_to_rax(cond, stack);
            res.append(&mut if_check(Reg::Rax));
            *counter += 1;
            let els_label = format!("else_{}", counter);
            let done_label = format!("done_{}", counter);
            res.append(&mut vec![
                // todo: fix cmp with types
                Instr::Mov(MovArgs::ToReg(Reg::Rdx, Arg64::Unsigned(SNAKE_FLS))),
                Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))),
                Instr::Je(els_label.clone()),
            ]);

            res.append(&mut compile_to_instrs_inner(
                thn,
                counter,
                max_stack,
                &mut stack.clone(),
            ));
            res.push(Instr::Jmp(done_label.clone()));

            res.push(Instr::Label(els_label));
            res.append(&mut compile_to_instrs_inner(els, counter, max_stack, stack));
            res.push(Instr::Label(done_label));
            res
        }
        SeqExp::FunDefs { decls, body, ann } => todo!(),
        SeqExp::InternalTailCall(_, _, _) => todo!(),
        SeqExp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => todo!(),
    }
}

/* Feel free to add any helper functions you need */
fn compile_to_instrs(e: &SeqExp<()>, max_stack: u32) -> Vec<Instr> {
    let mut is = compile_to_instrs_inner(e, &mut 0, max_stack, &mut vec![]);
    is.push(Instr::Ret);
    is
}

fn space_needed(e: &SeqExp<()>) -> u32 {
    let mut stack = 0;
    match e {
        SeqExp::Let {
            var,
            bound_exp,
            body,
            ann,
        } => stack = space_needed(&bound_exp) + space_needed(&body) + 1,
        SeqExp::Imm(_, _) => {}
        SeqExp::Prim(_, _, _) => {}
        SeqExp::If {
            cond,
            thn,
            els,
            ann,
        } => stack = std::cmp::max(space_needed(&thn), space_needed(&els)),
        SeqExp::FunDefs { decls, body, ann } => todo!(),
        SeqExp::InternalTailCall(_, _, _) => todo!(),
        SeqExp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => todo!(),
    }
    if stack % 2 == 0 {
        stack += 1;
    }
    stack *= 8;
    stack
}

fn error_handle_instr(e: &SeqExp<()>) -> Vec<Instr> {
    let stack = space_needed(&e);
    vec![
        Instr::Label(ARITH_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(0))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(stack))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(CMP_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(1))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(stack))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(OVERFLOW.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(2))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(stack))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(IF_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(3))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(stack))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(LOGIC_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(4))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(stack))),
        Instr::Call(SNAKE_ERROR.to_string()),
    ]
}

pub fn compile_to_string<Span>(p: &SurfProg<Span>) -> Result<String, CompileErr<Span>>
where
    Span: Clone,
{
    check_prog(p)?;
    let unique_p = uniquify(&p, &mut HashMap::new(), &mut 0);
    // let (decls, main) = lambda_lift(&unique_p);
    // let program = seq_prog(&decls, &main);

    let seq = sequentialize(p, &mut 0);
    let max_stack = space_needed(&seq);
    let main_is = compile_to_instrs(&seq, max_stack);

    let main_str = instrs_to_string(&main_is);
    let res = format!(
        "\
        section .text
        global start_here
        extern snake_error
        extern print_snake_val
{}
start_here:
{}       
",
        instrs_to_string(&error_handle_instr(&seq)),
        main_str
    );
    println!("{}", res);
    Ok(res)
}

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
                let new_name = format!("{}", counter);
                scoped_mapping.insert(decl.name.to_string(), new_name.clone());
            }
            let uniq_decls = decls
                .iter()
                .map(|decl| FunDecl {
                    name: scoped_mapping[&decl.name].clone(),
                    parameters: decl
                        .parameters
                        .iter()
                        .map(|param| scoped_mapping[param].clone())
                        .collect(),
                    body: uniquify(&body, &scoped_mapping, counter),
                    ann: (),
                })
                .collect();
            Exp::FunDefs {
                decls: uniq_decls,
                body: Box::new(uniquify(&body, mapping, counter)),
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
fn should_lift<Ann>(p: &Exp<Ann>) -> HashSet<String> {
    panic!("NYI: should lift")
}

// Lift some functions to global definitions
fn lambda_lift<Ann>(p: &Exp<Ann>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {
    panic!("NYI: lambda_lift")
}

fn seq_prog(decls: &[FunDecl<Exp<()>, ()>], p: &Exp<()>) -> SeqProg<()> {
    panic!("NYI: seq_prog")
}
