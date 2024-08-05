use crate::asm::instrs_to_string;
use crate::asm::{Arg32, Arg64, BinArgs, Instr, Loc, MemRef, MovArgs, Reg, Reg32};
use crate::checker;
use crate::lambda_lift::lambda_lift;
use crate::sequentializer;
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

// returns instruction to move imm to Rax
fn imm_to_rax(imm: &ImmExp, stack: &HashMap<String, i32>) -> Vec<Instr> {
    vec![Instr::Mov(MovArgs::ToReg(
        Reg::Rax,
        imm_to_arg64(imm, stack),
    ))]
}

static SNAKE_TRU: u64 = 0xFF_FF_FF_FF_FF_FF_FF_FF;
static SNAKE_FLS: u64 = 0x7F_FF_FF_FF_FF_FF_FF_FF;

static OVERFLOW: &str = "overflow_error";
static ARITH_ERROR: &str = "arith_error";
static CMP_ERROR: &str = "cmp_error";
static IF_ERROR: &str = "if_error";
static LOGIC_ERROR: &str = "logic_error";
static SNAKE_ERROR: &str = "snake_error";

fn imm_to_arg64(imm: &ImmExp, stack: &HashMap<String, i32>) -> Arg64 {
    match &imm {
        ImmExp::Num(i) => Arg64::Signed(*i << 1),
        ImmExp::Var(s) => {
            let offset = stack[s];
            Arg64::Mem(MemRef {
                reg: Reg::Rsp,
                offset: -offset,
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

fn sub_for_cmp(exps: &Vec<ImmExp>, stack: &HashMap<String, i32>, reverse: bool) -> Vec<Instr> {
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
    stack: &'b mut HashMap<String, i32>,
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
                        Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_stack + 8))),
                        Instr::Call("print_snake_val".to_string()),
                        Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_stack + 8))),
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
                    offset: -offset,
                },
                Reg32::Reg(Reg::Rax),
            )));
            stack.insert(var.clone(), offset);

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
        SeqExp::FunDefs { decls, body, ann } => {
            let mut res = vec![];
            for decl in decls {
                res.push(Instr::Label(decl.name.clone()));
                res.extend(compile_to_instrs_inner(
                    &decl.body, counter, max_stack, stack,
                ));
                res.push(Instr::Ret);
            }
            res
        }
        SeqExp::InternalTailCall(_, _, _) => todo!(),
        SeqExp::ExternalCall {
            fun_name,
            args,
            is_tail,
            ann,
        } => {
            let mut offset: i32 = max_stack.try_into().unwrap();
            offset += 16;
            let mut res = vec![];
            for arg in args {
                res.push(Instr::Mov(MovArgs::ToReg(
                    Reg::Rax,
                    imm_to_arg64(arg, stack),
                )));
                res.push(Instr::Mov(MovArgs::ToMem(
                    MemRef {
                        reg: Reg::Rsp,
                        offset: -offset,
                    },
                    Reg32::Reg(Reg::Rax),
                )));
                offset += 8;
            }
            // record called function's parameters to [stack]
            res.push(Instr::Sub(BinArgs::ToReg(
                Reg::Rsp,
                Arg32::Unsigned(max_stack),
            )));
            res.push(Instr::Jmp(fun_name.clone()));
            res.push(Instr::Add(BinArgs::ToReg(
                Reg::Rsp,
                Arg32::Unsigned(max_stack),
            )));
            res
        }
    }
}

/* Feel free to add any helper functions you need */
fn compile_to_instrs(e: &SeqExp<()>, counter: &mut u32) -> Vec<Instr> {
    let max_stack = space_needed(e);
    let mut is = compile_to_instrs_inner(e, counter, max_stack, &mut HashMap::new());
    is.push(Instr::Ret);
    is
}

fn compile_func_to_instr(f: &FunDecl<SeqExp<()>, ()>, counter: &mut u32) -> Vec<Instr> {
    let max_stack = space_needed(&f.body);
    let mut stack = HashMap::<String, i32>::new();
    for (i, param) in f.parameters.iter().enumerate() {
        stack.insert(param.clone(), i32::try_from(i).unwrap() + 1);
    }
    compile_to_instrs_inner(&f.body, counter, max_stack, &mut stack)
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
    // even stack upon entry for internal SNAKE calls
    // odd variables alloc + 1 return address alloc
    if stack % 2 == 0 {
        stack += 1;
    }
    stack *= 8;
    stack
}

fn error_handle_instr() -> Vec<Instr> {
    vec![
        Instr::Label(ARITH_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(0))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(CMP_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(1))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(OVERFLOW.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(2))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(IF_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(3))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Call(SNAKE_ERROR.to_string()),
        Instr::Label(LOGIC_ERROR.to_string()),
        Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(4))),
        Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))),
        Instr::Call(SNAKE_ERROR.to_string()),
    ]
}

pub fn check_prog<Span>(p: &SurfProg<Span>) -> Result<(), CompileErr<Span>>
where
    Span: Clone,
{
    let res = checker::check_prog(p, &HashMap::new());
    res
}

pub fn compile_to_string<Span>(p: &SurfProg<Span>) -> Result<String, CompileErr<Span>>
where
    Span: Clone,
{
    checker::check_prog(p, &HashMap::new())?;
    let (global_functions, main) = lambda_lift(&p);
    let program = sequentializer::seq_prog(&global_functions, &main);

    let mut counter : u32 = 0;
    let functions_is: String = program
        .funs
        .iter()
        .map(|f| {
            instrs_to_string(&compile_func_to_instr(&f, &mut counter))
        })
        .collect();
    let main_is = instrs_to_string(&compile_to_instrs(&program.main, &mut counter));

    let res = format!(
        "\
        section .text
        global start_here
        extern snake_error
        extern print_snake_val
{}
{}
start_here:
        call main
        ret
main:
{}
        ret
",
        instrs_to_string(&error_handle_instr()),
        functions_is,
        main_is
    );
    println!("{}", res);
    Ok(res)
}
