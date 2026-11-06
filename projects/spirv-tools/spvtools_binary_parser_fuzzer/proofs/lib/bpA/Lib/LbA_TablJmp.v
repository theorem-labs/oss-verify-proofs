(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_TablStmt LbA_TablReg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition IO_RET1 : Z := 0xfdaf8.
Definition IO_RET0 : Z := 0xfdb00.
Definition FP_RETS : list Z := [0xfe86c; 0xfe878; 0xfe880; 0xfe888; 0xfe890; 0xfe898; 0xfe8a0; 0xfe8a8; 0xfe8b0].

Section Jmp.
  Context {HCEIL : HeapCeil}.

  Theorem is_optional_okA : is_optional_stmtA.
  Proof.
    intros x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    destruct (Z_lt_le_dec x 42) as [Hlo | Hge]; [| destruct (Z_lt_le_dec 106 x) as [Hhi | Hle]].
    - rl_run_gen (Some (0, 41)) AT_IS_OPTIONAL [IO_RET1; IO_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (107, 4294967295)) AT_IS_OPTIONAL [IO_RET1; IO_RET0]. all: bool_lit_post.
    - assert (Hr : 42 <= x < 42 + Z.of_nat 65) by lia.
      enum_range x 42 65%nat Hr; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_IS_OPTIONAL [IO_RET1; IO_RET0]; bool_lit_post).
  Qed.

  Ltac fp_post :=
    idtac;
    lazymatch goal with HR' : regs_ok _ _ ?R' |- _ =>
      let G := fresh "G10" in rreg HR' 10%bv G; rewrite G end;
    lazymatch goal with |- exists r, _ /\ Z_to_bv 64 ?v = Z_to_bv 64 r => exists v; split; [lia | reflexivity] end.

  Theorem fpenc_okA : fpenc_stmtA.
  Proof.
    intros [] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC _.
    pose proof (Z_to_bv_bv_unsigned a0) as Ha0. symmetry in Ha0.
    pose proof (bv_unsigned_in_range _ a0) as Hx. unfold bv_modulus in Hx.
    set (x := bv_unsigned a0) in *. clearbody x. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hx.
    assert (Hc : x = 0 \/ 1 <= x <= 4213 \/ 4228 <= x \/ 4214 <= x < 4214 + Z.of_nat 14) by lia.
    destruct Hc as [Hc | [Hc | [Hc | Hc]]].
    - subst x. rl_run_gen (@None (Z * Z)) AT_FPENC FP_RETS. all: fp_post.
    - rl_run_gen (Some (1, 4213)) AT_FPENC FP_RETS. all: fp_post.
    - rl_run_gen (Some (4228, 18446744073709551615)) AT_FPENC FP_RETS. all: fp_post.
    - enum_range x 4214 14%nat Hc; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_FPENC FP_RETS; fp_post).
  Qed.
End Jmp.
