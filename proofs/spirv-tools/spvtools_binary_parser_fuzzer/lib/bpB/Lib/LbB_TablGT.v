(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg LbB_TablReg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition gt_at {HCEIL : HeapCeil} (x : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 0 ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m ->
    (0 <= x < 2 ^ 32 /\ a0 = Z_to_bv 64 x) ->
    evt asegs (tl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [] lo m
                 (fun r0 _ _ => exists b : bool, r0 = Z_to_bv 64 (if b then 1 else 0) /\ (b = true -> tg_generates_type x = true)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_GENERATES_TYPE) fc None m (seg_rom asegs)).

Definition GT_RET1 : Z := 0xfdc8c.
Definition GT_RET0 : Z := 0xfdd7c.

Section GT.
  Context {HCEIL : HeapCeil}.
  Lemma gt_lo : forall x, x < 4417 -> gt_at x.
  Proof.
    intros x XR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    assert (Hc : x < 19 \/ 19 <= x < 19 + Z.of_nat 20 \/ 39 <= x <= 321 \/ x = 322 \/ 323 <= x <= 326 \/ x = 327 \/ 328 <= x <= 4162
                 \/ x = 4163 \/ 4164 <= x <= 4189 \/ x = 4190 \/ 4191 <= x <= 4416) by lia.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
    - rl_run_gen (Some (0, 18)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - enum_range x 19 20%nat H; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]; bool_lit_post).
    - rl_run_gen (Some (39, 321)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (323, 326)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (328, 4162)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (4164, 4189)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (4191, 4416)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
  Qed.
End GT.
