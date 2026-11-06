(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

Definition SCALBNL : Z := 0x1fbfc.
Definition COPYSIGNL : Z := 0x1f8ec.
Definition FABSL : Z := 0x1fbf0.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs)
    /\ munch [] m m /\ wmono psegs m m /\ mem_inv psegs m.
Definition scal_reduce (x n : Z) : Z * Z :=
  (if 16383 <? n then
    let x := f128_mul x C_2P16383 in let n := n - 16383 in
    if 16383 <? n then
      let x := f128_mul x C_2P16383 in let n := n - 16383 in (x, if 16383 <? n then 16383 else n)
    else (x, n)
  else if n <? -16382 then
    let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in
    if n <? -16382 then
      let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in (x, if n <? -16382 then -16382 else n)
    else (x, n)
  else (x, n))%Z.
Definition U1 : Z := f128_of_d (bv_unsigned D_ONE).
Definition scal_u (n : Z) : Z :=
  mk128 (Z.lor (Z.land (hi64 U1) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n)%Z 0xffff) 48)) (lo64 U1).

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             (bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 112, q)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 112) q.

Definition scalbnl_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
  stk psegs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
  (-2^31 <= n < 2^31)%Z ->
  mem_inv psegs m ->
  evt psegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCALBNL) fc None m (seg_rom psegs)).
#[export] Instance P_scalbnl_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.scalbnl_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.scalbnl_spec_c_ok.
#[export] Instance P_fabsl_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.fabsl_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.fabsl_spec_c_ok.
#[export] Instance P_copysignl_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.copysignl_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scalbnl.copysignl_spec_c_ok.
