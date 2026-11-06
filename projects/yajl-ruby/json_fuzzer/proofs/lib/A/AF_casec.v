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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cstep := stepA; try first [if_true | if_false].
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section CA.
Variable P : acc -> Prop.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo CA sz : Z).
#[local] Notation INST := 697624.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis SZ : 0x10000 < sz <= 2^40.
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).

Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
Notation CFRAME m s0 s1 s2 s3 s4 := (rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

(* [comment removed for export] *)
Definition ca_at_lal (t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x37348) SP' gp tp t0 t1 t2 (Z_to_bv 64 8) s1 (Z_to_bv 64 (INST + 64)) (Z_to_bv 64 (INST + 688)) (Z_to_bv 64 sz) (Z_to_bv 64 8)
                 (Z_to_bv 64 (INST + 64)) (Z_to_bv 64 0x10000) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37578) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ CFRAME m' s0 s1 s2 s3 s4.

Lemma ca_sec_front :
  forall (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem),
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  evtA asegs P (ca_at_lal t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 CA) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x372a0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros SK MI.
  pose proof LOC as LOC1. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  Ltac arith := repeat match goal with
                | H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                | H : mem_inv _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H
                | H : forall a n, _ -> _ -> P _ |- _ => clear H end; lia.
  Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by arith; intros K; arith.
  Ltac br1 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill K|]).
  Ltac br2 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [| kill K]).
  carve_frame 48%nat SK.
  do 7 cstep.                     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace (sz <? 1) with false by (symmetry; apply Z.ltb_ge; clear -CEILB SZ; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small sz 18446744073709551616) by (clear -CEILB SZ; lia).
  rewrite lnot_mod64 by (clear -CEILB SZ; lia). unfold Z.lnot. change (Z.pred (- sz)) with (- sz - 1) || idtac.
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by arith. clear -CEILB SZ. intros K0. Z.div_mod_to_equations. lia. }
  do 2 zstepA. br2.               (* [comment removed for export] *)
  zstepA. cstep.                  (* [comment removed for export] *)
  br2.                            (* [comment removed for export] *)
  do 5 zstepA.                    (* [comment removed for export] *)
  apply evtA_done. unfold ca_at_lal. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.

(* [comment removed for export] *)
Definition ca_sec_ret (r : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma ca_sec_back :
  forall (xt0 xt1 xt2 s1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 s0 : word) (m : mem) (r : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -48) -> CFRAME m s0 s1 s2 s3 s4 -> 0 <= r < 2^64 ->
  evtA asegs P (ca_sec_ret r s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
    (MS (mkR (Z_to_bv 64 0x37348) SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 8) s1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x37348) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until r. intros MI SK CFR HR.
  pose proof LOC as LOC1. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  do 2 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 7 cstep.                     (* [comment removed for export] *)
  release_frame CFR SK (bv_unsigned sp).
  cstep.                          (* [comment removed for export] *)
  finishA.
Qed.
End CA.
End RC__1.
