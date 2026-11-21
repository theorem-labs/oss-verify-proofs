(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Dispatch.
  Variable flush : Z.

  Theorem dispatch_safe : forall w0 s c r,
    WINV (mkW s c r) -> PHI (mkW s c r) <= PHI w0 -> POST w0 (dispatch ivar_ref flush (mkW s c r)).
  Proof.
    intros w0 s c r HW HP. unfold dispatch. arun gs_eq. cbv zeta.
    Ltac try_arm lem := lazymatch goal with |- POST ?w0 ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [exact (lem w0 s c r ltac:(assumption) E ltac:(assumption))|] end.
    try_arm (arm_HEAD_safe). try_arm (arm_FLAGS_safe). try_arm (arm_TIME_safe). try_arm (arm_OS_safe).
    try_arm (arm_EXLEN_safe). try_arm (arm_EXTRA_safe). try_arm (arm_NAME_safe). try_arm (arm_COMMENT_safe).
    try_arm (arm_HCRC_safe). try_arm (arm_DICTID_safe ivar_ref flush). try_arm (arm_DICT_safe ivar_ref flush).
    try_arm (arm_TYPE_safe ivar_ref flush). try_arm (arm_TYPEDO_safe ivar_ref flush). try_arm (arm_STORED_safe ivar_ref flush).
    try_arm (arm_COPY__safe). try_arm (arm_COPY_safe). try_arm (arm_TABLE_safe flush). try_arm (arm_LENLENS_safe flush).
    try_arm (arm_CODELENS_safe flush). try_arm (arm_LEN__safe). try_arm (arm_LEN_safe). try_arm (arm_LENEXT_safe).
    try_arm (arm_DIST_safe). try_arm (arm_DISTEXT_safe). try_arm (arm_MATCH_safe ivar_ref). try_arm (arm_LIT_safe).
    try_arm (arm_CHECK_safe). try_arm (arm_LENGTH_safe). try_arm (arm_DONE_safe). try_arm (arm_BAD_safe). try_arm (arm_MEM_safe).
    exfalso. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & _ & HMF & _). unfold MF in HMF.
    repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
    cbn [orb] in HMF. exact HMF.
  Qed.
End Dispatch.


Lemma PHI_nonneg : forall w, WINV w -> 0 <= PHI w.
Proof.
  intros [s c r] HW. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & (RN & RH & _ & RP & RL & _ & [RB _] & _) & _).
  unfold PHI. cbn [w_s w_c w_r]. pose proof (rank_range (is_mode s)). lia.
Qed.


Section Loops.
  Variable flush : Z.

  Definition lstep (w : iw) : iw + (istop * iw) :=
    match dispatch ivar_ref flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

  Lemma inf_loop_nat : forall m w, WINV w -> PHI w < Z.of_nat m ->
    let '(stop, w') := iterZ (Z.of_nat m) lstep (fun w0 => (SLeave, w0)) w in
    WINV w' /\
    match stop with
    | SLeave => exists w1, WINV w1 /\ dispatch ivar_ref flush w1 = ALeave w'
    | SRet rc => INV (w_s w')
    end.
  Proof.
    induction m as [|m IH]; intros w HW HP.
    { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    unfold lstep at 1. destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW ltac:(lia)) as D.
    destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w'] eqn:ED.
    - destruct D as [HW' HP']. apply IH; [exact HW'|lia].
    - split; [exact D|]. exists (mkW s c r). split; [exact HW|exact ED].
    - exact D.
  Qed.

  Theorem inf_loop_post : forall w, WINV w ->
    PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
    let '(stop, w') := inf_loop ivar_ref flush w in
    WINV w' /\
    match stop with
    | SLeave => exists w1, WINV w1 /\ dispatch ivar_ref flush w1 = ALeave w'
    | SRet rc => INV (w_s w')
    end.
  Proof.
    intros w HW HP. unfold inf_loop. change (fun w0 : iw => _) with lstep at 1.
    pose proof (PHI_nonneg w HW).
    rewrite <- (Z2Nat.id (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64))) by lia.
    apply inf_loop_nat; [exact HW|]. rewrite Z2Nat.id by lia. exact HP.
  Qed.


  Section Checker.
    Variable arm_ok : Z -> iw -> bool.
    Hypothesis OK : forall w, WINV w -> arm_ok flush w = true.

    Definition okstep' (w : iw) : iw + bool :=
      if arm_ok flush w then
        match dispatch ivar_ref flush w with
        | ARun _ w' => inl w'
        | ALeave _ => inr true
        | ARet _ _ => inr true
        end
      else inr false.

  End Checker.
End Loops.
