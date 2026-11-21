(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section ArmFor.
  Variable iv : ivariant.
Variable flush : Z.
  Definition arm_for (m : Z) : AM unit :=
    if m =? HEAD then arm_HEAD iv
    else if m =? FLAGS then arm_FLAGS
    else if m =? TIME then arm_TIME
    else if m =? OS then arm_OS
    else if m =? EXLEN then arm_EXLEN
    else if m =? EXTRA then arm_EXTRA
    else if m =? NAME then arm_NAME
    else if m =? COMMENT then arm_COMMENT
    else if m =? HCRC then arm_HCRC
    else if m =? DICTID then arm_DICTID iv flush
    else if m =? DICT then arm_DICT iv flush
    else if m =? TYPE then arm_TYPE iv flush
    else if m =? TYPEDO then arm_TYPEDO iv flush
    else if m =? STORED then arm_STORED iv flush
    else if m =? COPY_ then arm_COPY_
    else if m =? COPY then arm_COPY
    else if m =? TABLE then arm_TABLE iv flush
    else if m =? LENLENS then arm_LENLENS iv flush
    else if m =? CODELENS then arm_CODELENS iv flush
    else if m =? LEN_ then arm_LEN_ iv
    else if m =? LEN then arm_LEN iv
    else if m =? LENEXT then arm_LENEXT iv
    else if m =? DIST then arm_DIST iv
    else if m =? DISTEXT then arm_DISTEXT iv
    else if m =? MATCH then arm_MATCH iv
    else if m =? LIT then arm_LIT
    else if m =? CHECK then arm_CHECK
    else if m =? LENGTH then arm_LENGTH
    else if m =? DONE then arm_DONE
    else if m =? BAD then arm_BAD
    else if m =? MEM then arm_MEM
    else arm_SYNC.

  Lemma dispatch_eq : forall w, dispatch iv flush w = arm_for (is_mode (w_s w)) w.
  Proof. intros w. reflexivity. Qed.
End ArmFor.


Definition jt_entry (i : Z) : Z := nth (Z.to_nat i) arm_pcs 0.

Lemma arm_pc_jt : forall m, HEAD <= m < SYNC -> arm_pc m = jt_entry (m - HEAD).
Proof. intros m Hm. unfold arm_pc, jt_entry. rewrite (nth_indep _ 0x190c4 0); [reflexivity|]. cbn [length arm_pcs]. unfold HEAD, SYNC in *. lia. Qed.

Lemma same_blocks_refl : forall s, same_blocks s s.
Proof. intros s. repeat split; reflexivity. Qed.
Lemma same_blocks_trans : forall s1 s2 s3, same_blocks s1 s2 -> same_blocks s2 s3 -> same_blocks s1 s3.
Proof. intros s1 s2 s3 (A1 & A2 & A3) (B1 & B2 & B3). unfold same_blocks. rewrite B1, B2, B3. repeat split; assumption. Qed.

Section Dispatch.

  Lemma jt_entry_range : forall k, 0 <= k < 31 -> 0 <= jt_entry k < 2 ^ 32.
  Proof.
    intros k Hk. unfold jt_entry.
    assert (H : forall n, (n < 31)%nat -> 0 <= nth n arm_pcs 0 < 2 ^ 32).
    { intros n Hn. do 31 (destruct n as [|n]; [cbn; lia|]). lia. }
    apply H. lia.
  Qed.
End Dispatch.


Section Loop.
  Variable arm_ok : Z -> iw -> bool.

  Definition mstep (flush : Z) (w : iw) : iw + (istop * iw) :=
    match dispatch ivar_ref flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

  Lemma inf_loop_mstep : forall flush w,
    inf_loop ivar_ref flush w = iterZ (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64)) (mstep flush) (fun w => (SLeave, w)) w.
  Proof. reflexivity. Qed.
End Loop.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
