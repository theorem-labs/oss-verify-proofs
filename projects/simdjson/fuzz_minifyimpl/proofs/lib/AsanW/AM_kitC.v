(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma bytes_at_app_split : forall segs m A b1 b2, bytes_at segs m A (b1 ++ b2) ->
  bytes_at segs m A b1 /\ bytes_at segs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros segs m A b1 b2 (H0 & H1 & H). rewrite length_app in H1. split.
  - split; [exact H0|]. split; [lia|]. intros i Hi. rewrite (H i ltac:(rewrite length_app; lia)). apply nth_error_app1. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (length b1) + Z.of_nat i) with (A + Z.of_nat (length b1 + i)) by lia.
    rewrite (H (length b1 + i)%nat ltac:(rewrite length_app; lia)). rewrite nth_error_app2 by lia. f_equal. lia.
Qed.
Lemma bytes_at_app_join : forall segs m A b1 b2, bytes_at segs m A b1 -> bytes_at segs m (A + Z.of_nat (length b1)) b2 ->
  bytes_at segs m A (b1 ++ b2).
Proof.
  intros segs m A b1 b2 (H0 & H1 & HA) (_ & H2 & HB). split; [exact H0|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length b1)) as [L|G].
  - rewrite nth_error_app1 by exact L. exact (HA i L).
  - rewrite nth_error_app2 by exact G. specialize (HB (i - length b1)%nat ltac:(lia)).
    replace (A + Z.of_nat (length b1) + Z.of_nat (i - length b1)) with (A + Z.of_nat i) in HB by lia. exact HB.
Qed.
Lemma rw_cells_app_split : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (W0 & W1 & W)]. apply cells_wf_app in Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app_split in Hb as [Hb1 Hb2]. rewrite cells_bytes_length in Hb2 by exact Hw1.
  rewrite cells_size_app in W1, W. split.
  - split; [split; assumption|]. split; [exact W0|]. split; [lia|]. intros i Hi. apply W. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W. lia.
Qed.
Lemma rw_cells_app_join : forall segs m A cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[Hw1 Hb1] (W0 & W1 & WA)] [[Hw2 Hb2] (_ & W2 & WB)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app_join; [exact Hb1|]. rewrite cells_bytes_length by exact Hw1. exact Hb2.
  - rewrite cells_size_app. split; [exact W0|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|G]; [apply WA; lia|].
    specialize (WB (i - Z.of_nat (cells_size cs1)) ltac:(lia)).
    replace (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) with (A + i) in WB by lia. exact WB.
Qed.


Lemma rw_cells_cut : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
Proof. intros segs m A cs k H. apply rw_cells_app_split. rewrite firstn_skipn. exact H. Qed.


(* [comment removed for export] *)
Definition skippedA (P : Prop) : Prop := P.
Ltac trmA MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedA T) in H end ]
  | H : stk asegs mo ?lo ?hi |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : stk asegs mn lo hi) by (eapply stk_transport_disjoint; [exact H| exact MU| exact WM| cbn [disjoint_from]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedA T) in H end ]
  | H : wr_at asegs mo ?A ?n |- _ =>
      let H' := fresh "T" in assert (H' : wr_at asegs mn A n) by (eapply wr_at_transport; [exact H| exact WM]); clear H; rename H' into H
  end end;
  repeat match goal with H : skippedA _ |- _ => unfold skippedA in H end.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac boxm H := lazymatch type of H with ?T => change (boxed T) in H end.
Ltac unbox H := unfold boxed in H.

(* [comment removed for export] *)
Lemma rw_cells_run_split : forall segs m A (a b : nat) (z : byte),
  rw_cells segs m A [CB (a + b) (repeat z (a + b))] ->
  rw_cells segs m A [CB a (repeat z a)] /\ rw_cells segs m (A + Z.of_nat a) [CB b (repeat z b)].
Proof.
  intros segs m A a b z H.
  assert (H2 : rw_cells segs m A ([CB a (repeat z a)] ++ [CB b (repeat z b)])).
  { eapply rw_cells_recast; [exact H| cbn; rewrite !repeat_length; tauto| cbn; rewrite !app_nil_r, repeat_app; reflexivity| cbn; lia]. }
  apply rw_cells_app_split in H2. cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.
Lemma rw_cells_run_C8 : forall segs m A, rw_cells segs m A [CB 8 (repeat (Z_to_bv 8 0) 8)] -> rw_cells segs m A [C8 (Z_to_bv 64 0)].
Proof. intros segs m A H. eapply rw_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity| reflexivity]. Qed.
Lemma rw_cells_run_C4 : forall segs m A, rw_cells segs m A [CB 4 (repeat (Z_to_bv 8 0) 4)] -> rw_cells segs m A [C4 (Z_to_bv 64 0)].
Proof. intros segs m A H. eapply rw_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity| reflexivity]. Qed.
Lemma rw_cells_run_C2 : forall segs m A, rw_cells segs m A [CB 2 (repeat (Z_to_bv 8 0) 2)] -> rw_cells segs m A [C2 (Z_to_bv 64 0)].
Proof. intros segs m A H. eapply rw_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity| reflexivity]. Qed.
