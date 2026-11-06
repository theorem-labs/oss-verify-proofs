(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase ADepot_iface ADepot ADepotKit ADepot_tabscan ARepInit_kit ADepot_init ADepotW.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Local Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.

(* [comment removed for export] *)
Lemma rwc8_val : forall m A x y, rw_cells bsegs m A [C8 (Z_to_bv 64 x)] -> rw_cells bsegs m A [C8 (Z_to_bv 64 y)] ->
  0 <= x < 2^64 -> 0 <= y < 2^64 -> x = y.
Proof.
  intros m A x y H1 H2 R1 R2.
  pose proof (rw_cells_read bsegs m A _ 0 _ H1 eq_refl) as E1. pose proof (rw_cells_read bsegs m A _ 0 _ H2 eq_refl) as E2.
  cbn [csize cbytes] in E1, E2. rewrite E1 in E2. assert (E : le8 (Z_to_bv 64 x) = le8 (Z_to_bv 64 y)) by congruence.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !unsigned_lit in E by lia. lia.
Qed.
Lemma rwc4_val : forall m A x y, rw_cells bsegs m A [C4 (Z_to_bv 64 x)] -> rw_cells bsegs m A [C4 (Z_to_bv 64 y)] ->
  0 <= x < 2^32 -> 0 <= y < 2^32 -> x = y.
Proof.
  intros m A x y H1 H2 R1 R2.
  pose proof (rw_cells_read bsegs m A _ 0 _ H1 eq_refl) as E1. pose proof (rw_cells_read bsegs m A _ 0 _ H2 eq_refl) as E2.
  cbn [csize cbytes] in E1, E2. rewrite E1 in E2. assert (E : le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y)) by congruence.
  apply (f_equal le_bytes_to_word) in E.
  apply (f_equal (@bv_unsigned 64)) in E. rewrite !le_bytes_to_word_le4 in E. rewrite !unsigned_lit in E by lia.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

Theorem adepotk_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok bsegs V m) both_mem_facts ->
  Forall (mfact_ok bsegs V m) (both_mem_facts_w w) ->
  Forall (pfact_ok V) both_pure_facts ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
  (length U <= 2976)%nat ->
  ADEPOTk (mkALayout (LV V) w U) 0 m.
Proof.
  intros V w U m HM HMW HP LU FU HAT LU'.
  destruct (adepot_init V w U m HM HMW HP LU FU HAT) as (D & WF & DC & LY).
  pose proof WF as (N1 & _ & _ & _ & _ & TF0 & TFB & NB).
  pose proof (BUD_nonneg U (dhs D) (Z.to_nat (dN D))) as BN. pose proof (CNT_nonneg U (dhs D) (Z.to_nat (dN D))) as CN.
  pose proof DC as (C1 & _ & _ & C4 & _).
  mf V m HM (MCell (ZLit 6280536) 4 (ZLit 1)) CNU.
  assert (EN : dN D = 1).
  { unfold NUNIQ in C4. apply (rwc4_val m 6280536); [exact C4| exact CNU| cbn [al_U] in NB; lia| lia]. }
  assert (ET : dtf D <= 3).
  { unfold SSTF in C1. destruct w; unfold both_mem_facts_w in HMW.
    - mf V m HMW (MCell (ZLit 2020680) 8 (ZLit 3)) F1.
      assert (dtf D = 3) by (apply (rwc8_val m 2020680); [exact C1| exact F1| cbn [al_U] in TFB; lia| lia]). lia.
    - mf V m HMW (MCell (ZLit 2020680) 8 (ZLit 2)) F1.
      assert (dtf D = 2) by (apply (rwc8_val m 2020680); [exact C1| exact F1| cbn [al_U] in TFB; lia| lia]). lia. }
  pose proof (BUD_le U (dhs D) (Z.to_nat (dN D)) FU) as BL. pose proof (CNT_le U (dhs D) (Z.to_nat (dN D))) as CL.
  exists D, 0. cbn [al_U]. split.
  - split; [exact WF|]. unfold DWMAX. split; [lia|]. split; lia.
  - unfold DWMAX. split; [lia|]. split; [lia|]. split; [exact DC| exact LY].
Qed.
End CANSEC1.
