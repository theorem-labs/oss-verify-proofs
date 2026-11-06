(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation AG_harness_str := 0x21100 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_1 := 0x21160 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_2 := 0x211a0 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_3 := 0x211c0 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_4 := 0x211e0 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_5 := 0x21220 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_OF_base := 0x21280 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_OF_bits := 0x21320 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ML_base := 0x21360 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ML_bits := 0x21460 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_LL_base := 0x214c0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_LL_bits := 0x21580 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_repStartValue := 0x215e0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ZSTD_did_fieldSize := 0x21600 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ZSTD_fcs_fieldSize := 0x21640 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_base := 0x216e0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_bits := 0x217a0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_defaultDTable := 0x21800 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_base := 0x21aa0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_bits := 0x21b40 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_defaultDTable := 0x21b80 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_base := 0x21ce0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_bits := 0x21de0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_defaultDTable := 0x21e40 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_BIT_mask := 0x220e0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_BIT_reloadDStream_zeroFilled := 0x22180 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ZSTD_overlapCopy8_dec32table := 0x221a0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ZSTD_overlapCopy8_dec64table := 0x221e0 (only parsing).   (* [comment removed for export] *)
Notation AG_huf_algoTime := 0x22300 (only parsing).   (* [comment removed for export] *)
Notation AG_huf_BIT_reloadDStream_zeroFilled := 0x22440 (only parsing).   (* [comment removed for export] *)
Notation AG_fse_BIT_mask := 0x224e0 (only parsing).   (* [comment removed for export] *)
Notation AG_fse_BIT_reloadDStream_zeroFilled := 0x22580 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str := 0x22620 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_1 := 0x225dc (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_2 := 0x22680 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_3 := 0x226a0 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str := 0x226c0 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_1 := 0x22720 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_2 := 0x22760 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_3 := 0x22780 (only parsing).   (* [comment removed for export] *)

Definition ACLIENT_RO : list (Z * Z) :=
  [ (0x21100, 36); (0x21160, 63); (0x211a0, 7); (0x211c0, 1); (0x211e0, 29); (0x21220, 54);
    (0x21280, 128); (0x21320, 32); (0x21360, 212); (0x21460, 53); (0x214c0, 144); (0x21580, 36);
    (0x215e0, 12); (0x21600, 32); (0x21640, 32); (0x216e0, 144); (0x217a0, 36); (0x21800, 520);
    (0x21aa0, 128); (0x21b40, 32); (0x21b80, 264); (0x21ce0, 212); (0x21de0, 53); (0x21e40, 520);
    (0x220e0, 128); (0x22180, 8); (0x221a0, 32); (0x221e0, 32); (0x22300, 256); (0x22440, 8);
    (0x224e0, 128); (0x22580, 8); (0x22620, 36); (0x225dc, 64); (0x22680, 13); (0x226a0, 1);
    (0x226c0, 36); (0x22720, 58); (0x22760, 6); (0x22780, 1) ].

(* [comment removed for export] *)
Notation ACLIENT_HLO := 0x21100 (only parsing).
Notation ACLIENT_HHI := 0x227c0 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Lemma aclient_bounds : forall A n, In (A, n) ACLIENT_RO -> 0x21100 <= A /\ 1 <= n /\ A + n <= 0x22781.
Proof.
  assert (B : forallb (fun p => (0x21100 <=? fst p) && (1 <=? snd p) && (fst p + snd p <=? 0x22781)) ACLIENT_RO = true)
    by (vm_compute; reflexivity).
  intros A n H. rewrite forallb_forall in B. specialize (B (A, n) H). cbn [fst snd] in B.
  apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1, B2, B3. lia.
Qed.

Lemma disjoint_from_app2 : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[x y] W1 IH]; intros W2 a n H1 H2; cbn [app disjoint_from] in *; [exact H2|]. split; [tauto | apply IH; tauto]. Qed.

(* [comment removed for export] *)
Definition aro_clientM (m : amem) : Prop :=
  (forall A n, In (A, n) ACLIENT_RO -> unpoisoned m A (A + n)) /\
  wr_at bsegs m (shad ACLIENT_HLO) (shad ACLIENT_HHI - shad ACLIENT_HLO).

(* [comment removed for export] *)
Lemma aro_clientM_magree : forall (P : Z -> Prop) m m', magree bsegs P m m' ->
  (forall a, shad ACLIENT_HLO <= a < shad ACLIENT_HHI -> P a) -> aro_clientM m -> aro_clientM m'.
Proof.
  intros P m m' AG HP [U W]. split.
  - intros A n HIn. destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). eapply unpoisoned_agree; [exact (U A n HIn)|].
    intros x Hx. refine (proj1 (AG x _ _)); [rewrite !shad_div in Hx; unfold ASHOFF in Hx; Z.div_mod_to_equations; lia|]. apply HP.
    rewrite !shad_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
  - eapply wr_at_magree; [exact AG| exact W|]. intros a Ha. apply HP. lia.
Qed.
End CANSEC1.
