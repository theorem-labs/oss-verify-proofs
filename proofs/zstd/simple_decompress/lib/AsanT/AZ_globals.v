(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation AG_harness_str := 0x21100 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_1 := 0x21160 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_2 := 0x211c0 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_3 := 0x211e0 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_4 := 0x21200 (only parsing).   (* [comment removed for export] *)
Notation AG_harness_str_5 := 0x21240 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_OF_base := 0x212e0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_OF_bits := 0x21380 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ML_base := 0x213c0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ML_bits := 0x214c0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_LL_base := 0x21520 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_LL_bits := 0x215e0 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_repStartValue := 0x21640 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ZSTD_did_fieldSize := 0x21660 (only parsing).   (* [comment removed for export] *)
Notation AG_dec_ZSTD_fcs_fieldSize := 0x216a0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_base := 0x21780 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_bits := 0x21840 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_LL_defaultDTable := 0x218a0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_base := 0x21b40 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_bits := 0x21be0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_OF_defaultDTable := 0x21c20 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_base := 0x21d80 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_bits := 0x21e80 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ML_defaultDTable := 0x21ee0 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_BIT_mask := 0x22180 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_BIT_reloadDStream_zeroFilled := 0x22220 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ZSTD_overlapCopy8_dec32table := 0x22240 (only parsing).   (* [comment removed for export] *)
Notation AG_blk_ZSTD_overlapCopy8_dec64table := 0x22280 (only parsing).   (* [comment removed for export] *)
Notation AG_huf_algoTime := 0x22460 (only parsing).   (* [comment removed for export] *)
Notation AG_huf_BIT_reloadDStream_zeroFilled := 0x225a0 (only parsing).   (* [comment removed for export] *)
Notation AG_fse_BIT_mask := 0x22660 (only parsing).   (* [comment removed for export] *)
Notation AG_fse_BIT_reloadDStream_zeroFilled := 0x22700 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str := 0x22760 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_1 := 0x227c0 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_2 := 0x22820 (only parsing).   (* [comment removed for export] *)
Notation AG_prod_str_3 := 0x22840 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str := 0x228a0 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_1 := 0x22900 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_2 := 0x22960 (only parsing).   (* [comment removed for export] *)
Notation AG_helpers_str_3 := 0x22980 (only parsing).   (* [comment removed for export] *)

Definition ACLIENT_RO : list (Z * Z) :=
  [ (0x21100, 36); (0x21160, 63); (0x211c0, 7); (0x211e0, 1); (0x21200, 29); (0x21240, 54);
    (0x212e0, 128); (0x21380, 32); (0x213c0, 212); (0x214c0, 53); (0x21520, 144); (0x215e0, 36);
    (0x21640, 12); (0x21660, 32); (0x216a0, 32); (0x21780, 144); (0x21840, 36); (0x218a0, 520);
    (0x21b40, 128); (0x21be0, 32); (0x21c20, 264); (0x21d80, 212); (0x21e80, 53); (0x21ee0, 520);
    (0x22180, 128); (0x22220, 8); (0x22240, 32); (0x22280, 32); (0x22460, 256); (0x225a0, 8);
    (0x22660, 128); (0x22700, 8); (0x22760, 36); (0x227c0, 64); (0x22820, 13); (0x22840, 1);
    (0x228a0, 36); (0x22900, 58); (0x22960, 6); (0x22980, 1) ].

(* [comment removed for export] *)
Notation ACLIENT_HLO := 0x21100 (only parsing).
Notation ACLIENT_HHI := 0x229c0 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Lemma aclient_bounds : forall A n, In (A, n) ACLIENT_RO -> 0x21100 <= A /\ 1 <= n /\ A + n <= 0x22981.
Proof.
  assert (B : forallb (fun p => (0x21100 <=? fst p) && (1 <=? snd p) && (fst p + snd p <=? 0x22981)) ACLIENT_RO = true)
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
