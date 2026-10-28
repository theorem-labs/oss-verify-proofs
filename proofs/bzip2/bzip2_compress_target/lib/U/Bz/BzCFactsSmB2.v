(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutSM CmpCutSmA BzCFactsSmA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSmB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
Lemma lor_lt_pow2' : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb.
  assert (N : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact N|].
  destruct (Z.eq_dec a 0) as [->|A]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B]; [rewrite Z.lor_0_r; lia|].
  assert (K : 0 <= k). { destruct (Z.neg_nonneg_cases k); [|lia]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  assert (NZ : Z.lor a b <> 0). { intros E. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
(* [comment removed for export] *)
Lemma lenpack_word_range : forall l0 l1, 0 <= l0 <= 17 -> 0 <= l1 <= 17 -> 0 <= Z.lor (l1 * 65536) l0 < 2097152.
Proof. intros l0 l1 H0 H1. change 2097152 with (2 ^ 21). apply lor_lt_pow2'; lia. Qed.
Lemma lenpack_word_eq : forall l0 l1, 0 <= l1 -> Z.lor (Z.shiftl l1 16) l0 = Z.lor (l1 * 65536) l0.
Proof. intros l0 l1 H. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sm_best_snoc : forall n cost t bc bt,
  sm_best (S n) cost t bc bt =
  (let r := sm_best n cost t bc bt in
   if zget cost (t + Z.of_nat n) <? fst r then (zget cost (t + Z.of_nat n), t + Z.of_nat n) else r).
Proof.
  induction n as [|n IH]; intros cost t bc bt.
  - cbn [sm_best fst]. replace (t + Z.of_nat 0) with t by lia. reflexivity.
  - cbv zeta. rewrite (sm_best_S (S n) cost t bc bt). rewrite (sm_best_S n cost t bc bt).
    replace (t + Z.of_nat (S n)) with (t + 1 + Z.of_nat n) by lia.
    destruct (zget cost t <? bc); rewrite IH; cbv zeta; reflexivity.
Qed.

End ACeilS1.
