(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma put_syms_S : forall n b len code arr1 sel i,
  sm_put_syms (S n) b len code arr1 sel i =
  sm_put_syms n (bsW b (zget len (258 * sel + mtfv_at arr1 i)) (zget code (258 * sel + mtfv_at arr1 i))) len code arr1 sel (i + 1).
Proof. reflexivity. Qed.
Lemma put_syms_0 : forall b len code arr1 sel i, sm_put_syms 0 b len code arr1 sel i = b.
Proof. reflexivity. Qed.

Lemma put_in16_S : forall n b in16 i,
  sm_put_in16 (S n) b in16 i = sm_put_in16 n (bsW b 1 (if negb (zget in16 i =? 0) then 1 else 0)) in16 (i + 1).
Proof. reflexivity. Qed.
Lemma put_inuse_row_S : forall n b inUse i j,
  sm_put_inuse_row (S n) b inUse i j = sm_put_inuse_row n (bsW b 1 (if negb (zget inUse (i * 16 + j) =? 0) then 1 else 0)) inUse i (j + 1).
Proof. reflexivity. Qed.
Lemma put_inuse_S : forall n b in16 inUse i,
  sm_put_inuse (S n) b in16 inUse i =
  sm_put_inuse n (if negb (zget in16 i =? 0) then sm_put_inuse_row 16 b inUse i 0 else b) in16 inUse (i + 1).
Proof. reflexivity. Qed.
Lemma put_ones_S : forall n b, sm_put_ones (S n) b = sm_put_ones n (bsW b 1 1).
Proof. reflexivity. Qed.
Lemma put_sels_S : forall n b selMtf i,
  sm_put_sels (S n) b selMtf i = sm_put_sels n (bsW (sm_put_ones (Z.to_nat (zget selMtf i)) b) 1 0) selMtf (i + 1).
Proof. reflexivity. Qed.
Lemma put_up_S : forall f b curr tgt,
  sm_put_up (S f) b curr tgt = (if curr <? tgt then sm_put_up f (bsW b 2 2) (curr + 1) tgt else (b, curr)).
Proof. reflexivity. Qed.
Lemma put_down_S : forall f b curr tgt,
  sm_put_down (S f) b curr tgt = (if tgt <? curr then sm_put_down f (bsW b 2 3) (curr - 1) tgt else (b, curr)).
Proof. reflexivity. Qed.
Lemma put_lens_row_S : forall n b len t i curr,
  sm_put_lens_row (S n) b len t i curr =
  (let tgt := zget len (258 * t + i) in
   let '(b1, c1) := sm_put_up 40 b curr tgt in
   let '(b2, c2) := sm_put_down 40 b1 c1 tgt in
   sm_put_lens_row n (bsW b2 1 0) len t (i + 1) c2).
Proof. reflexivity. Qed.
Lemma put_lens_S : forall n b len A t,
  sm_put_lens (S n) b len A t =
  (let curr := zget len (258 * t + 0) in
   let '(b1, _) := sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) len t 0 curr in
   sm_put_lens n b1 len A (t + 1)).
Proof. reflexivity. Qed.
Lemma put_data_S : forall f b len code arr1 sel nMTF gs selCtr,
  sm_put_data (S f) b len code arr1 sel nMTF gs selCtr =
  (if nMTF <=? gs then (b, selCtr) else
   let ge := gs + BZ_G_SIZE - 1 in
   let ge := if nMTF <=? ge then nMTF - 1 else ge in
   let b := sm_put_syms (Z.to_nat (ge - gs + 1)) b len code arr1 (zget sel selCtr) gs in
   sm_put_data f b len code arr1 sel nMTF (ge + 1) (selCtr + 1)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bw_ok_bsW : forall b n v, bw_ok b -> 1 <= n <= 24 -> 0 <= v -> bw_ok (bsW b n v).
Proof. intros b n v OK Hn Hv. cps_destruct (bsW_facts b n v OK Hn Hv) as (_ & OK' & _). exact OK'. Qed.
Lemma bsW_live_le : forall b n v, bw_ok b -> 1 <= n <= 24 -> 0 <= v -> bw_live (bsW b n v) <= 7 + n.
Proof.
  intros b n v OK Hn Hv. cps_destruct (bsW_facts b n v OK Hn Hv) as (_ & _ & L & _). rewrite L.
  pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma in16_row_01 : forall n inUse i j acc, (acc = 0 \/ acc = 1) ->
  sm_in16_row n inUse i j acc = 0 \/ sm_in16_row n inUse i j acc = 1.
Proof.
  induction n as [|n IH]; intros inUse i j acc H; cbn [sm_in16_row]; [exact H|].
  apply IH. destruct (negb (zget inUse (i * 16 + j) =? 0)); [right; reflexivity| exact H].
Qed.
Lemma in16_row_S : forall n inUse i j acc,
  sm_in16_row (S n) inUse i j acc = sm_in16_row n inUse i (j + 1) (if negb (zget inUse (i * 16 + j) =? 0) then 1 else acc).
Proof. reflexivity. Qed.
Lemma in16_S : forall n in16 inUse i,
  sm_in16 (S n) in16 inUse i = sm_in16 n (zset in16 i (sm_in16_row 16 inUse i 0 0)) inUse (i + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma put_syms_split : forall a c b len code arr1 sel i,
  sm_put_syms (a + c) b len code arr1 sel i = sm_put_syms c (sm_put_syms a b len code arr1 sel i) len code arr1 sel (i + Z.of_nat a).
Proof.
  induction a as [|a IH]; intros c b len code arr1 sel i.
  - cbn [sm_put_syms Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add]. rewrite !put_syms_S. rewrite IH. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma put_data_snd_ge : forall f b len code arr1 sel nMTF gs sc,
  sc <= snd (sm_put_data f b len code arr1 sel nMTF gs sc).
Proof.
  induction f as [|f IH]; intros; cbn [sm_put_data]; [cbn; lia|].
  destruct (nMTF <=? gs); [cbn; lia|]. cbv zeta. etransitivity; [| apply IH]. lia.
Qed.
Lemma put_data_snd_step : forall f b len code arr1 sel nMTF gs sc, gs < nMTF ->
  sc + 1 <= snd (sm_put_data (S f) b len code arr1 sel nMTF gs sc).
Proof.
  intros. rewrite put_data_S. destruct (Z.leb_spec nMTF gs); [lia|]. cbv zeta. apply put_data_snd_ge.
Qed.
