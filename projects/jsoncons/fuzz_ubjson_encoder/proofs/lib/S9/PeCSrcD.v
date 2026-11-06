(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSD.

Lemma firstn_add {A} (k m : nat) : forall (l : list A), firstn (k + m) l = firstn k l ++ firstn m (skipn k l).
Proof.
  induction k as [|k IH]; intros [|x l]; [reflexivity| reflexivity| cbn; destruct m; reflexivity|].
  cbn. f_equal. apply IH.
Qed.
Lemma skipn_add {A} (n k : nat) : forall (l : list A), skipn k (skipn n l) = skipn (n + k) l.
Proof.
  induction n as [|n IH]; intros [|x l]; [reflexivity| reflexivity| cbn; destruct k; reflexivity|]. cbn. apply IH.
Qed.
Lemma slice_app p i a b : 0 <= i -> 0 <= a -> 0 <= b -> UbjRef.slice p i (a + b) = UbjRef.slice p i a ++ UbjRef.slice p (i + a) b.
Proof.
  intros Hi Ha Hb. unfold UbjRef.slice. rewrite Z2Nat.inj_add by lia. rewrite (Z2Nat.inj_add i a) by lia.
  rewrite firstn_add. f_equal. rewrite skipn_add. reflexivity.
Qed.
Lemma slice_len p i n : 0 <= i -> 0 <= n -> i + n <= blen p -> length (UbjRef.slice p i n) = Z.to_nat n.
Proof. intros. unfold UbjRef.slice, blen in *. rewrite length_firstn, length_skipn. lia. Qed.
Lemma slice_len_le p i n : 0 <= n -> (length (UbjRef.slice p i n) <= Z.to_nat n)%nat.
Proof. intros. unfold UbjRef.slice. rewrite length_firstn. lia. Qed.
Lemma slice_bytes p i n : bytes_ok p -> Forall (fun b => 0 <= b < 256) (UbjRef.slice p i n).
Proof. intros Hp. unfold UbjRef.slice. apply Forall_firstn. apply Forall_skipn. exact Hp. Qed.

Section B.
Variable segs : list MemImageType.Segment.
Lemma bytes_at_nil M a : L5.bytes_at segs M a [].
Proof. intros i Hi. cbn in Hi. lia. Qed.
Lemma bytes_at_app M a l1 l2 :
  L5.bytes_at segs M a (l1 ++ l2) <-> (L5.bytes_at segs M a l1 /\ L5.bytes_at segs M (a + Z.of_nat (length l1)) l2).
Proof.
  unfold L5.bytes_at. split.
  - intros H. split.
    + intros i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by exact Hi. exact H.
    + intros i Hi. specialize (H (length l1 + i)%nat ltac:(rewrite length_app; lia)).
      rewrite app_nth2 in H by lia. replace (length l1 + i - length l1)%nat with i in H by lia.
      replace (a + Z.of_nat (length l1 + i)) with (a + Z.of_nat (length l1) + Z.of_nat i) in H by lia. exact H.
  - intros (H1 & H2) i Hi. rewrite length_app in Hi.
    destruct (Nat.lt_ge_cases i (length l1)) as [L|L].
    + rewrite app_nth1 by exact L. apply H1. exact L.
    + rewrite app_nth2 by exact L. specialize (H2 (i - length l1)%nat ltac:(lia)).
      replace (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) with (a + Z.of_nat i) in H2 by lia. exact H2.
Qed.
Lemma bytes_at_skip M a l1 l2 : L5.bytes_at segs M a (l1 ++ l2) -> L5.bytes_at segs M (a + Z.of_nat (length l1)) l2.
Proof. intros H. apply (proj1 (bytes_at_app M a l1 l2)) in H. exact (proj2 H). Qed.
Lemma bytes_at_take M a l1 l2 : L5.bytes_at segs M a (l1 ++ l2) -> L5.bytes_at segs M a l1.
Proof. intros H. apply (proj1 (bytes_at_app M a l1 l2)) in H. exact (proj1 H). Qed.

Lemma window_advance M p de pos d rem :
  0 <= pos -> 0 <= d <= rem -> pos + rem <= blen p ->
  L5.bytes_at segs M de (UbjRef.slice p pos rem) -> L5.bytes_at segs M (de + d) (UbjRef.slice p (pos + d) (rem - d)).
Proof.
  intros Hp Hd Hr B. replace rem with (d + (rem - d)) in B by lia. rewrite (slice_app p pos d (rem - d)) in B by lia.
  pose proof (bytes_at_skip M de _ _ B) as B2. rewrite (slice_len p pos d) in B2 by lia. rewrite Z2Nat.id in B2 by lia. exact B2.
Qed.

Lemma window_head M p de pos d rem :
  0 <= pos -> 0 <= d <= rem -> L5.bytes_at segs M de (UbjRef.slice p pos rem) -> L5.bytes_at segs M de (UbjRef.slice p pos d).
Proof.
  intros Hp Hd B. replace rem with (d + (rem - d)) in B by lia. rewrite (slice_app p pos d (rem - d)) in B by lia. exact (bytes_at_take M de _ _ B).
Qed.

Lemma bytes_agree (M0 M1 : word -> option byte) a n l :
  Z.of_nat (length l) <= n -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, a <= i < a + n -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)) -> L5.bytes_at segs M0 a l -> L5.bytes_at segs M1 a l.
Proof.
  intros Hl Ha Hn AG B. apply (L5C.bytes_at_agree segs M0 M1 a l); [intros i Hi; apply AG; lia| lia| lia| exact B].
Qed.

Lemma payload_at_gptr (M0 : word -> option byte) p data g n :
  L5.bytes_at segs M0 data p -> data <= g -> 0 <= n -> g + n <= data + blen p -> L5.bytes_at segs M0 g (UbjRef.slice p (g - data) n).
Proof.
  intros B Hg Hn Hgn.
  assert (SP : UbjRef.slice p 0 (blen p) = p).
  { unfold UbjRef.slice, blen. rewrite Nat2Z.id. cbn [Z.to_nat skipn]. apply firstn_all. }
  rewrite <- SP in B. replace (blen p) with ((g - data) + (blen p - (g - data))) in B by lia.
  rewrite (slice_app p 0 (g - data) (blen p - (g - data))) in B by lia.
  pose proof (bytes_at_skip M0 data _ _ B) as B2.
  rewrite (slice_len p 0 (g - data)) in B2 by lia. rewrite Z2Nat.id in B2 by lia.
  replace (data + (g - data)) with g in B2 by lia. rewrite Z.add_0_l in B2.
  exact (window_head M0 p g (g - data) n (blen p - (g - data)) ltac:(lia) ltac:(lia) B2).
Qed.

Lemma u64_at_inj (M0 : word -> option byte) a v w : L5.u64_at segs M0 a v -> L5.u64_at segs M0 a w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros A B0 Hv Hw. unfold L5.u64_at in A, B0.
  assert (E : word_to_le_bytes 8 (Z_to_bv 64 v) = word_to_le_bytes 8 (Z_to_bv 64 w)) by congruence.
  apply (f_equal bytes_le_to_Z) in E. rewrite !SeqExec.bytes_le_to_Z_8, !L5.unsigned_lit in E by lia. exact E.
Qed.

Lemma u8_at_inj (M0 : word -> option byte) a b b' : L5.u8_at segs M0 a b -> L5.u8_at segs M0 a b' -> 0 <= b < 256 -> 0 <= b' < 256 -> b = b'.
Proof.
  intros U U' Hb Hb'. unfold L5.u8_at in U, U'. rewrite U in U'.
  apply (f_equal (fun o : option (list byte) => match o with Some (x :: _) => bv_unsigned x | _ => 0 end)) in U'. cbn beta iota in U'.
  rewrite !Z_to_bv_small in U' by (unfold bv_modulus; cbn; Lia.lia). exact U'.
Qed.

Lemma window_byte (M0 : word -> option byte) p de pos rem :
  0 <= pos -> 1 <= rem -> pos + rem <= blen p -> L5.bytes_at segs M0 de (UbjRef.slice p pos rem) -> L5.u8_at segs M0 de (bat p pos).
Proof.
  intros Hp Hr Hb B. specialize (B 0%nat ltac:(rewrite (slice_len p pos rem) by lia; lia)).
  rewrite Z.add_0_r in B. unfold UbjRef.slice, bat in B |- *. rewrite nth_firstn in B.
  replace (0 <? Z.to_nat rem)%nat with true in B by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn, Nat.add_0_r in B. exact B.
Qed.
End B.

End PECSD.
