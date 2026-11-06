(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation W64 x := (Z_to_bv 64 x) (only parsing).
Definition wlimbs (ls : list Z) : list word := map (fun x => Z_to_bv 64 x) ls.
Definition lbytes (ls : list Z) : list byte := u64s (wlimbs ls).

Lemma lbytes_nil : lbytes [] = []. Proof. reflexivity. Qed.
Lemma lbytes_cons : forall x ls, lbytes (x :: ls) = le8 (W64 x) ++ lbytes ls. Proof. reflexivity. Qed.
Lemma lbytes_app : forall a b, lbytes (a ++ b) = lbytes a ++ lbytes b.
Proof. intros. unfold lbytes, wlimbs. rewrite map_app, u64s_app. reflexivity. Qed.
Lemma lbytes_length : forall ls, length (lbytes ls) = (8 * length ls)%nat.
Proof. intros. unfold lbytes, wlimbs. rewrite u64s_length, length_map. reflexivity. Qed.
Lemma lbytes_lengthZ : forall ls, Z.of_nat (length (lbytes ls)) = (8 * Z.of_nat (length ls))%Z.
Proof. intros. rewrite lbytes_length. lia. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition limbs_at (m : word -> option byte) (A : Z) (ls : list Z) : Prop := bytes_at segs m A (lbytes ls).

Lemma limbs_at_bound : forall m A ls, limbs_at m A ls -> (0 <= A /\ A + 8 * Z.of_nat (length ls) <= 2^64)%Z.
Proof. intros m A ls H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite lbytes_lengthZ in B. exact B. Qed.

Lemma limbs_at_nil : forall m A, (0 <= A <= 2^64)%Z -> limbs_at m A [].
Proof. intros. apply bytes_at_nil. assumption. Qed.

Lemma limbs_at_app : forall m A l1 l2,
  limbs_at m A (l1 ++ l2) <-> limbs_at m A l1 /\ limbs_at m (A + 8 * Z.of_nat (length l1)) l2.
Proof.
  intros m A l1 l2. unfold limbs_at. rewrite lbytes_app, bytes_at_app, lbytes_lengthZ. reflexivity.
Qed.

Lemma limbs_at_cons_inv : forall m A x ls, limbs_at m A (x :: ls) -> limbs_at m (A + 8) ls.
Proof.
  intros m A x ls H. change (x :: ls) with ([x] ++ ls) in H. apply limbs_at_app in H. destruct H as [_ H].
  cbn [length] in H. exact H.
Qed.

Lemma limbs_at_read_hd : forall m A x ls a,
  limbs_at m A (x :: ls) -> a = wa A ->
  ov_read_bytes segs m a 8 = Some (le8 (W64 x)).
Proof.
  intros m A x ls a H ->. unfold limbs_at in H. rewrite lbytes_cons in H.
  pose proof (bytes_at_read segs m A _ 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R.
  2:{ rewrite length_app, length_le8. cbn. lia. }
  change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
  rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma limbs_at_read_nth : forall m A ls k x a,
  limbs_at m A ls -> nth_error ls k = Some x -> a = wa (A + 8 * Z.of_nat k) ->
  ov_read_bytes segs m a 8 = Some (le8 (Z_to_bv 64 x)).
Proof.
  intros m A ls k x a H Hn ->.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & -> & Hlen).
  apply limbs_at_app in H. destruct H as [_ H]. rewrite Hlen in H.
  eapply limbs_at_read_hd; [exact H | reflexivity].
Qed.

Lemma limbs_at_write_other : forall m A ls a bs,
  limbs_at m A ls -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + 8 * Z.of_nat (length ls) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  limbs_at (write_to_mem m (wa a) bs) A ls.
Proof.
  intros m A ls a bs H Ha Hl Hd. unfold limbs_at in *. apply bytes_at_write_other; try assumption.
  rewrite lbytes_lengthZ. exact Hd.
Qed.

Lemma limbs_at_snoc_write : forall m R pre v,
  limbs_at m R pre -> (R + 8 * Z.of_nat (length pre) + 8 <= 2^64)%Z ->
  limbs_at (write_to_mem m (wa (R + 8 * Z.of_nat (length pre))) (le8 (W64 v))) R (pre ++ [v]).
Proof.
  intros m R pre v H Hb. pose proof (limbs_at_bound _ _ _ H) as B.
  apply limbs_at_app. split.
  - apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | left; lia].
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r.
    apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

Lemma limbs_at_transport : forall W m m' A ls,
  limbs_at m A ls -> munch W m m' -> disjoint_from W A (8 * Z.of_nat (length ls)) -> limbs_at m' A ls.
Proof.
  intros W m m' A ls H MU D. unfold limbs_at in *. eapply bytes_at_transport; eauto. rewrite lbytes_lengthZ. exact D.
Qed.

Lemma limbs_at_of_u64arr : forall m A ls, u64arr segs m A (wlimbs ls) -> limbs_at m A ls.
Proof. intros m A ls [H _]. exact H. Qed.

Lemma u64arr_of_limbs_at : forall m A ls,
  limbs_at m A ls -> wr_at segs m A (8 * Z.of_nat (length ls)) -> u64arr segs m A (wlimbs ls).
Proof.
  intros m A ls H Hw. split; [exact H|]. unfold wlimbs. rewrite length_map. exact Hw.
Qed.

End WithSegs.

Definition alias_ok (rp ap n : Z) : Prop := (rp = ap \/ rp + 8 * n <= ap \/ ap + 8 * n <= rp)%Z.

From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase.
Lemma limbs_cons_lit : forall x l, limbs (x :: l) -> (0 <= x < 18446744073709551616)%Z /\ limbs l.
Proof. intros x l H. apply limbs_cons_inv in H. destruct H as [H1 H2]. split; [exact H1 | exact H2]. Qed.

Lemma bn_swrap32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

