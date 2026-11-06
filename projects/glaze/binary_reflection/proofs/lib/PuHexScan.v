(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsanHexScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition c0 : char63 := 48%uint63.


(* [comment removed for export] *)
Definition is_hexc (c : char63) : bool :=
  (((48 <=? c)%uint63 && (c <=? 57)%uint63) || ((97 <=? c)%uint63 && (c <=? 102)%uint63))%bool.

(* [comment removed for export] *)
Fixpoint hexw (s : PrimString.string) (f : nat) (i n : int) : bool :=
  match f with
  | O => false
  | S f =>
      if (n =? 0)%uint63 then true
      else if (n =? 1)%uint63 then is_hexc (PrimString.get s i)
      else let h := (n >> 1)%uint63 in (hexw s f i h && hexw s f (i + h)%uint63 (n - h)%uint63)%bool
  end.






(* [comment removed for export] *)
Lemma is_hexc_get_in : forall s (j : int), is_hexc (PrimString.get s j) = true -> (to_Z j < to_Z (PrimString.length s))%Z.
Proof.
  intros s j H. destruct (Z.lt_ge_cases (to_Z j) (to_Z (PrimString.length s))) as [L|G]; [exact L|exfalso].
  rewrite PrimStringAxioms.get_spec in H. rewrite nth_overflow in H; [discriminate|].
  pose proof (PrimStringAxioms.length_spec s) as LS. pose proof (to_Z_bounded j) as Bj. lia.
Qed.

Lemma hexw_sound : forall s f (i n : int),
  hexw s f i n = true -> (to_Z i + to_Z n < wB)%Z ->
  forall j : int, (to_Z i <= to_Z j < to_Z i + to_Z n)%Z -> is_hexc (PrimString.get s j) = true.
Proof.
  intros s f. induction f as [|f IH]; intros i n H Hw j Hj; cbn [hexw] in H; [discriminate|].
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded n) as Bn. pose proof (to_Z_bounded j) as Bj.
  destruct ((n =? 0)%uint63) eqn:E0.
  { exfalso. apply Uint63.eqb_spec in E0. subst n. change (to_Z 0%uint63) with 0%Z in Hj. lia. }
  destruct ((n =? 1)%uint63) eqn:E1.
  { apply Uint63.eqb_spec in E1. subst n. change (to_Z 1%uint63) with 1%Z in Hj. replace j with i by (apply to_Z_inj; lia). exact H. }
  apply andb_prop in H as [H1 H2].
  assert (En : to_Z n <> 0%Z).
  { intro X. assert (n = 0%uint63) by (apply to_Z_inj; exact X). subst n. discriminate E0. }
  assert (Eh : to_Z (n >> 1)%uint63 = (to_Z n / 2)%Z).
  { rewrite Uint63.lsr_spec. change (to_Z 1%uint63) with 1%Z. reflexivity. }
  assert (Hh0 : (0 <= to_Z n / 2 <= to_Z n)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Ei : to_Z (i + (n >> 1))%uint63 = (to_Z i + to_Z n / 2)%Z).
  { rewrite Uint63.add_spec, Eh. apply Z.mod_small. lia. }
  assert (Ed : to_Z (n - (n >> 1))%uint63 = (to_Z n - to_Z n / 2)%Z).
  { rewrite Uint63.sub_spec, Eh. apply Z.mod_small. lia. }
  destruct (Z.lt_ge_cases (to_Z j) (to_Z i + to_Z n / 2)) as [L|G].
  - apply (IH i (n >> 1)%uint63 H1); rewrite Eh; lia.
  - apply (IH (i + (n >> 1))%uint63 (n - (n >> 1))%uint63 H2); rewrite Ei, Ed; lia.
Qed.


Lemma is_hexc_nybble : forall c, is_hexc c = true -> (hex_nybble c < 16)%N.
Proof.
  intros c H. unfold is_hexc in H. unfold hex_nybble.
  pose proof (to_Z_bounded c) as Bc.
  destruct ((48 <=? c)%uint63 && (c <=? 57)%uint63)%bool eqn:E1.
  - apply andb_prop in E1 as [A B]. apply Uint63.leb_spec in A, B. change (to_Z 48%uint63) with 48%Z in A.
    change (to_Z 57%uint63) with 57%Z in B. lia.
  - cbn [orb] in H. rewrite H. apply andb_prop in H as [A B]. apply Uint63.leb_spec in A, B.
    change (to_Z 97%uint63) with 97%Z in A. change (to_Z 102%uint63) with 102%Z in B. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_of_chars : forall s (b : N),
  (Z.of_N (2 * b + 1) < to_Z (PrimString.length s))%Z ->
  is_hexc (PrimString.get s (of_Z (Z.of_N (2 * b)))) = true ->
  is_hexc (PrimString.get s (of_Z (Z.of_N (2 * b + 1)))) = true ->
  hex_byte_at s b <> None.
Proof.
  intros s b HL H0 H1. unfold hex_byte_at. cbv zeta.
  pose proof (to_Z_bounded (PrimString.length s)) as BL.
  assert (E1 : to_Z (of_Z (Z.of_N (2 * b + 1))) = Z.of_N (2 * b + 1)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (HLT : (of_Z (Z.of_N (2 * b + 1)) <? PrimString.length s)%uint63 = true) by (apply ltb_spec; rewrite E1; lia).
  rewrite HLT. cbn [orb].
  apply is_hexc_nybble in H0, H1.
  apply N.ltb_lt in H0, H1. rewrite H0, H1. cbn [andb]. discriminate.
Qed.


(* [comment removed for export] *)
Lemma hexw_hex_byte_at : forall s f (off len : int) (i : N),
  hexw s f off len = true -> (to_Z off + to_Z len < wB)%Z ->
  (to_Z off <= Z.of_N (2 * i))%Z -> (Z.of_N (2 * i + 1) < to_Z off + to_Z len)%Z ->
  hex_byte_at s i <> None.
Proof.
  intros s f off len i Hw Hov H1 H2.
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl.
  assert (E0 : to_Z (of_Z (Z.of_N (2 * i))) = Z.of_N (2 * i)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (E1 : to_Z (of_Z (Z.of_N (2 * i + 1))) = Z.of_N (2 * i + 1)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  pose proof (hexw_sound s f off len Hw Hov (of_Z (Z.of_N (2 * i))) ltac:(rewrite E0; lia)) as G0.
  pose proof (hexw_sound s f off len Hw Hov (of_Z (Z.of_N (2 * i + 1))) ltac:(rewrite E1; lia)) as G1.
  apply hex_byte_at_of_chars; [|exact G0|exact G1].
  pose proof (is_hexc_get_in s _ G1) as X. rewrite E1 in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scanN_complete : forall s f base n,
  (n <= 2 ^ N.of_nat f)%N ->
  (forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None) ->
  scanN s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H.
  - cbn [scanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
    unfold byte_ok. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. destruct (hex_byte_at s base); [reflexivity | congruence].
  - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
    remember (S f) as f1 eqn:Ef1. cbn [scanN].
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1].
    + unfold byte_ok. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. destruct (hex_byte_at s base); [reflexivity | congruence].
    + rewrite N.div2_div. set (h := (n / 2)%N).
      assert (Hh : (2 * h <= n < 2 * h + 2)%N).
      { unfold h. pose proof (N.div_mod n 2 ltac:(lia)) as D. pose proof (N.mod_lt n 2 ltac:(lia)). lia. }
      subst f1. apply andb_true_intro. split.
      * apply IH; [lia|]. intros i Hi. apply H. lia.
      * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma scanN_hexw : forall s (n : N) (len : int),
  hexw s 64 0 len = true -> to_Z len = Z.of_N (2 * n) ->
  scanN s 64 0 n = true.
Proof.
  intros s n len Hw El. pose proof (to_Z_bounded len) as Bl.
  apply (scanN_complete s 63 0 n).
  - change (2 ^ N.of_nat 63)%N with 9223372036854775808%N. change wB with 9223372036854775808%Z in Bl. lia.
  - intros i Hi. rewrite N.add_0_l. apply (hexw_hex_byte_at s 64 0 len i Hw);
      change (to_Z 0%uint63) with 0%Z; lia.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition i_of_N (n : N) : int := of_Z (Z.of_N n).

(* [comment removed for export] *)
Definition data_ok (s : PrimString.string) (n : N) : bool :=
  (N.ltb (2 * n) (2 ^ 62) && hexw s 64 0 (i_of_N (2 * n)))%bool.


Lemma i_of_N_spec : forall n : N, (Z.of_N n < wB)%Z -> to_Z (i_of_N n) = Z.of_N n.
Proof. intros n H. unfold i_of_N. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma scanN_of_data : forall s n, data_ok s n = true -> scanN s 64 0 n = true.
Proof.
  intros s n H. unfold data_ok in H. apply andb_prop in H as [H1 H2]. apply N.ltb_lt in H1.
  change wB with 9223372036854775808%Z.
  apply (scanN_hexw s n (i_of_N (2 * n)) H2). apply i_of_N_spec. change wB with 9223372036854775808%Z.
  change (2 ^ 62)%N with 4611686018427387904%N in H1. lia.
Qed.


