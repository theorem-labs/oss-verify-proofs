(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition c0 : char63 := 48%uint63.

Definition zwin (s : PrimString.string) (off len : int) : bool :=
match PrimString.compare (PrimString.sub s off len) (PrimString.make len c0) with Eq => true | _ => false end.

Lemma int_compare_eq : forall x y : int, PrimInt63.compare x y = Eq -> x = y.
Proof. intros x y H. apply to_Z_inj. apply Z.compare_eq. rewrite <- Uint63.compare_spec. exact H. Qed.

Lemma list_compare_eq : forall l1 l2 : list int, ListDef.list_compare PrimInt63.compare l1 l2 = Eq -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
destruct (PrimInt63.compare x y) eqn:E; try discriminate.
apply int_compare_eq in E. subst y. f_equal. exact (IH _ H).
Qed.

Lemma nth_firstn_skipn : forall {A} (l : list A) (o n k : nat) (d : A), (k < n)%nat ->
nth k (firstn n (skipn o l)) d = nth (o + k) l d.
Proof.
intros A l o n k d Hk. rewrite nth_firstn. destruct (Nat.ltb_spec k n) as [_|X]; [|lia].
rewrite nth_skipn. reflexivity.
Qed.

Lemma zwin_get : forall s off len (i : int),
zwin s off len = true ->
(to_Z len <= to_Z PrimString.max_length)%Z ->
(to_Z off <= to_Z i < to_Z off + to_Z len)%Z ->
PrimString.get s i = c0 /\ (to_Z off + to_Z len <= to_Z (PrimString.length s))%Z.
Proof.
intros s off len i Hz Hmax Hi. unfold zwin in Hz.
destruct (PrimString.compare (PrimString.sub s off len) (PrimString.make len c0)) eqn:E; try discriminate. clear Hz.
rewrite PrimStringAxioms.compare_spec in E. apply list_compare_eq in E.
rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec in E.
pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl. pose proof (to_Z_bounded i) as Bi.
rewrite Nat.min_l in E by lia.
change (PrimInt63.land c0 255%uint63) with c0 in E.

assert (HL : (Z.to_nat (to_Z off) + Z.to_nat (to_Z len) <= length (to_list s))%nat).
{ pose proof (f_equal (@length _) E) as EL. rewrite repeat_length, length_firstn, length_skipn in EL. lia. }
split.
- rewrite PrimStringAxioms.get_spec.
set (k := (Z.to_nat (to_Z i) - Z.to_nat (to_Z off))%nat).
assert (Hk : (k < Z.to_nat (to_Z len))%nat) by (unfold k; lia).
pose proof (nth_firstn_skipn (to_list s) (Z.to_nat (to_Z off)) (Z.to_nat (to_Z len)) k 0%uint63 Hk) as N.
rewrite E in N. rewrite nth_repeat_lt in N by exact Hk.
replace (Z.to_nat (to_Z off) + k)%nat with (Z.to_nat (to_Z i)) in N by (unfold k; lia). symmetry. exact N.
- pose proof (PrimStringAxioms.length_spec s) as LS. pose proof (to_Z_bounded (PrimString.length s)) as BL. lia.
Qed.

Lemma hex_nybble_c0 : hex_nybble c0 = 0%N.
Proof. vm_compute. reflexivity. Qed.

Lemma zwin_hex_byte_at : forall s off len (i : N),
zwin s off len = true ->
(to_Z len <= to_Z PrimString.max_length)%Z ->
(to_Z off <= Z.of_N (2 * i))%Z -> (Z.of_N (2 * i + 1) < to_Z off + to_Z len)%Z ->
hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
intros s off len i Hz Hmax H1 H2.
pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl.
pose proof (to_Z_bounded PrimString.max_length) as Bm. change (to_Z PrimString.max_length) with 16777211%Z in *.
pose proof (to_Z_bounded (PrimString.length s)) as BL.

destruct (zwin_get s off len off Hz Hmax ltac:(lia)) as [_ HLs].
assert (E0 : to_Z (of_Z (Z.of_N (2 * i))) = Z.of_N (2 * i)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
assert (E1 : to_Z (of_Z (Z.of_N (2 * i + 1))) = Z.of_N (2 * i + 1)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
destruct (zwin_get s off len (of_Z (Z.of_N (2 * i))) Hz Hmax ltac:(rewrite E0; lia)) as [G0 _].
destruct (zwin_get s off len (of_Z (Z.of_N (2 * i + 1))) Hz Hmax ltac:(rewrite E1; lia)) as [G1 _].
unfold hex_byte_at. cbv zeta.
assert (HLT : (of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 = true) by (apply ltb_spec; rewrite E1; lia).
rewrite HLT. cbn [orb]. rewrite G0, G1, hex_nybble_c0. reflexivity.
Qed.

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

Lemma scanN_prefix_zwin : forall s (p n : N) (off len : int),
scanN s 64 0 p = true ->
zwin s off len = true ->
to_Z off = Z.of_N (2 * p) -> to_Z len = Z.of_N (2 * (n - p)) -> (p <= n)%N ->
(to_Z len <= to_Z PrimString.max_length)%Z ->
scanN s 64 0 n = true.
Proof.
intros s p n off len Hp Hz Eo El Hpn Hmax.
change (to_Z PrimString.max_length) with 16777211%Z in Hmax.
apply (scanN_complete s 63 0 n).
- change (2 ^ N.of_nat 63)%N with 9223372036854775808%N. pose proof (to_Z_bounded off) as Bo.
change wB with 9223372036854775808%Z in Bo. lia.
- intros i Hi. rewrite N.add_0_l. destruct (N.lt_ge_cases i p) as [L|G].
+ pose proof (scanN_sound s 64 0 p Hp i L) as X. rewrite N.add_0_l in X. exact X.
+ rewrite (zwin_hex_byte_at s off len i Hz); [discriminate | exact Hmax | lia | lia].
Qed.
