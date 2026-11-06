(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache.
Import ListNotations.
From Stdlib Require Import Uint63.
Definition hx_okc (c : PrimString.char63) : bool := ((48 <=? c)%uint63 && (c <=? 57)%uint63 || (97 <=? c)%uint63 && (c <=? 102)%uint63)%bool.
Definition hx_okz (c : PrimString.char63) : bool := (c =? 48)%uint63.
Fixpoint scan63 (P : PrimString.char63 -> bool) (s : PrimString.string) (fuel : nat) (lo len : int) : bool :=
match fuel with
| O => (len =? 0)%uint63
| S f =>
if (len =? 0)%uint63 then true
else if (len =? 1)%uint63 then P (PrimString.get s lo)
else let h := (len >> 1)%uint63 in (scan63 P s f lo h && scan63 P s f (lo + h)%uint63 (len - h)%uint63)%bool
end.
Lemma scan63_sound : forall P s fuel lo len,
scan63 P s fuel lo len = true -> (to_Z lo + to_Z len < wB)%Z ->
forall j, (to_Z lo <= to_Z j < to_Z lo + to_Z len)%Z -> P (PrimString.get s j) = true.
Proof.
intros P s fuel. induction fuel as [|f IH]; intros lo len H Hov j Hj; cbn [scan63] in H.
- apply eqb_spec in H. subst len. rewrite to_Z_0 in Hj. lia.
- destruct (len =? 0)%uint63 eqn:E0. { apply eqb_spec in E0. subst len. rewrite to_Z_0 in Hj. lia. }
destruct (len =? 1)%uint63 eqn:E1.
{ apply eqb_spec in E1. subst len. rewrite to_Z_1 in Hj. assert (j = lo) by (apply to_Z_inj; lia). subst j. exact H. }
apply andb_prop in H as [H1 H2].
pose proof (to_Z_bounded len) as Bl. pose proof (to_Z_bounded lo) as Bo.
assert (Hh : to_Z (len >> 1)%uint63 = (to_Z len / 2)%Z) by (rewrite lsr_spec, to_Z_1; reflexivity).
assert (Hq : (0 <= to_Z len / 2 <= to_Z len)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hlh : to_Z (lo + (len >> 1))%uint63 = (to_Z lo + to_Z len / 2)%Z) by (rewrite add_spec, Hh; apply Z.mod_small; lia).
assert (Hsub : to_Z (len - (len >> 1))%uint63 = (to_Z len - to_Z len / 2)%Z) by (rewrite sub_spec, Hh; apply Z.mod_small; lia).
destruct (Z.lt_ge_cases (to_Z j) (to_Z lo + to_Z len / 2)) as [L|G].
+ apply (IH lo (len >> 1)%uint63 H1); [rewrite Hh; lia | rewrite Hh; lia].
+ apply (IH (lo + (len >> 1))%uint63 (len - (len >> 1))%uint63 H2); [rewrite Hlh, Hsub; lia | rewrite Hlh, Hsub; lia].
Qed.
Lemma hx_okc_nybble : forall c, hx_okc c = true -> N.ltb (hex_nybble c) 16 = true.
Proof.
intros c H. unfold hx_okc in H. unfold hex_nybble.
assert (T48 : to_Z 48 = 48%Z) by reflexivity. assert (T57 : to_Z 57 = 57%Z) by reflexivity.
assert (T97 : to_Z 97 = 97%Z) by reflexivity. assert (T102 : to_Z 102 = 102%Z) by reflexivity.
destruct ((48 <=? c)%uint63 && (c <=? 57)%uint63)%bool eqn:E1.
- cbv iota. apply andb_prop in E1 as [A B]. apply leb_spec in A. apply leb_spec in B. rewrite T48 in A. rewrite T57 in B.
apply N.ltb_lt. lia.
- try rewrite E1 in H. cbn [orb] in H. rewrite H. cbv iota. apply andb_prop in H as [A B]. apply leb_spec in A. apply leb_spec in B.
rewrite T97 in A. rewrite T102 in B. apply N.ltb_lt. lia.
Qed.
Lemma hex_byte_at_ok : forall s (i : N),
(to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z ->
hx_okc (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true ->
hx_okc (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true ->
hex_byte_at s i <> None.
Proof.
intros s i Hlen H0 H1. unfold hex_byte_at. cbv zeta.
replace (Uint63.of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 with true by (symmetry; apply ltb_spec; exact Hlen).
cbn [orb]. rewrite (hx_okc_nybble _ H0), (hx_okc_nybble _ H1). cbn [andb]. discriminate.
Qed.
Lemma hex_byte_at_zero : forall s (i : N),
(to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z ->
hx_okz (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true ->
hx_okz (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true ->
hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
intros s i Hlen H0 H1. unfold hx_okz in H0, H1. apply eqb_spec in H0. apply eqb_spec in H1.
unfold hex_byte_at. cbv zeta.
replace (Uint63.of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 with true by (symmetry; apply ltb_spec; exact Hlen).
cbn [orb]. rewrite H0, H1. reflexivity.
Qed.
Definition scan63_guard (s : PrimString.string) (b2 n2 : int) : bool :=
((b2 <=? 2305843009213693952)%uint63 && (n2 <=? 2305843009213693952)%uint63 && ((b2 + n2)%uint63 <=? PrimString.length s)%uint63)%bool.
Definition hexscan63 (s : PrimString.string) (b2 n2 : int) : bool := (scan63_guard s b2 n2 && scan63 hx_okc s 64 b2 n2)%bool.
Definition zscan63 (s : PrimString.string) (b2 n2 : int) : bool := (scan63_guard s b2 n2 && scan63 hx_okz s 64 b2 n2)%bool.
Lemma scan63_guard_sound : forall s b2 n2, scan63_guard s b2 n2 = true ->
(to_Z b2 + to_Z n2 < wB /\ to_Z b2 + to_Z n2 <= to_Z (PrimString.length s))%Z.
Proof.
intros s b2 n2 H. unfold scan63_guard in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply leb_spec in H1. apply leb_spec in H2. apply leb_spec in H3.
assert (T : to_Z 2305843009213693952 = 2305843009213693952%Z) by reflexivity. rewrite T in H1, H2.
pose proof (to_Z_bounded b2). pose proof (to_Z_bounded n2).
assert (W : wB = 9223372036854775808%Z) by reflexivity.
rewrite add_spec, Z.mod_small in H3 by lia. lia.
Qed.
Lemma scan63_bytes : forall P s b2 n2 (i : N),
scan63_guard s b2 n2 = true -> scan63 P s 64 b2 n2 = true ->
(to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z ->
(to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) < to_Z (PrimString.length s))%Z
/\ P (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i)))) = true
/\ P (PrimString.get s (Uint63.of_Z (Z.of_N (2 * i + 1)))) = true.
Proof.
intros P s b2 n2 i G S L U. destruct (scan63_guard_sound _ _ _ G) as [OV LEN].
pose proof (to_Z_bounded b2). pose proof (to_Z_bounded n2).
assert (E0 : to_Z (Uint63.of_Z (Z.of_N (2 * i))) = (2 * Z.of_N i)%Z) by (rewrite of_Z_spec, Z.mod_small by lia; lia).
assert (E1 : to_Z (Uint63.of_Z (Z.of_N (2 * i + 1))) = (2 * Z.of_N i + 1)%Z) by (rewrite of_Z_spec, Z.mod_small by lia; lia).
split; [rewrite E1; lia|]. split; apply (scan63_sound P s 64 b2 n2 S OV); [rewrite E0 | rewrite E1]; lia.
Qed.
Lemma hexscan63_sound : forall s b2 n2, hexscan63 s b2 n2 = true ->
forall i : N, (to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z -> hex_byte_at s i <> None.
Proof.
intros s b2 n2 H i L U. unfold hexscan63 in H. apply andb_prop in H as [G S].
destruct (scan63_bytes hx_okc s b2 n2 i G S L U) as (A & B & C). exact (hex_byte_at_ok s i A B C).
Qed.
Lemma zscan63_sound : forall s b2 n2, zscan63 s b2 n2 = true ->
forall i : N, (to_Z b2 <= 2 * Z.of_N i)%Z -> (2 * Z.of_N i + 1 < to_Z b2 + to_Z n2)%Z -> hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
intros s b2 n2 H i L U. unfold zscan63 in H. apply andb_prop in H as [G S].
destruct (scan63_bytes hx_okz s b2 n2 i G S L U) as (A & B & C). exact (hex_byte_at_zero s i A B C).
Qed.
Definition zrange_ok (b n : Z) : bool :=
((0 <=? b)%Z && (0 <=? n)%Z && (b <? 1152921504606846976)%Z && (n <? 1152921504606846976)%Z)%bool.
Definition hexscanZ (s : PrimString.string) (b n : Z) : bool := (zrange_ok b n && hexscan63 s (of_Z (2 * b)) (of_Z (2 * n)))%bool.
Definition zscanZ (s : PrimString.string) (b n : Z) : bool := (zrange_ok b n && zscan63 s (of_Z (2 * b)) (of_Z (2 * n)))%bool.
Lemma zrange_ok_sound : forall b n, zrange_ok b n = true ->
(to_Z (of_Z (2 * b)) = 2 * b /\ to_Z (of_Z (2 * n)) = 2 * n /\ 0 <= b /\ 0 <= n)%Z.
Proof.
intros b n H. unfold zrange_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4.
assert (W : wB = 9223372036854775808%Z) by reflexivity.
rewrite !of_Z_spec, !Z.mod_small by lia. lia.
Qed.
Lemma hexscanZ_sound : forall s b n, hexscanZ s b n = true ->
forall i : N, (b <= Z.of_N i < b + n)%Z -> hex_byte_at s i <> None.
Proof.
intros s b n H i Hi. unfold hexscanZ in H. apply andb_prop in H as [R H]. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
apply (hexscan63_sound _ _ _ H i); rewrite ?E1, ?E2; lia.
Qed.
Lemma zscanZ_sound : forall s b n, zscanZ s b n = true ->
forall i : N, (b <= Z.of_N i < b + n)%Z -> hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
intros s b n H i Hi. unfold zscanZ in H. apply andb_prop in H as [R H]. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
apply (zscan63_sound _ _ _ H i); rewrite ?E1, ?E2; lia.
Qed.
Lemma segment_byte_at_someZ : forall s (n : Z) (off : N),
hexscanZ s 0 n = true -> (Z.of_N off < n)%Z -> segment_byte_at [s] off <> None.
Proof.
intros s n off H Hoff. cbn [segment_byte_at].
pose proof H as H'. unfold hexscanZ in H'. apply andb_prop in H' as [R H'']. destruct (zrange_ok_sound _ _ R) as (E1 & E2 & _ & _).
unfold hexscan63 in H''. apply andb_prop in H'' as [G _]. destruct (scan63_guard_sound _ _ _ G) as [_ LEN].
rewrite E1, E2 in LEN. pose proof (to_Z_bounded (PrimString.length s)).
replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true.
- apply (hexscanZ_sound s 0 n H off). lia.
- symmetry. apply N.ltb_lt. apply N2Z.inj_lt. rewrite Z2N.id by (apply Z.div_pos; lia).
assert (Z.of_N off + 1 <= to_Z (PrimString.length s) / 2)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.
