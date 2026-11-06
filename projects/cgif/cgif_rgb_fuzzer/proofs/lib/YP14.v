(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation FinFun.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition getz (l : list Z) (i : Z) : Z := nth (Z.to_nat i) l 0.
Definition setz (l : list Z) (i : Z) (v : Z) : list Z := updn l (Z.to_nat i) v.
Definition zlen (l : list Z) : Z := Z.of_nat (length l).
Definition elen {A : Type} (l : list A) : Z := Z.of_nat (length l).
Lemma zlen_setz : forall l i v, zlen (setz l i v) = zlen l.
Proof. intros. unfold zlen, setz. rewrite updn_length. reflexivity. Qed.
Lemma length_setz : forall l i v, length (setz l i v) = length l.
Proof. intros. unfold setz. apply updn_length. Qed.
Lemma getz_setz : forall l i j v, 0 <= i -> 0 <= j ->
getz (setz l i v) j = if (j =? i) && (i <? zlen l) then v else getz l j.
Proof.
intros l i j v Hi Hj. unfold getz, setz, zlen. rewrite nth_updn.
destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat i)), (Z.eqb_spec j i); try lia;
destruct (Nat.ltb_spec (Z.to_nat i) (length l)), (Z.ltb_spec i (Z.of_nat (length l))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma getz_setz_same : forall l i v, 0 <= i < zlen l -> getz (setz l i v) i = v.
Proof.
intros l i v Hi. rewrite getz_setz by lia. rewrite Z.eqb_refl.
destruct (Z.ltb_spec i (zlen l)); [reflexivity | lia].
Qed.
Lemma getz_setz_other : forall l i j v, 0 <= i -> 0 <= j -> j <> i -> getz (setz l i v) j = getz l j.
Proof.
intros l i j v Hi Hj Hne. rewrite getz_setz by lia. destruct (Z.eqb_spec j i); [lia | reflexivity].
Qed.
Lemma getz_app_l : forall l1 l2 i, 0 <= i < zlen l1 -> getz (l1 ++ l2) i = getz l1 i.
Proof. intros l1 l2 i Hi. unfold getz, zlen in *. apply app_nth1. lia. Qed.
Lemma getz_app_r : forall l1 l2 i, zlen l1 <= i -> getz (l1 ++ l2) i = getz l2 (i - zlen l1).
Proof.
intros l1 l2 i Hi. unfold getz, zlen in *. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma getz_oob : forall l i, zlen l <= i -> getz l i = 0.
Proof. intros l i Hi. unfold getz, zlen in *. apply nth_overflow. lia. Qed.
Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.
Fixpoint cnt1 (l : list Z) : Z :=
match l with
| [] => 0
| v :: r => (if v =? 0 then 0 else 1) + cnt1 r
end.
Lemma cnt1_nonneg : forall l, 0 <= cnt1 l.
Proof. induction l as [|v r IH]; cbn; [lia|]. destruct (v =? 0); lia. Qed.

Lemma cnt1_repeat0 : forall n, cnt1 (repeat 0 n) = 0.
Proof. induction n; cbn; lia. Qed.
Lemma cnt1_updn : forall l i v, (i < length l)%nat ->
cnt1 (updn l i v) = cnt1 l - (if nth i l 0 =? 0 then 0 else 1) + (if v =? 0 then 0 else 1).
Proof.
induction l as [|x r IH]; intros [|i] v Hi; cbn in *; try lia.
rewrite IH by lia. pose proof (cnt1_nonneg r). destruct (x =? 0), (nth i r 0 =? 0), (v =? 0); lia.
Qed.
Lemma cnt1_setz : forall l i v, 0 <= i < zlen l ->
cnt1 (setz l i v) = cnt1 l - (if getz l i =? 0 then 0 else 1) + (if v =? 0 then 0 else 1).
Proof. intros l i v Hi. unfold setz, getz, zlen in *. apply cnt1_updn. lia. Qed.

Lemma cnt1_has_zero : forall l, cnt1 l < zlen l -> exists i, 0 <= i < zlen l /\ getz l i = 0.
Proof.
unfold zlen, getz. induction l as [|v r IH]; intros Hc; cbn [length cnt1] in *; [lia|].
destruct (Z.eqb_spec v 0).
- exists 0. cbn. split; [lia | exact e].
- destruct (IH ltac:(lia)) as (i & Hi & Hz). exists (i + 1).
split; [lia|]. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [nth]. exact Hz.
Qed.
Fixpoint upos_from (l : list Z) (b : Z) : list Z :=
match l with
| [] => []
| v :: r => (if v =? 0 then [] else [b]) ++ upos_from r (b + 1)
end.
Definition upos (l : list Z) : list Z := upos_from l 0.
Lemma upos_from_length : forall l b, Z.of_nat (length (upos_from l b)) = cnt1 l.
Proof.
induction l as [|v r IH]; intros b; cbn [upos_from cnt1 length]; [reflexivity|].
rewrite length_app, Nat2Z.inj_add, IH. destruct (v =? 0); cbn; lia.
Qed.
Lemma upos_from_In : forall l b p, In p (upos_from l b) <-> b <= p < b + Z.of_nat (length l) /\ nth (Z.to_nat (p - b)) l 0 <> 0.
Proof.
induction l as [|v r IH]; intros b p; cbn [upos_from length].
- split; [intros []| intros [H _]; lia].
- rewrite in_app_iff, IH. split.
+ intros [H|H].
* destruct (Z.eqb_spec v 0); cbn in H; [tauto|]. destruct H as [<-|[]].
rewrite Z.sub_diag. cbn. split; [lia | exact n].
* destruct H as [H1 H2]. split; [lia|].
replace (Z.to_nat (p - b)) with (S (Z.to_nat (p - (b + 1)))) by lia. cbn [nth]. exact H2.
+ intros [H1 H2]. destruct (Z.eq_dec p b) as [->|].
* left. rewrite Z.sub_diag in H2. cbn in H2. destruct (Z.eqb_spec v 0); [congruence|]. left. reflexivity.
* right. split; [lia|].
replace (Z.to_nat (p - b)) with (S (Z.to_nat (p - (b + 1)))) in H2 by lia. cbn [nth] in H2. exact H2.
Qed.
Lemma upos_In : forall l p, In p (upos l) <-> 0 <= p < zlen l /\ getz l p <> 0.
Proof.
intros l p. unfold upos, zlen, getz. rewrite upos_from_In. rewrite Z.sub_0_r. lia.
Qed.

Lemma upos_length : forall l, Z.of_nat (length (upos l)) = cnt1 l.
Proof. intros l. apply upos_from_length. Qed.
Lemma cnt1_nodup_bound : forall (ps : list Z) l,
NoDup ps -> (forall p, In p ps -> 0 <= p < zlen l /\ getz l p <> 0) -> Z.of_nat (length ps) <= cnt1 l.
Proof.
intros ps l Hnd Hps. rewrite <- upos_length. apply Nat2Z.inj_le.
apply NoDup_incl_length; [exact Hnd|]. intros p Hp. apply upos_In. apply Hps. exact Hp.
Qed.
Fixpoint ffirst (ok : Z -> bool) (j0 : Z) (n : nat) : option Z :=
match n with
| O => None
| S n' => if ok j0 then Some j0 else ffirst ok (j0 + 1) n'
end.
Lemma ffirst_Some : forall ok n j0 j, ffirst ok j0 n = Some j ->
j0 <= j < j0 + Z.of_nat n /\ ok j = true /\ (forall i, j0 <= i < j -> ok i = false).
Proof.
intros ok n. induction n as [|n IH]; intros j0 j H; cbn [ffirst] in H; [discriminate|].
destruct (ok j0) eqn:E.
- injection H as <-. split; [lia|]. split; [exact E|]. intros; lia.
- destruct (IH _ _ H) as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
intros i Hi. destruct (Z.eq_dec i j0) as [->|]; [exact E|]. apply H3. lia.
Qed.
Lemma ffirst_None : forall ok n j0, ffirst ok j0 n = None -> forall i, j0 <= i < j0 + Z.of_nat n -> ok i = false.
Proof.
intros ok n. induction n as [|n IH]; intros j0 H i Hi; cbn [ffirst] in H; [lia|].
destruct (ok j0) eqn:E; [discriminate|].
destruct (Z.eq_dec i j0) as [->|]; [exact E|]. apply (IH (j0 + 1) H). lia.
Qed.
Lemma ffirst_exists : forall ok n j0 i, j0 <= i < j0 + Z.of_nat n -> ok i = true ->
exists j, ffirst ok j0 n = Some j /\ j <= i.
Proof.
intros ok n j0 i Hi Hok. destruct (ffirst ok j0 n) as [j|] eqn:E.
- exists j. split; [reflexivity|]. destruct (ffirst_Some _ _ _ _ E) as (_ & _ & H3).
destruct (Z_lt_le_dec i j) as [Hlt|]; [|lia]. rewrite (H3 i) in Hok by lia. discriminate.
- exfalso. rewrite (ffirst_None _ _ _ E i Hi) in Hok. discriminate.
Qed.
Lemma ffirst_charact : forall ok n j0 j, j0 <= j < j0 + Z.of_nat n -> ok j = true ->
(forall i, j0 <= i < j -> ok i = false) -> ffirst ok j0 n = Some j.
Proof.
intros ok n j0 j Hj Hok Hbefore. destruct (ffirst_exists ok n j0 j Hj Hok) as (j' & E & Hle).
destruct (ffirst_Some _ _ _ _ E) as (H1 & H2 & H3).
destruct (Z_lt_le_dec j' j) as [Hlt|]; [|rewrite E; f_equal; lia].
rewrite (Hbefore j') in H2 by lia. discriminate.
Qed.
Definition MAX_TABLE_SIZE : Z := 16777216.
Definition MAX_COLLISIONS : Z := 30.
Definition INIT_TABLE_ARG : Z := 262147.
Definition getNextPrimePower2 (N : Z) : Z :=
if N <=? 512 then 521
else if N <=? 1024 then 1031
else if N <=? 2048 then 2053
else if N <=? 4096 then 4099
else if N <=? 8192 then 8209
else if N <=? 16384 then 16411
else if N <=? 32768 then 32771
else if N <=? 65536 then 65537
else if N <=? 131072 then 131101
else if N <=? 262144 then 262147
else if N <=? 524288 then 524309
else if N <=? 1048576 then 1048583
else if N <=? 2097152 then 2097169
else if N <=? 4194304 then 4194319
else if N <=? 8388608 then 8388617
else MAX_TABLE_SIZE.
Definition TS0 : Z := 524309.
Definition ts_chain : list Z := [524309; 1048583; 2097169; 4194319; 8388617; 16777216].

Lemma ts_chain_next : forall T, In T ts_chain -> T < MAX_TABLE_SIZE -> In (getNextPrimePower2 T) ts_chain.
Proof.
intros T HT Hlt. cbv [ts_chain In] in HT.
repeat (destruct HT as [<-|HT]; [cbv; tauto|]). destruct HT.
Qed.
Lemma ts_chain_next_gt : forall T, In T ts_chain -> T < MAX_TABLE_SIZE -> T < getNextPrimePower2 T.
Proof.
intros T HT Hlt. cbv [ts_chain In] in HT.
repeat (destruct HT as [<-|HT]; [cbv; reflexivity || (cbv in Hlt; discriminate)|]). destruct HT.
Qed.

Definition ts_ok (T : Z) : Prop := 521 <= T <= MAX_TABLE_SIZE /\ 4 * T < 2 ^ 31 /\ 20002 < T.
Lemma ts_chain_ok : forall T, In T ts_chain -> ts_ok T.
Proof.
intros T HT. cbv [ts_chain In] in HT. unfold ts_ok, MAX_TABLE_SIZE.
repeat (destruct HT as [<-|HT]; [lia|]). destruct HT.
Qed.


Abbreviation colour := (Z * Z * Z)%type.
Definition cR (c : colour) : Z := fst (fst c).
Definition cG (c : colour) : Z := snd (fst c).
Definition cB (c : colour) : Z := snd c.
Definition mkcol (r g b : Z) : colour := (r, g, b).
Definition colour_ok (c : colour) : Prop := 0 <= cR c < 256 /\ 0 <= cG c < 256 /\ 0 <= cB c < 256.
Definition colour_eqb (a b : colour) : bool := (cR a =? cR b) && (cG a =? cG b) && (cB a =? cB b).
Lemma colour_eqb_spec : forall a b, colour_eqb a b = true <-> a = b.
Proof.
intros [[r g] b] [[r' g'] b']. unfold colour_eqb, cR, cG, cB. cbn.
rewrite !Bool.andb_true_iff, !Z.eqb_eq. split; [intros [[-> ->] ->]; reflexivity | intros H; injection H as -> -> ->; auto].
Qed.
Lemma colour_eqb_refl : forall a, colour_eqb a a = true.
Proof. intros a. apply colour_eqb_spec. reflexivity. Qed.
Lemma colour_eq_dec : forall a b : colour, {a = b} + {a <> b}.
Proof.
intros a b. destruct (colour_eqb a b) eqn:E; [left; apply colour_eqb_spec; exact E | right].
intros H. apply colour_eqb_spec in H. congruence.
Qed.
Definition comp (d : Z) (c : colour) : Z := if d =? 0 then cR c else if d =? 1 then cG c else cB c.
Definition px_colour (px : list Z) : colour := mkcol (getz px 0) (getz px 1) (getz px 2).
Definition opaque (fmtChan : Z) (px : list Z) : bool :=
if fmtChan =? 4 then negb (getz px 3 <=? 127) else true.


Definition hash0 (T : Z) (c : colour) : Z := (cR c * 65536 + cG c * 256 + cB c) mod T.
Lemma hash0_range : forall T c, 0 < T -> 0 <= hash0 T c < T.
Proof. intros T c HT. unfold hash0. apply Z.mod_pos_bound. exact HT. Qed.

Lemma lor_low_disjoint : forall a x k, 0 <= a -> 0 <= k -> 0 <= x < 2 ^ k -> Z.lor (a * 2 ^ k) x = a * 2 ^ k + x.
Proof.
intros a x k Ha Hk Hx.
assert (Hland : Z.land (a * 2 ^ k) x = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n k).
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- destruct (Z.eq_dec x 0) as [->|]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia. }
pose proof (Z.add_lor_land (a * 2 ^ k) x) as E. rewrite Hland in E. lia.
Qed.

Definition probe_next (T h : Z) : Z := if h + 1 =? T then 0 else h + 1.
Lemma probe_next_mod : forall T h, 0 <= h < T -> probe_next T h = (h + 1) mod T.
Proof.
intros T h Hh. unfold probe_next. destruct (Z.eqb_spec (h + 1) T) as [E|E].
- rewrite E. rewrite Z.mod_same; lia.
- rewrite Z.mod_small; lia.
Qed.
Lemma probe_next_range : forall T h, 0 <= h < T -> 0 <= probe_next T h < T.
Proof. intros T h Hh. unfold probe_next. destruct (Z.eqb_spec (h + 1) T); lia. Qed.
Definition cyc (T a j : Z) : Z := (a + j) mod T.
Lemma cyc_range : forall T a j, 0 < T -> 0 <= cyc T a j < T.
Proof. intros. unfold cyc. apply Z.mod_pos_bound. lia. Qed.
Lemma cyc_0 : forall T a, 0 <= a < T -> cyc T a 0 = a.
Proof. intros. unfold cyc. rewrite Z.add_0_r. apply Z.mod_small. lia. Qed.
Lemma cyc_succ : forall T a j, 0 < T -> cyc T a (j + 1) = probe_next T (cyc T a j).
Proof.
intros T a j HT. rewrite probe_next_mod by (apply cyc_range; lia). unfold cyc.
rewrite Z.add_assoc. rewrite <- (Z.add_mod_idemp_l (a + j) 1 T) by lia. reflexivity.
Qed.
Lemma cyc_inj : forall T a i j, 0 < T -> 0 <= i < T -> 0 <= j < T -> cyc T a i = cyc T a j -> i = j.
Proof.
intros T a i j HT Hi Hj E. unfold cyc in E.
assert (H : (a + i - (a + j)) mod T = 0).
{ rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
replace (a + i - (a + j)) with (i - j) in H by lia.
destruct (Z_lt_le_dec (i - j) 0).
- assert (H2 : (i - j + T) mod T = 0).
{ rewrite <- (Z.add_mod_idemp_r (i - j) T T) by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. exact H. }
rewrite Z.mod_small in H2 by lia. lia.
- rewrite Z.mod_small in H by lia. lia.
Qed.

Definition offs (T a h : Z) : Z := (h - a) mod T.
Lemma offs_range : forall T a h, 0 < T -> 0 <= offs T a h < T.
Proof. intros. unfold offs. apply Z.mod_pos_bound. lia. Qed.
Lemma cyc_offs : forall T a h, 0 < T -> 0 <= h < T -> cyc T a (offs T a h) = h.
Proof.
intros T a h HT Hh. unfold cyc, offs. rewrite Z.add_mod_idemp_r by lia.
replace (a + (h - a)) with h by lia. apply Z.mod_small. lia.
Qed.
Lemma offs_cyc : forall T a j, 0 < T -> 0 <= j < T -> offs T a (cyc T a j) = j.
Proof.
intros T a j HT Hj. unfold cyc, offs. rewrite Zminus_mod_idemp_l.
replace (a + j - a) with j by lia. apply Z.mod_small. lia.
Qed.
Record htab := mkHT {
ht_frequ : list Z;
ht_keys : list Z;
ht_used : list Z;
ht_pal : list Z;
ht_colidx : list Z;
ht_cnt : Z;
ht_T : Z
}.
Definition col_at (l : list Z) (i : Z) : colour := mkcol (getz l (3 * i)) (getz l (3 * i + 1)) (getz l (3 * i + 2)).
Definition set_col (l : list Z) (i : Z) (c : colour) : list Z :=
setz (setz (setz l (3 * i) (cR c)) (3 * i + 1) (cG c)) (3 * i + 2) (cB c).
Lemma zlen_set_col : forall l i c, zlen (set_col l i c) = zlen l.
Proof. intros. unfold set_col. rewrite !zlen_setz. reflexivity. Qed.
Lemma getz_set_col : forall l i c j, 0 <= i -> 0 <= j -> 3 * i + 3 <= zlen l ->
getz (set_col l i c) j =
if j =? 3 * i then cR c else if j =? 3 * i + 1 then cG c else if j =? 3 * i + 2 then cB c else getz l j.
Proof.
intros l i c j Hi Hj Hlen. unfold set_col.
rewrite !getz_setz by lia. rewrite !zlen_setz.
destruct (Z.eqb_spec j (3 * i + 2)), (Z.eqb_spec j (3 * i + 1)), (Z.eqb_spec j (3 * i)); try lia;
destruct (Z.ltb_spec (3 * i + 2) (zlen l)), (Z.ltb_spec (3 * i + 1) (zlen l)), (Z.ltb_spec (3 * i) (zlen l)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma col_at_set_col_same : forall l i c, 0 <= i -> 3 * i + 3 <= zlen l -> col_at (set_col l i c) i = c.
Proof.
intros l i c Hi Hlen. unfold col_at. rewrite !getz_set_col by lia.
rewrite Z.eqb_refl.
destruct (Z.eqb_spec (3 * i + 1) (3 * i)); [lia|]. rewrite Z.eqb_refl.
destruct (Z.eqb_spec (3 * i + 2) (3 * i)); [lia|]. destruct (Z.eqb_spec (3 * i + 2) (3 * i + 1)); [lia|]. rewrite Z.eqb_refl.
destruct c as [[r g] b]; reflexivity.
Qed.
Lemma col_at_set_col_other : forall l i c i', 0 <= i -> 0 <= i' -> i' <> i -> 3 * i + 3 <= zlen l ->
col_at (set_col l i c) i' = col_at l i'.
Proof.
intros l i c i' Hi Hi' Hne Hlen. unfold col_at. rewrite !getz_set_col by lia.
destruct (Z.eqb_spec (3 * i') (3 * i)); [lia|]. destruct (Z.eqb_spec (3 * i') (3 * i + 1)); [lia|]. destruct (Z.eqb_spec (3 * i') (3 * i + 2)); [lia|].
destruct (Z.eqb_spec (3 * i' + 1) (3 * i)); [lia|]. destruct (Z.eqb_spec (3 * i' + 1) (3 * i + 1)); [lia|]. destruct (Z.eqb_spec (3 * i' + 1) (3 * i + 2)); [lia|].
destruct (Z.eqb_spec (3 * i' + 2) (3 * i)); [lia|]. destruct (Z.eqb_spec (3 * i' + 2) (3 * i + 1)); [lia|]. destruct (Z.eqb_spec (3 * i' + 2) (3 * i + 2)); [lia|].
reflexivity.
Qed.
Lemma col_at_ok : forall l i, Forall (fun v => 0 <= v < 256) l -> 0 <= i -> 3 * i + 3 <= zlen l -> colour_ok (col_at l i).
Proof.
intros l i Hl Hi Hlen. unfold colour_ok, col_at, cR, cG, cB, mkcol. cbn [fst snd].
unfold getz, zlen in *.
pose proof (proj1 (Forall_nth_Z _ l) Hl) as Hb. cbn beta in Hb.
split; [|split]; apply Hb; lia.
Qed.
Lemma comp_col_at : forall l i d, 0 <= d < 3 -> comp d (col_at l i) = getz l (3 * i + d).
Proof.
intros l i d Hd. unfold comp, col_at, cR, cG, cB, mkcol. cbn.
destruct (Z.eqb_spec d 0) as [->|]; [rewrite Z.add_0_r; reflexivity|].
destruct (Z.eqb_spec d 1) as [->|]; [reflexivity|]. replace d with 2 by lia. reflexivity.
Qed.
Definition T_of (H : htab) : Z := ht_T H.
Definition usedz (H : htab) (h : Z) : Z := getz (ht_used H) h.
Definition key (H : htab) (h : Z) : colour := col_at (ht_keys H) h.
Definition freq (H : htab) (h : Z) : Z := getz (ht_frequ H) h.
Definition cidx (H : htab) (h : Z) : Z := getz (ht_colidx H) h.
Definition palc (H : htab) (i : Z) : colour := col_at (ht_pal H) i.
Definition in_slot (H : htab) (h : Z) : Prop := 0 <= h < ht_T H /\ usedz H h <> 0.
Abbreviation entry := (colour * Z)%type.
Definition ht_inv (H : htab) (ent : list entry) : Prop :=
let T := ht_T H in
(zlen (ht_used H) = T /\ zlen (ht_keys H) = 3 * T /\ zlen (ht_frequ H) = T /\
zlen (ht_colidx H) = T /\ zlen (ht_pal H) = 3 * T) /\
(0 <= ht_cnt H < T /\ elen ent = ht_cnt H /\ cnt1 (ht_used H) = ht_cnt H) /\
((forall h, 0 <= h < T -> usedz H h = 0 \/ usedz H h = 1) /\
Forall (fun v => 0 <= v < 256) (ht_keys H) /\ Forall (fun v => 0 <= v < 256) (ht_pal H)) /\
(forall h, in_slot H h ->
0 <= cidx H h < ht_cnt H /\ nth_error ent (Z.to_nat (cidx H h)) = Some (key H h, freq H h) /\ 1 <= freq H h) /\
(forall i, 0 <= i < ht_cnt H ->
(exists f, nth_error ent (Z.to_nat i) = Some (palc H i, f)) /\ (exists h, in_slot H h /\ cidx H h = i)) /\
(forall h h', in_slot H h -> in_slot H h' -> key H h = key H h' -> h = h') /\
(forall h j, in_slot H h -> 0 <= j < offs T (hash0 T (key H h)) h -> usedz H (cyc T (hash0 T (key H h)) j) <> 0).
Definition zseq (a n : Z) : list Z := map (fun k => a + Z.of_nat k) (seq 0 (Z.to_nat n)).
Lemma In_zseq : forall a n x, In x (zseq a n) <-> a <= x < a + n.
Proof.
intros a n x. unfold zseq. rewrite in_map_iff. split.
- intros (k & <- & Hk). apply in_seq in Hk. lia.
- intros H. exists (Z.to_nat (x - a)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma zseq_length : forall a n, length (zseq a n) = Z.to_nat n.
Proof. intros. unfold zseq. rewrite length_map, length_seq. reflexivity. Qed.
Lemma zseq_NoDup : forall a n, NoDup (zseq a n).
Proof.
intros a n. unfold zseq. apply Injective_map_NoDup; [intros x y; lia | apply seq_NoDup].
Qed.

Lemma zseq_succ : forall a n, 0 <= n -> zseq a (n + 1) = zseq a n ++ [a + n].
Proof.
intros a n Hn. unfold zseq. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
rewrite seq_S, map_app. cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Definition slot_stop (H : htab) (c : colour) (h : Z) : bool :=
(usedz H h =? 0) || colour_eqb (key H h) c.
Definition find_off (H : htab) (c : colour) : option Z :=
ffirst (fun j => slot_stop H c (cyc (ht_T H) (hash0 (ht_T H) c) j)) 0 (Z.to_nat (ht_T H)).
Definition find_slot (H : htab) (c : colour) : option Z :=
match find_off H c with Some j => Some (cyc (ht_T H) (hash0 (ht_T H) c) j) | None => None end.
Definition col_hash (H : htab) (fmtChan : Z) (px : list Z) : option Z :=
if opaque fmtChan px then find_slot H (px_colour px) else Some (-1).
Section o.
Variable H : htab.
Variable ent : list entry.
Hypothesis INV : ht_inv H ent.
Let T := ht_T H.
Lemma inv_T_pos : 0 < T.
Proof. destruct INV as (_ & (Hc & _) & _). subst T. lia. Qed.
Lemma inv_used01 : forall h, 0 <= h < T -> usedz H h = 0 \/ usedz H h = 1.
Proof. destruct INV as (_ & _ & (Hu & _) & _). exact Hu. Qed.
Lemma free_slot_exists : exists h, 0 <= h < T /\ usedz H h = 0.
Proof.
destruct INV as ((HlU & _) & (Hc & _ & Hcu) & _).
destruct (cnt1_has_zero (ht_used H)) as (h & Hh & Hz); [lia|].
exists h. unfold usedz. subst T. split; [lia | exact Hz].
Qed.
Lemma find_off_exists : forall c, exists j, find_off H c = Some j.
Proof.
intros c. destruct free_slot_exists as (h & Hh & Hz).
pose proof inv_T_pos as HT.
destruct (ffirst_exists (fun j => slot_stop H c (cyc T (hash0 T c) j)) (Z.to_nat T) 0 (offs T (hash0 T c) h))
as (j & E & _).
- pose proof (offs_range T (hash0 T c) h HT). lia.
- rewrite cyc_offs by lia. unfold slot_stop. rewrite Hz. reflexivity.
- exists j. exact E.
Qed.
Lemma find_off_spec : forall c j, find_off H c = Some j ->
0 <= j < T /\ slot_stop H c (cyc T (hash0 T c) j) = true /\
(forall i, 0 <= i < j -> slot_stop H c (cyc T (hash0 T c) i) = false).
Proof.
intros c j E. unfold find_off in E. apply ffirst_Some in E. destruct E as (H1 & H2 & H3).
pose proof inv_T_pos. subst T. split; [lia|]. split; [exact H2|]. intros i Hi. apply H3. lia.
Qed.
Lemma find_slot_of_off : forall c j, find_off H c = Some j -> find_slot H c = Some (cyc T (hash0 T c) j).
Proof. intros c j E. unfold find_slot. subst T. rewrite E. reflexivity. Qed.
Lemma find_slot_exists : forall c, exists h, find_slot H c = Some h /\ 0 <= h < T.
Proof.
intros c. destruct (find_off_exists c) as (j & E). exists (cyc T (hash0 T c) j).
split; [apply find_slot_of_off; exact E | apply cyc_range; apply inv_T_pos].
Qed.
Lemma probe_start : forall c, cyc T (hash0 T c) 0 = hash0 T c.
Proof. intros c. apply cyc_0. apply hash0_range. apply inv_T_pos. Qed.
Lemma probe_step : forall c js j, find_off H c = Some js -> 0 <= j < js ->
let h := cyc T (hash0 T c) j in
0 <= h < T /\ usedz H h <> 0 /\ key H h <> c /\ colour_eqb (key H h) c = false /\
cyc T (hash0 T c) (j + 1) = probe_next T h /\ 0 <= probe_next T h < T.
Proof.
intros c js j E Hj h. destruct (find_off_spec c js E) as (H1 & _ & H3).
specialize (H3 j Hj). unfold slot_stop in H3. apply Bool.orb_false_iff in H3 as [Hu Hk].
pose proof inv_T_pos as HT.
assert (Hh : 0 <= h < T) by (apply cyc_range; exact HT).
split; [exact Hh|]. split; [apply Z.eqb_neq; exact Hu|].
split; [intros Heq; fold h in Hk; rewrite (proj2 (colour_eqb_spec _ _) Heq) in Hk; discriminate|].
split; [exact Hk|]. split; [apply cyc_succ; exact HT | apply probe_next_range; exact Hh].
Qed.
Lemma probe_end : forall c js, find_off H c = Some js ->
let h := cyc T (hash0 T c) js in
find_slot H c = Some h /\ 0 <= h < T /\
(usedz H h = 0 \/ (usedz H h = 1 /\ key H h = c /\ colour_eqb (key H h) c = true)).
Proof.
intros c js E h. destruct (find_off_spec c js E) as (H1 & H2 & _).
pose proof inv_T_pos as HT.
assert (Hh : 0 <= h < T) by (apply cyc_range; exact HT).
split; [apply find_slot_of_off; exact E|]. split; [exact Hh|].
unfold slot_stop in H2. destruct (inv_used01 h Hh) as [Hu|Hu]; [left; exact Hu | right].
fold h in H2. rewrite Hu in H2. cbn in H2. split; [exact Hu|]. split; [apply colour_eqb_spec; exact H2 | exact H2].
Qed.
Lemma find_off_le_cnt : forall c js, find_off H c = Some js -> js <= ht_cnt H.
Proof.
intros c js E. destruct (find_off_spec c js E) as (H1 & _ & H3).
pose proof inv_T_pos as HT. destruct INV as ((HlU & _) & (Hc & _ & Hcu) & _).
rewrite <- Hcu.
assert (Hlen : Z.of_nat (length (map (cyc T (hash0 T c)) (zseq 0 js))) = js).
{ rewrite length_map, zseq_length. lia. }
rewrite <- Hlen. apply cnt1_nodup_bound.
- apply Injective_map_NoDup_in; [|apply zseq_NoDup].
intros x y Hx Hy Exy. apply In_zseq in Hx. apply In_zseq in Hy. apply (cyc_inj T (hash0 T c)); try lia; exact Exy.
- intros p Hp. apply in_map_iff in Hp as (i & <- & Hi). apply In_zseq in Hi.
specialize (H3 i ltac:(lia)). unfold slot_stop in H3. apply Bool.orb_false_iff in H3 as [Hu _].
apply Z.eqb_neq in Hu. unfold usedz in Hu. fold T. rewrite HlU. split; [apply cyc_range; exact HT | exact Hu].
Qed.
Lemma find_present : forall h, in_slot H h -> find_slot H (key H h) = Some h.
Proof.
intros h Hin. pose proof inv_T_pos as HT. destruct Hin as [Hh Hu].
destruct INV as (_ & _ & _ & _ & _ & I7 & I8).
set (c := key H h). set (a := hash0 T c).
assert (E : find_off H c = Some (offs T a h)).
{ unfold find_off. apply ffirst_charact.
- pose proof (offs_range T a h HT). lia.
- fold T. fold a. rewrite cyc_offs by (subst T; auto). unfold slot_stop. subst c. rewrite colour_eqb_refl. apply Bool.orb_true_r.
- intros i Hi. fold T. fold a. unfold slot_stop. apply Bool.orb_false_iff. split.
+ apply Z.eqb_neq. apply (I8 h i); [split; assumption | exact Hi].
+ destruct (colour_eqb (key H (cyc T a i)) c) eqn:Ek; [|reflexivity]. exfalso.
apply colour_eqb_spec in Ek.
assert (Hci : in_slot H (cyc T a i)).
{ split; [apply cyc_range; exact HT|]. apply (I8 h i); [split; assumption | exact Hi]. }
pose proof (I7 _ _ Hci (conj Hh Hu) Ek) as Heq.
pose proof (offs_range T a h HT).
assert (HiT : 0 <= i < T) by lia.
rewrite <- Heq in Hi. rewrite offs_cyc in Hi by lia. lia. }
rewrite (find_slot_of_off c _ E). f_equal. apply cyc_offs; [exact HT | subst T; exact Hh].
Qed.
Lemma find_slot_used : forall c h, find_slot H c = Some h -> usedz H h <> 0 -> in_slot H h /\ key H h = c.
Proof.
intros c h E Hu. destruct (find_off_exists c) as (js & Ej).
destruct (probe_end c js Ej) as (E' & Hh & Hcase). rewrite E in E'. injection E' as E'. rewrite <- E' in *.
destruct Hcase as [Hz|(H1 & Hk & _)]; [congruence|]. split; [split; [exact Hh| exact Hu] | exact Hk].
Qed.
Lemma find_slot_free : forall c h, find_slot H c = Some h -> usedz H h = 0 ->
forall h', in_slot H h' -> key H h' <> c.
Proof.
intros c h E Hz h' Hin Hk. subst c. rewrite (find_present h' Hin) in E. injection E as ->.
destruct Hin as [_ Hu]. exact (Hu Hz).
Qed.
Lemma find_slot_range : forall c h, find_slot H c = Some h -> 0 <= h < T.
Proof.
intros c h E. unfold find_slot in E. destruct (find_off H c); [|discriminate].
injection E as <-. apply cyc_range. apply inv_T_pos.
Qed.
Lemma inv_cnt : elen ent = ht_cnt H /\ 0 <= ht_cnt H < T.
Proof. destruct INV as (_ & (Hc & He & _) & _). subst T. auto. Qed.
Lemma ent_slot : forall i, 0 <= i < ht_cnt H ->
exists h, in_slot H h /\ cidx H h = i /\ nth_error ent (Z.to_nat i) = Some (key H h, freq H h) /\
palc H i = key H h /\ 1 <= freq H h.
Proof.
intros i Hi. destruct INV as (_ & _ & _ & I4 & I5 & _).
destruct (I5 i Hi) as ((f & Hf) & (h & Hin & Hci)). destruct (I4 h Hin) as (_ & He & Hfr).
rewrite Hci in He. exists h.
assert (E1 : palc H i = key H h) by congruence. assert (E2 : f = freq H h) by congruence.
split; [exact Hin|]. split; [exact Hci|]. split; [exact He|]. split; [exact E1 | exact Hfr].
Qed.
Lemma ent_nth : forall i cf, nth_error ent (Z.to_nat i) = Some cf -> 0 <= i ->
exists h, in_slot H h /\ cidx H h = i /\ cf = (key H h, freq H h) /\ palc H i = key H h /\ 1 <= freq H h /\ i < ht_cnt H.
Proof.
intros i cf Hcf Hi. destruct inv_cnt as [He Hc].
assert (Hlt : i < ht_cnt H).
{ assert (Hn : (Z.to_nat i < length ent)%nat) by (apply nth_error_Some; congruence). unfold elen in He. lia. }
destruct (ent_slot i ltac:(lia)) as (h & H1 & H2 & H3 & H4 & H5).
exists h. rewrite Hcf in H3. injection H3 as ->.
split; [exact H1|]. split; [exact H2|]. split; [reflexivity|]. split; [exact H4|]. split; [exact H5| exact Hlt].
Qed.
Lemma ent_freq_pos : Forall (fun cf => 1 <= snd cf) ent.
Proof.
apply Forall_forall. intros cf Hin. apply In_nth_error in Hin as [n Hn].
destruct (ent_nth (Z.of_nat n) cf) as (h & _ & _ & -> & _ & Hf & _); [rewrite Nat2Z.id; exact Hn | lia |].
exact Hf.
Qed.
Lemma ent_colour_ok : Forall (fun cf => colour_ok (fst cf)) ent.
Proof.
apply Forall_forall. intros cf Hin. apply In_nth_error in Hin as [n Hn].
destruct (ent_nth (Z.of_nat n) cf) as (h & Hin & _ & -> & _ & _ & _); [rewrite Nat2Z.id; exact Hn | lia |].
cbn [fst]. destruct INV as ((_ & HlK & _) & _ & (_ & HK & _) & _). destruct Hin as [Hh _].
unfold key. apply col_at_ok; [exact HK | lia | subst T; lia].
Qed.
Lemma ent_distinct : forall i i' c f f', nth_error ent (Z.to_nat i) = Some (c, f) -> nth_error ent (Z.to_nat i') = Some (c, f') ->
0 <= i -> 0 <= i' -> i = i'.
Proof.
intros i i' c f f' Hi Hi' Hi0 Hi'0.
destruct (ent_nth i _ Hi Hi0) as (h & Hin & Hci & E & _). destruct (ent_nth i' _ Hi' Hi'0) as (h' & Hin' & Hci' & E' & _).
injection E as Ek Ef. injection E' as Ek' Ef'.
destruct INV as (_ & _ & _ & _ & _ & I7 & _).
assert (h = h') by (apply I7; [exact Hin | exact Hin' | congruence]). subst h'. congruence.
Qed.
Lemma ent_NoDup : NoDup (map fst ent).
Proof.
apply (proj2 (NoDup_nth_error _)). intros n m Hn E.
rewrite length_map in Hn.
destruct (nth_error ent n) as [[c f]|] eqn:En; [|apply (proj1 (nth_error_None _ _)) in En; lia].
rewrite !nth_error_map, En in E. cbn in E.
destruct (nth_error ent m) as [[c' f']|] eqn:Em; [|discriminate]. cbn in E. injection E as <-.
enough (Z.of_nat n = Z.of_nat m) by lia.
apply (ent_distinct (Z.of_nat n) (Z.of_nat m) c f f'); rewrite ?Nat2Z.id; auto; lia.
Qed.
Definition has_key (c : colour) : Prop := In c (map fst ent).
Lemma has_key_slot : forall c, has_key c <-> exists h, in_slot H h /\ key H h = c.
Proof.
intros c. unfold has_key. rewrite in_map_iff. split.
- intros ([c' f] & E & Hin). cbn in E. subst c'. apply In_nth_error in Hin as [n Hn].
destruct (ent_nth (Z.of_nat n) _ ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia)) as (h & Hin & _ & E & _).
exists h. injection E as -> ->. auto.
- intros (h & Hin & <-). destruct INV as (_ & _ & _ & I4 & _). destruct (I4 h Hin) as (_ & He & _).
exists (key H h, freq H h). split; [reflexivity|]. eapply nth_error_In. exact He.
Qed.
Lemma find_slot_has_key : forall c h, find_slot H c = Some h -> (usedz H h <> 0 <-> has_key c).
Proof.
intros c h E. rewrite has_key_slot. split.
- intros Hu. exists h. apply find_slot_used; assumption.
- intros (h' & Hin & Hk) Hz. exact (find_slot_free c h E Hz h' Hin Hk).
Qed.
End o.
Fixpoint lset {A : Type} (l : list A) (n : nat) (x : A) : list A :=
match l, n with
| [], _ => []
| _ :: r, O => x :: r
| y :: r, S n' => y :: lset r n' x
end.
Lemma lset_length : forall {A} (l : list A) n x, length (lset l n x) = length l.
Proof. induction l as [|y r IH]; intros [|n] x; cbn; try rewrite IH; reflexivity. Qed.
Lemma nth_error_lset : forall {A} (l : list A) n x m,
nth_error (lset l n x) m = if (Nat.eqb m n && Nat.ltb n (length l))%bool then Some x else nth_error l m.
Proof.
induction l as [|y r IH]; intros [|n] x [|m]; cbn; try reflexivity.
- rewrite Bool.andb_false_r. reflexivity.
- rewrite IH. destruct (Nat.eqb m n); cbn; [|reflexivity].
destruct (length r) as [|k]; [destruct (Nat.ltb_spec n 0); [lia|reflexivity]|].
destruct (Nat.ltb_spec n (S k)), (Nat.leb_spec n k); try reflexivity; lia.
Qed.
Lemma nth_error_lset_same : forall {A} (l : list A) n x, (n < length l)%nat -> nth_error (lset l n x) n = Some x.
Proof.
intros A l n x Hn. rewrite nth_error_lset, Nat.eqb_refl. destruct (Nat.ltb_spec n (length l)); [reflexivity | lia].
Qed.
Lemma nth_error_lset_other : forall {A} (l : list A) n x m, m <> n -> nth_error (lset l n x) m = nth_error l m.
Proof. intros A l n x m Hm. rewrite nth_error_lset. destruct (Nat.eqb_spec m n); [lia | reflexivity]. Qed.
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|x r IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma zsum_lset_snd : forall (l : list entry) n c f f',
nth_error l n = Some (c, f) -> zsum (map snd (lset l n (c, f'))) = zsum (map snd l) - f + f'.
Proof.
induction l as [|[c0 f0] r IH]; intros [|n] c f f' H; cbn in *; try discriminate.
- injection H as -> ->. lia.
- rewrite (IH n c f f' H). lia.
Qed.

Lemma zsum_nonneg : forall (l : list entry), Forall (fun cf => 1 <= snd cf) l -> 0 <= zsum (map snd l).
Proof.
induction l as [|[a b] r IH]; intros Hall; cbn; [lia|].
apply Forall_cons_iff in Hall as [H1 H2]. cbn in H1. specialize (IH H2). lia.
Qed.
Lemma zsum_pos_le : forall (l : list entry) n c f,
Forall (fun cf => 1 <= snd cf) l -> nth_error l n = Some (c, f) -> f <= zsum (map snd l).
Proof.
induction l as [|[c0 f0] r IH]; intros [|n] c f Hall H; cbn in *; try discriminate.
- injection H as -> ->. apply Forall_cons_iff in Hall as [H1 H2]. pose proof (zsum_nonneg r H2). lia.
- apply Forall_cons_iff in Hall as [H1 H2]. cbn in H1. specialize (IH n c f H2 H). lia.
Qed.
Lemma zsum_ge_length : forall (l : list entry), Forall (fun cf => 1 <= snd cf) l -> elen l <= zsum (map snd l).
Proof.
unfold elen. induction l as [|[a b] r IH]; intros Hall; cbn [zsum map length snd]; [lia|].
apply Forall_cons_iff in Hall as [H1 H2]. cbn in H1. specialize (IH H2). lia.
Qed.
Definition ht_init (T : Z) (frequ keys colidx : list Z) : htab :=
mkHT frequ keys (repeat 0 (Z.to_nat T)) (repeat 0 (Z.to_nat (3 * T))) colidx 0 T.
Lemma ht_init_inv : forall T frequ keys colidx,
0 < T -> zlen frequ = T -> zlen keys = 3 * T -> zlen colidx = T ->
Forall (fun v => 0 <= v < 256) keys ->
ht_inv (ht_init T frequ keys colidx) [].
Proof.
intros T frequ keys colidx HT Hf Hk Hc Hkb. unfold ht_inv, ht_init. cbn -[Z.mul repeat Z.to_nat].
assert (Hu0 : forall h, usedz (mkHT frequ keys (repeat 0 (Z.to_nat T)) (repeat 0 (Z.to_nat (3 * T))) colidx 0 T) h = 0).
{ intros h. unfold usedz. cbn. unfold getz. destruct (Nat.lt_ge_cases (Z.to_nat h) (Z.to_nat T)).
- apply nth_repeat_lt. exact H.
- rewrite nth_overflow; [reflexivity|]. rewrite repeat_length. exact H. }
assert (Hno : forall h, ~ in_slot (mkHT frequ keys (repeat 0 (Z.to_nat T)) (repeat 0 (Z.to_nat (3 * T))) colidx 0 T) h).
{ intros h [_ Hu]. apply Hu. apply Hu0. }
split; [unfold zlen in *; rewrite !repeat_length; lia|].
split; [rewrite cnt1_repeat0; cbn; lia|].
split; [split; [intros h Hh; left; apply Hu0|]; split; [exact Hkb | apply Forall_repeat_Z; lia]|].
split; [intros h Hin; exfalso; exact (Hno h Hin)|].
split; [intros i Hi; lia|].
split; [intros h h' Hin; exfalso; exact (Hno h Hin)|].
intros h j Hin; exfalso; exact (Hno h Hin).
Qed.
Definition ht_hit (H : htab) (h : Z) : htab :=
mkHT (setz (ht_frequ H) h (freq H h + 1)) (ht_keys H) (ht_used H) (ht_pal H) (ht_colidx H) (ht_cnt H) (ht_T H).
Definition ht_ins (H : htab) (h : Z) (c : colour) (f : Z) : htab :=
mkHT (setz (ht_frequ H) h f) (set_col (ht_keys H) h c) (setz (ht_used H) h 1)
(set_col (ht_pal H) (ht_cnt H) c) (setz (ht_colidx H) h (ht_cnt H)) (ht_cnt H + 1) (ht_T H).
Lemma ht_ins_usedz : forall H h c f x, 0 <= h -> 0 <= x -> zlen (ht_used H) = ht_T H ->
usedz (ht_ins H h c f) x = if (x =? h) && (h <? ht_T H) then 1 else usedz H x.
Proof. intros H h c f x Hh Hx L. unfold usedz. cbn [ht_used ht_ins]. rewrite getz_setz, L by lia. reflexivity. Qed.
Lemma ht_ins_cidx : forall H h c f x, 0 <= h -> 0 <= x -> zlen (ht_colidx H) = ht_T H ->
cidx (ht_ins H h c f) x = if (x =? h) && (h <? ht_T H) then ht_cnt H else cidx H x.
Proof. intros H h c f x Hh Hx L. unfold cidx. cbn [ht_colidx ht_cnt ht_ins]. rewrite getz_setz, L by lia. reflexivity. Qed.
Lemma ht_ins_freq : forall H h c f x, 0 <= h -> 0 <= x -> zlen (ht_frequ H) = ht_T H ->
freq (ht_ins H h c f) x = if (x =? h) && (h <? ht_T H) then f else freq H x.
Proof. intros H h c f x Hh Hx L. unfold freq. cbn [ht_frequ ht_ins]. rewrite getz_setz, L by lia. reflexivity. Qed.
Lemma ht_ins_key : forall H h c f x, 0 <= h -> 0 <= x -> 3 * h + 3 <= zlen (ht_keys H) ->
key (ht_ins H h c f) x = if x =? h then c else key H x.
Proof.
intros H h c f x Hh Hx L. unfold key. cbn [ht_keys ht_ins]. destruct (Z.eqb_spec x h) as [->|Hne].
- apply col_at_set_col_same; lia.
- apply col_at_set_col_other; lia.
Qed.
Lemma ht_ins_palc : forall H h c f i, 0 <= ht_cnt H -> 0 <= i -> 3 * ht_cnt H + 3 <= zlen (ht_pal H) ->
palc (ht_ins H h c f) i = if i =? ht_cnt H then c else palc H i.
Proof.
intros H h c f i Hc Hi L. unfold palc. cbn [ht_pal ht_cnt ht_ins]. destruct (Z.eqb_spec i (ht_cnt H)) as [->|Hne].
- apply col_at_set_col_same; lia.
- apply col_at_set_col_other; lia.
Qed.
Section q.
Variable H : htab.
Variable ent : list entry.
Hypothesis INV : ht_inv H ent.
Let T := ht_T H.
Lemma cidx_inj : forall h h', in_slot H h -> in_slot H h' -> cidx H h = cidx H h' -> h = h'.
Proof.
intros h h' Hin Hin' E. destruct INV as (_ & _ & _ & I4 & _ & I7 & _).
destruct (I4 h Hin) as (_ & He & _). destruct (I4 h' Hin') as (_ & He' & _).
rewrite E in He. rewrite He in He'.
assert (Hp : (key H h, freq H h) = (key H h', freq H h')) by congruence.
apply (f_equal fst) in Hp. cbn [fst] in Hp. apply I7; auto.
Qed.
Theorem ht_hit_inv : forall h, in_slot H h ->
ht_inv (ht_hit H h) (lset ent (Z.to_nat (cidx H h)) (key H h, freq H h + 1)).
Proof.
intros h Hin. pose proof INV as INV'.
destruct INV' as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & I5 & I7 & I8).
destruct (I4 h Hin) as (Hci & He & Hf). pose proof Hin as [Hh Hu].
assert (Efr : forall x, 0 <= x -> freq (ht_hit H h) x = if x =? h then freq H h + 1 else freq H x).
{ intros x Hx. unfold freq at 1. cbn [ht_frequ ht_hit]. rewrite getz_setz by lia. rewrite L3.
destruct (Z.eqb_spec x h), (Z.ltb_spec h (ht_T H)); cbn [andb]; try reflexivity; lia. }
assert (Ein : forall x, in_slot (ht_hit H h) x <-> in_slot H x) by (intros; unfold in_slot; cbn; tauto).
assert (Eus : forall x, usedz (ht_hit H h) x = usedz H x) by (intros; reflexivity).
assert (Eky : forall x, key (ht_hit H h) x = key H x) by (intros; reflexivity).
assert (Eci : forall x, cidx (ht_hit H h) x = cidx H x) by (intros; reflexivity).
assert (Epa : forall x, palc (ht_hit H h) x = palc H x) by (intros; reflexivity).
assert (Hlen : (Z.to_nat (cidx H h) < length ent)%nat) by (apply nth_error_Some; congruence).
unfold ht_inv. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_cnt ht_T ht_hit].
split; [rewrite zlen_setz; repeat split; assumption|].
split; [unfold elen; rewrite lset_length; split; [exact C1| split; [exact C2| exact C3]]|].
split; [split; [intros x Hx; rewrite !Eus; apply B1; exact Hx| split; assumption]|].
split.
{ intros x Hx. apply Ein in Hx. rewrite Eci, Eky, Efr by (destruct Hx; lia).
destruct (I4 x Hx) as (Hcx & Hex & Hfx). split; [exact Hcx|].
destruct (Z.eqb_spec x h) as [->|Hne].
- split; [|lia]. apply nth_error_lset_same. exact Hlen.
- split; [|exact Hfx]. rewrite nth_error_lset_other; [exact Hex|].
intros E. apply Hne. apply cidx_inj; [exact Hx | exact Hin | lia]. }
split.
{ intros i Hi. destruct (I5 i Hi) as ((f & Hfi) & (x & Hx & Hxi)). split.
- rewrite Epa. destruct (Z.eq_dec i (cidx H h)) as [->|Hne].
+ exists (freq H h + 1). rewrite nth_error_lset_same by exact Hlen.
assert (Ep : palc H (cidx H h) = key H h) by congruence. rewrite Ep. reflexivity.
+ exists f. rewrite nth_error_lset_other; [exact Hfi | lia].
- exists x. rewrite Ein, Eci. auto. }
split; [intros x y Hx Hy; rewrite !Eky; apply Ein in Hx; apply Ein in Hy; apply I7; assumption|].
intros x j Hx. rewrite Eky, Eus. apply Ein in Hx. apply I8. exact Hx.
Qed.
Lemma ht_hit_sum : forall h, in_slot H h ->
zsum (map snd (lset ent (Z.to_nat (cidx H h)) (key H h, freq H h + 1))) = zsum (map snd ent) + 1.
Proof.
intros h Hin. destruct INV as (_ & _ & _ & I4 & _). destruct (I4 h Hin) as (_ & He & _).
rewrite (zsum_lset_snd _ _ _ _ _ He). lia.
Qed.

Theorem ht_ins_inv : forall h c f,
find_slot H c = Some h -> usedz H h = 0 -> colour_ok c -> 1 <= f -> ht_cnt H + 1 < T ->
ht_inv (ht_ins H h c f) (ent ++ [(c, f)]).
Proof.
intros h c f Hfs Hz Hc Hf HcT. pose proof INV as INV'.
destruct INV' as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & I5 & I7 & I8).
pose proof (find_slot_range H ent INV c h Hfs) as Hh.
pose proof (find_slot_free H ent INV c h Hfs Hz) as Hfree.
destruct (find_off_exists H ent INV c) as (js & Ejs).
destruct (find_off_spec H ent INV c js Ejs) as (Hjs & _ & Hbefore).
pose proof (find_slot_of_off H c js Ejs) as Eh. rewrite Hfs in Eh. injection Eh as Eh.
set (K := ht_ins H h c f).
assert (Eus : forall x, 0 <= x -> usedz K x = if x =? h then 1 else usedz H x).
{ intros x Hx. unfold K. rewrite ht_ins_usedz by lia. destruct (Z.ltb_spec h (ht_T H)); [rewrite Bool.andb_true_r; reflexivity| lia]. }
assert (Eci : forall x, 0 <= x -> cidx K x = if x =? h then ht_cnt H else cidx H x).
{ intros x Hx. unfold K. rewrite ht_ins_cidx by lia. destruct (Z.ltb_spec h (ht_T H)); [rewrite Bool.andb_true_r; reflexivity| lia]. }
assert (Efr : forall x, 0 <= x -> freq K x = if x =? h then f else freq H x).
{ intros x Hx. unfold K. rewrite ht_ins_freq by lia. destruct (Z.ltb_spec h (ht_T H)); [rewrite Bool.andb_true_r; reflexivity| lia]. }
assert (Eky : forall x, 0 <= x -> key K x = if x =? h then c else key H x).
{ intros x Hx. unfold K. apply ht_ins_key; lia. }
assert (Epa : forall i, 0 <= i -> palc K i = if i =? ht_cnt H then c else palc H i).
{ intros i Hi. unfold K. apply ht_ins_palc; lia. }
assert (Ein : forall x, in_slot K x <-> x = h \/ in_slot H x).
{ intros x. unfold in_slot. change (ht_T K) with (ht_T H). split.
- intros [Hx Hu]. rewrite Eus in Hu by lia. destruct (Z.eqb_spec x h); [left; assumption | right; auto].
- intros [->|[Hx Hu]]; (split; [lia|]); rewrite Eus by lia; [rewrite Z.eqb_refl; lia|].
destruct (Z.eqb_spec x h); [lia | exact Hu]. }
assert (Hne_used : forall x, in_slot H x -> x <> h) by (intros x [_ Hu] ->; exact (Hu Hz)).
assert (Elen : length ent = Z.to_nat (ht_cnt H)) by (unfold elen in C2; lia).
unfold ht_inv. change (ht_T K) with (ht_T H). change (ht_cnt K) with (ht_cnt H + 1).
split.
{ unfold K. cbn [ht_used ht_keys ht_frequ ht_colidx ht_pal ht_ins]. rewrite !zlen_setz, !zlen_set_col. repeat split; assumption. }
split.
{ split; [lia|]. split; [unfold elen in *; rewrite length_app; cbn [length]; lia|].
unfold K. cbn [ht_used ht_ins]. rewrite cnt1_setz by lia. fold (usedz H h). rewrite Hz. cbn. lia. }
split.
{ split.
- intros x Hx. rewrite Eus by lia. destruct (Z.eqb x h); [right; reflexivity | apply B1; exact Hx].
- unfold K. cbn [ht_keys ht_pal ht_ins]. destruct Hc as (Hc1 & Hc2 & Hc3). unfold set_col, setz.
split; repeat apply Forall_updn; assumption. }
split.
{ intros x Hx. apply Ein in Hx. assert (Hx0 : 0 <= x < ht_T H) by (destruct Hx as [->|[Hx _]]; [exact Hh| exact Hx]).
rewrite Eci, Eky, Efr by lia. destruct (Z.eqb_spec x h) as [->|Hne].
- split; [lia|]. split; [|exact Hf]. rewrite nth_error_app2 by lia. rewrite Elen, Nat.sub_diag. reflexivity.
- destruct Hx as [->|Hx]; [lia|]. destruct (I4 x Hx) as (Hcx & Hex & Hfx).
split; [lia|]. split; [|exact Hfx]. rewrite nth_error_app1 by lia. exact Hex. }
split.
{ intros i Hi. rewrite Epa by lia. destruct (Z.eqb_spec i (ht_cnt H)) as [->|Hne].
- split.
+ exists f. rewrite nth_error_app2 by lia. rewrite Elen, Nat.sub_diag. reflexivity.
+ exists h. rewrite Ein, Eci, Z.eqb_refl by lia. auto.
- destruct (I5 i ltac:(lia)) as ((fi & Hfi) & (x & Hx & Hxi)). split.
+ exists fi. rewrite nth_error_app1 by lia. exact Hfi.
+ exists x. rewrite Ein, Eci by (destruct Hx; lia).
destruct (Z.eqb_spec x h) as [->|]; [exfalso; exact (Hne_used h Hx eq_refl) | auto]. }
split.
{ intros x y Hx Hy. apply Ein in Hx. apply Ein in Hy.
assert (Hx0 : 0 <= x < ht_T H) by (destruct Hx as [->|[? _]]; auto).
assert (Hy0 : 0 <= y < ht_T H) by (destruct Hy as [->|[? _]]; auto).
rewrite !Eky by lia.
destruct (Z.eqb_spec x h) as [->|Hnx], (Z.eqb_spec y h) as [->|Hny]; intros E; try reflexivity.
- destruct Hy as [->|Hy]; [reflexivity|]. exfalso. exact (Hfree y Hy (eq_sym E)).
- destruct Hx as [->|Hx]; [lia|]. exfalso. exact (Hfree x Hx E).
- destruct Hx as [->|Hx]; [lia|]. destruct Hy as [->|Hy]; [lia|]. apply I7; assumption. }
{ intros x j Hx Hj. apply Ein in Hx.
assert (Hx0 : 0 <= x < ht_T H) by (destruct Hx as [->|[? _]]; auto).
rewrite Eky in Hj |- * by lia.
assert (HT : 0 < ht_T H) by lia.
rewrite Eus by (apply (proj1 (cyc_range (ht_T H) _ j HT))).
destruct (Z.eqb_spec x h) as [->|Hnx].
-
rewrite Eh in Hj. rewrite offs_cyc in Hj by lia.
specialize (Hbefore j Hj). unfold slot_stop in Hbefore. apply Bool.orb_false_iff in Hbefore as [Hu _].
apply Z.eqb_neq in Hu.
destruct (Z.eqb (cyc (ht_T H) (hash0 (ht_T H) c) j) h); [lia | exact Hu].
- destruct Hx as [->|Hx]; [lia|]. specialize (I8 x j Hx Hj).
destruct (Z.eqb (cyc (ht_T H) (hash0 (ht_T H) (key H x)) j) h); [lia | exact I8]. }
Qed.
End q.
