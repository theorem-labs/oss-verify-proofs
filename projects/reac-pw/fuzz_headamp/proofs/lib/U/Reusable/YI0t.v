(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition MAGIC_0101 : Z := 72340172838076674.
Lemma magic0101_eq : MAGIC_0101 * 255 = 2 ^ 64 + 254.
Proof. reflexivity. Qed.
Lemma magic0101_div : forall x, 0 <= x < 2 ^ 40 -> (x * MAGIC_0101) / 2 ^ 64 = x / 255.
Proof.
intros x Hx.
pose proof (Z.div_mod x 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 255 ltac:(lia)) as Hmb.
set (q := x / 255) in *. set (r := x mod 255) in *.
pose proof magic0101_eq as HM.
symmetry. apply (Z.div_unique_pos _ _ _ ((r * 2 ^ 64 + 254 * x) / 255)).
- split.
+ apply Z.div_pos; lia.
+ apply Z.div_lt_upper_bound; [lia|]. nia.
- apply (Z.mul_cancel_r _ _ 255); [lia|].
assert (E : x * MAGIC_0101 * 255 = (2 ^ 64 * q) * 255 + (r * 2 ^ 64 + 254 * x)) by nia.
rewrite E, Z.mul_add_distr_r. f_equal.
rewrite (Z.mul_comm (_ / 255) 255). apply (proj2 (Z.div_exact _ 255 ltac:(lia))).
apply Z.mod_divide; [lia|]. exists (x * MAGIC_0101 - 2 ^ 64 * q). nia.
Qed.
Lemma blb_size_ok : forall L n, 0 <= L -> 0 <= n -> 8 * n <= 12 * L + 8 -> n + n / 255 + 2 <= (384 * L) / 255 + 4.
Proof.
intros L n HL Hn Hle.
pose proof (Z.div_mod n 255 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 255 ltac:(lia)) as Hmb.
pose proof (Z.div_mod (384 * L) 255 ltac:(lia)) as Hdm2. pose proof (Z.mod_pos_bound (384 * L) 255 ltac:(lia)) as Hmb2.
set (q := n / 255) in *. set (r := n mod 255) in *.
set (q2 := 384 * L / 255) in *. set (r2 := (384 * L) mod 255) in *. lia.
Qed.
Fixpoint updn (l : list Z) (i : nat) (v : Z) : list Z :=
match l, i with
| [], _ => []
| _ :: r, O => v :: r
| x :: r, S i' => x :: updn r i' v
end.
Lemma updn_length : forall l i v, length (updn l i v) = length l.
Proof. induction l as [|x r IH]; intros [|i] v; cbn; try rewrite IH; reflexivity. Qed.
Lemma nth_updn : forall l i v j d, nth j (updn l i v) d = if Nat.eqb j i && Nat.ltb i (length l) then v else nth j l d.
Proof.
induction l as [|x r IH]; intros i v j d.
- cbn. rewrite Bool.andb_false_r. destruct j; reflexivity.
- destruct i as [|i]; destruct j as [|j]; cbn [updn nth length]; try reflexivity.
rewrite IH. change (S j =? S i)%nat with (j =? i)%nat. change (S i <? S (length r))%nat with (i <? length r)%nat.
reflexivity.
Qed.
Lemma nth_updn_same : forall l i v d, (i < length l)%nat -> nth i (updn l i v) d = v.
Proof. intros l i v d Hi. rewrite nth_updn, Nat.eqb_refl. cbn [andb]. destruct (Nat.ltb_spec i (length l)); [reflexivity | lia]. Qed.
Lemma nth_updn_other : forall l i v j d, j <> i -> nth j (updn l i v) d = nth j l d.
Proof. intros l i v j d Hj. rewrite nth_updn. destruct (Nat.eqb_spec j i); [lia | reflexivity]. Qed.
Lemma Forall_nth_Z : forall (P : Z -> Prop) l, Forall P l <-> forall j, (j < length l)%nat -> P (nth j l 0).
Proof.
intros P l. split.
- intros H j Hj. apply (proj1 (Forall_nth P l) H). exact Hj.
- intros H. apply (proj2 (Forall_nth P l)). intros j d Hj. rewrite (nth_indep _ d 0 Hj). apply H. exact Hj.
Qed.
Lemma Forall_updn : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (updn l i v).
Proof.
intros P l i v H Hv. apply Forall_nth_Z. intros j Hj. rewrite updn_length in Hj. rewrite nth_updn.
destruct (Nat.eqb j i && Nat.ltb i (length l)); [exact Hv|]. apply (proj1 (Forall_nth_Z P l) H). exact Hj.
Qed.
Lemma Forall_repeat_Z : forall (P : Z -> Prop) n v, P v -> Forall P (repeat v n).
Proof. intros P n v Hv. induction n; cbn; constructor; assumption. Qed.
Fixpoint zero_range (l : list Z) (i n : nat) : list Z :=
match n with
| O => l
| S n' => zero_range (updn l i 0) (S i) n'
end.
Lemma zero_range_length : forall n l i, length (zero_range l i n) = length l.
Proof. induction n as [|n IH]; intros l i; cbn; [reflexivity|]. rewrite IH, updn_length. reflexivity. Qed.
Lemma nth_zero_range : forall n l i j d, (i + n <= length l)%nat ->
nth j (zero_range l i n) d = if Nat.leb i j && Nat.ltb j (i + n) then 0 else nth j l d.
Proof.
induction n as [|n IH]; intros l i j d Hlen; cbn [zero_range].
- destruct (Nat.leb_spec i j), (Nat.ltb_spec j (i + 0)); cbn [andb]; try reflexivity. lia.
- rewrite IH by (rewrite updn_length; lia). rewrite nth_updn.
destruct (Nat.leb_spec (S i) j), (Nat.ltb_spec j (S i + n)), (Nat.eqb_spec j i), (Nat.ltb_spec i (length l)), (Nat.leb_spec i j), (Nat.ltb_spec j (i + S n)); cbn [andb]; try reflexivity; lia.
Qed.
Fixpoint countA (LI LM : list Z) : Z :=
match LI, LM with
| x :: LI', y :: LM' => (if (negb (x =? 0)) && (y =? 0) then 1 else 0) + countA LI' LM'
| _, _ => 0
end.
Lemma countA_nonneg : forall LI LM, 0 <= countA LI LM.
Proof. induction LI as [|x LI IH]; intros [|y LM]; cbn; try lia. specialize (IH LM). destruct (_ && _); lia. Qed.
Lemma countA_repeat0 : forall n LM, countA (repeat 0 n) LM = 0.
Proof. induction n as [|n IH]; intros [|y LM]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma countA_updn_LI : forall LI LM i v,
length LM = length LI -> (i < length LI)%nat ->
countA (updn LI i v) LM = countA LI LM
- (if (negb (nth i LI 0 =? 0)) && (nth i LM 0 =? 0) then 1 else 0)
+ (if (negb (v =? 0)) && (nth i LM 0 =? 0) then 1 else 0).
Proof.
induction LI as [|x LI IH]; intros [|y LM] [|i] v Hlen Hi; cbn in *; try lia.
rewrite (IH LM i v) by lia. pose proof (countA_nonneg LI LM).
destruct (negb (x =? 0) && (y =? 0)), (negb (nth i LI 0 =? 0) && (nth i LM 0 =? 0)), (negb (v =? 0) && (nth i LM 0 =? 0)); lia.
Qed.
Lemma countA_updn_LM : forall LI LM i v,
length LM = length LI -> (i < length LI)%nat ->
countA LI (updn LM i v) = countA LI LM
- (if (negb (nth i LI 0 =? 0)) && (nth i LM 0 =? 0) then 1 else 0)
+ (if (negb (nth i LI 0 =? 0)) && (v =? 0) then 1 else 0).
Proof.
induction LI as [|x LI IH]; intros [|y LM] [|i] v Hlen Hi; cbn in *; try lia.
rewrite (IH LM i v) by lia. pose proof (countA_nonneg LI LM).
destruct (negb (x =? 0) && (y =? 0)), (negb (nth i LI 0 =? 0) && (nth i LM 0 =? 0)), (negb (nth i LI 0 =? 0) && (v =? 0)); lia.
Qed.
Lemma countA_pos : forall LI LM i, length LM = length LI -> (i < length LI)%nat ->
nth i LI 0 <> 0 -> nth i LM 0 = 0 -> 1 <= countA LI LM.
Proof.
induction LI as [|x LI IH]; intros [|y LM] i Hlen Hi HLI HLM; cbn in Hlen, Hi; try lia.
cbn [countA]. pose proof (countA_nonneg LI LM).
destruct i as [|i]; cbn [nth] in HLI, HLM.
- subst y. destruct (Z.eqb_spec x 0); [lia|]. cbn [negb andb Z.eqb]. lia.
- specialize (IH LM i ltac:(lia) ltac:(lia) HLI HLM). destruct (_ && _); lia.
Qed.
Record lzw_abs := mkLA {
la_TI : list Z;  la_LM : list Z;  la_LI : list Z;  la_TM : list Z;
la_s : Z;  la_lp : Z;  la_dp : Z;  la_mp : Z;  la_Cn : Z;  la_R : Z }.
Definition u16s (l : list Z) : Prop := Forall (fun v => 0 <= v < 65536) l.
Definition below (b : Z) (l : list Z) : Prop := Forall (fun v => 0 <= v < b) l.
Definition lzw_inv (idl nP : Z) (X : lzw_abs) : Prop :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
length TI = Z.to_nat (idl * idl) /\ length LM = 4096%nat /\ length LI = 4096%nat /\
length TM = Z.to_nat (2049 * idl) /\
below 4096 TI /\ below 4096 LI /\ below mp LM /\ u16s TM /\
(forall j, (j < Z.to_nat ((mp - 1) * idl))%nat -> 0 <= nth j TM 0 < 4096) /\
idl + 2 <= dp <= 4096 /\ 1 <= mp /\
countA LI LM + 2 * (mp - 1) <= dp - idl - 2 /\
0 <= R /\ R * (4095 - idl) + (dp - idl - 2) <= Cn /\ Cn <= s /\ lp = 1 + Cn + R /\
0 <= s <= nP.
Definition lzw_par (idl nP MR : Z) : Prop :=
2 <= idl <= 256 /\ 1 <= nP <= 100000000 /\ MR * (4094 - idl) <= nP < (MR + 1) * (4094 - idl) /\ 0 <= MR.
Definition cap (nP MR : Z) : Z := nP + 2 + MR.
Lemma R_le_MR : forall idl nP MR R Cn,
lzw_par idl nP MR -> 0 <= R -> R * (4095 - idl) <= Cn -> Cn <= nP -> R <= MR.
Proof.
intros idl nP MR R Cn (Hidl & HnP & HMR & HMR0) HR HRC HCn.
destruct (Z_lt_le_dec MR R) as [Hlt|Hle]; [|exact Hle]. exfalso.
assert (H1 : (MR + 1) * (4095 - idl) <= R * (4095 - idl)) by (apply Z.mul_le_mono_nonneg_r; lia).
nia.
Qed.
Lemma lp_head_bound : forall idl nP MR X,
lzw_par idl nP MR -> lzw_inv idl nP X -> la_s X < nP -> 0 <= la_lp X /\ la_lp X + 1 < cap nP MR - 1 + 1 /\ la_lp X + 2 <= cap nP MR.
Proof.
intros idl nP MR [TI LM LI TM s lp dp mp Cn R] HP HI Hs. cbn [la_s la_lp lzw_inv] in *.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & Hmp & HA & HR & HRC & HCn & Hlp & Hs0).
pose proof HP as (Hidl & HnP & HMR & HMR0).
assert (HRle : R <= MR).
{ eapply (R_le_MR idl nP MR R Cn HP HR); lia. }
unfold cap. destruct (Z.eq_dec R MR) as [->|Hne]; [|nia].
nia.
Qed.
Lemma lp_exit_bound : forall idl nP MR X,
lzw_par idl nP MR -> lzw_inv idl nP X -> 2 <= la_lp X + 1 <= cap nP MR /\ 0 <= la_lp X.
Proof.
intros idl nP MR [TI LM LI TM s lp dp mp Cn R] HP HI. cbn [la_s la_lp lzw_inv] in *.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & Hmp & HA & HR & HRC & HCn & Hlp & Hs0).
pose proof HP as (Hidl & HnP & HMR & HMR0).
assert (HRle : R <= MR) by (eapply (R_le_MR idl nP MR R Cn HP HR); lia).
unfold cap. pose proof (countA_nonneg LI LM). nia.
Qed.
Lemma mp_bound : forall idl nP X, 2 <= idl -> lzw_inv idl nP X -> 1 <= la_mp X <= 2047.
Proof.
intros idl nP [TI LM LI TM s lp dp mp Cn R] Hidl HI. cbn [la_mp lzw_inv] in *.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & Hmp & HA & _).
pose proof (countA_nonneg LI LM). lia.
Qed.
Lemma below_nth : forall b l j, below b l -> (j < length l)%nat -> 0 <= nth j l 0 < b.
Proof. intros b l j H Hj. apply (proj1 (Forall_nth_Z _ l) H). exact Hj. Qed.
Lemma u16s_nth : forall l j, u16s l -> (j < length l)%nat -> 0 <= nth j l 0 < 65536.
Proof. intros l j H Hj. apply (proj1 (Forall_nth_Z _ l) H). exact Hj. Qed.
Lemma idx2_bound : forall idl q c, 0 <= q -> 0 <= c < idl -> q * idl + c < (q + 1) * idl.
Proof. intros. nia. Qed.
Lemma TI_read : forall idl nP X q c, 2 <= idl -> lzw_inv idl nP X -> 0 <= q < idl -> 0 <= c < idl ->
(Z.to_nat (q * idl + c) < length (la_TI X))%nat /\ 0 <= nth (Z.to_nat (q * idl + c)) (la_TI X) 0 < 4096.
Proof.
intros idl nP [TI LM LI TM s lp dp mp Cn R] q c Hidl HI Hq Hc. cbn [la_TI lzw_inv] in *.
destruct HI as (HlTI & _ & _ & _ & HbTI & _).
assert (Hlt : (Z.to_nat (q * idl + c) < length TI)%nat).
{ rewrite HlTI. assert (q * idl + c < idl * idl) by nia. apply Z2Nat.inj_lt; nia. }
split; [exact Hlt|]. apply below_nth; [exact HbTI | exact Hlt].
Qed.
Lemma LI_read : forall idl nP X q, lzw_inv idl nP X -> 0 <= q < 4096 ->
(Z.to_nat q < length (la_LI X))%nat /\ 0 <= nth (Z.to_nat q) (la_LI X) 0 < 4096.
Proof.
intros idl nP [TI LM LI TM s lp dp mp Cn R] q HI Hq. cbn [la_LI lzw_inv] in *.
destruct HI as (_ & _ & HlLI & _ & _ & HbLI & _).
assert (Hlt : (Z.to_nat q < length LI)%nat) by (rewrite HlLI; lia).
split; [exact Hlt|]. apply below_nth; [exact HbLI | exact Hlt].
Qed.
Lemma LM_read : forall idl nP X q, lzw_inv idl nP X -> 0 <= q < 4096 ->
(Z.to_nat q < length (la_LM X))%nat /\ 0 <= nth (Z.to_nat q) (la_LM X) 0 < la_mp X.
Proof.
intros idl nP [TI LM LI TM s lp dp mp Cn R] q HI Hq. cbn [la_LM la_mp lzw_inv] in *.
destruct HI as (_ & HlLM & _ & _ & _ & _ & HbLM & _).
assert (Hlt : (Z.to_nat q < length LM)%nat) by (rewrite HlLM; lia).
split; [exact Hlt|]. apply below_nth; [exact HbLM | exact Hlt].
Qed.
Lemma TM_read : forall idl nP X m c, 2 <= idl -> lzw_inv idl nP X -> 1 <= m < la_mp X -> 0 <= c < idl ->
(Z.to_nat ((m - 1) * idl + c) < length (la_TM X))%nat /\ 0 <= nth (Z.to_nat ((m - 1) * idl + c)) (la_TM X) 0 < 4096 /\
(m - 1) * idl + c + 1 <= 2049 * idl.
Proof.
intros idl nP [TI LM LI TM s lp dp mp Cn R] m c Hidl HI Hm Hc. cbn [la_TM la_mp lzw_inv] in *.
destruct HI as (_ & _ & _ & HlTM & _ & _ & _ & HuTM & HaTM & Hdp & Hmp & HA & _).
pose proof (countA_nonneg LI LM) as HA0.
assert (Hrow : (m - 1) * idl + c < (mp - 1) * idl) by nia.
assert (Hall : (mp - 1) * idl <= 2049 * idl) by nia.
split; [rewrite HlTM; apply Z2Nat.inj_lt; nia|]. split; [|nia].
apply HaTM. apply Z2Nat.inj_lt; nia.
Qed.
Section a.
Variables idl nP : Z.
Hypothesis Hidl : 2 <= idl <= 256.
Let inv := lzw_inv idl nP.
Definition st_typec (X : lzw_abs) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in mkLA TI LM LI TM nP (lp + 1) dp mp (Cn + 1) R.
Lemma inv_typec : forall X, inv X -> la_s X < nP -> inv (st_typec X).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] HI Hs. unfold inv, lzw_inv in *. cbn [st_typec la_dp la_s la_LI la_LM la_mp] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
repeat split; try assumption; try lia; apply H9; assumption.
Qed.
Definition st_ti (X : lzw_abs) (q c k : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA (updn TI (Z.to_nat (q * idl + c)) dp) LM LI TM (k + 1) (lp + 1) (dp + 1) mp (Cn + 1) R.
Lemma inv_ti : forall X q c k, inv X -> la_dp X < 4096 -> la_s X <= k < nP -> 0 <= q < idl -> 0 <= c < idl ->
inv (st_ti X q c k).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] q c k HI Hdp Hk Hq Hc. unfold inv, lzw_inv in *. cbn [st_ti la_dp la_s la_LI la_LM la_mp] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
repeat split; try assumption; try lia; try (apply H9; assumption).
- rewrite updn_length; exact H1.
- apply Forall_updn; [exact H5 | lia].
Qed.
Definition st_first (X : lzw_abs) (q k : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA TI LM (updn LI (Z.to_nat q) dp) TM (k + 1) (lp + 1) (dp + 1) mp (Cn + 1) R.
Lemma inv_first : forall X q k, inv X -> la_dp X < 4096 -> la_s X <= k < nP -> 0 <= q < 4096 ->
nth (Z.to_nat q) (la_LI X) 0 = 0 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
inv (st_first X q k).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] q k HI Hdp Hk Hq HLI HLM. unfold inv, lzw_inv in *. cbn [st_first la_dp la_s la_LI la_LM la_mp] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
assert (HA' : countA (updn LI (Z.to_nat q) dp) LM = countA LI LM + 1).
{ rewrite countA_updn_LI by lia. rewrite HLI, HLM. cbn [Z.eqb negb andb].
destruct (Z.eqb_spec dp 0); [lia|]. cbn [negb andb]. lia. }
repeat split; try assumption; try lia; try (apply H9; assumption).
- rewrite updn_length; exact H3.
- apply Forall_updn; [exact H6 | lia].
Qed.
Definition st_switch (X : lzw_abs) (q c k : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA TI (updn LM (Z.to_nat q) mp) LI
(updn (zero_range TM (Z.to_nat ((mp - 1) * idl)) (Z.to_nat idl)) (Z.to_nat ((mp - 1) * idl + c)) dp)
(k + 1) (lp + 1) (dp + 1) (mp + 1) (Cn + 1) R.
Lemma inv_switch : forall X q c k, inv X -> la_dp X < 4096 -> la_s X <= k < nP -> 0 <= q < 4096 -> 0 <= c < idl ->
nth (Z.to_nat q) (la_LI X) 0 <> 0 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
inv (st_switch X q c k) /\ (la_mp X - 1) * idl + idl <= 2049 * idl /\ 0 <= (la_mp X - 1) * idl.
Proof.
intros [TI LM LI TM s lp dp mp Cn R] q c k HI Hdp Hk Hq Hc HLI HLM. unfold inv, lzw_inv in *. cbn [st_switch la_dp la_s la_LI la_LM la_mp] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
pose proof (countA_nonneg LI LM) as HA0.
assert (HA1 : 1 <= countA LI LM) by (apply (countA_pos LI LM (Z.to_nat q)); [lia | lia | exact HLI | exact HLM]).
assert (Hrow : (mp - 1) * idl + idl <= 2049 * idl) by nia.
assert (Hrow0 : 0 <= (mp - 1) * idl) by nia.
assert (HA' : countA LI (updn LM (Z.to_nat q) mp) = countA LI LM - 1).
{ rewrite countA_updn_LM by lia. rewrite HLM.
destruct (Z.eqb_spec (nth (Z.to_nat q) LI 0) 0); [lia|]. destruct (Z.eqb_spec mp 0); [lia|]. cbn [Z.eqb negb andb]. lia. }
assert (Hlen4 : (Z.to_nat ((mp - 1) * idl) + Z.to_nat idl <= length TM)%nat) by (rewrite H4; nia).
set (TM' := updn (zero_range TM (Z.to_nat ((mp - 1) * idl)) (Z.to_nat idl)) (Z.to_nat ((mp - 1) * idl + c)) dp).
assert (HTM1 : u16s TM').
{ subst TM'. apply Forall_updn; [|lia]. unfold u16s. apply Forall_nth_Z. intros j Hj. rewrite zero_range_length in Hj.
rewrite nth_zero_range by exact Hlen4. destruct (_ && _); [lia|]. apply u16s_nth; [exact H8 | exact Hj]. }
assert (HTM2 : forall j, (j < Z.to_nat ((mp + 1 - 1) * idl))%nat -> 0 <= nth j TM' 0 < 4096).
{ intros j Hj. subst TM'. rewrite nth_updn. destruct (_ && _); [lia|].
rewrite nth_zero_range by exact Hlen4.
destruct (Nat.leb_spec (Z.to_nat ((mp - 1) * idl)) j), (Nat.ltb_spec j (Z.to_nat ((mp - 1) * idl) + Z.to_nat idl)); cbn [andb]; try lia.
apply H9. nia. }
assert (HLM' : below (mp + 1) (updn LM (Z.to_nat q) mp)).
{ apply Forall_updn; [|lia]. eapply Forall_impl; [|exact H7]. intros v Hv. cbn beta in Hv. lia. }
split; [| split; [exact Hrow | exact Hrow0]].
repeat split; try assumption; try lia; try (apply HTM2; assumption).
- rewrite updn_length; exact H2.
- subst TM'. rewrite updn_length, zero_range_length; exact H4.
Qed.
Definition st_map (X : lzw_abs) (m c k : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA TI LM LI (updn TM (Z.to_nat ((m - 1) * idl + c)) dp) (k + 1) (lp + 1) (dp + 1) mp (Cn + 1) R.
Lemma inv_map : forall X m c k, inv X -> la_dp X < 4096 -> la_s X <= k < nP -> 1 <= m < la_mp X -> 0 <= c < idl ->
inv (st_map X m c k).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] m c k HI Hdp Hk Hm Hc. unfold inv, lzw_inv in *. cbn [st_map la_dp la_s la_LI la_LM la_mp] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
assert (HTM2 : forall j, (j < Z.to_nat ((mp - 1) * idl))%nat -> 0 <= nth j (updn TM (Z.to_nat ((m - 1) * idl + c)) dp) 0 < 4096).
{ intros j Hj. rewrite nth_updn. destruct (_ && _); [lia|]. apply H9. exact Hj. }
repeat split; try assumption; try lia; try (apply HTM2; assumption).
- rewrite updn_length; exact H4.
- apply Forall_updn; [exact H8 | lia].
Qed.
Definition st_reset (X : lzw_abs) (k : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA (repeat 0 (Z.to_nat (idl * idl))) (repeat 0 4096) (repeat 0 4096) TM (k + 1) (lp + 2) (idl + 2) 1 (Cn + 1) (R + 1).
Lemma inv_reset : forall X k, inv X -> la_dp X = 4096 -> la_s X <= k < nP -> inv (st_reset X k).
Proof.
intros [TI LM LI TM s lp dp mp Cn R] k HI Hdp Hk. unfold inv, lzw_inv in *. cbn [st_reset la_dp la_s] in *.
destruct HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
rewrite countA_repeat0.
repeat split; try assumption; try lia; try (apply repeat_length); try (apply Forall_repeat_Z; lia).
Qed.
End a.
Definition lzw_init (idl : Z) (TM : list Z) : lzw_abs :=
mkLA (repeat 0 (Z.to_nat (idl * idl))) (repeat 0 4096) (repeat 0 4096) TM 0 1 (idl + 2) 1 0 0.
Lemma inv_init : forall idl nP TM, 2 <= idl <= 256 -> 1 <= nP ->
length TM = Z.to_nat (2049 * idl) -> u16s TM -> lzw_inv idl nP (lzw_init idl TM).
Proof.
intros idl nP TM Hidl HnP Hlen Hu. unfold lzw_inv, lzw_init.
rewrite countA_repeat0.
repeat split; try assumption; try lia; try (apply repeat_length); try (apply Forall_repeat_Z; lia).
Qed.
