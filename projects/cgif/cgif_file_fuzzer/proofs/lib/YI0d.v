(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma first_true_none : forall l i, first_true l i = None <-> (forall j, (j < length l)%nat -> nth j l false = false).
Proof.
induction l as [|b t IH]; intros i; cbn [first_true length].
- split; [intros _ j Hj; lia | reflexivity].
- destruct b.
+ split; [discriminate | intros H; specialize (H 0%nat ltac:(lia)); discriminate H].
+ rewrite IH. split; intros H j Hj; [destruct j as [|j]; [reflexivity | apply H; lia] | apply (H (S j)); lia].
Qed.
Lemma first_true_some : forall l i k, first_true l i = Some k <->
(i <= k /\ (Z.to_nat (k - i) < length l)%nat /\ nth (Z.to_nat (k - i)) l false = true /\ forall j, (j < Z.to_nat (k - i))%nat -> nth j l false = false).
Proof.
induction l as [|b t IH]; intros i k; cbn [first_true length].
- split; [discriminate | intros (_ & H & _); lia].
- destruct b.
+ split.
* intros E. injection E as <-. rewrite Z.sub_diag. cbn. repeat split; try lia.
* intros (H1 & H2 & H3 & H4). destruct (Z.to_nat (k - i)) as [|n] eqn:E; [f_equal; lia|]. specialize (H4 0%nat ltac:(lia)). discriminate H4.
+ rewrite IH. split.
* intros (H1 & H2 & H3 & H4). replace (Z.to_nat (k - i)) with (S (Z.to_nat (k - (i + 1)))) by lia. cbn [nth].
repeat split; try lia; [exact H3|]. intros [|j] Hj; [reflexivity | apply H4; lia].
* intros (H1 & H2 & H3 & H4). destruct (Z.to_nat (k - i)) as [|n] eqn:E; [cbn in H3; discriminate H3|].
replace (Z.to_nat (k - (i + 1))) with n by lia. cbn [nth] in H3. repeat split; try lia; [exact H3|]. intros j Hj. apply (H4 (S j)). lia.
Qed.
Lemma last_true_spec : forall l i acc r, last_true l i acc = r ->
(r = acc /\ forall j, (j < length l)%nat -> nth j l false = false) \/
(exists k, r = Some k /\ i <= k /\ (Z.to_nat (k - i) < length l)%nat /\ nth (Z.to_nat (k - i)) l false = true /\
forall j, (Z.to_nat (k - i) < j < length l)%nat -> nth j l false = false).
Proof.
induction l as [|b t IH]; intros i acc r H; cbn [last_true length] in *.
- left. split; [symmetry; exact H | intros j Hj; lia].
- destruct (IH (i + 1) (if b then Some i else acc) r H) as [[E1 E2] | (k & E1 & E2 & E3 & E4 & E5)].
+ destruct b.
* right. exists i. rewrite Z.sub_diag. cbn. repeat split; try lia; [exact E1|]. intros [|j] Hj; [lia | apply E2; lia].
* left. split; [exact E1|]. intros [|j] Hj; [reflexivity | apply E2; lia].
+ right. exists k. replace (Z.to_nat (k - i)) with (S (Z.to_nat (k - (i + 1)))) by lia. cbn [nth].
repeat split; try lia; [exact E1 | exact E4|]. intros [|j] Hj; [lia | apply E5; lia].
Qed.
Lemma rows_of_spec : forall h w l fuel, (0 < w)%nat -> length l = (w * h)%nat -> (h < fuel)%nat ->
length (rows_of fuel w l) = h /\ forall i, (i < h)%nat -> nth i (rows_of fuel w l) [] = firstn w (skipn (i * w) l).
Proof.
induction h as [|h IH]; intros w l fuel Hw Hl Hf; (destruct fuel as [|f]; [lia|]).
- destruct l; [|cbn in Hl; lia]. cbn. split; [reflexivity | intros i Hi; lia].
- destruct l as [|x0 l0]; [cbn in Hl; lia|]. cbn [rows_of]. set (l := x0 :: l0) in *.
destruct (IH w (skipn w l) f Hw ltac:(rewrite length_skipn; lia) ltac:(lia)) as [IH1 IH2].
split; [cbn [length]; rewrite IH1; reflexivity|].
intros [|i] Hi; [reflexivity|]. cbn [nth]. rewrite IH2 by lia. rewrite skipn_skipn. do 2 f_equal. lia.
Qed.
Lemma nth_firstn_skipn : forall (l : list Z) a w x, (x < w)%nat -> nth x (firstn w (skipn a l)) 0 = nth (a + x) l 0.
Proof. intros l a w x Hx. rewrite nth_firstn. replace (x <? w)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hx). apply nth_skipn. Qed.
Lemma band_min_spec : forall (band : list (list bool)) res,
fold_right (fun r acc => omin (first_true r 0) acc) None band = res ->
match res with
| None => forall row, In row band -> forall j, (j < length row)%nat -> nth j row false = false
| Some m => 0 <= m /\ (exists row, In row band /\ (Z.to_nat m < length row)%nat /\ nth (Z.to_nat m) row false = true) /\
forall row, In row band -> forall j, (j < Z.to_nat m)%nat -> (j < length row)%nat -> nth j row false = false
end.
Proof.
induction band as [|r band IH]; intros res Hres; cbn [fold_right] in Hres.
- subst res. intros row [].
- set (acc := fold_right (fun r acc => omin (first_true r 0) acc) None band) in *. specialize (IH acc eq_refl).
destruct (first_true r 0) as [k|] eqn:Ek.
+ apply first_true_some in Ek as (K0 & K1 & K2 & K3). rewrite Z.sub_0_r in K1, K2, K3.
destruct acc as [a|]; cbn [omin] in Hres; subst res.
* destruct IH as (A0 & (rowa & Ina & La & Ta) & Fa). split; [lia|]. split.
-- destruct (Z.le_ge_cases k a); [rewrite Z.min_l by lia; exists r; split; [left; reflexivity | split; assumption]
| rewrite Z.min_r by lia; exists rowa; split; [right; exact Ina | split; assumption]].
-- intros row [<- | Hin] j Hj Hjl; [apply K3; lia | apply (Fa row Hin j); lia].
* split; [lia|]. split; [exists r; split; [left; reflexivity | split; assumption]|].
intros row [<- | Hin] j Hj Hjl; [apply K3; lia | apply (IH row Hin j Hjl)].
+ pose proof (proj1 (first_true_none r 0) Ek) as K.
destruct acc as [a|]; cbn [omin] in Hres; subst res.
* destruct IH as (A0 & (rowa & Ina & La & Ta) & Fa). split; [lia|]. split; [exists rowa; split; [right; exact Ina | split; assumption]|].
intros row [<- | Hin] j Hj Hjl; [apply K; exact Hjl | apply (Fa row Hin j Hj Hjl)].
* intros row [<- | Hin] j Hjl; [apply K; exact Hjl | apply (IH row Hin j Hjl)].
Qed.
Lemma band_max_spec : forall (band : list (list bool)) res,
fold_right (fun r acc => omax (last_true r 0 None) acc) None band = res ->
match res with
| None => forall row, In row band -> forall j, (j < length row)%nat -> nth j row false = false
| Some m => 0 <= m /\ (exists row, In row band /\ (Z.to_nat m < length row)%nat /\ nth (Z.to_nat m) row false = true) /\
forall row, In row band -> forall j, (Z.to_nat m < j < length row)%nat -> nth j row false = false
end.
Proof.
induction band as [|r band IH]; intros res Hres; cbn [fold_right] in Hres.
- subst res. intros row [].
- set (acc := fold_right (fun r acc => omax (last_true r 0 None) acc) None band) in *. specialize (IH acc eq_refl).
destruct (last_true_spec r 0 None _ eq_refl) as [[E1 K] | (k & E1 & K0 & K1 & K2 & K3)]; rewrite E1 in Hres; rewrite ?Z.sub_0_r in *.
+ destruct acc as [a|]; cbn [omax] in Hres; subst res.
* destruct IH as (A0 & (rowa & Ina & La & Ta) & Fa). split; [lia|]. split; [exists rowa; split; [right; exact Ina | split; assumption]|].
intros row [<- | Hin] j Hj; [apply K; lia | apply (Fa row Hin j Hj)].
* intros row [<- | Hin] j Hjl; [apply K; exact Hjl | apply (IH row Hin j Hjl)].
+ destruct acc as [a|]; cbn [omax] in Hres; subst res.
* destruct IH as (A0 & (rowa & Ina & La & Ta) & Fa). split; [lia|]. split.
-- destruct (Z.le_ge_cases k a); [rewrite Z.max_r by lia; exists rowa; split; [right; exact Ina | split; assumption]
| rewrite Z.max_l by lia; exists r; split; [left; reflexivity | split; assumption]].
-- intros row [<- | Hin] j Hj; [apply K3; lia | apply (Fa row Hin j); lia].
* split; [lia|]. split; [exists r; split; [left; reflexivity | split; assumption]|].
intros row [<- | Hin] j Hj; [apply K3; lia | apply (IH row Hin j); lia].
Qed.
Section c.
Variables (g : gcfg) (cur bef : frame) (H : nat).
Let W := Z.to_nat (g_w g).
Hypothesis HW : (0 < W)%nat.
Hypothesis LenC : length (f_img cur) = (W * H)%nat.
Hypothesis LenB : length (f_img bef) = (W * H)%nat.
Definition dpx (i x : nat) : bool := px_ne g cur bef (nth (i * W + x) (f_img cur) 0) (nth (i * W + x) (f_img bef) 0).
Let dm := map (fun rb => map (fun p => px_ne g cur bef (fst p) (snd p)) (combine (fst rb) (snd rb)))
(combine (rows_of (S (length (f_img cur))) W (f_img cur)) (rows_of (S (length (f_img bef))) W (f_img bef))).
Lemma dm_length : length dm = H.
Proof.
subst dm. rewrite length_map, length_combine.
destruct (rows_of_spec H W (f_img cur) (S (length (f_img cur))) HW LenC ltac:(rewrite LenC; nia)) as [E1 _].
destruct (rows_of_spec H W (f_img bef) (S (length (f_img bef))) HW LenB ltac:(rewrite LenB; nia)) as [E2 _].
rewrite E1, E2. lia.
Qed.
Lemma dm_row : forall i, (i < H)%nat -> length (nth i dm []) = W /\ forall x, (x < W)%nat -> nth x (nth i dm []) false = dpx i x.
Proof.
intros i Hi. subst dm.
destruct (rows_of_spec H W (f_img cur) (S (length (f_img cur))) HW LenC ltac:(rewrite LenC; nia)) as [E1 R1].
destruct (rows_of_spec H W (f_img bef) (S (length (f_img bef))) HW LenB ltac:(rewrite LenB; nia)) as [E2 R2].
set (f := fun rb : list Z * list Z => map (fun p => px_ne g cur bef (fst p) (snd p)) (combine (fst rb) (snd rb))).
change (@nil bool) with (f ([], [])). rewrite map_nth. rewrite combine_nth by lia. subst f. cbv beta. cbn [fst snd].
rewrite (R1 i Hi), (R2 i Hi).
assert (L1 : length (firstn W (skipn (i * W) (f_img cur))) = W) by (rewrite length_firstn, length_skipn, LenC; nia).
assert (L2 : length (firstn W (skipn (i * W) (f_img bef))) = W) by (rewrite length_firstn, length_skipn, LenB; nia).
split; [rewrite length_map, length_combine, L1, L2; lia|].
intros x Hx. set (h := fun p : Z * Z => px_ne g cur bef (fst p) (snd p)).
rewrite (nth_indep _ false (h (0, 0))) by (rewrite length_map, length_combine, L1, L2; lia).
rewrite map_nth, combine_nth by lia. subst h. cbv beta. cbn [fst snd]. rewrite !nth_firstn_skipn by exact Hx. reflexivity.
Qed.
Lemma rowany_nth : forall i, (i < H)%nat ->
(nth i (map (existsb (fun b : bool => b)) dm) false = true <-> exists x, (x < W)%nat /\ dpx i x = true).
Proof.
intros i Hi. change false with (existsb (fun b : bool => b) []) at 1. rewrite map_nth.
destruct (dm_row i Hi) as [L R]. rewrite existsb_exists. split.
- intros (b0 & Hin & ->). destruct (In_nth _ _ false Hin) as (x & Hx & Ex). exists x. rewrite L in Hx. split; [exact Hx|]. rewrite <- (R x Hx). exact Ex.
- intros (x & Hx & Ex). exists true. split; [|reflexivity]. rewrite <- Ex, <- (R x Hx). apply nth_In. rewrite L. exact Hx.
Qed.
Theorem diff_area_none : (forall i x, (i < H)%nat -> (x < W)%nat -> dpx i x = false) -> diff_area g cur bef = None.
Proof.
intros HD. unfold diff_area. cbv zeta. fold W. fold dm.
assert (E : first_true (map (existsb (fun b : bool => b)) dm) 0 = None).
{ apply first_true_none. intros j Hj. rewrite length_map, dm_length in Hj.
destruct (nth j (map (existsb (fun b : bool => b)) dm) false) eqn:Ej; [|reflexivity].
apply (rowany_nth j Hj) in Ej as (x & Hx & Ex). rewrite (HD j x Hj Hx) in Ex. discriminate Ex. }
rewrite E. reflexivity.
Qed.
Theorem diff_area_char : forall t b l r : nat, (t <= b < H)%nat -> (l <= r < W)%nat ->
(exists x, (x < W)%nat /\ dpx t x = true) -> (forall i x, (i < t)%nat -> (x < W)%nat -> dpx i x = false) ->
(exists x, (x < W)%nat /\ dpx b x = true) -> (forall i x, (b < i < H)%nat -> (x < W)%nat -> dpx i x = false) ->
(exists i, (t <= i <= b)%nat /\ dpx i l = true) -> (forall i x, (t <= i <= b)%nat -> (x < l)%nat -> dpx i x = false) ->
(exists i, (t <= i <= b)%nat /\ dpx i r = true) -> (forall i x, (t <= i <= b)%nat -> (r < x < W)%nat -> dpx i x = false) ->
diff_area g cur bef = Some (Z.of_nat r + 1 - Z.of_nat l, Z.of_nat b + 1 - Z.of_nat t, Z.of_nat t, Z.of_nat l).
Proof.
intros t b l r Htb Hlr Tt Ft Tb Fb Tl Fl Tr Fr. unfold diff_area. cbv zeta. fold W. fold dm.
set (rowany := map (existsb (fun b : bool => b)) dm).
assert (Lra : length rowany = H) by (subst rowany; rewrite length_map; apply dm_length).
assert (RN : forall i, (i < H)%nat -> (nth i rowany false = true <-> exists x, (x < W)%nat /\ dpx i x = true)) by exact rowany_nth.
assert (E1 : first_true rowany 0 = Some (Z.of_nat t)).
{ apply first_true_some. rewrite Z.sub_0_r, Nat2Z.id. split; [lia|]. split; [lia|]. split.
- apply (RN t ltac:(lia)). exact Tt.
- intros j Hj. destruct (nth j rowany false) eqn:Ej; [|reflexivity].
apply (RN j ltac:(lia)) in Ej as (x & Hx & Ex). rewrite (Ft j x Hj Hx) in Ex. discriminate Ex. }
assert (E2 : last_true rowany 0 None = Some (Z.of_nat b)).
{ destruct (last_true_spec rowany 0 None _ eq_refl) as [[_ K] | (k & Ek & K0 & K1 & K2 & K3)].
- specialize (K b ltac:(lia)). rewrite (proj2 (RN b ltac:(lia)) Tb) in K. discriminate K.
- rewrite Ek. f_equal. rewrite Z.sub_0_r in K1, K2, K3.
destruct (Nat.lt_trichotomy (Z.to_nat k) b) as [Hlt | [Heq | Hgt]]; [| lia |].
+ specialize (K3 b ltac:(lia)). rewrite (proj2 (RN b ltac:(lia)) Tb) in K3. discriminate K3.
+ apply (RN (Z.to_nat k) ltac:(lia)) in K2 as (x & Hx & Ex). rewrite (Fb (Z.to_nat k) x ltac:(lia) Hx) in Ex. discriminate Ex. }
rewrite E1, E2.
replace (Z.to_nat (Z.of_nat b + 1 - Z.of_nat t)) with (b + 1 - t)%nat by lia. rewrite Nat2Z.id.
set (band := firstn (b + 1 - t) (skipn t dm)).
assert (Lb : length band = (b + 1 - t)%nat) by (subst band; rewrite length_firstn, length_skipn, dm_length; lia).
assert (Inb : forall row, In row band <-> exists i, (t <= i <= b)%nat /\ row = nth i dm []).
{ intros row. split.
- intros Hin. destruct (In_nth _ _ [] Hin) as (k & Hk & Ek). exists (t + k)%nat. split; [lia|].
subst band. rewrite nth_firstn in Ek. replace (k <? b + 1 - t)%nat with true in Ek by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn in Ek. symmetry. exact Ek.
- intros (i & Hi & ->). replace i with (t + (i - t))%nat by lia. rewrite <- nth_skipn.
assert (Hk : (i - t < b + 1 - t)%nat) by lia.
replace (nth (i - t) (skipn t dm) []) with (nth (i - t) band []).
+ apply nth_In. lia.
+ subst band. rewrite nth_firstn. replace (i - t <? b + 1 - t)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
assert (E3 : fold_right (fun r0 acc => omin (first_true r0 0) acc) None band = Some (Z.of_nat l)).
{ destruct Tl as (il & Hil & Dil). destruct (dm_row il ltac:(lia)) as [Lil Ril].
pose proof (band_min_spec band _ eq_refl) as SP.
destruct (fold_right (fun r0 acc => omin (first_true r0 0) acc) None band) as [m|].
- destruct SP as (M0 & (row & Hin & Lm & Tm) & Fm). f_equal.
apply Inb in Hin as (i & Hi & ->). destruct (dm_row i ltac:(lia)) as [Li Ri]. rewrite Li in Lm.
destruct (Nat.lt_trichotomy (Z.to_nat m) l) as [Hlt | [Heq | Hgt]]; [| lia |].
+ rewrite (Ri _ Lm), (Fl i (Z.to_nat m) Hi Hlt) in Tm. discriminate Tm.
+ specialize (Fm (nth il dm []) (proj2 (Inb _) (ex_intro _ il (conj Hil eq_refl))) l Hgt ltac:(lia)).
rewrite (Ril l ltac:(lia)), Dil in Fm. discriminate Fm.
- specialize (SP (nth il dm []) (proj2 (Inb _) (ex_intro _ il (conj Hil eq_refl))) l ltac:(lia)).
rewrite (Ril l ltac:(lia)), Dil in SP. discriminate SP. }
assert (E4 : fold_right (fun r0 acc => omax (last_true r0 0 None) acc) None band = Some (Z.of_nat r)).
{ destruct Tr as (ir & Hir & Dir). destruct (dm_row ir ltac:(lia)) as [Lir Rir].
pose proof (band_max_spec band _ eq_refl) as SP.
destruct (fold_right (fun r0 acc => omax (last_true r0 0 None) acc) None band) as [m|].
- destruct SP as (M0 & (row & Hin & Lm & Tm) & Fm). f_equal.
apply Inb in Hin as (i & Hi & ->). destruct (dm_row i ltac:(lia)) as [Li Ri]. rewrite Li in Lm.
destruct (Nat.lt_trichotomy (Z.to_nat m) r) as [Hlt | [Heq | Hgt]]; [| lia |].
+ specialize (Fm (nth ir dm []) (proj2 (Inb _) (ex_intro _ ir (conj Hir eq_refl))) r ltac:(lia)).
rewrite (Rir r ltac:(lia)), Dir in Fm. discriminate Fm.
+ rewrite (Ri _ Lm), (Fr i (Z.to_nat m) Hi ltac:(lia)) in Tm. discriminate Tm.
- specialize (SP (nth ir dm []) (proj2 (Inb _) (ex_intro _ ir (conj Hir eq_refl))) r ltac:(lia)).
rewrite (Rir r ltac:(lia)), Dir in SP. discriminate SP. }
rewrite E3, E4. reflexivity.
Qed.
End c.
