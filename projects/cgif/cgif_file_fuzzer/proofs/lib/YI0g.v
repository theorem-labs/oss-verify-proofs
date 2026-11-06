(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI00 YI01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a.
Definition rowN (w : nat) (img : list Z) (r : nat) : list Z := firstn w (skipn (w * r) img).
Fixpoint ipassN (w : nat) (img : list Z) (s t m : nat) : list Z :=
match m with O => [] | S m' => rowN w img s ++ ipassN w img (s + t) t m' end.
Lemma rows_of_rows : forall h fuel w img, length img = (w * h)%nat -> (0 < w)%nat -> (h < fuel)%nat ->
YO07.rows_of fuel w img = map (rowN w img) (seq 0 h).
Proof.
induction h as [|h IH]; intros fuel w img Hl Hw Hf.
- rewrite Nat.mul_0_r in Hl. destruct img; [|discriminate Hl]. destruct fuel; reflexivity.
- destruct fuel as [|f]; [lia|]. cbn [YO07.rows_of].
destruct img as [|x l] eqn:Himg; [cbn in Hl; lia|]. rewrite <- Himg in *. clear Himg x l.
cbn [seq map]. rewrite <- seq_shift, map_map. f_equal.
+ unfold rowN. rewrite Nat.mul_0_r. reflexivity.
+ rewrite (IH f w (skipn w img)); [| rewrite length_skipn, Hl; lia | exact Hw | lia].
apply map_ext. intros r. unfold rowN. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.
Lemma pick_rows_shift : forall rows i s t, (0 < t)%nat -> (s < i)%nat ->
YO07.pick_rows rows i s t = YO07.pick_rows rows i (s + t) t.
Proof.
induction rows as [|r rs IH]; intros i s t Ht Hs; [reflexivity|]. cbn [YO07.pick_rows].
rewrite (IH (S i) s t Ht ltac:(lia)). f_equal.
destruct (Nat.le_gt_cases (s + t) i) as [Hge | Hlt].
- replace (s <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia).
replace (s + t <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia).
replace (i - s)%nat with ((i - (s + t)) + t)%nat by lia. rewrite Nat.Div0.add_mod, Nat.Div0.mod_same, Nat.add_0_r, Nat.Div0.mod_mod. reflexivity.
- replace (s + t <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia).
replace (s <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
rewrite (Nat.mod_small (i - s) t) by lia. replace (i - s =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
Definition mrowsN (s t e m : nat) : Prop := (m = 0 /\ e <= s)%nat \/ (0 < m /\ s + t * m - t < e /\ e <= s + t * m)%nat.
Fixpoint ipassF (F : nat -> list Z) (s t m : nat) : list Z :=
match m with O => [] | S m' => F s ++ ipassF F (s + t) t m' end.
Lemma ipassN_F : forall w img s t m, ipassN w img s t m = ipassF (rowN w img) s t m.
Proof. intros w img s t m. revert s. induction m as [|m IH]; intros s; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma pick_rows_ipass : forall n i s t m (F : nat -> list Z), (0 < t)%nat -> (i <= s)%nat -> mrowsN s t (i + n) m ->
YO07.pick_rows (map F (seq i n)) i s t = ipassF F s t m.
Proof.
induction n as [|n IH]; intros i s t m F Ht His Hm.
- destruct Hm as [[-> _] | (H1 & H2 & H3)]; [reflexivity | exfalso; nia].
- cbn [seq map YO07.pick_rows].
destruct (Nat.eq_dec i s) as [-> | Hne].
+ rewrite Nat.leb_refl, Nat.sub_diag. rewrite Nat.Div0.mod_0_l. cbn [Nat.eqb andb].
destruct m as [|m']; [exfalso; destruct Hm as [[_ H] | (H & _)]; lia|]. cbn [ipassF]. f_equal.
rewrite (pick_rows_shift _ (S s) s t Ht ltac:(lia)).
apply IH; [exact Ht | lia |].
destruct Hm as [[H _] | (H1 & H2 & H3)]; [lia|].
destruct m' as [|m'']; [left; split; [reflexivity | nia] | right; nia].
+ replace (s <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia). cbn [andb app].
apply IH; [exact Ht | lia |]. destruct Hm as [[H H'] | (H1 & H2 & H3)]; [left; split; lia | right; repeat split; lia].
Qed.
Theorem interlace_passes : forall w h img m1 m2 m3 m4,
(0 < w)%nat -> length img = (w * h)%nat ->
mrowsN 0 8 h m1 -> mrowsN 4 8 h m2 -> mrowsN 2 4 h m3 -> mrowsN 1 2 h m4 ->
YO07.interlace (Z.of_nat w) img = ipassN w img 0 8 m1 ++ ipassN w img 4 8 m2 ++ ipassN w img 2 4 m3 ++ ipassN w img 1 2 m4.
Proof.
intros w h img m1 m2 m3 m4 Hw Hl H1 H2 H3 H4. unfold YO07.interlace. rewrite Nat2Z.id.
rewrite (rows_of_rows h (S (length img)) w img Hl Hw) by (rewrite Hl; nia).
rewrite !ipassN_F.
rewrite (pick_rows_ipass h 0 0 8 m1) by first [lia | exact H1]. rewrite (pick_rows_ipass h 0 4 8 m2) by first [lia | exact H2].
rewrite (pick_rows_ipass h 0 2 4 m3) by first [lia | exact H3]. rewrite (pick_rows_ipass h 0 1 2 m4) by first [lia | exact H4]. reflexivity.
Qed.
Lemma rowN_length : forall w img r, (w * r + w <= length img)%nat -> length (rowN w img r) = w.
Proof. intros w img r H. unfold rowN. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.
Lemma ipassN_length : forall w img s t m, (0 < m -> w * (s + t * (m - 1)) + w <= length img)%nat -> length (ipassN w img s t m) = (w * m)%nat.
Proof.
intros w img s t m. revert s. induction m as [|m IH]; intros s H; [cbn; lia|].
cbn [ipassN]. rewrite length_app, rowN_length by nia. rewrite IH by (intros Hm; nia). lia.
Qed.
Lemma rowN_nth : forall w img r k d, (k < w)%nat -> nth k (rowN w img r) d = nth (w * r + k) img d.
Proof.
intros w img r k d Hk. unfold rowN. rewrite nth_firstn. replace (k <? w)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
rewrite nth_skipn. reflexivity.
Qed.
Lemma ipassN_nth : forall w img s t m j k d, (j < m)%nat -> (k < w)%nat -> (w * (s + t * (m - 1)) + w <= length img)%nat ->
nth (w * j + k) (ipassN w img s t m) d = nth (w * (s + t * j) + k) img d.
Proof.
intros w img s t m. revert s. induction m as [|m IH]; intros s j k d Hj Hk Hl; [lia|].
cbn [ipassN]. destruct j as [|j].
- rewrite app_nth1 by (rewrite rowN_length by nia; lia).
rewrite !Nat.mul_0_r, !Nat.add_0_r. cbn [Nat.add]. apply rowN_nth. exact Hk.
- rewrite app_nth2 by (rewrite rowN_length by nia; nia). rewrite rowN_length by nia.
replace (w * S j + k - w)%nat with (w * j + k)%nat by nia. rewrite (IH (s + t)%nat j k d) by first [lia | nia]. f_equal. nia.
Qed.
Lemma mrows_sum : forall h m1 m2 m3 m4, mrowsN 0 8 h m1 -> mrowsN 4 8 h m2 -> mrowsN 2 4 h m3 -> mrowsN 1 2 h m4 -> (m1 + m2 + m3 + m4 = h)%nat.
Proof.
intros h m1 m2 m3 m4 H1 H2 H3 H4. unfold mrowsN in *.
pose proof (Nat.div_mod_eq h 8) as Hd. pose proof (Nat.mod_upper_bound h 8 ltac:(lia)) as Hr.
set (q := (h / 8)%nat) in *. set (r := (h mod 8)%nat) in *.
assert (Hc : (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7)%nat) by lia.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]]; lia.
Qed.
Lemma interlace_length : forall w h img m1 m2 m3 m4,
(0 < w)%nat -> length img = (w * h)%nat ->
mrowsN 0 8 h m1 -> mrowsN 4 8 h m2 -> mrowsN 2 4 h m3 -> mrowsN 1 2 h m4 ->
length (YO07.interlace (Z.of_nat w) img) = length img.
Proof.
intros w h img m1 m2 m3 m4 Hw Hl H1 H2 H3 H4.
rewrite (interlace_passes w h img m1 m2 m3 m4 Hw Hl H1 H2 H3 H4), !length_app.
pose proof (mrows_sum h m1 m2 m3 m4 H1 H2 H3 H4) as Hs. unfold mrowsN in *.
rewrite !ipassN_length by (intros; rewrite Hl; nia). nia.
Qed.
End a.
Definition ipassZ (img : list Z) (w s t m : Z) : list Z := ipassN (Z.to_nat w) img (Z.to_nat s) (Z.to_nat t) (Z.to_nat m).
Definition mrows (s t e m : Z) : Prop := (m = 0 /\ e <= s) \/ (0 < m /\ s + t * (m - 1) < e <= s + t * m).
Lemma mrows_N : forall s t e m, 0 <= s -> 0 <= t -> 0 <= e -> 0 <= m -> mrows s t e m -> mrowsN (Z.to_nat s) (Z.to_nat t) (Z.to_nat e) (Z.to_nat m).
Proof.
intros s t e m Hs Ht He Hm [[-> H] | (H1 & H2 & H3)]; [left; split; [reflexivity | apply Z2Nat.inj_le; lia] | right].
repeat split; try lia.
apply Nat2Z.inj_lt. rewrite Nat2Z.inj_sub by nia. rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, !Z2Nat.id by lia. nia.
Qed.
Section b.
Variable segs : list Segment.
Lemma ipassZ_length : forall img w h s t m, Z.of_nat (length img) = w * h -> 1 <= w -> 0 <= s -> 1 <= t -> 0 <= m ->
(0 < m -> s + t * (m - 1) < h) -> Z.of_nat (length (ipassZ img w s t m)) = w * m.
Proof.
intros img w h s t m Hl Hw Hs Ht Hm Hin. unfold ipassZ. rewrite ipassN_length; [nia|].
intros H0. apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_sub, !Z2Nat.id by lia. cbn [Z.of_nat]. nia.
Qed.
Lemma garr8_ipass : forall (memc mem' : word -> option byte) (img pint : Z) (IMGV : list Z) (w h s t m R : Z),
garr8 segs memc img IMGV -> Z.of_nat (length IMGV) = w * h -> 1 <= w -> 0 <= s -> 1 <= t -> 0 <= m -> 0 <= R ->
(0 < m -> s + t * (m - 1) < h) ->
(forall j k, 0 <= j < m -> 0 <= k < w -> mbyte segs mem' (pint + w * (R + j) + k) = mbyte segs memc (img + w * (s + t * j) + k)) ->
garr8 segs mem' (pint + w * R) (ipassZ IMGV w s t m).
Proof.
intros memc mem' img pint IMGV w h s t m R HG Hl Hw Hs Ht Hm HR Hin Hcp.
pose proof (ipassZ_length IMGV w h s t m Hl Hw Hs Ht Hm Hin) as HL.
apply garr8_intro. intros jj Hjj.
pose proof (Z.div_mod (Z.of_nat jj) w ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (Z.of_nat jj) w ltac:(lia)) as Hmb.
set (j := Z.of_nat jj / w) in *. set (k := Z.of_nat jj mod w) in *.
assert (Hj : 0 <= j < m) by (subst j; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
replace (pint + w * R + Z.of_nat jj) with (pint + w * (R + j) + k) by lia. rewrite (Hcp j k Hj Hmb).
assert (Hidx : (Z.to_nat (w * (s + t * j) + k) < length IMGV)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by nia; nia).
pose proof (garr8_mbyte segs memc img IMGV (Z.to_nat (w * (s + t * j) + k)) HG Hidx) as Hb. rewrite Z2Nat.id in Hb by nia.
replace (nth jj (ipassZ IMGV w s t m) 0) with (nth (Z.to_nat (w * (s + t * j) + k)) IMGV 0).
{ replace (img + w * (s + t * j) + k) with (img + (w * (s + t * j) + k)) by lia. split; [exact Hb | exact (proj2 (HG _ Hidx))]. }
unfold ipassZ. replace jj with (Z.to_nat w * Z.to_nat j + Z.to_nat k)%nat by lia.
rewrite ipassN_nth; [f_equal; lia | lia | lia |].
apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_sub, !Z2Nat.id by lia. cbn [Z.of_nat]. nia.
Qed.
End b.
