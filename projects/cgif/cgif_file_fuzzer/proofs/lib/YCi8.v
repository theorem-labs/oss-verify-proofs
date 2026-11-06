(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07 YI0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section b.
Variable DEC : Z -> Z -> bool.
Variable tv : Z.
Definition trfa (ox oy : option Z) : option Z :=
match ox, oy with
| Some x, Some y => Some (if DEC x y then x else tv mod 256)
| _, _ => ox
end.
Definition tinB (rdc rdn : Z -> option Z) (pt npt p bimg idx : Z) : Prop :=
forall a, pt <= a < pt + npt -> rdn a = if a =? p then trfa (rdc p) (rdc (bimg + idx)) else rdc a.
Definition tinV (rdc rd' : Z -> option Z) (pt npt p c bimg idx : Z) : Prop :=
forall a, pt <= a < pt + npt ->
rd' a = if (p <=? a) && (a <? p + c) then trfa (rdc a) (rdc (bimg + (idx + (a - p)))) else rdc a.
Lemma tinV_last : forall rdc rdn rd' pt npt p bimg idx,
tinB rdc rdn pt npt p bimg idx -> (forall a, pt <= a < pt + npt -> rd' a = rdn a) -> tinV rdc rd' pt npt p 1 bimg idx.
Proof.
intros rdc rdn rd' pt npt p bimg idx HB HK a Ha. rewrite (HK a Ha), (HB a Ha).
destruct (Z.eqb_spec a p) as [-> | Hne].
- replace ((p <=? p) && (p <? p + 1)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace (idx + (p - p)) with idx by lia. reflexivity.
- replace ((p <=? a) && (a <? p + 1)) with false; [reflexivity|].
symmetry. apply andb_false_iff. destruct (Z.leb_spec p a); [right; apply Z.ltb_ge; lia | left; reflexivity].
Qed.
Lemma tinV_step : forall rdc rdn rdm rd' pt npt p c bimg idx,
1 <= c - 1 -> tinB rdc rdn pt npt p bimg idx ->
(forall a, pt <= a < pt + npt -> rdm a = rdn a) ->
(forall j, 0 <= j < c -> rdm (bimg + (idx + j)) = rdc (bimg + (idx + j))) ->
tinV rdm rd' pt npt (p + 1) (c - 1) bimg (idx + 1) -> tinV rdc rd' pt npt p c bimg idx.
Proof.
intros rdc rdn rdm rd' pt npt p c bimg idx Hc HB HK HI HV a Ha. rewrite (HV a Ha).
destruct (Z.eqb_spec a p) as [-> | Hne].
- replace ((p + 1 <=? p) && (p <? p + 1 + (c - 1))) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
replace ((p <=? p) && (p <? p + c)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
rewrite (HK p Ha), (HB p Ha), Z.eqb_refl. replace (idx + (p - p)) with idx by lia. reflexivity.
- destruct (Z.lt_ge_cases a p) as [Hlo | Hlo].
+ replace ((p + 1 <=? a) && (a <? p + 1 + (c - 1))) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
replace ((p <=? a) && (a <? p + c)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
rewrite (HK a Ha), (HB a Ha). replace (a =? p) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
+ destruct (Z.lt_ge_cases a (p + c)) as [Hhi | Hhi].
* replace ((p + 1 <=? a) && (a <? p + 1 + (c - 1))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace ((p <=? a) && (a <? p + c)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
rewrite (HK a Ha), (HB a Ha). replace (a =? p) with false by (symmetry; apply Z.eqb_neq; exact Hne).
replace (idx + 1 + (a - (p + 1))) with (idx + (a - p)) by lia. rewrite (HI (a - p) ltac:(lia)). reflexivity.
* replace ((p + 1 <=? a) && (a <? p + 1 + (c - 1))) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
replace ((p <=? a) && (a <? p + c)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
rewrite (HK a Ha), (HB a Ha). replace (a =? p) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
Qed.
Lemma tinV_pre : forall rdc rdi rd' pt npt p c bimg idx,
(forall a, pt <= a < pt + npt -> rdi a = rdc a) ->
(forall j, 0 <= j < c -> rdi (bimg + (idx + j)) = rdc (bimg + (idx + j))) ->
tinV rdi rd' pt npt p c bimg idx -> tinV rdc rd' pt npt p c bimg idx.
Proof.
intros rdc rdi rd' pt npt p c bimg idx HK HI HV a Ha. rewrite (HV a Ha), (HK a Ha).
destruct ((p <=? a) && (a <? p + c)) eqn:Ec; [|reflexivity].
apply andb_true_iff in Ec. destruct Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
rewrite (HI (a - p) ltac:(lia)). reflexivity.
Qed.
Lemma tinV_post : forall rdc rd1 rd' pt npt p c bimg idx,
(forall a, pt <= a < pt + npt -> rd' a = rd1 a) -> tinV rdc rd1 pt npt p c bimg idx -> tinV rdc rd' pt npt p c bimg idx.
Proof. intros rdc rd1 rd' pt npt p c bimg idx HK HV a Ha. rewrite (HK a Ha). exact (HV a Ha). Qed.
Section d.
Variables (w h top left Wd : Z).
Hypothesis Hw : 1 <= w.
Definition BOF (k : Z) : Z := (top + k / w) * Wd + left + k mod w.
Lemma BOF_row : forall y c, 0 <= c < w -> BOF (y * w + c) = (top + y) * Wd + left + c.
Proof.
intros y c Hc. unfold BOF. rewrite (Z.add_comm (y * w) c), Z.div_add, Z.mod_add, (Z.div_small c w), (Z.mod_small c w) by lia. f_equal; lia.
Qed.
Definition toutV (rdc rd' : Z -> option Z) (pt bimg y : Z) : Prop :=
forall a, pt <= a < pt + w * h ->
rd' a = if (pt + y * w <=? a) && (a <? pt + h * w) then trfa (rdc a) (rdc (bimg + BOF (a - pt))) else rdc a.
Lemma toutV_last : forall rdc rd1 pt bimg y, y + 1 = h -> 0 <= y ->
tinV rdc rd1 pt (w * h) (pt + y * w) w bimg ((top + y) * Wd + left) -> toutV rdc rd1 pt bimg y.
Proof.
intros rdc rd1 pt bimg y Hy Hy0 HV a Ha. rewrite (HV a Ha).
replace (pt + h * w) with (pt + y * w + w) by (rewrite <- Hy; lia).
destruct ((pt + y * w <=? a) && (a <? pt + y * w + w)) eqn:Ec; [|reflexivity].
apply andb_true_iff in Ec. destruct Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
replace (a - pt) with (y * w + (a - (pt + y * w))) by lia. rewrite BOF_row by lia.
replace ((top + y) * Wd + left + (a - (pt + y * w))) with ((top + y) * Wd + left + (a - (pt + y * w))) by lia. reflexivity.
Qed.
Lemma toutV_step : forall rdc rd1 rd3 rd' pt bimg y Nb, 0 <= y -> y + 1 < h ->
0 <= top -> 0 <= left -> left + w <= Wd -> (top + h) * Wd <= Nb ->
tinV rdc rd1 pt (w * h) (pt + y * w) w bimg ((top + y) * Wd + left) ->
(forall a, pt <= a < pt + w * h -> rd3 a = rd1 a) ->
(forall j, 0 <= j < Nb -> rd3 (bimg + j) = rdc (bimg + j)) ->
toutV rd3 rd' pt bimg (y + 1) -> toutV rdc rd' pt bimg y.
Proof.
intros rdc rd1 rd3 rd' pt bimg y Nb Hy0 Hy Ht0 Hl0 Hlw HNb HV HK HI HIH a Ha. rewrite (HIH a Ha).
assert (Hrw : (y + 1) * w <= h * w) by nia.
assert (Hm1 : rd3 a = rd1 a) by exact (HK a Ha). specialize (HV a Ha).
destruct (Z.lt_ge_cases a (pt + y * w)) as [Hlo | Hlo].
- replace (pt + (y + 1) * w <=? a) with false by (symmetry; apply Z.leb_gt; nia).
replace (pt + y * w <=? a) with false by (symmetry; apply Z.leb_gt; exact Hlo). cbn [andb].
replace (pt + y * w <=? a) with false in HV by (symmetry; apply Z.leb_gt; exact Hlo). cbn [andb] in HV.
rewrite Hm1, HV. reflexivity.
- replace (pt + y * w <=? a) with true by (symmetry; apply Z.leb_le; exact Hlo).
replace (pt + y * w <=? a) with true in HV by (symmetry; apply Z.leb_le; exact Hlo). cbn [andb] in HV |- *.
destruct (Z.lt_ge_cases a (pt + y * w + w)) as [Hrow | Hrow].
+ replace (pt + (y + 1) * w <=? a) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
replace (a <? pt + y * w + w) with true in HV by (symmetry; apply Z.ltb_lt; exact Hrow).
replace (a <? pt + h * w) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Hm1, HV. replace (a - pt) with (y * w + (a - (pt + y * w))) by lia. rewrite BOF_row by lia. reflexivity.
+ replace (pt + (y + 1) * w <=? a) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
replace (a <? pt + y * w + w) with false in HV by (symmetry; apply Z.ltb_ge; exact Hrow).
destruct (a <? pt + h * w) eqn:Eh; [|rewrite Hm1, HV; reflexivity].
apply Z.ltb_lt in Eh. rewrite Hm1, HV.
assert (Hk : 0 <= a - pt < w * h) by lia.
assert (Hkw : 0 <= (a - pt) / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= (a - pt) mod w < w) by (apply Z.mod_pos_bound; lia).
rewrite (HI (BOF (a - pt))); [reflexivity|]. unfold BOF. nia.
Qed.
End d.
End b.
Lemma window_specZ : forall (Wd Hd : Z) (img : list Z) (w h top lf : Z),
0 < Wd -> 0 <= Hd -> Z.of_nat (length img) = Wd * Hd ->
1 <= w -> 0 <= lf -> lf + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd ->
length (YO07.window Wd img w h top lf) = Z.to_nat (w * h) /\
forall k, 0 <= k < w * h -> nth (Z.to_nat k) (YO07.window Wd img w h top lf) 0 = nth (Z.to_nat ((top + k / w) * Wd + lf + k mod w)) img 0.
Proof.
intros Wd Hd img w h top lf HWd HHd Hlen Hw Hl0 Hlw Hh Ht0 Hth.
set (W := Z.to_nat Wd). set (HH := Z.to_nat Hd).
assert (HW : (0 < W)%nat) by (subst W; lia).
assert (Hlen' : length img = (W * HH)%nat) by (subst W HH; nia).
unfold YO07.window. fold W.
destruct (YI0d.rows_of_spec HH W img (S (length img)) HW Hlen' ltac:(rewrite Hlen'; nia)) as [RL RN].
set (rows := YO07.rows_of (S (length img)) W img) in *.
assert (BL : length (firstn (Z.to_nat h) (skipn (Z.to_nat top) rows)) = Z.to_nat h).
{ rewrite length_firstn, length_skipn, RL. subst HH. lia. }
assert (BN : forall i, (i < Z.to_nat h)%nat -> nth i (firstn (Z.to_nat h) (skipn (Z.to_nat top) rows)) [] = firstn W (skipn ((Z.to_nat top + i) * W) img)).
{ intros i Hi. rewrite nth_firstn. replace (i <? Z.to_nat h)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
rewrite nth_skipn. apply RN. subst HH. lia. }
assert (GEN : forall (band : list (list Z)) n, length band = n -> (forall i, (i < n)%nat -> length (nth i band []) >= Z.to_nat lf + Z.to_nat w)%nat ->
length (flat_map (fun r => firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) band) = (n * Z.to_nat w)%nat /\
forall i c, (i < n)%nat -> (c < Z.to_nat w)%nat ->
nth (i * Z.to_nat w + c) (flat_map (fun r => firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) band) 0 = nth (Z.to_nat lf + c) (nth i band []) 0).
{ clear. intros band. induction band as [|r band IH]; intros n Hn Hl.
- subst n. split; [reflexivity | intros i c Hi; cbn in Hi; lia].
- destruct n as [|n]; [discriminate Hn|]. injection Hn as Hn.
destruct (IH n Hn ltac:(intros i Hi; apply (Hl (S i)); lia)) as [L1 N1].
assert (Lr : length (firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) = Z.to_nat w).
{ rewrite length_firstn, length_skipn. specialize (Hl 0%nat ltac:(lia)). cbn [nth] in Hl. lia. }
cbn [flat_map]. split; [rewrite length_app, L1, Lr; lia|].
intros [|i] c Hi Hc.
+ cbn [Nat.mul Nat.add nth]. rewrite app_nth1 by lia. rewrite nth_firstn. replace (c <? Z.to_nat w)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hc). apply nth_skipn.
+ rewrite app_nth2 by (rewrite Lr; nia). rewrite Lr. replace (S i * Z.to_nat w + c - Z.to_nat w)%nat with (i * Z.to_nat w + c)%nat by nia.
cbn [nth]. apply N1; lia. }
destruct (GEN _ (Z.to_nat h) BL) as [L N].
{ intros i Hi. rewrite BN by exact Hi. rewrite length_firstn, length_skipn, Hlen'. subst W HH. nia. }
split; [rewrite L; nia|].
intros k Hk.
assert (Hkw : 0 <= k / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= k mod w < w) by (apply Z.mod_pos_bound; lia).
pose proof (Z.div_mod k w ltac:(lia)) as Hdm.
replace (Z.to_nat k) with (Z.to_nat (k / w) * Z.to_nat w + Z.to_nat (k mod w))%nat by nia.
rewrite N by nia. rewrite BN by nia. rewrite YI0d.nth_firstn_skipn by (subst W; nia).
f_equal. subst W. nia.
Qed.
