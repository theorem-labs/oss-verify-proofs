(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayDamage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma zsum_point : forall (x v : Z) lo n, lo <= x < lo + Z.of_nat n -> zsum (fun b => if b =? x then v else 0) lo n = v.
Proof.
  intros x v lo n Hx. rewrite (zsum_single (fun b => if b =? x then v else 0) lo n x); [rewrite Z.eqb_refl; reflexivity | exact Hx |].
  intros i Hi Ni. replace (i =? x) with false by (symmetry; apply Z.eqb_neq; exact Ni). reflexivity.
Qed.

Lemma zsum_point_out : forall (x v : Z) lo n, ~ (lo <= x < lo + Z.of_nat n) -> zsum (fun b => if b =? x then v else 0) lo n = 0.
Proof. intros x v lo n Hx. apply zsum_0. intros i Hi. replace (i =? x) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Definition sz (l : Z) : Z := 2 ^ (15 - l) - 1.

Lemma pow15_pos : forall l, l <= 15 -> 1 <= 2 ^ (15 - l).
Proof. intros. pose proof (Z.pow_pos_nonneg 2 (15 - l) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma sz_facts : forall l, 1 <= l <= 14 -> 1 <= sz l /\ sz l = 2 * sz (l + 1) + 1 /\ 2 ^ (15 - l) = 2 * 2 ^ (15 - (l + 1)).
Proof.
  intros l Hl. unfold sz. replace (15 - l) with (Z.succ (15 - (l + 1))) by lia. rewrite Z.pow_succ_r by lia.
  pose proof (pow15_pos (l + 1) ltac:(lia)). lia.
Qed.

Lemma find_spec : forall fuel (a : hist) bits u,
  u <= bits -> bits - u < Z.of_nat fuel -> a u <> 0 -> (forall l, u < l <= bits -> a l = 0) ->
  rep_find fuel a bits = u.
Proof.
  induction fuel as [|fuel IH]; intros a bits u Hu Hf Au Z0; [lia|]. cbn [rep_find].
  destruct (Z.eqb_spec (a bits) 0) as [E|NE].
  - assert (u <> bits) by (intros ->; exact (Au E)). apply IH; [lia|lia|exact Au|intros; apply Z0; lia].
  - destruct (Z.eq_dec u bits) as [->|N]; [reflexivity|]. exfalso. apply NE. apply Z0. lia.
Qed.


Definition rstep (a : hist) (u : Z) : hist := rep_step 15 a u.

Lemma rstep_get : forall a u b, 1 <= u <= 14 ->
  rstep a u b = (if b =? 15 then (if u =? 14 then a 15 + 1 else a 15 - 1)
                 else if b =? u then a u - 1 else if b =? u + 1 then a (u + 1) + 2 else a b).
Proof.
  intros a u b Hu. unfold rstep, rep_step.
  destruct (Z.eqb_spec b 15) as [->|N15].
  - replace (15 =? u) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec u 14) as [->|N14]; [change (15 =? 14 + 1) with true; cbn; lia|].
    replace (15 =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (Z.eqb_spec b u) as [->|Nu]; [reflexivity|].
    destruct (Z.eqb_spec b (u + 1)) as [->|Nu1]; [|reflexivity].
    replace (u + 1 =? 15) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Definition levels_ok (a : hist) : Prop := forall b, 0 <= a b /\ ((b < 1 \/ 15 < b) -> a b = 0).

Section Repair15.
Variable c1 : hist.
Variable nl : Z.
Variable K : Z.
Hypothesis C1OK : levels_ok c1.
Hypothesis C1T : zsum c1 1 15 = nl.
Hypothesis C1K : zsum (fun b => c1 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K.
Hypothesis C1C : K + 1 <= c1 15.
Hypothesis HK : 1 <= K.
Hypothesis Hnl : 2 <= nl <= 286.

Let C1N : forall b, 0 <= c1 b := fun b => proj1 (C1OK b).

Definition Rm (a : hist) (v : Z) : Z := zsum (fun l => a l * sz l) (v + 1) (Z.to_nat (14 - v)).
Definition Tc (v : Z) : Z := zsum (fun l => c1 l * sz l) (v + 1) (Z.to_nat (14 - v)).

Record RINV (t : Z) (a : hist) : Prop := {
  ri_ok : levels_ok a;
  ri_tot : zsum a 1 15 = nl;
  ri_kr : zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - t;
  ri_kc : K + 1 - t <= a 15;
  ri_prof : exists v tau, 1 <= v <= 14 /\ 1 <= tau <= c1 v /\ 0 <= Rm a v <= 2 ^ (15 - v) - 2 /\
            (forall b, 1 <= b < v -> a b = c1 b) /\ a v = c1 v - tau /\
            t = Tc v + tau * sz v - Rm a v /\ 2 ^ (15 - v) + 1 <= nl }.

Lemma level_le_tot : forall (a : hist) b, levels_ok a -> zsum a 1 15 = nl -> 1 <= b <= 15 -> a b <= nl.
Proof.
  intros a b OK T Hb. rewrite <- T. apply (zsum_ge_point a 1 15 b); [intros j Hj; apply (proj1 (OK j)) | lia].
Qed.

Lemma kraft_split : forall (a : hist) u, (forall b, 0 <= a b) -> 0 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) ->
  let Q := zsum (fun b => a b * 2 ^ (u - b)) 1 (Z.to_nat u) in
  0 <= Q /\ zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = Q * 2 ^ (15 - u) + a 15.
Proof.
  intros a u B Hu Z0 Q. split.
  { apply zsum_nonneg. intros b Hb. pose proof (B b). pose proof (Z.pow_nonneg 2 (u - b)). nia. }
  replace 15%nat with (Z.to_nat u + (Z.to_nat (14 - u) + 1))%nat at 1 by lia.
  rewrite zsum_split, zsum_split. change (zsum (fun b : Z => a b * 2 ^ (15 - b)) (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u))) 1)
    with (0 + a (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0) * 2 ^ (15 - (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0))).
  rewrite (zsum_0 _ (1 + Z.of_nat (Z.to_nat u)) (Z.to_nat (14 - u))) by (intros l Hl; rewrite Z0 by lia; lia).
  replace (1 + Z.of_nat (Z.to_nat u) + Z.of_nat (Z.to_nat (14 - u)) + Z.of_nat 0) with 15 by lia.
  rewrite Z.sub_diag, Z.pow_0_r.
  enough (E : zsum (fun b => a b * 2 ^ (15 - b)) 1 (Z.to_nat u) = zsum (fun b => 2 ^ (15 - u) * (a b * 2 ^ (u - b))) 1 (Z.to_nat u)) by (rewrite zsum_scale in E; lia).
  apply zsum_ext. intros b Hb. replace (15 - b) with ((15 - u) + (u - b)) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma max_level : forall (a : hist) u, (forall b, 0 <= a b) -> (exists b, 1 <= b <= u /\ 1 <= a b) ->
  exists u', 1 <= u' <= u /\ 1 <= a u' /\ forall l, u' < l <= u -> a l = 0.
Proof.
  intros a u B. remember (Z.to_nat u) as n eqn:En. revert u En. induction n as [|n IH]; intros u En (b & Hb & Ab); [lia|].
  destruct (Z.le_gt_cases 1 (a u)).
  - exists u. split; [lia|]. split; [assumption|]. intros; lia.
  - destruct (IH (u - 1) ltac:(lia)) as (u' & H1 & H2 & H3).
    + exists b. split; [|exact Ab]. destruct (Z.eq_dec b u) as [->|]; lia.
    + exists u'. split; [lia|]. split; [exact H2|]. intros l Hl. destruct (Z.eq_dec l u) as [->|]; [pose proof (B u); lia|apply H3; lia].
Qed.

Lemma deepest_level : forall (a : hist) t u,
  levels_ok a -> zsum a 1 15 = nl -> zsum (fun b => a b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - t ->
  K + 1 - t <= a 15 -> 0 <= t < K -> 0 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) ->
  exists u', 1 <= u' <= u /\ 1 <= a u' /\ (forall l, u' < l <= 14 -> a l = 0) /\ 2 ^ (15 - u') + 1 <= nl.
Proof.
  intros a t u OK T KR KC Ht Hu Z0.
  assert (B0 : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  pose proof (level_le_tot a 15 OK T ltac:(lia)) as A15.
  destruct (max_level a u B0) as (u' & H1 & H2 & H3).
  { destruct (Z.lt_ge_cases 0 (zsum (fun b => zind (1 <=? a b)) 1 (Z.to_nat u))) as [POS|ZE].
    - destruct (zsum_pos_has (fun b => 1 <=? a b) 1 (Z.to_nat u) POS) as (b & Hb & Pb & _).
      apply Z.leb_le in Pb. exists b. split; [lia|exact Pb].
    - exfalso. pose proof (kraft_split a 0 B0 ltac:(lia)) as KS. cbv zeta in KS.
      destruct KS as [_ E].
      { intros l Hl. destruct (Z.le_gt_cases l u); [|apply Z0; lia].
        pose proof (zsum_nonneg (fun b => zind (1 <=? a b)) 1 (Z.to_nat u) ltac:(intros; apply (proj1 (zind_le1 _)))).
        destruct (Z.le_gt_cases 1 (a l)); [|pose proof (B0 l); lia].
        pose proof (zsum_ind_ge1 (fun b => 1 <=? a b) 1 (Z.to_nat u) l ltac:(lia) ltac:(apply Z.leb_le; assumption)). lia. }
      rewrite KR in E. change (Z.to_nat 0) with 0%nat in E. cbn [zsum] in E. change (2 ^ (15 - 0)) with 32768 in E. change (2 ^ 15) with 32768 in E. lia. }
  exists u'. split; [exact H1|]. split; [exact H2|]. split.
  { intros l Hl. destruct (Z.le_gt_cases l u); [apply H3; lia|apply Z0; lia]. }
  pose proof (kraft_split a u' B0 ltac:(lia)) as KS. cbv zeta in KS. destruct KS as [QN E].
  { intros l Hl. destruct (Z.le_gt_cases l u); [apply H3; lia|apply Z0; lia]. }
  rewrite KR in E.
  set (Q := zsum (fun b => a b * 2 ^ (u' - b)) 1 (Z.to_nat u')) in *.
  assert (P : 2 ^ 15 = 2 ^ u' * 2 ^ (15 - u')) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (pow15_pos u' ltac:(lia)) as PP.
  assert (D : (2 ^ u' - Q) * 2 ^ (15 - u') = a 15 - (K - t)) by lia.
  assert (1 <= 2 ^ u' - Q) by nia.
  clearbody Q. nia.
Qed.

Lemma rstep_wsum : forall a u (wgt : Z -> Z) lo n, 1 <= u <= 14 -> 1 <= lo ->
  zsum (fun b => rstep a u b * wgt b) lo n =
  zsum (fun b => a b * wgt b) lo n
  + (if (lo <=? 15) && (15 <? lo + Z.of_nat n) then (if u =? 14 then wgt 15 else - wgt 15) else 0)
  + (if (lo <=? u) && (u <? lo + Z.of_nat n) then - wgt u else 0)
  + (if (lo <=? u + 1) && (u + 1 <? lo + Z.of_nat n) && negb (u =? 14) then 2 * wgt (u + 1) else 0).
Proof.
  intros a u wgt lo n Hu Hlo.
  transitivity (zsum (fun b => a b * wgt b + ((if b =? 15 then (if u =? 14 then wgt 15 else - wgt 15) else 0) + (if b =? u then - wgt u else 0)
                        + (if b =? u + 1 then (if negb (u =? 14) then 2 * wgt (u + 1) else 0) else 0))) lo n).
  { apply zsum_ext. intros b Hb. rewrite rstep_get by assumption.
    destruct (Z.eqb_spec b 15) as [->|N15].
    - replace (15 =? u) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (Z.eqb_spec u 14) as [->|NU]; [change (15 =? 14 + 1) with true; cbn [negb]; lia|].
      replace (15 =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    - destruct (Z.eqb_spec b u) as [->|NU]; [replace (u =? u + 1) with false by (symmetry; apply Z.eqb_neq; lia); lia|].
      destruct (Z.eqb_spec b (u + 1)) as [->|NU1]; [|lia].
      destruct (Z.eqb_spec u 14) as [->|N14]; [exfalso; lia|]. cbn [negb]. lia. }
  rewrite !zsum_add.
  assert (PT : forall x v, zsum (fun b => if b =? x then v else 0) lo n = if (lo <=? x) && (x <? lo + Z.of_nat n) then v else 0).
  { intros x v. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + Z.of_nat n)); cbn [andb];
      first [apply zsum_point; lia | apply zsum_point_out; lia]. }
  rewrite !PT. destruct (u =? 14); cbn [negb]; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r;
    destruct ((lo <=? u + 1) && (u + 1 <? lo + Z.of_nat n)); lia.
Qed.

Lemma rstep_ok : forall a u, levels_ok a -> 1 <= u <= 14 -> 1 <= a u -> (u = 14 \/ 1 <= a 15) ->
  zsum a 1 15 = nl ->
  levels_ok (rstep a u) /\ zsum (rstep a u) 1 15 = nl /\
  zsum (fun b => rstep a u b * 2 ^ (15 - b)) 1 15 = zsum (fun b => a b * 2 ^ (15 - b)) 1 15 - 1.
Proof.
  intros a u OK Hu Au A15 T.
  assert (B : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  assert (NN : forall b, 0 <= rstep a u b).
  { intros b. rewrite rstep_get by assumption. pose proof (B b). pose proof (B 15). pose proof (B (u + 1)). pose proof (B u).
    destruct (b =? 15); [destruct (Z.eqb_spec u 14); lia|]. destruct (b =? u); [lia|]. destruct (b =? u + 1); lia. }
  assert (T' : zsum (rstep a u) 1 15 = nl).
  { pose proof (rstep_wsum a u (fun _ => 1) 1 15 Hu ltac:(lia)) as W.
    rewrite (zsum_ext (fun b => rstep a u b * 1) (rstep a u)) in W by (intros; lia).
    rewrite (zsum_ext (fun b => a b * 1) a) in W by (intros; lia).
    rewrite W, T. change (Z.of_nat 15) with 15.
    replace ((1 <=? 15) && (15 <? 1 + 15)) with true by reflexivity.
    replace ((1 <=? u) && (u <? 1 + 15)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb]; [rewrite Bool.andb_false_r; lia|].
    replace ((1 <=? u + 1) && (u + 1 <? 1 + 15) && true) with true by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    lia. }
  split; [|split; [exact T'|]].
  - intros b. split; [apply NN|]. intros Hb. rewrite rstep_get by assumption. pose proof (proj2 (OK b) Hb).
    destruct (Z.eqb_spec b 15); [lia|]. destruct (Z.eqb_spec b u); [lia|]. destruct (Z.eqb_spec b (u + 1)); lia.
  - rewrite (rstep_wsum a u (fun b => 2 ^ (15 - b)) 1 15 Hu ltac:(lia)). change (Z.of_nat 15) with 15.
    replace ((1 <=? 15) && (15 <? 1 + 15)) with true by reflexivity.
    replace ((1 <=? u) && (u <? 1 + 15)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    change (2 ^ (15 - 15)) with 1.
    destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb]; [rewrite Bool.andb_false_r; change (2 ^ (15 - 14)) with 2; lia|].
    replace ((1 <=? u + 1) && (u + 1 <? 1 + 15) && true) with true by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & _ & P). lia.
Qed.

Lemma Rm_nonneg : forall a v, (forall b, 0 <= a b) -> 1 <= v <= 14 -> 0 <= Rm a v.
Proof. intros a v B Hv. unfold Rm. apply zsum_nonneg. intros l Hl. pose proof (B l). pose proof (sz_facts l ltac:(lia)). nia. Qed.

Lemma Rm_zero : forall a v, (forall b, 0 <= a b) -> 1 <= v <= 14 -> Rm a v = 0 -> forall l, v < l <= 14 -> a l = 0.
Proof.
  intros a v B Hv R l Hl. unfold Rm in R.
  pose proof (zsum_ge_point (fun l => a l * sz l) (v + 1) (Z.to_nat (14 - v)) l
                ltac:(intros j Hj; pose proof (B j); pose proof (sz_facts j ltac:(lia)); nia) ltac:(lia)) as X.
  cbv beta in X. pose proof (B l). pose proof (sz_facts l ltac:(lia)). nia.
Qed.

Lemma Rm_of_zero : forall a v, 1 <= v <= 14 -> (forall l, v < l <= 14 -> a l = 0) -> Rm a v = 0.
Proof. intros a v Hv Z0. unfold Rm. apply zsum_0. intros l Hl. rewrite Z0 by lia. lia. Qed.

Lemma Rm_inner : forall a u v, 1 <= u <= 14 -> 1 <= v < u -> Rm (rstep a u) v = Rm a v - 1.
Proof.
  intros a u v Hu Hv. unfold Rm. rewrite (rstep_wsum a u sz (v + 1) (Z.to_nat (14 - v)) Hu ltac:(lia)).
  replace ((v + 1 <=? 15) && (15 <? v + 1 + Z.of_nat (Z.to_nat (14 - v)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((v + 1 <=? u) && (u <? v + 1 + Z.of_nat (Z.to_nat (14 - v)))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb].
  - rewrite Bool.andb_false_r. unfold sz. change (2 ^ (15 - 14)) with 2. lia.
  - replace ((v + 1 <=? u + 1) && (u + 1 <? v + 1 + Z.of_nat (Z.to_nat (14 - v))) && true) with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & E & _). lia.
Qed.

Lemma Rm_touch : forall a u, 1 <= u <= 14 -> (forall l, u < l <= 14 -> a l = 0) -> Rm (rstep a u) u = sz u - 1.
Proof.
  intros a u Hu Z0. unfold Rm. rewrite (rstep_wsum a u sz (u + 1) (Z.to_nat (14 - u)) Hu ltac:(lia)).
  fold (Rm a u). rewrite (Rm_of_zero a u) by (lia || exact Z0).
  replace ((u + 1 <=? 15) && (15 <? u + 1 + Z.of_nat (Z.to_nat (14 - u)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((u + 1 <=? u) && (u <? u + 1 + Z.of_nat (Z.to_nat (14 - u)))) with false
    by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.leb_gt; lia).
  destruct (Z.eqb_spec u 14) as [->|NU]; cbn [negb].
  - rewrite Bool.andb_false_r. unfold sz. change (2 ^ (15 - 14)) with 2. lia.
  - replace ((u + 1 <=? u + 1) && (u + 1 <? u + 1 + Z.of_nat (Z.to_nat (14 - u))) && true) with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    pose proof (sz_facts u ltac:(lia)) as (_ & E & _). lia.
Qed.

Lemma Tc_split : forall u v, 1 <= u -> u < v <= 14 -> (forall l, u < l < v -> c1 l = 0) -> Tc u = c1 v * sz v + Tc v.
Proof.
  intros u v Hu Hv Z0. unfold Tc.
  replace (Z.to_nat (14 - u)) with (Z.to_nat (v - 1 - u) + S (Z.to_nat (14 - v)))%nat by lia.
  rewrite zsum_split, zsum_shift.
  rewrite (zsum_0 _ (u + 1) (Z.to_nat (v - 1 - u))) by (intros l Hl; rewrite Z0 by lia; lia).
  replace (u + 1 + Z.of_nat (Z.to_nat (v - 1 - u))) with v by lia. lia.
Qed.

Lemma Tc_14_zero : forall u, 1 <= u <= 14 -> (forall l, u < l <= 14 -> c1 l = 0) -> Tc u = 0.
Proof. intros u Hu Z0. unfold Tc. apply zsum_0. intros l Hl. rewrite Z0 by lia. lia. Qed.

Lemma Tc_nonneg : forall v, 1 <= v <= 14 -> 0 <= Tc v.
Proof. intros v Hv. unfold Tc. apply zsum_nonneg. intros l Hl. pose proof (C1N l). pose proof (sz_facts l ltac:(lia)). nia. Qed.

Definition rnext (a : hist) : hist := rstep a (rep_find (Z.to_nat 15) a (15 - 1)).

Lemma rinv_step : forall t a, RINV t a -> t < K -> RINV (t + 1) (rnext a).
Proof.
  intros t a [OK T KR KC (v & tau & Hv & Ht & HR & LOW & AV & ET & NB)] TK. unfold rnext. change (15 - 1) with 14.
  assert (B0 : forall b, 0 <= a b) by (intros b; apply (proj1 (OK b))).
  assert (T0 : 0 <= t).
  { pose proof (Rm_nonneg a v B0 ltac:(lia)). pose proof (Tc_nonneg v ltac:(lia)). pose proof (pow15_pos v ltac:(lia)). unfold sz in *. nia. }
  assert (A15 : 1 <= a 15) by lia.
  destruct (Z.lt_ge_cases 0 (Rm a v)) as [RP|RZ].
  -
    assert (EX : exists b, 1 <= b <= 14 /\ 1 <= a b /\ v < b).
    { unfold Rm in RP.
      destruct (Z.lt_ge_cases 0 (zsum (fun l => zind (1 <=? a l)) (v + 1) (Z.to_nat (14 - v)))) as [P|Z0].
      - destruct (zsum_pos_has (fun l => 1 <=? a l) (v + 1) (Z.to_nat (14 - v)) P) as (b & Hb & Pb & _).
        apply Z.leb_le in Pb. exists b. lia.
      - exfalso. rewrite (zsum_0 _ (v + 1)) in RP; [lia|].
        intros l Hl. pose proof (zsum_nonneg (fun l => zind (1 <=? a l)) (v + 1) (Z.to_nat (14 - v)) ltac:(intros; apply (proj1 (zind_le1 _)))).
        destruct (Z.le_gt_cases 1 (a l)); [|pose proof (B0 l); replace (a l) with 0 by lia; lia].
        pose proof (zsum_ind_ge1 (fun l => 1 <=? a l) (v + 1) (Z.to_nat (14 - v)) l Hl ltac:(apply Z.leb_le; assumption)). lia. }
    destruct EX as (b & Hb & Ab & Vb).
    destruct (max_level a 14 B0 ltac:(exists b; split; [lia|exact Ab])) as (u & U1 & U2 & U3).
    assert (Vu : v < u) by (destruct (Z.lt_ge_cases v u); [assumption|]; exfalso; pose proof (U3 b ltac:(lia)); lia).
    rewrite (find_spec (Z.to_nat 15) a 14 u) by (first [lia | intros; apply U3; lia]).
    destruct (rstep_ok a u OK ltac:(lia) U2 ltac:(lia) T) as (OK' & T' & KR').
    constructor; [exact OK'|exact T'|rewrite KR', KR; lia| |].
    + rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
    + exists v, tau. rewrite (Rm_inner a u v ltac:(lia) ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros b' Hb'. rewrite rstep_get by lia.
        destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. apply LOW. lia. }
      split; [|split; [lia|exact NB]].
      rewrite rstep_get by lia.
      destruct (Z.eqb_spec v 15); [lia|]. destruct (Z.eqb_spec v u); [lia|]. destruct (Z.eqb_spec v (u + 1)); [lia|]. exact AV.
  -
    assert (RZ0 : Rm a v = 0) by (pose proof (Rm_nonneg a v B0 ltac:(lia)); lia).
    pose proof (Rm_zero a v B0 ltac:(lia) RZ0) as EMP.
    destruct (deepest_level a t v OK T KR KC ltac:(lia) ltac:(lia) EMP) as (u & U1 & U2 & U3 & U4).
    rewrite (find_spec (Z.to_nat 15) a 14 u) by (first [lia | intros; apply U3; lia]).
    destruct (rstep_ok a u OK ltac:(lia) U2 ltac:(lia) T) as (OK' & T' & KR').
    constructor; [exact OK'|exact T'|rewrite KR', KR; lia| |].
    + rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
    + pose proof (Rm_touch a u ltac:(lia) U3) as RT.
      destruct (Z.eq_dec u v) as [->|NE].
      * exists v, (tau + 1). rewrite RT. pose proof (sz_facts v ltac:(lia)) as (S1 & S2 & S3).
        split; [lia|]. split; [lia|]. split; [unfold sz; lia|]. split.
        { intros b' Hb'. rewrite rstep_get by lia.
          destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' v); [lia|]. destruct (Z.eqb_spec b' (v + 1)); [lia|]. apply LOW. lia. }
        split; [|split; [unfold sz in *; lia|exact NB]].
        rewrite rstep_get by lia. destruct (Z.eqb_spec v 15); [lia|]. rewrite Z.eqb_refl. lia.
      * assert (Uv : u < v) by lia.
        assert (AV0 : a v = 0) by (apply U3; lia).
        exists u, 1. rewrite RT. pose proof (sz_facts u ltac:(lia)) as (S1 & S2 & S3).
        split; [lia|]. split; [rewrite <- (LOW u) by lia; lia|]. split; [unfold sz; lia|]. split.
        { intros b' Hb'. rewrite rstep_get by lia.
          destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. apply LOW. lia. }
        split.
        { rewrite rstep_get by lia. destruct (Z.eqb_spec u 15); [lia|]. rewrite Z.eqb_refl. rewrite (LOW u) by lia. lia. }
        split; [|exact U4].
        rewrite (Tc_split u v) by (first [lia | intros l Hl; rewrite <- (LOW l) by lia; apply U3; lia]).
        unfold sz in *. lia.
Qed.

Lemma rinv_first : RINV 1 (rnext c1).
Proof.
  unfold rnext. change (15 - 1) with 14.
  assert (KR : zsum (fun b => c1 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 + K - 0) by (rewrite C1K; lia).
  assert (KC : K + 1 - 0 <= c1 15) by lia.
  destruct (deepest_level c1 0 14 C1OK C1T KR KC ltac:(lia) ltac:(lia) ltac:(intros; lia)) as (u & U1 & U2 & U3 & U4).
  rewrite (find_spec (Z.to_nat 15) c1 14 u) by (first [lia | intros; apply U3; lia]).
  destruct (rstep_ok c1 u C1OK ltac:(lia) U2 ltac:(lia) C1T) as (OK' & T' & KR').
  constructor; [exact OK'|exact T'|rewrite KR', C1K; lia| |].
  - rewrite rstep_get by lia. destruct (Z.eqb_spec u 14); change (15 =? 15) with true; cbv iota; lia.
  - exists u, 1. rewrite (Rm_touch c1 u ltac:(lia) U3). pose proof (sz_facts u ltac:(lia)) as (S1 & S2 & S3).
    split; [lia|]. split; [lia|]. split; [unfold sz; lia|]. split.
    { intros b' Hb'. rewrite rstep_get by lia.
      destruct (Z.eqb_spec b' 15); [lia|]. destruct (Z.eqb_spec b' u); [lia|]. destruct (Z.eqb_spec b' (u + 1)); [lia|]. reflexivity. }
    split.
    { rewrite rstep_get by lia. destruct (Z.eqb_spec u 15); [lia|]. rewrite Z.eqb_refl. lia. }
    split; [|exact U4].
    rewrite (Tc_14_zero u) by (first [lia | intros l Hl; apply U3; lia]). unfold sz in *. lia.
Qed.

Lemma rep_iter_rnext : forall n a, rep_iter (S n) 15 a = rep_iter n 15 (rnext a).
Proof. reflexivity. Qed.

Lemma rinv_iter : forall n t a, RINV t a -> t + Z.of_nat n <= K -> RINV (t + Z.of_nat n) (rep_iter n 15 a).
Proof.
  induction n as [|n IH]; intros t a R Hn; [rewrite Z.add_0_r; exact R|].
  rewrite rep_iter_rnext. replace (t + Z.of_nat (S n)) with (t + 1 + Z.of_nat n) by lia. apply IH; [|lia]. apply rinv_step; [exact R|lia].
Qed.

Theorem repair_profile :
  let a2 := repair 15 c1 in
  levels_ok a2 /\ zsum a2 1 15 = nl /\ zsum (fun b => a2 b * 2 ^ (15 - b)) 1 15 = 2 ^ 15 /\
  exists v tau, 1 <= v <= 14 /\ 1 <= tau <= c1 v /\ 2 ^ (15 - v) + 1 <= nl /\
    (forall b, 1 <= b < v -> a2 b = c1 b) /\ a2 v = c1 v - tau /\
    Tc v + (tau - 1) * sz v <= K - 1.
Proof.
  cbv zeta.
  assert (EK : kraftZ 15 c1 - 2 ^ 15 = K) by (unfold kraftZ; change (Z.to_nat 15) with 15%nat; rewrite C1K; lia).
  unfold repair. rewrite EK. replace (Z.to_nat K) with (S (Z.to_nat (K - 1))) by lia. rewrite rep_iter_rnext.
  pose proof (rinv_iter (Z.to_nat (K - 1)) 1 _ rinv_first ltac:(lia)) as R.
  replace (1 + Z.of_nat (Z.to_nat (K - 1))) with K in R by lia.
  destruct R as [OK T KR KC (v & tau & Hv & Ht & HR & LOW & AV & ET & NB)].
  split; [exact OK|]. split; [exact T|]. split; [rewrite KR; lia|]. exists v, tau.
  split; [exact Hv|]. split; [exact Ht|]. split; [exact NB|]. split; [exact LOW|]. split; [exact AV|].
  unfold sz in *. lia.
Qed.
End Repair15.


Definition Gs (a : hist) (Lv : Z) : Z := zsum a Lv (Z.to_nat (16 - Lv)).
Definition lev (a : hist) (i : Z) : Z := zsum (fun Lv => zind (i <? Gs a Lv)) 1 15.

Lemma Gs_step : forall a Lv, Lv <= 15 -> Gs a Lv = a Lv + Gs a (Lv + 1).
Proof.
  intros a Lv HL. unfold Gs. replace (Z.to_nat (16 - Lv)) with (S (Z.to_nat (16 - (Lv + 1)))) by lia.
  rewrite zsum_shift. reflexivity.
Qed.
Lemma Gs_16 : forall a, Gs a 16 = 0.
Proof. reflexivity. Qed.
Lemma Gs_mono : forall a Lv Lv', (forall b, 0 <= a b) -> Lv <= Lv' <= 16 -> Gs a Lv' <= Gs a Lv.
Proof.
  intros a Lv Lv' B H. remember (Z.to_nat (Lv' - Lv)) as n eqn:En. revert Lv H En. induction n as [|n IH]; intros Lv H En; [replace Lv with Lv' by lia; lia|].
  rewrite (Gs_step a Lv) by lia. pose proof (B Lv). specialize (IH (Lv + 1) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma Gs_nonneg : forall a Lv, (forall b, 0 <= a b) -> 0 <= Gs a Lv.
Proof. intros a Lv B. unfold Gs. apply zsum_nonneg. intros; apply B. Qed.
Lemma Gs_1 : forall a, Gs a 1 = zsum a 1 15.
Proof. reflexivity. Qed.

Lemma lev_eq : forall a i b, (forall b, 0 <= a b) -> 1 <= b <= 15 -> Gs a (b + 1) <= i < Gs a b -> lev a i = b.
Proof.
  intros a i b B Hb Hi. unfold lev.
  replace 15%nat with (Z.to_nat (b - 1) + S (Z.to_nat (15 - b)))%nat by lia. rewrite zsum_split, zsum_shift.
  rewrite (zsum_ext _ (fun _ => 1) 1 (Z.to_nat (b - 1))), zsum_const1.
  2:{ intros Lv HL. pose proof (Gs_mono a Lv b B ltac:(lia)). replace (i <? Gs a Lv) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  replace (1 + Z.of_nat (Z.to_nat (b - 1))) with b by lia.
  replace (i <? Gs a b) with true by (symmetry; apply Z.ltb_lt; lia). cbn [zind].
  rewrite (zsum_0 _ (b + 1)); [lia|].
  intros Lv HL. pose proof (Gs_mono a (b + 1) Lv B ltac:(lia)). replace (i <? Gs a Lv) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma lev_range : forall a i, (forall b, 0 <= a b) -> 0 <= i < Gs a 1 -> 1 <= lev a i <= 15 /\ Gs a (lev a i + 1) <= i < Gs a (lev a i).
Proof.
  intros a i B Hi.
  assert (EX : exists b, 1 <= b <= 15 /\ Gs a (b + 1) <= i < Gs a b).
  { assert (GEN : forall n b, Z.of_nat n = b - 1 -> 1 <= b <= 15 -> Gs a (b + 1) <= i -> exists b', 1 <= b' <= b /\ Gs a (b' + 1) <= i < Gs a b').
    { induction n as [|n IH]; intros b En Hb Hle.
      - exists b. assert (b = 1) by lia. subst b. split; [lia|]. lia.
      - destruct (Z.lt_ge_cases i (Gs a b)); [exists b; split; [lia|lia]|].
        destruct (IH (b - 1) ltac:(lia) ltac:(lia) ltac:(replace (b - 1 + 1) with b by lia; lia)) as (b' & H1 & H2). exists b'. split; [lia|exact H2]. }
    destruct (GEN 14%nat 15 eq_refl ltac:(lia) ltac:(rewrite Gs_16; lia)) as (b' & H1 & H2). exists b'. split; [lia|exact H2]. }
  destruct EX as (b & Hb & Hib). rewrite (lev_eq a i b B Hb Hib). split; [exact Hb|exact Hib].
Qed.

Lemma Gs_cnt : forall (L : list Z) (v : Z -> Z) Lv, (forall i, In i L -> 1 <= v i <= 15) -> 1 <= Lv <= 16 ->
  Gs (fun b => cnt (fun i => v i =? b) L) Lv = cnt (fun i => Lv <=? v i) L.
Proof.
  intros L v Lv Hv HL. unfold Gs, cnt. rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (Hv i Hi).
  destruct (Z.leb_spec Lv (v i)).
  - rewrite (zsum_single (fun b => zind (v i =? b)) Lv (Z.to_nat (16 - Lv)) (v i)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros b Hb Nb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - cbn [zind]. apply zsum_0. intros b Hb. replace (v i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.


Lemma cnt_eq_one : forall (L : list Z) i, NoDup L -> In i L -> cnt (fun k => k =? i) L = 1.
Proof.
  intros L i ND Hi. unfold cnt. induction L as [|x L IH]; [destruct Hi|]. inversion ND; subst. cbn [lsum].
  destruct Hi as [->|Hi].
  - rewrite Z.eqb_refl. cbn [zind]. enough (lsum (fun k => zind (k =? i)) L = 0) by lia.
    etransitivity; [apply lsum_ext | apply lsum_zero]. intros k Hk. replace (k =? i) with false by (symmetry; apply Z.eqb_neq; intros ->; tauto). reflexivity.
  - replace (x =? i) with false by (symmetry; apply Z.eqb_neq; intros ->; tauto). cbn [zind]. rewrite IH by assumption. reflexivity.
Qed.

Lemma cnt_at : forall (P : Z -> bool) (L : list Z) i, NoDup L -> In i L ->
  cnt P L = cnt (fun k => P k && negb (k =? i)) L + zind (P i).
Proof.
  intros P L i ND Hi. rewrite (cnt_split P (fun k => negb (k =? i)) L). f_equal.
  rewrite (cnt_ext (fun k => P k && negb (negb (k =? i))) (fun k => P i && (k =? i)) L).
  2:{ intros k Hk. destruct (Z.eqb_spec k i) as [->|N]; cbn [negb]; [destruct (P i); reflexivity | rewrite !Bool.andb_false_r; reflexivity]. }
  destruct (P i); cbn [zind andb]; [apply cnt_eq_one; assumption|].
  unfold cnt. etransitivity; [apply lsum_ext; intros; reflexivity | apply lsum_zero].
Qed.

Section Ranks.
Variable L : list Z.
Variable w : Z -> Z.
Variable lam : Z -> Z.
Hypothesis ND : NoDup L.
Hypothesis LR : forall i j, In i L -> In j L -> w j < w i -> lam i <= lam j.

Definition before (j i : Z) : bool :=
  (w j <? w i) || ((w j =? w i) && ((lam i <? lam j) || ((lam j =? lam i) && (j <? i)))).
Definition rank (i : Z) : Z := cnt (fun j => before j i) L.
Definition nR : Z := Z.of_nat (length L).

Lemma before_irrefl : forall i, before i i = false.
Proof. intros i. unfold before. rewrite Z.ltb_irrefl, Z.eqb_refl, Z.ltb_irrefl, Z.eqb_refl, Z.ltb_irrefl. reflexivity. Qed.

Lemma before_trans : forall i j k, before i j = true -> before j k = true -> before i k = true.
Proof.
  intros i j k A B. unfold before in *.
  repeat match goal with
  | H : (_ || _) = true |- _ => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H; destruct H as [H ?]
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end;
  apply Bool.orb_true_iff;
  first [ left; apply Z.ltb_lt; lia
        | right; apply Bool.andb_true_iff; split; [apply Z.eqb_eq; lia|]; apply Bool.orb_true_iff;
          first [ left; apply Z.ltb_lt; lia | right; apply Bool.andb_true_iff; split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia] ] ].
Qed.

Lemma before_total : forall i j, i <> j -> before i j = true \/ before j i = true.
Proof.
  intros i j N. unfold before.
  destruct (Z.lt_total (w i) (w j)) as [A|[A|A]].
  - left. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact A.
  - destruct (Z.lt_total (lam i) (lam j)) as [B|[B|B]].
    + right. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact B.
    + destruct (Z.lt_total i j) as [C|[C|C]]; [| lia |].
      * left. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia].
      * right. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia].
    + left. apply Bool.orb_true_iff. right. apply Bool.andb_true_iff. split; [apply Z.eqb_eq; lia|]. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact B.
  - right. apply Bool.orb_true_iff. left. apply Z.ltb_lt. exact A.
Qed.

Lemma before_w : forall j i, before j i = true -> w j <= w i.
Proof.
  intros j i A. unfold before in A. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; lia|].
  apply Bool.andb_true_iff in A. destruct A as [A _]. apply Z.eqb_eq in A. lia.
Qed.

Lemma before_lam : forall j i, In i L -> In j L -> before j i = true -> lam i <= lam j.
Proof.
  intros j i Hi Hj A. unfold before in A. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; exact (LR i j Hi Hj A)|].
  apply Bool.andb_true_iff in A. destruct A as [_ A]. apply Bool.orb_true_iff in A. destruct A as [A|A]; [apply Z.ltb_lt in A; lia|].
  apply Bool.andb_true_iff in A. destruct A as [A _]. apply Z.eqb_eq in A. lia.
Qed.

Lemma rank_range : forall i, In i L -> 0 <= rank i <= nR - 1.
Proof.
  intros i Hi. unfold rank, nR. split; [apply cnt_nonneg|].
  rewrite (cnt_at (fun j => before j i) L i ND Hi). rewrite before_irrefl. cbn [zind].
  pose proof (cnt_le_length (fun k => before k i && negb (k =? i)) L).
  pose proof (cnt_at (fun _ => true) L i ND Hi) as T. rewrite cnt_true in T. cbn [zind andb] in T.
  pose proof (cnt_mono (fun k => before k i && negb (k =? i)) (fun k => negb (k =? i)) L ltac:(intros k Hk X; apply Bool.andb_true_iff in X; tauto)). lia.
Qed.

Lemma rank_lt : forall i j, In i L -> In j L -> before i j = true -> rank i < rank j.
Proof.
  intros i j Hi Hj B. unfold rank.
  rewrite (cnt_at (fun k => before k j) L i ND Hi). rewrite B. cbn [zind].
  pose proof (cnt_mono (fun k => before k i) (fun k => before k j && negb (k =? i)) L) as M.
  specialize (M ltac:(intros k Hk X; apply Bool.andb_true_iff; split; [exact (before_trans k i j X B)|];
                    destruct (Z.eqb_spec k i) as [->|N]; [rewrite before_irrefl in X; discriminate|reflexivity])). lia.
Qed.

Lemma rank_inj : forall i j, In i L -> In j L -> rank i = rank j -> i = j.
Proof.
  intros i j Hi Hj E. destruct (Z.eq_dec i j) as [->|N]; [reflexivity|]. exfalso.
  destruct (before_total i j N) as [B|B]; [pose proof (rank_lt i j Hi Hj B) | pose proof (rank_lt j i Hj Hi B)]; lia.
Qed.


Lemma rank_once : forall r, 0 <= r < nR -> cnt (fun i => rank i =? r) L = 1.
Proof.
  assert (LE1 : forall r, cnt (fun i => rank i =? r) L <= 1).
  { intros r. destruct (Z_lt_le_dec 1 (cnt (fun i => rank i =? r) L)) as [A|A]; [|exact A]. exfalso.
    destruct (cnt_pigeon (fun i => rank i =? r) (fun _ => false) L ltac:(pose proof (cnt_nonneg (fun i => rank i =? r) L); unfold cnt at 1; rewrite (lsum_ext (fun i => zind false) (fun _ => 0)), lsum_zero by (intros; reflexivity); lia)) as (i & Hi & Ri & _).
    apply Z.eqb_eq in Ri. rewrite (cnt_at (fun k => rank k =? r) L i ND Hi) in A. rewrite Ri, Z.eqb_refl in A. cbn [zind] in A.
    destruct (cnt_pigeon (fun k => (rank k =? r) && negb (k =? i)) (fun _ => false) L) as (j & Hj & Rj & _).
    { unfold cnt at 1. rewrite (lsum_ext (fun k => zind false) (fun _ => 0)), lsum_zero by (intros; reflexivity). lia. }
    apply Bool.andb_true_iff in Rj. destruct Rj as [Rj Nj]. apply Z.eqb_eq in Rj. apply Bool.negb_true_iff in Nj. apply Z.eqb_neq in Nj.
    apply Nj. apply (rank_inj j i Hj Hi). lia. }
  assert (SUM : zsum (fun r => cnt (fun i => rank i =? r) L) 0 (Z.to_nat nR) = nR).
  { unfold cnt. rewrite <- lsum_zsum_swap. transitivity (lsum (fun _ => 1) L); [| unfold nR; clear; induction L; cbn [lsum length]; lia].
    apply lsum_ext. intros i Hi.
    pose proof (rank_range i Hi). rewrite (zsum_single (fun r => zind (rank i =? r)) 0 (Z.to_nat nR) (rank i)); [rewrite Z.eqb_refl; reflexivity | lia |].
    intros r Hr Nr. replace (rank i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  intros r Hr. destruct (Z.eq_dec (cnt (fun i => rank i =? r) L) 1) as [E|N]; [exact E|]. exfalso.
  pose proof (LE1 r).
  pose proof (zsum_mono (fun r => cnt (fun i => rank i =? r) L) (fun r' => if r' =? r then 0 else 1) 0 (Z.to_nat nR)
                ltac:(intros r' Hr'; cbv beta; destruct (Z.eqb_spec r' r) as [->|Nr]; [lia | apply LE1])) as M.
  rewrite SUM in M.
  pose proof (zsum_mono (fun r' => if r' =? r then 0 else 1) (fun r' => 1 - (if r' =? r then 1 else 0)) 0 (Z.to_nat nR) ltac:(intros r' _; cbv beta; destruct (r' =? r); lia)) as M2.
  rewrite <- zsum_sub, zsum_const1, zsum_point in M2 by lia. lia.
Qed.

Theorem sum_by_rank : forall f : Z -> Z, lsum (fun i => f (rank i)) L = zsum f 0 (Z.to_nat nR).
Proof.
  intros f.
  transitivity (lsum (fun i => zsum (fun r => zind (rank i =? r) * f r) 0 (Z.to_nat nR)) L).
  - apply lsum_ext. intros i Hi. pose proof (rank_range i Hi).
    rewrite (zsum_single (fun r => zind (rank i =? r) * f r) 0 (Z.to_nat nR) (rank i)); [rewrite Z.eqb_refl; cbn [zind]; lia | lia |].
    intros r Hr Nr. replace (rank i =? r) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite lsum_zsum_swap. apply zsum_ext. intros r Hr.
    transitivity (f r * cnt (fun i => rank i =? r) L); [| rewrite rank_once by lia; lia].
    unfold cnt. rewrite <- lsum_scale. apply lsum_ext. intros; lia.
Qed.

Definition hlam (b : Z) : Z := cnt (fun j => lam j =? b) L.

Lemma lev_hlam : (forall i, In i L -> 1 <= lam i <= 15) -> forall i, In i L -> lev hlam (rank i) = lam i.
Proof.
  intros Hl i Hi. pose proof (Hl i Hi) as Ri.
  assert (B : forall b, 0 <= hlam b) by (intros; unfold hlam; apply cnt_nonneg).
  apply (lev_eq hlam (rank i) (lam i) B Ri). unfold hlam. rewrite !Gs_cnt by (try exact Hl; lia). split.
  -
    unfold rank. apply cnt_mono. intros j Hj X. apply Z.leb_le in X.
    destruct (Z.eq_dec j i) as [->|N]; [lia|].
    destruct (before_total j i N) as [Bf|Bf]; [exact Bf|]. exfalso. pose proof (before_lam i j Hj Hi Bf). lia.
  -
    unfold rank. rewrite (cnt_at (fun j => lam i <=? lam j) L i ND Hi). rewrite Z.leb_refl. cbn [zind].
    pose proof (cnt_mono (fun j => before j i) (fun k => (lam i <=? lam k) && negb (k =? i)) L) as M.
    specialize (M ltac:(intros k Hk X; apply Bool.andb_true_iff; split; [apply Z.leb_le; exact (before_lam k i Hi Hk X)|];
                      destruct (Z.eqb_spec k i) as [->|Nk]; [rewrite before_irrefl in X; discriminate|reflexivity])). lia.
Qed.

Lemma rank_rarity : forall (kap : Z -> Z) (Wt : Z),
  (forall i, In i L -> 1 <= kap i <= 15) -> (forall i, In i L -> 0 <= w i) ->
  (forall i, In i L -> w i * fib (kap i + 1) <= Wt) ->
  forall i, In i L -> w i * fib (lev (fun b => cnt (fun j => kap j =? b) L) (rank i) + 1) <= Wt.
Proof.
  intros kap Wt Hk Hw FIB i Hi.
  set (hk := fun b => cnt (fun j => kap j =? b) L).
  assert (B : forall b, 0 <= hk b) by (intros; subst hk; apply cnt_nonneg).
  assert (G1 : Gs hk 1 = nR) by (subst hk; rewrite Gs_cnt by (try exact Hk; lia); unfold nR; rewrite <- cnt_true; apply cnt_ext; intros j Hj; symmetry; symmetry; apply Z.leb_le; pose proof (Hk j Hj); lia).
  pose proof (rank_range i Hi) as RR.
  destruct (lev_range hk (rank i) B ltac:(lia)) as (LV & GA & GB).
  set (lv := lev hk (rank i)) in *.
  assert (GB' : cnt (fun j => before j i) L < cnt (fun j => lv <=? kap j) L) by (unfold rank in GB; subst hk; rewrite Gs_cnt in GB by (try exact Hk; lia); exact GB).
  destruct (cnt_pigeon (fun j => lv <=? kap j) (fun j => before j i) L GB') as (j & Hj & Kj & Bj).
  apply Z.leb_le in Kj.
  assert (Wij : w i <= w j).
  { destruct (Z.eq_dec j i) as [->|N]; [lia|]. destruct (before_total j i N) as [Bf|Bf]; [congruence|]. exact (before_w i j Bf). }
  pose proof (FIB j Hj). pose proof (fib_mono (lv + 1) (kap j + 1) ltac:(lia)). pose proof (fib_nonneg (lv + 1)). pose proof (Hw i Hi). nia.
Qed.
End Ranks.


Definition hexL (c L : Z) : Z := if (257 <=? c) && (c <=? 285) then Z.max 0 (L + xl_of_lcode c - 9) else 0.
Definition hexD (d L : Z) : Z := if (0 <=? d) && (d <=? 29) then Z.max 0 (L + xd_of_dcode d - 15) else 0.

Definition ML_l : list Z := [14; 14; 14; 14; 14; 14; 14; 14; 23; 23; 23; 23; 37; 37; 37; 37; 59; 59; 59; 59; 96; 96; 96; 96; 154; 154; 154; 154; 14].
Definition MD_l : list Z := [0; 0; 0; 0; 2; 2; 3; 3; 4; 4; 6; 6; 9; 9; 14; 14; 23; 23; 37; 37; 59; 59; 96; 96; 154; 154; 250; 250; 400; 400].
Definition MofL (c : Z) : Z := if (257 <=? c) && (c <=? 285) then nth (Z.to_nat (c - 257)) ML_l 0 else 0.
Definition MofD (d : Z) : Z := if (0 <=? d) && (d <=? 29) then nth (Z.to_nat d) MD_l 0 else 0.

Lemma forallb_seq : forall (f : Z -> bool) s n, forallb (fun k => f (Z.of_nat k)) (seq s n) = true ->
  forall x, Z.of_nat s <= x < Z.of_nat s + Z.of_nat n -> f x = true.
Proof.
  intros f s n H x Hx. rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma hexL_rarity : forall c L, 1 <= L <= 15 -> 1000 * hexL c L <= MofL c * fib (L + 1).
Proof.
  intros c L HL. unfold hexL, MofL.
  destruct (Z.leb_spec 257 c); destruct (Z.leb_spec c 285); cbn [andb]; try lia.
  pose proof (forallb_seq (fun c => forallb (fun L => 1000 * Z.max 0 (Z.of_nat L + xl_of_lcode c - 9) <=? nth (Z.to_nat (c - 257)) ML_l 0 * fib (Z.of_nat L + 1)) (seq 1 15)) 257 29
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as X. cbv beta in X.
  rewrite forallb_forall in X. specialize (X (Z.to_nat L) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in X by lia. apply Z.leb_le in X. exact X.
Qed.

Lemma hexD_rarity : forall d L, 1 <= L <= 15 -> 1000 * hexD d L <= MofD d * fib (L + 1).
Proof.
  intros d L HL. unfold hexD, MofD.
  destruct (Z.leb_spec 0 d); destruct (Z.leb_spec d 29); cbn [andb]; try lia.
  pose proof (forallb_seq (fun d => forallb (fun L => 1000 * Z.max 0 (Z.of_nat L + xd_of_dcode d - 15) <=? nth (Z.to_nat d) MD_l 0 * fib (Z.of_nat L + 1)) (seq 1 15)) 0 30
                ltac:(vm_compute; reflexivity) d ltac:(lia)) as X. cbv beta in X.
  rewrite forallb_forall in X. specialize (X (Z.to_nat L) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in X by lia. apply Z.leb_le in X. exact X.
Qed.

Lemma MofL_nonneg : forall c, 0 <= MofL c.
Proof.
  intros c. unfold MofL. destruct (Z.leb_spec 257 c); destruct (Z.leb_spec c 285); cbn [andb]; try lia.
  pose proof (forallb_seq (fun c => 0 <=? nth (Z.to_nat (c - 257)) ML_l 0) 257 29 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X. apply Z.leb_le in X. exact X.
Qed.
Lemma MofD_nonneg : forall d, 0 <= MofD d.
Proof.
  intros d. unfold MofD. destruct (Z.leb_spec 0 d); destruct (Z.leb_spec d 29); cbn [andb]; try lia.
  pose proof (forallb_seq (fun d => 0 <=? nth (Z.to_nat d) MD_l 0) 0 30 ltac:(vm_compute; reflexivity) d ltac:(lia)) as X. apply Z.leb_le in X. exact X.
Qed.

Lemma MofL_sum : zsum MofL 0 (Z.to_nat 286) = 1602.
Proof. vm_compute. reflexivity. Qed.
Lemma MofD_sum : zsum MofD 0 (Z.to_nat 30) = 2114.
Proof. vm_compute. reflexivity. Qed.

Lemma hexL_facts : forall c L L', 0 <= hexL c L /\ (L <= L' -> hexL c L <= hexL c L') /\ hexL c L' <= hexL c L + Z.max 0 (L' - L).
Proof. intros. unfold hexL. destruct (_ && _); lia. Qed.
Lemma hexD_facts : forall d L L', 0 <= hexD d L /\ (L <= L' -> hexD d L <= hexD d L') /\ hexD d L' <= hexD d L + Z.max 0 (L' - L).
Proof. intros. unfold hexD. destruct (_ && _); lia. Qed.

Lemma slack540 : forall L, 7 <= L <= 14 -> 540 * (15 - L) <= fib (L + 1) * sz L.
Proof.
  intros L HL. unfold sz.
  pose proof (forallb_seq (fun L => 540 * (15 - L) <=? fib (L + 1) * (2 ^ (15 - L) - 1)) 7 8 ltac:(vm_compute; reflexivity) L ltac:(lia)) as X.
  apply Z.leb_le in X. exact X.
Qed.


Lemma ar_HR1 : forall W M h fb F, 0 <= W -> 0 <= M -> 1000 * h <= M * fb -> W * fb <= F -> 1000 * (W * h) <= M * F.
Proof.
  intros W M h fb F HW HM H1 H2. transitivity (W * (M * fb)).
  - replace (1000 * (W * h)) with (W * (1000 * h)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HW|exact H1].
  - replace (W * (M * fb)) with (M * (W * fb)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HM|exact H2].
Qed.

Lemma ar_X2 : forall W D fb S F, 0 <= W -> 0 <= S -> 540 * D <= fb * S -> W * fb <= F -> 540 * (W * D) <= F * S.
Proof.
  intros W D fb S F HW HS H1 H2. transitivity (W * (fb * S)).
  - replace (540 * (W * D)) with (W * (540 * D)) by lia. apply Z.mul_le_mono_nonneg_l; [exact HW|exact H1].
  - replace (W * (fb * S)) with ((W * fb) * S) by lia. apply Z.mul_le_mono_nonneg_r; [exact HS|exact H2].
Qed.

Lemma ar_touched : forall W F h1 h2 M S L1 L2,
  0 <= W -> 0 <= h1 -> 1000 * (W * h1) <= M * F -> 540 * (W * (15 - L1)) <= F * S ->
  h2 <= h1 + Z.max 0 (L2 - L1) -> L2 <= 15 -> L1 <= 14 ->
  540000 * (W * h2) <= 540 * (M * F) + 1000 * F * S.
Proof.
  intros W F h1 h2 M S L1 L2 HW Hh1 X1 X2 LIP HL2 HL1.
  assert (A : W * h2 <= W * (h1 + (15 - L1))) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma ar_low : forall W F h2 h15 M, 0 <= W -> h2 <= h15 -> 1000 * (W * h15) <= M * F ->
  540000 * (W * h2) <= 540 * (M * F) + 1000 * F * 0.
Proof. intros W F h2 h15 M HW Hh X1. assert (A : W * h2 <= W * h15) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.

Lemma ar_plain : forall W F h M, 1000 * (W * h) <= M * F -> 540000 * (W * h) <= 540 * (M * F) + 1000 * F * 0.
Proof. intros. lia. Qed.

Lemma ar_total : forall T tau s K c15 nl, 0 <= T -> T + (tau - 1) * s <= K - 1 -> s <= nl - 2 -> 1 <= s -> 1 <= tau ->
  K + 1 <= c15 -> c15 <= nl -> 0 <= T + tau * s <= 2 * nl.
Proof. intros. nia. Qed.

Lemma lev_ext : forall (a a' : hist) i, (forall b, 1 <= b <= 15 -> a b = a' b) -> lev a i = lev a' i.
Proof.
  intros a a' i E. unfold lev. apply zsum_ext. intros Lv HL. f_equal. f_equal. unfold Gs. apply zsum_ext. intros b Hb. apply E. lia.
Qed.

Lemma Gs_prefix : forall (a : hist) Lv, 1 <= Lv <= 16 -> Gs a Lv = Gs a 1 - zsum a 1 (Z.to_nat (Lv - 1)).
Proof.
  intros a Lv HL. unfold Gs. replace (Z.to_nat (16 - 1)) with (Z.to_nat (Lv - 1) + Z.to_nat (16 - Lv))%nat by lia.
  rewrite zsum_split. replace (1 + Z.of_nat (Z.to_nat (Lv - 1))) with Lv by lia. lia.
Qed.

Lemma block_sum : forall (a1 : hist) (nl v tau : Z),
  (forall b, 0 <= a1 b) -> Gs a1 1 = nl -> 1 <= v <= 14 -> 0 <= tau <= a1 v ->
  zsum (fun i => if (Gs a1 15 <=? i) && (i <? Gs a1 (v + 1) + tau) then sz (lev a1 i) else 0) 0 (Z.to_nat nl)
  = zsum (fun l => a1 l * sz l) (v + 1) (Z.to_nat (14 - v)) + tau * sz v.
Proof.
  intros a1 nl v tau B G1 Hv Ht.
  pose proof (Gs_mono a1 1 v B ltac:(lia)) as M1. pose proof (Gs_mono a1 (v + 1) 15 B ltac:(lia)) as M2.
  pose proof (Gs_step a1 v ltac:(lia)) as SV. pose proof (Gs_nonneg a1 15 B) as P15.
  set (A := Gs a1 15) in *. set (Bv := Gs a1 (v + 1)) in *.
  replace (Z.to_nat nl) with (Z.to_nat A + (Z.to_nat (Bv - A) + (Z.to_nat tau + Z.to_nat (nl - Bv - tau))))%nat by lia.
  rewrite !zsum_split.
  rewrite (zsum_0 _ 0 (Z.to_nat A)) by (intros i Hi; replace (A <=? i) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  replace (0 + Z.of_nat (Z.to_nat A)) with A by lia.
  replace (A + Z.of_nat (Z.to_nat (Bv - A))) with Bv by lia.
  replace (Bv + Z.of_nat (Z.to_nat tau)) with (Bv + tau) by lia.
  rewrite (zsum_0 _ (Bv + tau) (Z.to_nat (nl - Bv - tau))) by (intros i Hi; replace (i <? Bv + tau) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r; reflexivity).
  rewrite (zsum_ext _ (fun _ => sz v) Bv (Z.to_nat tau)).
  2:{ intros i Hi. replace ((A <=? i) && (i <? Bv + tau)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite (lev_eq a1 i v B ltac:(lia)) by (subst Bv; lia). reflexivity. }
  assert (CS : forall m lo c, zsum (fun _ => c) lo m = Z.of_nat m * c) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
  rewrite CS. replace (Z.of_nat (Z.to_nat tau)) with tau by lia.
  enough (FB : forall n m, Z.of_nat n = 15 - m -> v + 1 <= m <= 15 ->
            zsum (fun i => if (A <=? i) && (i <? Bv + tau) then sz (lev a1 i) else 0) A (Z.to_nat (Gs a1 m - A))
            = zsum (fun l => a1 l * sz l) m n).
  { rewrite <- (FB (Z.to_nat (14 - v)) (v + 1)) by lia. subst Bv. lia. }
  induction n as [|n IH]; intros m En Hm.
  - assert (m = 15) by lia. subst m. subst A. rewrite Z.sub_diag. reflexivity.
  - rewrite zsum_shift.
    pose proof (Gs_step a1 m ltac:(lia)) as SM. pose proof (Gs_mono a1 (v + 1) m B ltac:(lia)) as MM. pose proof (Gs_mono a1 (m + 1) 15 B ltac:(lia)) as MM2.
    pose proof (B m) as Bm.
    replace (Z.to_nat (Gs a1 m - A)) with (Z.to_nat (Gs a1 (m + 1) - A) + Z.to_nat (a1 m))%nat by (subst A; lia).
    rewrite zsum_split. rewrite (IH (m + 1)) by lia.
    replace (A + Z.of_nat (Z.to_nat (Gs a1 (m + 1) - A))) with (Gs a1 (m + 1)) by (subst A; lia).
    rewrite (zsum_ext _ (fun _ => sz m) (Gs a1 (m + 1)) (Z.to_nat (a1 m))).
    2:{ intros i Hi. replace ((A <=? i) && (i <? Bv + tau)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; subst A Bv; lia).
        rewrite (lev_eq a1 i m B ltac:(lia)) by lia. reflexivity. }
    rewrite CS. replace (Z.of_nat (Z.to_nat (a1 m))) with (a1 m) by lia. lia.
Qed.


Section TreeX.
Variable z : ztree.
Variable E : Z.
Variable F : Z -> Z.
Variable Fl : list Z.
Variable hex : Z -> Z -> Z.
Variable M : Z -> Z.
Variable SM : Z.
Hypothesis TF : tree_facts z E 15 F Fl.
Hypothesis HE : E <= 286.
Hypothesis HW : g_W (zt_g z) < fib 24.
Hypothesis HEXF : forall c L L', 0 <= hex c L /\ (L <= L' -> hex c L <= hex c L') /\ hex c L' <= hex c L + Z.max 0 (L' - L).
Hypothesis HEXR : forall c L, 1 <= L <= 15 -> 1000 * hex c L <= M c * fib (L + 1).
Hypothesis M0 : forall c, 0 <= M c.
Hypothesis MS : zsum M 0 (Z.to_nat E) = SM.

Local Notation g := (zt_g z).
Let GG : gtree_ok g := G z E 15 F Fl TF.
Let ZOK : ztree_ok z := tf_ok z E 15 F Fl TF.
Local Notation W := (ffreq F Fl).
Local Notation Lv := (leaves g).
Local Notation wt := (g_wt g).
Local Notation dp := (g_depth g).
Definition kap (i : Z) : Z := Z.min (dp i) 15.
Definition lnz (i : Z) : Z := zt_len z (g_code g i).
Local Notation cd := (g_code g).

Lemma ML15 : zt_ML z = 15. Proof. exact (tf_ML z E 15 F Fl TF). Qed.
Lemma Lv_in' : forall i, In i Lv <-> (g_lo g <= i <= g_hi g /\ g_leaf g i = true).
Proof. intros i. exact (leaves_in g GG i). Qed.
Lemma E0 : 0 <= E. Proof. exact (E_nonneg z E 15 F Fl TF). Qed.

Lemma leaf_facts : forall i, In i Lv -> 1 <= wt i /\ 1 <= dp i <= 22 /\ 1 <= lnz i <= 15 /\ 0 <= cd i < E /\ wt i = W (cd i).
Proof.
  intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L].
  destruct (leaf_W z E 15 F Fl TF i P L) as [C Wc].
  split; [exact (go_wt_leaf g GG i P L)|]. split.
  - split; [| apply (depth_le_of_W z E 15 F Fl TF 22); [exact HW | lia | exact P | exact L]].
    apply (depth_pos g GG). destruct (Z.eq_dec i (g_lo g)) as [->|N]; [rewrite (root_internal g GG) in L; discriminate | lia].
  - split; [| auto]. unfold lnz. rewrite <- ML15. apply (zo_len_used z ZOK (g_code g i) i). split; [exact P | split; [exact L | reflexivity]].
Qed.

Lemma nLv : 2 <= Z.of_nat (length Lv) <= E.
Proof.
  pose proof (tused_two z E 15 F Fl TF) as T2. rewrite (reindex z E 15 F Fl TF (fun _ => 1)) in T2.
  pose proof E0.
  assert (LEN : lsum (fun _ : Z => 1) Lv = Z.of_nat (length Lv)) by (clear; induction (leaves g); cbn [lsum length]; lia).
  rewrite LEN in T2. split; [exact T2|].
  rewrite <- LEN, <- (reindex z E 15 F Fl TF (fun _ => 1)).
  pose proof (zsum_mono (fun c => if W c =? 0 then 0 else 1) (fun _ => 1) 0 (Z.to_nat E) ltac:(intros; cbv beta; destruct (_ =? 0); lia)). rewrite zsum_const1 in H0. lia.
Qed.

Lemma code_sumX : forall h : Z -> Z -> Z, zsum (fun c => W c * h c (zt_len z c)) 0 (Z.to_nat E) = lsum (fun i => wt i * h (cd i) (lnz i)) Lv.
Proof.
  intros h. transitivity (zsum (fun c => if W c =? 0 then 0 else W c * h c (zt_len z c)) 0 (Z.to_nat E)).
  - apply zsum_ext. intros c Hc. destruct (Z.eqb_spec (W c) 0) as [Ez|N]; [rewrite Ez; lia | reflexivity].
  - rewrite (reindex z E 15 F Fl TF (fun c => W c * h c (zt_len z c))). apply lsum_ext. intros i Hi.
    destruct (leaf_facts i Hi) as (_ & _ & _ & _ & Wc). rewrite Wc. reflexivity.
Qed.

Lemma M_sum : lsum (fun i => M (cd i)) Lv <= SM.
Proof.
  rewrite <- MS, <- (reindex z E 15 F Fl TF M). apply zsum_mono. intros c Hc. pose proof (M0 c). destruct (_ =? 0); lia.
Qed.

Lemma HR1 : forall Wc c L Fz, 0 <= Wc -> 1 <= L <= 15 -> Wc * fib (L + 1) <= Fz -> 1000 * (Wc * hex c L) <= M c * Fz.
Proof. intros Wc c L Fz W0 HL WF. apply (ar_HR1 Wc (M c) (hex c L) (fib (L + 1)) Fz W0 (M0 c) (HEXR c L HL) WF). Qed.

Lemma bound_from_leaves : forall (extra : Z -> Z) (X : Z),
  (forall i, In i Lv -> 540000 * (wt i * hex (cd i) (lnz i)) <= 540 * (M (cd i) * g_W g) + 1000 * g_W g * extra i) ->
  (forall i, In i Lv -> 0 <= extra i) -> lsum extra Lv <= X -> 0 <= X <= 2 * E ->
  540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  intros extra X PL EN ES XB. rewrite (code_sumX hex).
  pose proof (W_leaves g GG) as WL. pose proof (lsum_nonneg wt Lv ltac:(intros j Hj; pose proof (leaf_facts j Hj); lia)) as W0. rewrite <- WL in W0.
  transitivity (lsum (fun i => 540 * g_W g * M (cd i) + 1000 * g_W g * extra i) Lv).
  - rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (PL i Hi). lia.
  - rewrite lsum_add, !lsum_scale. pose proof M_sum. nia.
Qed.

Definition c1h (b : Z) : Z := cnt (fun j => kap j =? b) Lv.
Definition Kx : Z := zsum (fun b => c1h b * 2 ^ (15 - b)) 1 15 - 2 ^ 15.

Lemma kap_range : forall i, In i Lv -> 1 <= kap i <= 15.
Proof. intros i Hi. pose proof (leaf_facts i Hi). unfold kap. lia. Qed.

Lemma c1h_ok : levels_ok c1h /\ zsum c1h 1 15 = Z.of_nat (length Lv) /\ (forall b, 0 <= c1h b).
Proof.
  assert (B : forall b, 0 <= c1h b) by (intros; unfold c1h; apply cnt_nonneg).
  split; [|split; [|exact B]].
  - intros b. split; [apply B|]. intros Hb. unfold c1h, cnt.
    etransitivity; [apply lsum_ext; intros j Hj; replace (kap j =? b) with false by (symmetry; apply Z.eqb_neq; pose proof (kap_range j Hj); lia); reflexivity | apply lsum_zero].
  - unfold c1h. rewrite <- (Gs_1 (fun b => cnt (fun j : Z => kap j =? b) Lv)). rewrite (Gs_cnt Lv kap 1 kap_range ltac:(lia)).
    rewrite <- cnt_true. apply cnt_ext. intros j Hj. pose proof (kap_range j Hj). symmetry. symmetry. apply Z.leb_le. lia.
Qed.

Lemma Kx_ok : forall i0, In i0 Lv -> 15 < dp i0 -> 1 <= Kx /\ Kx + 1 <= c1h 15.
Proof.
  intros i0 Hi0 D0.
  assert (KRb : zsum (fun b => c1h b * 2 ^ (15 - b)) 1 15 = lsum (fun i => 2 ^ (15 - kap i)) Lv).
  { unfold c1h, cnt. rewrite (zsum_ext _ (fun b => lsum (fun i => zind (kap i =? b) * 2 ^ (15 - b)) Lv)) by (intros; rewrite Z.mul_comm, <- lsum_scale; apply lsum_ext; intros; lia).
    rewrite <- lsum_zsum_swap. apply lsum_ext. intros i Hi. pose proof (kap_range i Hi).
    rewrite (zsum_single (fun b => zind (kap i =? b) * 2 ^ (15 - b)) 1 15 (kap i)); [rewrite Z.eqb_refl; cbn [zind]; lia | lia |].
    intros b Hb Nb. replace (kap i =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof (kraft_eq g GG 22 ltac:(intros i P L; pose proof (leaf_facts i ltac:(apply Lv_in'; auto)); lia)) as KR22.
  assert (MC : cnt (fun i => 15 <? dp i) Lv <= c1h 15).
  { unfold c1h. apply cnt_mono. intros i Hi X. apply Z.ltb_lt in X. apply Z.eqb_eq. unfold kap. lia. }
  assert (M1 : 1 <= cnt (fun i => 15 <? dp i) Lv).
  { unfold cnt. pose proof (lsum_ge_member (fun i => zind (15 <? dp i)) Lv i0 ltac:(intros; apply (proj1 (zind_le1 _))) Hi0) as X.
    cbv beta in X. replace (15 <? dp i0) with true in X by (symmetry; apply Z.ltb_lt; exact D0). cbn [zind] in X. exact X. }
  assert (E7 : 128 * lsum (fun i => 2 ^ (15 - kap i)) Lv = lsum (fun i => 2 ^ (22 - dp i)) Lv + lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv).
  { rewrite <- lsum_scale, <- lsum_add. apply lsum_ext. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _). unfold kap.
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind].
    - rewrite Z.min_r by lia. change (2 ^ (15 - 15)) with 1. lia.
    - rewrite Z.min_l by lia. replace (22 - dp i) with (7 + (15 - dp i)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 7) with 128. lia. }
  rewrite KR22 in E7. change (2 ^ 22) with (128 * 2 ^ 15) in E7.
  assert (LO : 64 * cnt (fun i => 15 <? dp i) Lv <= lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv).
  { unfold cnt. rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _).
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind]; [|lia].
    assert (P6 : 2 ^ (22 - dp i) <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2 ^ 6) with 64 in P6. lia. }
  assert (HI : lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv <= 127 * cnt (fun i => 15 <? dp i) Lv).
  { unfold cnt. rewrite <- lsum_scale. apply lsum_le. intros i Hi. pose proof (leaf_facts i Hi) as (_ & Di & _).
    destruct (Z.ltb_spec 15 (dp i)); cbn [zind]; [|lia]. pose proof (pow15_pos (dp i - 7) ltac:(lia)) as PP. replace (15 - (dp i - 7)) with (22 - dp i) in PP by lia. lia. }
  unfold Kx. rewrite KRb.
  revert E7 LO HI M1 MC. generalize (lsum (fun i => 2 ^ (15 - kap i)) Lv) as S1. generalize (lsum (fun i => zind (15 <? dp i) * (128 - 2 ^ (22 - dp i))) Lv) as S2.
  generalize (cnt (fun i => 15 <? dp i) Lv) as m. generalize (c1h 15) as c15. intros. lia.
Qed.

Lemma per_leaf : forall (a2 : hist) (v tau n : Z) (r L1 L2 Wi c Fz : Z),
  (forall b, 0 <= c1h b) -> (forall b, 0 <= a2 b) ->
  Gs c1h 1 = n -> Gs a2 1 = n -> 7 <= v <= 14 -> 1 <= tau <= c1h v ->
  (forall Lx, 1 <= Lx <= v -> Gs a2 Lx = Gs c1h Lx) -> Gs a2 (v + 1) = Gs c1h (v + 1) + tau ->
  0 <= r < n -> L1 = lev c1h r -> L2 = lev a2 r -> 1 <= Wi -> 1 <= L2 <= 15 ->
  Wi * fib (L1 + 1) <= Fz ->
  540000 * (Wi * hex c L2)
    <= 540 * (M c * Fz) + 1000 * Fz * (if (Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau) then sz L1 else 0).
Proof.
  intros a2 v tau n r L1 L2 Wi c Fz B1 B2 G11 G21 Hv Ht GEQ GV1 RR EL1 EL2 HWi HL2 RRY.
  pose proof (lev_range a2 r B2 ltac:(rewrite G21; lia)) as [L2R [G2a G2b]]. rewrite <- EL2 in L2R, G2a, G2b.
  pose proof (lev_range c1h r B1 ltac:(rewrite G11; lia)) as [L1R [G1a G1b]]. rewrite <- EL1 in L1R, G1a, G1b.
  pose proof (Gs_mono c1h (v + 1) 15 B1 ltac:(lia)) as M15. pose proof (Gs_step c1h v ltac:(lia)) as SV.
  pose proof (fun (HLx : 1 <= L1 + 1 <= v) => Gs_mono c1h (L1 + 1) v B1 ltac:(lia)) as MA.
  pose proof (fun (HLx : v + 1 <= L2 <= 16) => Gs_mono a2 (v + 1) L2 B2 HLx) as MB.
  pose proof (fun (HLx : 1 <= L2 <= v) => GEQ L2 HLx) as GE2.
  pose proof (fun (HLx : 1 <= L2 + 1 <= v) => GEQ (L2 + 1) HLx) as GE2'.
  pose proof (lev_eq c1h r 15 B1 ltac:(lia)) as LE15. rewrite Gs_16 in LE15. rewrite <- EL1 in LE15.
  pose proof (lev_eq c1h r L2 B1) as LE2. rewrite <- EL1 in LE2.
  pose proof (HR1 Wi c) as HRp. pose proof (proj1 (proj2 (HEXF c L2 15))) as HM.
  pose proof (proj2 (proj2 (HEXF c L1 L2))) as LIP. pose proof (proj1 (HEXF c L1 0)) as HN1.
  destruct (Z.lt_ge_cases r (Gs c1h 15)) as [LOWR|HIR].
  - replace (Gs c1h 15 <=? r) with false by (symmetry; apply Z.leb_gt; exact LOWR). cbn [andb].
    assert (E1 : L1 = 15) by (apply LE15; lia).
    apply (ar_low Wi Fz (hex c L2) (hex c 15) (M c) ltac:(lia) ltac:(apply HM; lia)).
    apply HRp; [lia|lia|]. rewrite <- E1. exact RRY.
  - destruct (Z.lt_ge_cases r (Gs c1h (v + 1) + tau)) as [TOU|UNT].
    + replace ((Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; exact HIR|apply Z.ltb_lt; exact TOU]).
      assert (L114 : L1 <= 14) by (destruct (Z.eq_dec L1 15) as [E1|NE]; [rewrite E1 in G1b; lia|lia]).
      assert (L1v : v <= L1) by (destruct (Z.lt_ge_cases L1 v) as [LT|GE]; [specialize (MA ltac:(lia)); lia|exact GE]).
      pose proof (HRp L1 Fz ltac:(lia) ltac:(lia) RRY) as X1.
      assert (X2 : 540 * (Wi * (15 - L1)) <= Fz * sz L1).
      { apply (ar_X2 Wi (15 - L1) (fib (L1 + 1)) (sz L1) Fz ltac:(lia)); [| apply slack540; lia | exact RRY]. pose proof (sz_facts L1 ltac:(lia)). lia. }
      exact (ar_touched Wi Fz (hex c L1) (hex c L2) (M c) (sz L1) L1 L2 ltac:(lia) HN1 X1 X2 LIP ltac:(lia) L114).
    + replace (r <? Gs c1h (v + 1) + tau) with false by (symmetry; apply Z.ltb_ge; exact UNT). rewrite Bool.andb_false_r.
      assert (L2v : L2 <= v) by (destruct (Z.lt_ge_cases v L2) as [LT|GE]; [specialize (MB ltac:(lia)); lia|exact GE]).
      assert (E12 : L1 = L2).
      { apply LE2; [lia|]. rewrite <- (GE2 ltac:(lia)). split; [|exact G2b].
        destruct (Z.eq_dec L2 v) as [E2|NE]; [rewrite E2; lia|]. rewrite <- (GE2' ltac:(lia)). exact G2a. }
      apply (ar_plain Wi Fz (hex c L2) (M c)). apply HRp; [lia|exact HL2|]. rewrite <- E12. exact RRY.
Qed.

Lemma excess_ov : forall i0, In i0 Lv -> 15 < dp i0 ->
  540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  intros i0 Hi0 D0. pose proof nLv as NL.
  assert (W0 : forall i, In i Lv -> 0 <= wt i) by (intros i Hi; pose proof (leaf_facts i Hi); lia).
  assert (FIBd : forall i, In i Lv -> wt i * fib (dp i + 1) <= g_W g).
  { intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L]. pose proof (fib_bound g GG i P). lia. }
  assert (OV : exists i, g_pos g i /\ g_leaf g i = true /\ zt_ML z < g_depth g i).
  { exists i0. rewrite ML15. apply Lv_in' in Hi0. destruct Hi0 as [P L]. auto. }
  destruct c1h_ok as (C1OK & C1T & B1). destruct (Kx_ok i0 Hi0 D0) as [K1 KC].
  destruct (repair_profile c1h (Z.of_nat (length Lv)) Kx C1OK C1T ltac:(unfold Kx; lia) KC K1 ltac:(lia)) as (OK2 & T2 & KR2 & v & tau & Hv & Ht & NB & LOW & AV & STEPS).
  remember (repair 15 c1h) as a2 eqn:Ea2.
  assert (B2 : forall b, 0 <= a2 b) by (intros b; apply (proj1 (OK2 b))).
  assert (HL : forall b, 1 <= b <= 15 -> cnt (fun j => lnz j =? b) Lv = a2 b).
  { intros b Hb. rewrite Ea2. unfold lnz. rewrite <- (g_hist_cnt z (fun i => zt_len z (g_code g i)) b). rewrite (zo_len_hist z ZOK b) by (rewrite ML15; exact Hb).
    rewrite ML15. apply d_repair_ext. intros x. rewrite (g_hist_cnt z). reflexivity. }
  assert (LR : forall i j, In i Lv -> In j Lv -> wt j < wt i -> lnz i <= lnz j).
  { intros i j Hi Hj Wij. apply Lv_in' in Hi. apply Lv_in' in Hj. destruct Hi as [Pi Li], Hj as [Pj Lj]. unfold lnz. exact (zo_len_rank z ZOK OV j i Pj Pi Lj Li Wij). }
  pose proof (leaves_nodup g) as ND.
  assert (NR : nR Lv = Z.of_nat (length Lv)) by reflexivity.
  assert (G11 : Gs c1h 1 = Z.of_nat (length Lv)) by (rewrite Gs_1; exact C1T).
  assert (G21 : Gs a2 1 = Z.of_nat (length Lv)) by (rewrite Gs_1; exact T2).
  assert (GEQ : forall Lx, 1 <= Lx <= v -> Gs a2 Lx = Gs c1h Lx).
  { intros Lx HLx. rewrite (Gs_prefix a2 Lx), (Gs_prefix c1h Lx) by lia. rewrite G11, G21.
    rewrite (zsum_ext a2 c1h); [reflexivity|]. intros b Hb. apply LOW. lia. }
  assert (GV1 : Gs a2 (v + 1) = Gs c1h (v + 1) + tau).
  { rewrite (Gs_prefix a2 (v + 1)), (Gs_prefix c1h (v + 1)) by lia. rewrite G11, G21.
    replace (Z.to_nat (v + 1 - 1)) with (S (Z.to_nat (v - 1)))%nat by lia. rewrite !zsum_snoc.
    replace (1 + Z.of_nat (Z.to_nat (v - 1))) with v by lia. rewrite AV.
    rewrite (zsum_ext a2 c1h) by (intros b Hb; apply LOW; lia). lia. }
  pose proof (Gs_mono c1h (v + 1) 15 B1 ltac:(lia)) as M15. pose proof (Gs_nonneg c1h 15 B1) as P15.
  pose proof (Gs_mono c1h 1 v B1 ltac:(lia)) as M1v. rewrite G11 in M1v.
  pose proof (Gs_step c1h v ltac:(lia)) as SV.
  assert (V7 : 7 <= v).
  { destruct (Z.lt_ge_cases v 7) as [LT|GE]; [|exact GE]. exfalso.
    assert (P9 : 2 ^ 9 <= 2 ^ (15 - v)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in P9. lia. }
  apply (bound_from_leaves (fun i => if (Gs c1h 15 <=? rank Lv wt lnz i) && (rank Lv wt lnz i <? Gs c1h (v + 1) + tau) then sz (lev c1h (rank Lv wt lnz i)) else 0)
           (Tc c1h v + tau * sz v)).
  -
    intros i Hi. pose proof (leaf_facts i Hi) as (Wi & Di & Li & Ci & Wc).
    pose proof (rank_range Lv wt lnz ND i Hi) as RR. rewrite NR in RR.
    pose proof (rank_rarity Lv wt lnz ND kap (g_W g) kap_range W0
                  ltac:(intros j Hj; pose proof (FIBd j Hj); pose proof (Z.mul_le_mono_nonneg_l (fib (kap j + 1)) (fib (dp j + 1)) (wt j) (W0 j Hj) (fib_mono (kap j + 1) (dp j + 1) ltac:(pose proof (kap_range j Hj); unfold kap in *; lia))); lia) i Hi) as RRY.
    pose proof (lev_hlam Lv wt lnz ND LR ltac:(intros j Hj; pose proof (leaf_facts j Hj); lia) i Hi) as EL2. unfold hlam in EL2.
    rewrite (lev_ext (fun b => cnt (fun j => lnz j =? b) Lv) a2) in EL2 by exact HL.
    apply (per_leaf a2 v tau (Z.of_nat (length Lv)) (rank Lv wt lnz i) (lev c1h (rank Lv wt lnz i)) (lnz i) (wt i) (cd i) (g_W g) B1 B2 G11 G21 ltac:(lia) Ht GEQ GV1 ltac:(lia) eq_refl (eq_sym EL2) Wi Li RRY).
  -
    intros i Hi. destruct (_ && _); [|lia]. pose proof (rank_range Lv wt lnz ND i Hi) as RR. rewrite NR in RR.
    pose proof (lev_range c1h (rank Lv wt lnz i) B1 ltac:(rewrite G11; lia)) as [LR1 _].
    destruct (Z.eq_dec (lev c1h (rank Lv wt lnz i)) 15) as [E15|N15]; [rewrite E15; unfold sz; cbn; lia|].
    pose proof (sz_facts (lev c1h (rank Lv wt lnz i)) ltac:(lia)). lia.
  -
    rewrite (sum_by_rank Lv wt lnz ND (fun r => if (Gs c1h 15 <=? r) && (r <? Gs c1h (v + 1) + tau) then sz (lev c1h r) else 0)).
    rewrite NR, <- G11. rewrite (block_sum c1h (Gs c1h 1) v tau B1 eq_refl ltac:(lia) ltac:(lia)). unfold Tc. lia.
  -
    pose proof (Tc_nonneg c1h (Z.of_nat (length Lv)) Kx C1OK C1T ltac:(unfold Kx; lia) K1 ltac:(lia) v ltac:(lia)) as T0.
    assert (SZ : sz v <= Z.of_nat (length Lv) - 2) by (unfold sz; lia). pose proof (proj1 (sz_facts v ltac:(lia))) as SP.
    assert (C15 : c1h 15 <= Z.of_nat (length Lv)) by (rewrite <- C1T; apply (zsum_ge_point c1h 1 15 15); [intros; apply B1 | lia]).
    pose proof (ar_total (Tc c1h v) tau (sz v) Kx (c1h 15) (Z.of_nat (length Lv)) T0 STEPS SZ SP ltac:(lia) KC C15). lia.
Qed.

Theorem tree_excess_gen : 540000 * zsum (fun c => W c * hex c (zt_len z c)) 0 (Z.to_nat E) <= g_W g * (540 * SM + 2000 * E).
Proof.
  pose proof nLv as NL.
  assert (W0 : forall i, In i Lv -> 0 <= wt i) by (intros i Hi; pose proof (leaf_facts i Hi); lia).
  assert (FIBd : forall i, In i Lv -> wt i * fib (dp i + 1) <= g_W g).
  { intros i Hi. apply Lv_in' in Hi. destruct Hi as [P L]. pose proof (fib_bound g GG i P). lia. }
  destruct (existsb (fun i => 15 <? dp i) Lv) eqn:OVF.
  - apply existsb_exists in OVF. destruct OVF as (i0 & Hi0 & D0). apply Z.ltb_lt in D0. exact (excess_ov i0 Hi0 D0).
  -
    assert (NOV : forall j, g_pos g j -> g_leaf g j = true -> g_depth g j <= zt_ML z).
    { intros j Pj Lj. rewrite ML15. destruct (Z_lt_le_dec 15 (g_depth g j)) as [D15|D15]; [|exact D15]. exfalso.
      apply Bool.not_true_iff_false in OVF. apply OVF. apply existsb_exists. exists j. split; [apply Lv_in'; auto | apply Z.ltb_lt; exact D15]. }
    apply (bound_from_leaves (fun _ => 0) 0); [| intros; lia | rewrite lsum_zero; lia | pose proof E0; lia].
    intros i Hi. pose proof (leaf_facts i Hi) as (Wi & Di & Li & Ci & Wc).
    assert (EQ : lnz i = dp i).
    { unfold lnz. apply Lv_in' in Hi. destruct Hi as [P L]. exact (zo_len_noovf z ZOK NOV (g_code g i) i ltac:(split; [exact P | split; [exact L | reflexivity]])). }
    rewrite EQ. apply (ar_plain (wt i) (g_W g) (hex (cd i) (dp i)) (M (cd i))).
    apply HR1; [lia| lia |]. exact (FIBd i Hi).
Qed.
End TreeX.

Theorem tree_excess_L (z : ztree) (F : Z -> Z) (Fl : list Z) :
  tree_facts z 286 15 F Fl -> g_W (zt_g z) < fib 24 ->
  540000 * zsum (fun c => ffreq F Fl c * hexL c (zt_len z c)) 0 (Z.to_nat 286)
  <= g_W (zt_g z) * (540 * 1602 + 2000 * 286).
Proof.
  intros TF HW. exact (tree_excess_gen z 286 F Fl hexL MofL 1602 TF ltac:(lia) HW hexL_facts hexL_rarity MofL_nonneg MofL_sum).
Qed.

Theorem tree_excess_D (z : ztree) (F : Z -> Z) (Fl : list Z) :
  tree_facts z 30 15 F Fl -> g_W (zt_g z) < fib 24 ->
  540000 * zsum (fun d => ffreq F Fl d * hexD d (zt_len z d)) 0 (Z.to_nat 30)
  <= g_W (zt_g z) * (540 * 2114 + 2000 * 30).
Proof.
  intros TF HW. exact (tree_excess_gen z 30 F Fl hexD MofD 2114 TF ltac:(lia) HW hexD_facts hexD_rarity MofD_nonneg MofD_sum).
Qed.
