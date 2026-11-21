(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffFib HuffHeap HuffBuild.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import TreeModel BuildTreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import HuffBuild2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Fixpoint ndf (DL : arr) (root : Z) (n : nat) (x : Z) : Z :=
  match n with O => 0 | S n' => if x =? root then 0 else ndf DL root n' (arr_get DL x) + 1 end.

Lemma ndf_S : forall DL root n x, ndf DL root (S n) x = if x =? root then 0 else ndf DL root n (arr_get DL x) + 1.
Proof. reflexivity. Qed.

Section Gen.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr) (BC : arr) (OL SL : Z).
Variables (FC DL HP DP : arr) (sub : Z -> htree).

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation UPl := (UP FC0 t).
Local Notation FPf := (FP FC0 t).
Local Notation uu := (u t FC0).
Local Notation MCv := (MCP FC0 t).
Local Notation ML := (sd_max_length t).

Definition hm : Z := 575 - 2 * uu.
Hypothesis INV : Inv4 t FC0 (uu - 1) FC DL HP 1 hm DP sub.

Definition root : Z := arr_get HP 1.
Definition HP7 : arr := arr_set HP (hm - 1) root.
Definition nd (x : Z) : Z := ndf DL root 574 x.

Lemma u_ge2 : 2 <= uu /\ uu <= elems /\ hm <= 571 /\ 19 <= elems <= 286.
Proof.
  pose proof (pads_facts t FC0) as (_ & _ & U2 & _). pose proof (UP_len_elems t FC0). pose proof (elems_tsize t).
  unfold hm. unfold u in *. lia.
Qed.

Lemma root_val : root = elems + uu - 2.
Proof.
  destruct INV. pose proof u_ge2. destruct (i_int (uu - 1) ltac:(lia)) as (p & Hp & E).
  unfold root. assert (p = 1) by lia. subst p. rewrite E. lia.
Qed.

Lemma HP7v : forall h, arr_get HP7 h = if h =? hm - 1 then root else arr_get HP h.
Proof.
  intros h. destruct INV as [(L1 & L2 & L3 & L4)]. pose proof u_ge2. unfold HP7. rewrite arr_get_set, (Z.eqb_sym (hm - 1) h).
  destruct (Z.eqb_spec h (hm - 1)); cbn [andb]; [|reflexivity]. rewrite inb_true by lia. reflexivity.
Qed.

Lemma HP7_hi : forall h, hm <= h -> arr_get HP7 h = arr_get HP h.
Proof. intros. rewrite HP7v. destruct (Z.eqb_spec h (hm - 1)); [lia| reflexivity]. Qed.

Lemma HP7_root : arr_get HP7 (hm - 1) = root.
Proof. rewrite HP7v, Z.eqb_refl. reflexivity. Qed.

Lemma HP7_inj : forall h h', hm - 1 <= h <= 572 -> hm - 1 <= h' <= 572 -> arr_get HP7 h = arr_get HP7 h' -> h = h'.
Proof.
  intros h h' Hh Hh' E. destruct INV. pose proof u_ge2. rewrite !HP7v in E.
  destruct (Z.eqb_spec h (hm - 1)), (Z.eqb_spec h' (hm - 1)); try lia; unfold root in E.
  - apply i_inj in E; unfold PP; lia.
  - apply i_inj in E; unfold PP; lia.
  - apply i_inj in E; unfold PP; lia.
Qed.

Lemma parent_pos : forall h, hm <= h <= 572 ->
  exists h', hm - 1 <= h' < h /\ arr_get HP7 h' = arr_get DL (arr_get HP7 h).
Proof.
  intros h Hh. destruct INV. pose proof u_ge2 as U. rewrite HP7_hi by lia. rewrite i_dad by lia.
  set (i := (572 - h) / 2 + 1).
  destruct (i_int i ltac:(lia)) as (p & Hp & E).
  replace (elems + (572 - h) / 2) with (elems + i - 1) by lia.
  destruct Hp as [Hp|Hp].
  - exists (hm - 1). split; [lia|]. rewrite HP7_root. unfold root. replace p with 1 in E by lia. exact E.
  - exists p. split; [lia|]. rewrite HP7_hi by lia. exact E.
Qed.

Lemma ids_range : forall h, hm - 1 <= h <= 572 -> 0 <= arr_get HP7 h < elems + uu - 1 /\ (arr_get HP7 h < elems <-> In (arr_get HP7 h) UPl).
Proof.
  intros h Hh. destruct INV. pose proof u_ge2. pose proof (pads_facts t FC0) as (_ & RNGU & _). rewrite HP7v.
  destruct (Z.eqb_spec h (hm - 1)).
  - unfold root. destruct (i_rng 1 ltac:(unfold PP; lia)) as [[A B]|A]; (split; [lia|]); split; auto; intros; try lia.
    apply RNGU in H0. lia.
  - destruct (i_rng h ltac:(unfold PP; lia)) as [[A B]|A]; (split; [lia|]); split; auto; intros; try lia.
    apply RNGU in H0. lia.
Qed.

Lemma root_internal : elems <= root.
Proof. rewrite root_val. pose proof u_ge2. lia. Qed.

Lemma ndf_stable : forall j h, hm - 1 <= h <= 572 -> (Z.to_nat (h - (hm - 1)) <= j)%nat ->
  forall n, (j < n)%nat -> ndf DL root n (arr_get HP7 h) = ndf DL root (S j) (arr_get HP7 h).
Proof.
  induction j as [|j IH]; intros h Hh Hj n Hn.
  - assert (h = hm - 1) by lia. subst h. rewrite HP7_root. destruct n; [lia|]. rewrite !ndf_S. rewrite Z.eqb_refl. reflexivity.
  - destruct n as [|n]; [lia|]. rewrite !ndf_S.
    destruct (Z.eqb_spec (arr_get HP7 h) root); [reflexivity|].
    assert (h <> hm - 1) by (intros ->; rewrite HP7_root in n0; congruence).
    destruct (parent_pos h ltac:(lia)) as (h' & Hh' & E). rewrite <- E.
    rewrite (IH h' ltac:(lia) ltac:(lia) n ltac:(lia)). reflexivity.
Qed.

Lemma nd_root : nd root = 0.
Proof. unfold nd. rewrite ndf_S. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma nd_step : forall h, hm <= h <= 572 ->
  nd (arr_get HP7 h) = nd (arr_get DL (arr_get HP7 h)) + 1.
Proof.
  intros h Hh. pose proof u_ge2. unfold nd. rewrite (ndf_S DL root 573).
  destruct (Z.eqb_spec (arr_get HP7 h) root).
  { exfalso. rewrite <- HP7_root in e. apply HP7_inj in e; lia. }
  destruct (parent_pos h Hh) as (h' & Hh' & E). rewrite <- E.
  rewrite (ndf_stable 572 h' ltac:(lia) ltac:(unfold hm in *; unfold u in *; lia) 574%nat ltac:(lia)). reflexivity.
Qed.

Lemma nd_nonneg : forall h, hm - 1 <= h <= 572 -> 0 <= nd (arr_get HP7 h) /\ (hm <= h -> 1 <= nd (arr_get HP7 h)).
Proof.
  intros h. remember (Z.to_nat (h - (hm - 1))) as j eqn:Ej. revert h Ej.
  induction j as [j IH] using (well_founded_induction Wf_nat.lt_wf); intros h Ej Hh.
  destruct (Z.eq_dec h (hm - 1)) as [->|].
  - rewrite HP7_root, nd_root. lia.
  - destruct (parent_pos h ltac:(lia)) as (h' & Hh' & E). rewrite nd_step by lia. rewrite <- E.
    destruct (IH (Z.to_nat (h' - (hm - 1))) ltac:(lia) h' eq_refl ltac:(lia)). lia.
Qed.

Lemma chain_nd : forall a d, 
  (forall i, (i < d)%nat -> up DL i a < up DL (S i) a /\ exists h, hm <= h <= 572 /\ arr_get HP h = up DL i a) ->
  up DL d a = root -> nd a = Z.of_nat d.
Proof.
  intros a d CH E.
  assert (G : forall r, (r <= d)%nat -> nd (up DL (d - r) a) = Z.of_nat r).
  { induction r as [|r IH]; intros Hr.
    - rewrite Nat.sub_0_r, E. apply nd_root.
    - destruct (CH (d - S r)%nat ltac:(lia)) as (LT & h & Hh & Eh).
      rewrite <- Eh. rewrite <- HP7_hi by lia. rewrite nd_step by lia. rewrite HP7_hi by lia. rewrite Eh.
      change (arr_get DL (up DL (d - S r) a)) with (up DL (S (d - S r)) a).
      replace (S (d - S r)) with (d - r)%nat by lia. rewrite IH by lia. lia. }
  specialize (G d ltac:(lia)). rewrite Nat.sub_diag in G. exact G.
Qed.

Definition T : htree := sub root.

Lemma T_build : hbuild (F0 t FC0) T.
Proof.
  destruct INV. apply i_hb. change (Z.to_nat 1) with 1%nat. cbn. fold root. apply HB_one.
Qed.

Lemma T_prof : forall e, In e (hprof 0 T) -> In (ea e) UPl /\ nd (ea e) = ed e /\ 1 <= ed e.
Proof.
  intros e He. destruct INV. pose proof u_ge2.
  destruct (i_sub 1 ltac:(unfold PP; lia)) as (W & M & FL & FN & CH). fold root in FL, FN, CH |- *.
  destruct (CH e He) as (A1 & A2 & A3 & A4). split; [exact A1|].
  rewrite (chain_nd (ea e) (Z.to_nat (ed e)) A4 A3). split; [lia|].
  destruct (FN root_internal) as (l & r & ET). unfold T in He. rewrite ET in He. cbn [hprof] in He.
  apply in_app_iff in He. destruct He as [He|He]; apply hprof_dep in He; lia.
Qed.

Lemma T_leaves : Permutation (map ea (hprof 0 T)) UPl /\ forall e, In e (hprof 0 T) -> ew e = FPf (ea e).
Proof.
  pose proof (hbuild_leaves_w _ _ T_build) as P0.
  pose proof (hbuild_leaves _ _ T_build) as P1.
  assert (LF : leaf_forest (F0 t FC0)).
  { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). exact I. }
  rewrite (leaf_forest_flat _ LF) in P1. unfold F0 in P1. rewrite map_map in P1. cbn in P1.
  split.
  - pose proof (Permutation_map snd P1) as P2. rewrite !map_map in P2. cbn in P2. rewrite map_id in P2. exact P2.
  - intros e He. pose proof (Permutation_in (wa e) P1 ltac:(apply in_map; exact He)) as Hin.
    apply in_map_iff in Hin. destruct Hin as (j & Ej & Hj). unfold wa in Ej. injection Ej as <- <-. reflexivity.
Qed.



Definition Ld (h : Z) : Z := Z.min (nd (arr_get HP7 h)) ML.
Definition leafp (h : Z) : bool := negb (MCv <? arr_get HP7 h).
Local Notation xb := (xbits t).
Definition cntf (b h : Z) : Z := if leafp h && (Ld h =? b) then 1 else 0.
Definition olf (h : Z) : Z := if leafp h then arr_get FC (arr_get HP7 h) * (Ld h + xb (arr_get HP7 h)) else 0.
Definition slf (h : Z) : Z := if leafp h then arr_get FC (arr_get HP7 h) * (stree_Len t (arr_get HP7 h) + xb (arr_get HP7 h)) else 0.
Definition ovff (h : Z) : Z := if ML <? nd (arr_get HP7 h) then 1 else 0.
Definition rng (h : Z) : list Z := ziota hm (Z.to_nat (h - hm)).
Definition SUM (f : Z -> Z) (h : Z) : Z := zsum (map f (rng h)).

Lemma ML_range : 7 <= ML <= 15.
Proof. destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS; lia. Qed.

Lemma MC_facts : 0 <= MCv < elems /\ forall h, hm - 1 <= h <= 572 -> (leafp h = true <-> arr_get HP7 h < elems).
Proof.
  pose proof (pads_facts t FC0) as (NDU & RNGU & U2 & PD & MX1 & MX2). pose proof (RNGU _ MX2).
  split; [lia|]. intros h Hh. unfold leafp. rewrite Bool.negb_true_iff, Z.ltb_ge.
  destruct (ids_range h Hh) as [R [A B]]. split.
  - intros. destruct (Z_lt_le_dec (arr_get HP7 h) elems); [assumption|]. lia.
  - intros. apply MX1. apply A. assumption.
Qed.

Lemma rng_snoc : forall h, hm <= h -> rng (h + 1) = rng h ++ [h].
Proof.
  intros h Hh. unfold rng. replace (Z.to_nat (h + 1 - hm)) with (S (Z.to_nat (h - hm))) by lia.
  rewrite ziota_S_r. f_equal. f_equal. lia.
Qed.
Lemma SUM_snoc : forall f h, hm <= h -> SUM f (h + 1) = SUM f h + f h.
Proof. intros. unfold SUM. rewrite rng_snoc, map_app, zsum_app by assumption. cbn. lia. Qed.
Lemma SUM_hm : forall f, SUM f hm = 0.
Proof. intros. unfold SUM, rng. rewrite Z.sub_diag. reflexivity. Qed.
Lemma SUM_bound : forall f h, hm <= h -> (forall x, 0 <= f x <= 1) -> 0 <= SUM f h <= h - hm.
Proof.
  intros f h Hh Hf. replace h with (hm + Z.of_nat (Z.to_nat (h - hm))) by lia.
  induction (Z.to_nat (h - hm)) as [|n IH].
  - rewrite Z.add_0_r, SUM_hm. lia.
  - rewrite Nat2Z.inj_succ. replace (hm + Z.succ (Z.of_nat n)) with (hm + Z.of_nat n + 1) by lia.
    rewrite SUM_snoc by lia. pose proof (Hf (hm + Z.of_nat n)). lia.
Qed.

Lemma nd_chain : forall a d,
  (forall i, (i < d)%nat -> exists h, hm <= h <= 572 /\ arr_get HP h = up DL i a) ->
  nd a = nd (up DL d a) + Z.of_nat d.
Proof.
  intros a d CH. induction d as [|d IH]; [cbn; lia|].
  rewrite IH by (intros; apply CH; lia). destruct (CH d ltac:(lia)) as (h & Hh & Eh).
  cbn [up]. rewrite <- Eh, <- HP7_hi by lia. rewrite (nd_step h) by lia. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma nd_sub : forall h e, hm - 1 <= h <= 572 -> In e (hprof 0 (sub (arr_get HP7 h))) ->
  In (ea e) UPl /\ 0 <= ed e /\ nd (ea e) = nd (arr_get HP7 h) + ed e.
Proof.
  intros h e Hh He. destruct INV. pose proof u_ge2.
  assert (Hp : exists p, PP 1 hm p /\ arr_get HP p = arr_get HP7 h).
  { rewrite HP7v. destruct (Z.eqb_spec h (hm - 1)); [exists 1; unfold PP, root; split; [lia|reflexivity]|].
    exists h. unfold PP. split; [lia| reflexivity]. }
  destruct Hp as (p & Hp & Ep). rewrite <- Ep in He |- *.
  destruct (i_sub p Hp) as (W & M & FL & FN & CH). destruct (CH e He) as (A1 & A2 & A3 & A4).
  split; [exact A1|]. split; [exact A2|].
  rewrite (nd_chain (ea e) (Z.to_nat (ed e))), A3; [lia|].
  intros i Hi. destruct (A4 i Hi) as (_ & h' & Hh' & Eh'). exists h'. auto.
Qed.

Lemma ovff_01 : forall h, 0 <= ovff h <= 1.
Proof. intros. unfold ovff. destruct (ML <? _); lia. Qed.

Lemma no_overflow_iff : SUM ovff 573 = 0 <-> (forall e, In e (hprof 0 T) -> ed e <= ML).
Proof.
  pose proof u_ge2 as U.
  assert (ALL : forall h, hm <= h <= 573 -> SUM ovff h = 0 <-> forall h', hm <= h' < h -> nd (arr_get HP7 h') <= ML).
  { intros h Hh. replace h with (hm + Z.of_nat (Z.to_nat (h - hm))) by lia.
    induction (Z.to_nat (h - hm)) as [|n IH].
    - rewrite Z.add_0_r, SUM_hm. split; [intros; lia| reflexivity].
    - rewrite Nat2Z.inj_succ. replace (hm + Z.succ (Z.of_nat n)) with (hm + Z.of_nat n + 1) by lia.
      rewrite SUM_snoc by lia. pose proof (SUM_bound ovff (hm + Z.of_nat n) ltac:(lia) ovff_01). pose proof (ovff_01 (hm + Z.of_nat n)).
      split.
      + intros Hs h' Hh'. assert (SUM ovff (hm + Z.of_nat n) = 0 /\ ovff (hm + Z.of_nat n) = 0) as [S1 S2] by lia.
        destruct (Z.eq_dec h' (hm + Z.of_nat n)) as [->|].
        * unfold ovff in S2. destruct (Z.ltb_spec ML (nd (arr_get HP7 (hm + Z.of_nat n)))); lia.
        * apply (proj1 IH S1). lia.
      + intros Hn. rewrite (proj2 IH) by (intros; apply Hn; lia). unfold ovff.
        destruct (Z.ltb_spec ML (nd (arr_get HP7 (hm + Z.of_nat n)))); [|lia]. specialize (Hn (hm + Z.of_nat n) ltac:(lia)). lia. }
  rewrite (ALL 573) by lia. split.
  - intros Hn e He. destruct (T_prof e He) as (A1 & A2 & A3).
    destruct INV. destruct (i_leaf (ea e) A1) as (p & Hp & Ep).
    pose proof (pads_facts t FC0) as (_ & RNGU & _). pose proof (RNGU _ A1). pose proof root_internal as RI. unfold root in RI.
    assert (hm <= p <= 572) by (unfold PP in Hp; destruct Hp; [replace p with 1 in Ep by lia; rewrite Ep in RI; lia| lia]).
    rewrite <- A2, <- Ep, <- HP7_hi by lia. apply Hn. lia.
  - intros He h' Hh'. unfold T in He.
    destruct INV. pose proof (i_sub h' ltac:(unfold PP; lia)) as SK. rewrite <- HP7_hi in SK by lia.
    destruct SK as (W & M & FL & FN & CH).
    destruct (hprof 0 (sub (arr_get HP7 h'))) as [|e l] eqn:EP; [exfalso; exact (hprof_nonnil _ _ EP)|].
    destruct (nd_sub h' e ltac:(lia) ltac:(rewrite EP; now left)) as (B1 & B2 & B3).
    destruct T_leaves as [PT WT].
    assert (Hin : In (ea e) (map ea (hprof 0 (sub root)))) by (apply (Permutation_in _ (Permutation_sym PT)); exact B1).
    apply in_map_iff in Hin. destruct Hin as (e' & Ee & He').
    destruct (T_prof e' He') as (C1 & C2 & C3). rewrite Ee in C2. specialize (He e' He'). lia.
Qed.

Lemma NoDup_map_on : forall (g : Z -> Z) (l : list Z),
  NoDup l -> (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (map g l).
Proof.
  intros g l ND INJ. induction ND as [|x l Hx ND IH]; cbn; constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & E & Hy).
    assert (y = x) by (apply INJ; cbn; auto). subst. contradiction.
  - apply IH. intros a b Ha Hb. apply INJ; cbn; auto.
Qed.

Lemma leaf_positions : Permutation (map (arr_get HP7) (filter leafp (rng 573))) UPl.
Proof.
  pose proof u_ge2 as U. pose proof (pads_facts t FC0) as (NDU & RNGU & _). pose proof MC_facts as [MCr LF].
  apply NoDup_Permutation.
  - apply NoDup_map_on.
    + apply NoDup_filter. apply NoDup_ziota.
    + intros x y Hx Hy E. apply filter_In in Hx. apply filter_In in Hy. destruct Hx as [Hx _], Hy as [Hy _].
      unfold rng in Hx, Hy. apply in_ziota in Hx. apply in_ziota in Hy. apply HP7_inj; lia.
  - exact NDU.
  - intros x. rewrite in_map_iff. split.
    + intros (h & <- & Hh). apply filter_In in Hh. destruct Hh as [Hh Lh]. unfold rng in Hh. apply in_ziota in Hh.
      apply (proj1 (LF h ltac:(lia))) in Lh. apply (proj2 (ids_range h ltac:(lia))). exact Lh.
    + intros Hx. destruct INV. destruct (i_leaf x Hx) as (p & Hp & Ep). pose proof (RNGU _ Hx). pose proof root_internal as RI. unfold root in RI.
      assert (hm <= p <= 572) by (unfold PP in Hp; destruct Hp; [replace p with 1 in Ep by lia; rewrite Ep in RI; lia| lia]).
      exists p. rewrite HP7_hi by lia. split; [exact Ep|]. apply filter_In. split; [unfold rng; apply in_ziota; lia|].
      apply (proj2 (LF p ltac:(lia))). rewrite HP7_hi by lia. rewrite Ep. lia.
Qed.

Lemma zsum_filter_map : forall (p : Z -> bool) (g : Z -> Z) l,
  zsum (map (fun h => if p h then g h else 0) l) = zsum (map g (filter p l)).
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (p x); cbn; rewrite IH; lia. Qed.

Lemma SUM_leaves : forall (g : Z -> Z) (f : Z -> Z),
  (forall h, hm <= h <= 572 -> leafp h = true -> f h = g (arr_get HP7 h)) ->
  (forall h, hm <= h <= 572 -> leafp h = false -> f h = 0) ->
  SUM f 573 = zsum (map g UPl).
Proof.
  intros g f Hl Hi. unfold SUM.
  transitivity (zsum (map (fun h => if leafp h then g (arr_get HP7 h) else 0) (rng 573))).
  - apply zsum_map_ext. intros h Hh. unfold rng in Hh. apply in_ziota in Hh.
    destruct (leafp h) eqn:E; [apply Hl; lia || exact E| apply Hi; lia || exact E].
  - rewrite zsum_filter_map. rewrite <- (zsum_map_perm g _ _ leaf_positions). rewrite map_map. reflexivity.
Qed.

Theorem leaf_depths :
  Permutation (map (fun e => (ea e, ed e)) (hprof 0 T)) (map (fun j => (j, nd j)) UPl)
  /\ Permutation (map (fun e => (ea e, ew e)) (hprof 0 T)) (map (fun j => (j, FPf j)) UPl).
Proof.
  destruct T_leaves as [PT WT].
  split.
  - transitivity (map (fun j => (j, nd j)) (map ea (hprof 0 T))); [|apply Permutation_map; exact PT].
    rewrite map_map. erewrite map_ext_in; [apply Permutation_refl|]. intros e He. cbn beta.
    destruct (T_prof e He) as (_ & <- & _). reflexivity.
  - transitivity (map (fun j => (j, FPf j)) (map ea (hprof 0 T))); [|apply Permutation_map; exact PT].
    rewrite map_map. erewrite map_ext_in; [apply Permutation_refl|]. intros e He. cbn beta. rewrite (WT e He). reflexivity.
Qed.

Hypothesis LBC : arr_len BC = 16.
Hypothesis OLr : 0 <= OL < 2 ^ 64.
Hypothesis SLr : 0 <= SL < 2 ^ 64.

Local Notation X6 DLc BCc OLc SLc := (bt_upd s t FC DLc HP7 1 (hm - 1) DP BCc OLc SLc MCv).

Record GI (h : Z) (DLc BCc : arr) (OLc SLc ovc : Z) : Prop := GIc {
  g_len : arr_len DLc = tsize t /\ arr_len BCc = 16;
  g_done : forall h', hm - 1 <= h' < h -> arr_get DLc (arr_get HP7 h') = Ld h';
  g_todo : forall h', h <= h' <= 572 -> arr_get DLc (arr_get HP7 h') = arr_get DL (arr_get HP7 h');
  g_zero : forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLc j = 0;
  g_bc : forall b, 0 <= b <= 15 -> arr_get BCc b = SUM (cntf b) h;
  g_ol : OLc = wrap64 (OL + SUM olf h);
  g_sl : SLc = (if stree_has t then wrap64 (SL + SUM slf h) else SL);
  g_ov : ovc = SUM ovff h }.

Lemma Ld_root : Ld (hm - 1) = 0.
Proof. unfold Ld. rewrite HP7_root, nd_root. pose proof ML_range. lia. Qed.

Lemma Ld_range : forall h, hm <= h <= 572 -> 1 <= Ld h <= ML.
Proof. intros h Hh. unfold Ld. destruct (nd_nonneg h ltac:(lia)). pose proof ML_range. lia. Qed.

Lemma gb_step : forall h DLc BCc OLc SLc ovc, hm <= h <= 572 -> GI h DLc BCc OLc SLc ovc ->
  exists DLc' BCc' OLc' SLc' ovc', GB1 t MCv (X6 DLc BCc OLc SLc) h ovc = (X6 DLc' BCc' OLc' SLc', ovc')
    /\ GI (h + 1) DLc' BCc' OLc' SLc' ovc'.
Proof.
  intros h DLc BCc OLc SLc ovc Hh G. destruct G as [[LDLc LBCc] DONE TODO ZERO GBC GOL GSL GOV].
  pose proof u_ge2 as U. pose proof ML_range as MLr. pose proof (elems_tsize t) as ET. destruct INV as [(L1 & L2 & L3 & L4)].
  pose proof (GB1_flat t MCv s FC DLc HP7 1 (hm - 1) DP BCc OLc SLc h ovc) as E. cbv zeta in E. rewrite E. clear E.
  destruct (parent_pos h Hh) as (hp & Hhp & Ep).
  pose proof (nd_step h Hh) as ND. rewrite <- Ep in ND.
  rewrite (TODO h ltac:(lia)), <- Ep, (DONE hp ltac:(lia)).
  pose proof (ids_range h ltac:(lia)) as [IR IL].
  assert (Hbits : (if ML <? Ld hp + 1 then ML else Ld hp + 1) = Ld h /\ ((ML <? Ld hp + 1) = (ML <? nd (arr_get HP7 h)))).
  { unfold Ld in *. rewrite ND.
    assert (0 <= nd (arr_get HP7 hp)).
    { destruct (Z.eq_dec hp (hm - 1)) as [->|]; [rewrite HP7_root, nd_root; lia|]. destruct (nd_nonneg hp ltac:(lia)); lia. }
    destruct (Z.ltb_spec ML (Z.min (nd (arr_get HP7 hp)) ML + 1)); destruct (Z.ltb_spec ML (nd (arr_get HP7 hp) + 1)); split; try lia; reflexivity. }
  destruct Hbits as [HB1 HB2]. rewrite HB1.
  replace (if ML <? Ld hp + 1 then ovc + 1 else ovc) with (ovc + ovff h) by (unfold ovff; rewrite <- HB2; destruct (ML <? Ld hp + 1); lia).
  pose proof (Ld_range h Hh) as LR.
  assert (W16 : wrap16 (Ld h) = Ld h) by (apply wrap16_id; lia).
  rewrite W16.
  pose proof MC_facts as [MCr LF].
  assert (DL'ok : forall DLn, DLn = arr_set DLc (arr_get HP7 h) (Ld h) ->
            arr_len DLn = tsize t /\ (forall h', hm - 1 <= h' < h + 1 -> arr_get DLn (arr_get HP7 h') = Ld h')
            /\ (forall h', h + 1 <= h' <= 572 -> arr_get DLn (arr_get HP7 h') = arr_get DL (arr_get HP7 h'))
            /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLn j = 0)).
  { intros DLn ->. rewrite arr_len_set. split; [exact LDLc|]. split; [|split].
    - intros h' Hh'. rewrite arr_get_set. unfold arr_inb. rewrite LDLc.
      destruct (Z.eqb_spec (arr_get HP7 h) (arr_get HP7 h')).
      + apply HP7_inj in e; try lia. subst h'. cbn [andb]. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      + cbn [andb]. apply DONE. assert (h' <> h) by congruence. lia.
    - intros h' Hh'. rewrite arr_get_set. destruct (Z.eqb_spec (arr_get HP7 h) (arr_get HP7 h')); [apply HP7_inj in e; lia|]. cbn [andb]. apply TODO. lia.
    - intros j Hj Hnj. rewrite arr_get_set. destruct (Z.eqb_spec (arr_get HP7 h) j); [|cbn [andb]; apply ZERO; assumption].
      exfalso. apply Hnj. rewrite <- e. apply (proj1 IL). lia. }
  destruct (Z.ltb_spec MCv (arr_get HP7 h)) as [INTERNAL|LEAF].
  -
    assert (NL : leafp h = false) by (unfold leafp; apply Bool.negb_false_iff; apply Z.ltb_lt; exact INTERNAL).
    eexists _, _, _, _, _. split; [reflexivity|].
    destruct (DL'ok _ eq_refl) as (A1 & A2 & A3 & A4).
    split; [split; assumption| exact A2| exact A3| exact A4| | | |].
    + intros b Hb. rewrite SUM_snoc by lia. unfold cntf at 2. rewrite NL. cbn [andb]. rewrite GBC by lia. lia.
    + rewrite SUM_snoc by lia. unfold olf at 2. rewrite NL, Z.add_0_r. exact GOL.
    + rewrite SUM_snoc by lia. unfold slf at 2. rewrite NL, Z.add_0_r. exact GSL.
    + rewrite SUM_snoc by lia. lia.
  -
    assert (YL : leafp h = true) by (unfold leafp; apply Bool.negb_true_iff; apply Z.ltb_ge; exact LEAF).
    eexists _, _, _, _, _. split; [reflexivity|].
    destruct (DL'ok _ eq_refl) as (A1 & A2 & A3 & A4).
    pose proof (SUM_bound (cntf (Ld h)) h ltac:(lia) ltac:(intros; unfold cntf; destruct (_ && _); lia)) as SB.
    split; [split; [assumption| rewrite arr_len_set; exact LBCc]| exact A2| exact A3| exact A4| | | |].
    + intros b Hb. rewrite SUM_snoc by lia. rewrite arr_get_set. unfold arr_inb. rewrite LBCc.
      rewrite GBC by lia. unfold cntf at 3. rewrite YL. cbn [andb].
      destruct (Z.eqb_spec (Ld h) b).
      * subst b. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb]. rewrite wrap16_id by lia. reflexivity.
      * cbn [andb]. rewrite GBC by lia. lia.
    + rewrite SUM_snoc, GOL by lia. rewrite BuildTreeModel.wrap64_add_l. f_equal. unfold olf. rewrite YL. lia.
    + rewrite SUM_snoc, GSL by lia. destruct (stree_has t); [|reflexivity]. rewrite BuildTreeModel.wrap64_add_l. f_equal. unfold slf. rewrite YL. lia.
    + rewrite SUM_snoc by lia. lia.
Qed.

Lemma gb_loop1 : forall f h DLc BCc OLc SLc ovc, hm <= h <= 573 -> (Z.to_nat (573 - h) <= f)%nat ->
  GI h DLc BCc OLc SLc ovc ->
  exists DLc' BCc' OLc' SLc' ovc',
    gen_bitlen_loop1 f (X6 DLc BCc OLc SLc) t MCv (sd_extra_base t) ML h ovc = (X6 DLc' BCc' OLc' SLc', ovc')
    /\ GI 573 DLc' BCc' OLc' SLc' ovc'.
Proof.
  induction f as [|f IH]; intros h DLc BCc OLc SLc ovc Hh Hf G.
  - assert (h = 573) by lia. subst h. eexists _, _, _, _, _. split; [reflexivity| exact G].
  - rewrite GL1_step. unfold HEAP_SIZE. destruct (Z.ltb_spec h 573).
    + destruct (gb_step h DLc BCc OLc SLc ovc ltac:(lia) G) as (DL1 & BC1 & OL1 & SL1 & ov1 & E1 & G1).
      rewrite E1. apply IH; [lia| lia| exact G1].
    + assert (h = 573) by lia. subst h. eexists _, _, _, _, _. split; [reflexivity| exact G].
Qed.

Lemma GI_start : GI hm (arr_set DL root (wrap16 0)) (arr_fill BC 0 (MAX_BITS + 1) 0) OL SL 0.
Proof.
  destruct INV as [(L1 & L2 & L3 & L4) HK HOK HINJ HRNG HLEAF HINT HDAD HFC HWS HWO HWH HSUB HHB HDL0].
  pose proof u_ge2 as U. pose proof (elems_tsize t) as ET.
  split.
  - rewrite arr_len_set. split; [exact L2|]. rewrite arr_len_fill. exact LBC.
  - intros h' Hh'. assert (h' = hm - 1) by lia. subst h'. rewrite HP7_root, Ld_root.
    rewrite arr_get_set. unfold arr_inb. rewrite L2. pose proof root_internal. rewrite root_val in *.
    rewrite Z.eqb_refl, (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - intros h' Hh'. rewrite arr_get_set. destruct (Z.eqb_spec root (arr_get HP7 h')); [|reflexivity].
    exfalso. rewrite <- HP7_root in e. apply HP7_inj in e; lia.
  - intros j Hj Hnj. rewrite arr_get_set. destruct (Z.eqb_spec root j); [pose proof root_internal; lia|]. cbn [andb]. apply HDL0; assumption.
  - intros b Hb. rewrite SUM_hm. rewrite arr_get_fill. unfold arr_inb, MAX_BITS. rewrite LBC.
    replace ((0 <=? b) && (b <? 0 + Z.max 0 (15 + 1)) && ((0 <=? b) && (b <? 16))) with true; [reflexivity|].
    symmetry. rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
  - rewrite SUM_hm, Z.add_0_r. symmetry. apply wrap64_id. exact OLr.
  - rewrite SUM_hm, Z.add_0_r. destruct (stree_has t); [|reflexivity]. symmetry. apply wrap64_id. exact SLr.
  - rewrite SUM_hm. reflexivity.
Qed.



Local Notation X7 := (bt_upd s t FC DL HP7 1 (hm - 1) DP BC OL SL MCv).

Theorem gen_bitlen_pass1 : exists DLc BCc OLc SLc ovc,
  GI 573 DLc BCc OLc SLc ovc /\
  gen_bitlen X7 t =
    (if ovc =? 0 then X6 DLc BCc OLc SLc
     else gen_bitlen_loop3 (Z.to_nat ML) (gen_bitlen_loop2 573 (X6 DLc BCc OLc SLc) ML ovc) t MCv ML HEAP_SIZE).
Proof.
  pose proof u_ge2 as U.
  destruct (gb_loop1 573 hm _ _ _ _ _ ltac:(unfold hm in *; lia) ltac:(unfold hm in *; lia) GI_start) as (DLc & BCc & OLc & SLc & ovc & E & G).
  exists DLc, BCc, OLc, SLc, ovc. split; [exact G|].
  unfold gen_bitlen. autorewrite with btupd. rewrite HP7_root. replace (hm - 1 + 1) with hm by lia.
  rewrite E. reflexivity.
Qed.

Theorem pass1_summary : forall DLc BCc OLc SLc ovc, GI 573 DLc BCc OLc SLc ovc ->
  (forall j, In j UPl -> arr_get DLc j = Z.min (nd j) ML)
  /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLc j = 0)
  /\ (forall b, 0 <= b <= 15 -> arr_get BCc b = zsum (map (fun j => if Z.min (nd j) ML =? b then 1 else 0) UPl))
  /\ OLc = wrap64 (OL + zsum (map (fun j => FPf j * (Z.min (nd j) ML + xb j)) UPl))
  /\ SLc = (if stree_has t then wrap64 (SL + zsum (map (fun j => FPf j * (stree_Len t j + xb j)) UPl)) else SL)
  /\ (ovc = 0 <-> forall e, In e (hprof 0 T) -> ed e <= ML)
  /\ arr_len DLc = tsize t /\ arr_len BCc = 16.
Proof.
  intros DLc BCc OLc SLc ovc G. destruct G as [[LDLc LBCc] DONE TODO ZERO GBC GOL GSL GOV].
  pose proof u_ge2 as U. pose proof (pads_facts t FC0) as (NDU & RNGU & _). pose proof MC_facts as [MCr LF].
  assert (FCj : forall h, hm <= h <= 572 -> leafp h = true -> arr_get FC (arr_get HP7 h) = FPf (arr_get HP7 h)).
  { intros h Hh Lh. destruct INV. apply i_fc. apply LF in Lh; [|lia]. pose proof (ids_range h ltac:(lia)). lia. }
  split.
  { intros j Hj. destruct INV. destruct (i_leaf j Hj) as (p & Hp & Ep). pose proof (RNGU _ Hj). pose proof root_internal as RI. unfold root in RI.
    assert (hm <= p <= 572) by (unfold PP in Hp; destruct Hp; [replace p with 1 in Ep by lia; rewrite Ep in RI; lia| lia]).
    rewrite <- Ep, <- HP7_hi by lia. rewrite DONE by lia. reflexivity. }
  split; [exact ZERO|].
  split.
  { intros b Hb. rewrite GBC by lia. apply SUM_leaves.
    - intros h Hh Lh. unfold cntf. rewrite Lh. reflexivity.
    - intros h Hh Lh. unfold cntf. rewrite Lh. reflexivity. }
  split.
  { rewrite GOL. f_equal. f_equal. apply SUM_leaves.
    - intros h Hh Lh. unfold olf. rewrite Lh, FCj by assumption. reflexivity.
    - intros h Hh Lh. unfold olf. rewrite Lh. reflexivity. }
  split.
  { rewrite GSL. destruct (stree_has t); [|reflexivity]. f_equal. f_equal. apply SUM_leaves.
    - intros h Hh Lh. unfold slf. rewrite Lh, FCj by assumption. reflexivity.
    - intros h Hh Lh. unfold slf. rewrite Lh. reflexivity. }
  split; [rewrite GOV; apply no_overflow_iff|].
  split; assumption.
Qed.

End Gen.
