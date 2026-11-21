(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild HuffBuild2 HuffSpec HuffFlush HuffSend DeflRoom OverlayFBS OverlayRace OverlayCmp DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel ScanModel SendModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma xbits_TB : forall y, 0 <= y < 19 -> xbits TB y = blx y.
Proof.
  intros y Hy. unfold xbits, blx, REP_3_6, REPZ_3_10, REPZ_11_138. cbn [sd_extra_base sd_extra_bits]. rewrite Z.sub_0_r.
  replace (0 <=? y) with true by (symmetry; apply Z.leb_le; lia).
  assert (T : forall k, (k < 19)%nat -> arr_get extra_blbits_a (Z.of_nat k) = (if Z.of_nat k =? 16 then 2 else if Z.of_nat k =? 17 then 3 else if Z.of_nat k =? 18 then 7 else 0)).
  { intros k Hk. do 19 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
  specialize (T (Z.to_nat y) ltac:(lia)). rewrite Z2Nat.id in T by lia. exact T.
Qed.

Lemma xbits_TL : forall j, xbits TL j = if 257 <=? j then arr_get extra_lbits_a (j - 257) else 0.
Proof. intros j. unfold xbits. cbn [sd_extra_base sd_extra_bits]. unfold LITERALS. reflexivity. Qed.

Lemma xbits_TD : forall i, 0 <= i -> xbits TD i = arr_get extra_dbits_a i.
Proof. intros i Hi. unfold xbits. cbn [sd_extra_base sd_extra_bits]. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r. reflexivity. Qed.

Lemma extra_lbits_range : forall c, 0 <= c <= 28 -> 0 <= arr_get extra_lbits_a c <= 5.
Proof. intros c Hc. exact (table_range extra_lbits_a 0 5 29 ltac:(vm_compute; reflexivity) c ltac:(lia)). Qed.
Lemma extra_dbits_range : forall i, 0 <= i <= 29 -> 0 <= arr_get extra_dbits_a i <= 13.
Proof. intros i Hi. exact (table_range extra_dbits_a 0 13 30 ltac:(vm_compute; reflexivity) i ltac:(lia)). Qed.

Lemma static_ltree_len : forall j, 0 <= j < 288 ->
  arr_get static_ltree_dl j = (if j <? 144 then 8 else if j <? 256 then 9 else if j <? 280 then 7 else 8).
Proof.
  intros j Hj.
  pose proof (table_range static_ltree_dl 8 8 144 ltac:(vm_compute; reflexivity)) as A.
  assert (B : forall k, 144 <= k < 256 -> arr_get static_ltree_dl k = 9).
  { intros k Hk. pose proof (proj1 (forallb_forall (fun i => arr_get static_ltree_dl i =? 9) (ziota 144 112)) ltac:(vm_compute; reflexivity) k) as X.
    specialize (X ltac:(apply in_ziota; lia)). cbn beta in X. apply Z.eqb_eq in X. exact X. }
  assert (C : forall k, 256 <= k < 280 -> arr_get static_ltree_dl k = 7).
  { intros k Hk. pose proof (proj1 (forallb_forall (fun i => arr_get static_ltree_dl i =? 7) (ziota 256 24)) ltac:(vm_compute; reflexivity) k) as X.
    specialize (X ltac:(apply in_ziota; lia)). cbn beta in X. apply Z.eqb_eq in X. exact X. }
  assert (D : forall k, 280 <= k < 288 -> arr_get static_ltree_dl k = 8).
  { intros k Hk. pose proof (proj1 (forallb_forall (fun i => arr_get static_ltree_dl i =? 8) (ziota 280 8)) ltac:(vm_compute; reflexivity) k) as X.
    specialize (X ltac:(apply in_ziota; lia)). cbn beta in X. apply Z.eqb_eq in X. exact X. }
  destruct (Z.ltb_spec j 144); [specialize (A j ltac:(lia)); lia|].
  destruct (Z.ltb_spec j 256); [apply B; lia|]. destruct (Z.ltb_spec j 280); [apply C; lia| apply D; lia].
Qed.

Lemma static_dtree_len : forall i, 0 <= i < 30 -> arr_get static_dtree_dl i = 5.
Proof. intros i Hi. pose proof (table_range static_dtree_dl 5 5 30 ltac:(vm_compute; reflexivity) i ltac:(lia)). lia. Qed.

Definition scost (x : Z * Z) : Z :=
  let '(d, lc) := x in
  if d =? 0 then arr_get static_ltree_dl lc
  else arr_get static_ltree_dl (arr_get length_code_a lc + LITERALS + 1) + arr_get extra_lbits_a (arr_get length_code_a lc)
       + 5 + arr_get extra_dbits_a (d_code (d - 1)).

Lemma scost_bound : forall x, sym_valid x -> 1 <= scost x <= 31.
Proof.
  intros [d lc] V. unfold sym_valid in V. unfold scost.
  destruct (Z.eqb_spec d 0).
  - rewrite static_ltree_len by lia. destruct (lc <? 144); [lia|]. destruct (Z.ltb_spec lc 256); lia.
  - pose proof (length_code_range lc ltac:(lia)) as CR.
    pose proof (extra_lbits_range _ CR). unfold LITERALS.
    pose proof (d_code_range (d - 1) ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V; lia)) as DR.
    pose proof (extra_dbits_range _ DR).
    rewrite static_ltree_len by lia.
    destruct (Z.ltb_spec (arr_get length_code_a lc + 256 + 1) 144); [lia|].
    destruct (Z.ltb_spec (arr_get length_code_a lc + 256 + 1) 256); [lia|].
    assert (X : arr_get length_code_a lc <= 22 -> arr_get extra_lbits_a (arr_get length_code_a lc) <= 4).
    { intros Hc. pose proof (table_range extra_lbits_a 0 4 23 ltac:(vm_compute; reflexivity)) as TR.
      specialize (TR (arr_get length_code_a lc)). apply TR. lia. }
    destruct (Z.ltb_spec (arr_get length_code_a lc + 256 + 1) 280); lia.
Qed.

Definition Sstat (syms : list (Z * Z)) : Z := csum scost syms + 7.


Lemma sum_Ul : forall FC0 (w : Z -> Z) n, 0 <= n ->
  zsum (map (fun j => arr_get FC0 j * w j) (Ul FC0 n)) = zsum (map (fun j => arr_get FC0 j * w j) (ziota 0 (Z.to_nat n))).
Proof.
  intros FC0 w n Hn. unfold Ul. induction (ziota 0 (Z.to_nat n)) as [|j l IH]; cbn; [reflexivity|].
  unfold nzb at 1. destruct (Z.eqb_spec (arr_get FC0 j) 0) as [E|E]; cbn; rewrite IH; [rewrite E|]; lia.
Qed.

Lemma sum_UP : forall t FC0 (w : Z -> Z),
  zsum (map (fun j => FP FC0 t j * w j) (UP FC0 t))
  = zsum (map (fun j => arr_get FC0 j * w j) (ziota 0 (Z.to_nat (sd_elems t)))) + zsum (map w (pads FC0 t)).
Proof.
  intros t FC0 w. pose proof (pads_facts t FC0) as (ND & RNG & U2 & PD & MX1 & MX2). pose proof (elems_tsize t) as ET.
  unfold UP. rewrite map_app, zsum_app. f_equal.
  - rewrite <- sum_Ul by lia. unfold Ulist. apply zsum_map_ext. intros j Hj. unfold FP.
    destruct (existsb (Z.eqb j) (pads FC0 t)) eqn:E; [|reflexivity].
    apply existsb_exists in E. destruct E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x.
    apply PD in Hx. apply Ul_in in Hj; lia.
  - apply zsum_map_ext. intros j Hj. unfold FP. replace (existsb (Z.eqb j) (pads FC0 t)) with true; [lia|].
    symmetry. apply existsb_exists. exists j. split; [exact Hj| apply Z.eqb_refl].
Qed.

Lemma pads_small : forall t FC0, zlen (pads FC0 t) <= 2 /\ forall j, In j (pads FC0 t) -> 0 <= j <= 2 /\ arr_get FC0 j = 0.
Proof.
  intros t FC0. pose proof (pads_facts t FC0) as (ND & RNG & U2 & PD & MX1 & MX2).
  split; [unfold pads; destruct (Ulist FC0 t) as [|? [|? ?]]; unfold zlen; cbn; lia|].
  intros j Hj. specialize (PD j Hj). lia.
Qed.


Section FB.
  Variable syms : list (Z * Z).
  Variable s : deflate_state.
  Variable buf : option Z.
  Variables len last : Z.
  Hypothesis FB : FBS syms s buf len last.

  Definition nS : Z := Z.of_nat (length syms).
  Definition LS : Z := ds_lit_bufsize s.

  Definition fs0 : deflate_state :=
    if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s.

  Lemma fs0_eq : fs0 = set_strm s (ds_strm fs0).
  Proof. unfold fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); destruct s; reflexivity. Qed.

  Lemma fs0_tree_fc : forall t, tree_fc fs0 t = tree_fc s t.
  Proof. intros t. rewrite fs0_eq. destruct s, t; reflexivity. Qed.
  Lemma fs0_fields :
    ds_pending_buf fs0 = ds_pending_buf s /\ ds_pending fs0 = ds_pending s /\ ds_bi_valid fs0 = ds_bi_valid s
    /\ ds_bi_buf fs0 = ds_bi_buf s /\ ds_lit_bufsize fs0 = ds_lit_bufsize s /\ ds_sym_next fs0 = ds_sym_next s
    /\ ds_bl_count fs0 = ds_bl_count s /\ ds_heap fs0 = ds_heap s /\ ds_depth fs0 = ds_depth s
    /\ ds_opt_len fs0 = ds_opt_len s /\ ds_static_len fs0 = ds_static_len s /\ ds_level fs0 = ds_level s
    /\ ds_strategy fs0 = ds_strategy s /\ ds_window fs0 = ds_window s /\ ds_bl_tree_fc fs0 = ds_bl_tree_fc s
    /\ ds_sym_end fs0 = ds_sym_end s.
  Proof. rewrite fs0_eq. destruct s; repeat split; reflexivity. Qed.

  Lemma lcode_range : forall x, In x syms -> 0 <= sym_lcode x < 286 /\ (ism x = true -> 257 <= sym_lcode x <= 285 /\ 0 <= sdc x <= 29)
                                               /\ (ism x = false -> sym_lcode x <= 255).
  Proof.
    intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) (fbs_syms_valid _ _ _ _ _ FB) _ Hx) as V. unfold sym_valid in V.
    unfold sym_lcode, ism, sdc. cbn [fst]. unfold LITERALS, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
    destruct (Z.eqb_spec d 0); cbn [negb].
    - split; [lia|]. split; [intros; discriminate| intros; lia].
    - pose proof (length_code_range lc ltac:(lia)). pose proof (d_code_range (d - 1) ltac:(lia)). split; [lia|]. split; [intros _; lia| intros; discriminate].
  Qed.

  Lemma sumL_syms : forall w : Z -> Z,
    zsum (map (fun c => Freq s TL c * w c) (ziota 0 286)) = csum (fun x => w (sym_lcode x)) syms + w 256.
  Proof.
    intros w.
    transitivity (zsum (map (fun c => zcount (fun x => true && (sym_lcode x =? c)) syms * w c + (if 256 =? c then 1 else 0) * w c) (ziota 0 286))).
    - apply zsum_map_ext. intros c Hc. apply in_ziota in Hc. rewrite (fbs_freq_l _ _ _ _ _ FB) by (unfold L_CODES; lia).
      unfold zcount, END_BLOCK. cbn [andb]. rewrite (Z.eqb_sym c 256). destruct (256 =? c); lia.
    - rewrite zsum_map_add. rewrite <- (regroup_le syms (fun _ => true) sym_lcode w (ziota 0 286) (NoDup_ziota 0 286)).
      + rewrite (zsum_indicator w (ziota 0 286) 256 (NoDup_ziota 0 286) ltac:(apply in_ziota; lia)). reflexivity.
      + intros x Hx _. apply in_ziota. pose proof (lcode_range x Hx) as (R1 & _). lia.
  Qed.

  Lemma sumD_syms : forall w : Z -> Z,
    zsum (map (fun i => Freq s TD i * w i) (ziota 0 30)) = csum (fun x => if ism x then w (sdc x) else 0) syms.
  Proof.
    intros w.
    transitivity (zsum (map (fun i => zcount (fun x => ism x && (sdc x =? i)) syms * w i) (ziota 0 30))).
    - apply zsum_map_ext. intros i Hi. apply in_ziota in Hi. rewrite (fbs_freq_d _ _ _ _ _ FB) by (unfold D_CODES; lia).
      f_equal. unfold zcount. f_equal. f_equal.
      apply filter_ext. intros [d lc]. unfold sym_dcode, ism, sdc. cbn [fst]. destruct (d =? 0); reflexivity.
    - symmetry. apply regroup_le; [apply NoDup_ziota|]. intros x Hx Hm. apply in_ziota. pose proof (lcode_range x Hx) as (_ & R & _). specialize (R Hm). lia.
  Qed.

  Lemma zsum_const1 : forall (l : list Z), zsum (map (fun _ => 1) l) = zlen l.
  Proof. unfold zlen. induction l; cbn [map zsum length]; [lia|]. rewrite IHl, Nat2Z.inj_succ. lia. Qed.

  Lemma csum_constk : forall k (l : list (Z * Z)), csum (fun _ => k) l = k * Z.of_nat (length l).
  Proof. intros k l. induction l; cbn [csum length]; [lia|]. rewrite IHl, Nat2Z.inj_succ. lia. Qed.
  Lemma csum_const1 : forall (l : list (Z * Z)), csum (fun _ => 1) l = Z.of_nat (length l).
  Proof. intros. rewrite csum_constk. lia. Qed.

  Lemma csum_le : forall (f g : Z * Z -> Z) l, (forall x, In x l -> f x <= g x) -> csum f l <= csum g l.
  Proof. induction l as [|x l IH]; intros H; cbn; [lia|]. pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

  Lemma csum_nonneg : forall (f : Z * Z -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= csum f l.
  Proof. intros f l H. pose proof (csum_le (fun _ => 0) f l H). replace (csum (fun _ => 0) l) with 0 in H0; [lia|]. clear. induction l; cbn; lia. Qed.

  Lemma FtotL : zsum (map (Freq s TL) (ziota 0 286)) = nS + 1.
  Proof.
    pose proof (sumL_syms (fun _ => 1)) as X.
    rewrite (zsum_map_ext _ (Freq s TL)) in X by (intros; lia). rewrite X, csum_const1. reflexivity.
  Qed.

  Lemma FtotD : zsum (map (Freq s TD) (ziota 0 30)) = csum (fun x => if ism x then 1 else 0) syms /\ csum (fun x => if ism x then 1 else 0) syms <= nS.
  Proof.
    pose proof (sumD_syms (fun _ => 1)) as X.
    rewrite (zsum_map_ext _ (Freq s TD)) in X by (intros; lia). split; [exact X|].
    unfold nS. rewrite <- csum_const1. apply csum_le. intros x _. destruct (ism x); lia.
  Qed.

  Lemma bt_Ftot_TL : bt_Ftot s TL = nS + 1 + bt_npad s TL /\ 0 <= bt_npad s TL <= 2.
  Proof.
    unfold bt_Ftot, Ftot, bt_npad. pose proof (sum_UP TL (tree_fc s TL) (fun _ => 1)) as X.
    rewrite (zsum_map_ext _ (FP (tree_fc s TL) TL)) in X by (intros; lia).
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TL) j * 1) (Freq s TL)) in X by (intros; unfold Freq; lia).
    cbn [sd_elems] in X. unfold L_CODES in X. change (Z.to_nat 286) with 286%nat in X. rewrite FtotL in X.
    pose proof (pads_small TL (tree_fc s TL)) as [P _].
    rewrite zsum_const1 in X. unfold zlen in *. split; [lia|]. lia.
  Qed.

  Lemma bt_Ftot_TD : bt_Ftot s TD <= nS + 2 /\ 0 <= bt_npad s TD <= 2.
  Proof.
    unfold bt_Ftot, Ftot, bt_npad. pose proof (sum_UP TD (tree_fc s TD) (fun _ => 1)) as X.
    rewrite (zsum_map_ext _ (FP (tree_fc s TD) TD)) in X by (intros; lia).
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TD) j * 1) (Freq s TD)) in X by (intros; unfold Freq; lia).
    cbn [sd_elems] in X. unfold D_CODES in X. change (Z.to_nat 30) with 30%nat in X. destruct FtotD as [FD1 FD2]. rewrite FD1 in X.
    pose proof (pads_small TD (tree_fc s TD)) as [P _].
    rewrite zsum_const1 in X. unfold zlen in *. split; lia.
  Qed.

  Lemma L_range : 128 <= LS <= 32768 /\ 0 <= nS <= LS - 1.
  Proof.
    destruct (fbs_Lpow _ _ _ _ _ FB) as (k & Hk & E). pose proof (fbs_n_range _ _ _ _ _ FB) as R. unfold fbs_L, fbs_n, LS, nS in *.
    assert (2 ^ 7 <= 2 ^ k <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in H. change (2 ^ 15) with 32768 in H.
    rewrite E in *. lia.
  Qed.

  Lemma fs0_flush_pre : flush_pre fs0.
  Proof.
    pose proof fs0_fields as (Fpb & Fpd & Fbv & Fbb & Flb & Fsn & Fbc & Fhp & Fdp & Fol & Fsl & Flv & Fst & Fwi & Fbl & Fse).
    pose proof (fbs_lens _ _ _ _ _ FB) as TL0. pose proof L_range as [LR NR].
    split.
    - assert (G : forall st, tree_lens (set_strm s st) <-> tree_lens s) by (intros; destruct s; cbn; tauto).
      rewrite fs0_eq. apply G. exact TL0.
    - intros j Hj. unfold Freq. rewrite fs0_tree_fc. fold (Freq s TL j). rewrite (fbs_freq_l _ _ _ _ _ FB) by (unfold L_CODES; lia).
      pose proof (zcount_nonneg' := I). unfold zcount. destruct (j =? END_BLOCK); lia.
    - intros j Hj. unfold Freq. rewrite fs0_tree_fc. fold (Freq s TD j). rewrite (fbs_freq_d _ _ _ _ _ FB) by (unfold D_CODES; lia). unfold zcount. lia.
    - intros i Hi. rewrite Fbl. change (ds_bl_tree_fc s) with (tree_fc s TB).
      apply (proj1 (ct_bfc _ (fbs_cty _ _ _ _ _ FB) i ltac:(unfold fbs_tree_lens in TL0; lia))).
    - pose proof bt_Ftot_TL as [E P]. unfold bt_Ftot in *. rewrite fs0_tree_fc. rewrite E. unfold bt_npad in *. lia.
    - pose proof bt_Ftot_TD as [E P]. unfold bt_Ftot in *. rewrite fs0_tree_fc. lia.
    - rewrite Fbl. unfold bsum. rewrite (zsum_map_ext _ (fun _ => 0)).
      + replace (zsum (map (fun _ : Z => 0) (ziota 0 19))) with 0 by reflexivity. lia.
      + intros i Hi. apply in_ziota in Hi. change (arr_get (ds_bl_tree_fc s) i) with (Freq s TB i). apply (fbs_freq_b _ _ _ _ _ FB). unfold BL_CODES. lia.
    - rewrite Fol, (fbs_opt_len _ _ _ _ _ FB). lia.
    - rewrite Fsl, (fbs_static_len _ _ _ _ _ FB). lia.
  Qed.

  Variables fY1 fY2 fY3 fY4 fY5 fY6 : deflate_state.
  Definition fmb : Z := build_bl_tree_loop 17 fY5 18.
  Hypothesis EfY1 : fY1 = build_tree fs0 TL.
  Hypothesis EfY2 : fY2 = build_tree fY1 TD.
  Hypothesis EfY3 : fY3 = scan_tree fY2 TL (ds_l_max_code fY2).
  Hypothesis EfY4 : fY4 = scan_tree fY3 TD (ds_d_max_code fY3).
  Hypothesis EfY5 : fY5 = build_tree fY4 TB.
  Hypothesis EfY6 : fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb + 1) + 5 + 5 + 4)).

  Lemma bbl_loop_range : forall f X m, 2 <= m -> 2 <= build_bl_tree_loop f X m <= m.
  Proof.
    induction f as [|f IH]; intros X m Hm; cbn [build_bl_tree_loop]; [lia|].
    destruct (Z.leb_spec 3 m); [|lia]. destruct (negb _); [lia|]. specialize (IH X (m - 1) ltac:(lia)). lia.
  Qed.

  Lemma fmb_range : 2 <= fmb <= 18.
  Proof. unfold fmb. apply bbl_loop_range. lia. Qed.

  Definition dcost (LzL LzD : Z -> Z) (x : Z * Z) : Z :=
    LzL (sym_lcode x) + xbits TL (sym_lcode x) + (if ism x then LzD (sdc x) + xbits TD (sdc x) else 0).

  Lemma zcount_pos : forall (p : Z * Z -> bool) l x, In x l -> p x = true -> 1 <= zcount p l.
  Proof.
    intros p l x Hx Hp. unfold zcount. induction l as [|y l IH]; [destruct Hx|]. cbn [filter].
    destruct Hx as [->|Hx]; [rewrite Hp; cbn [length]; lia|]. specialize (IH Hx). destruct (p y); cbn [length]; lia.
  Qed.

  Lemma zcount_nonneg : forall (p : Z * Z -> bool) l, 0 <= zcount p l.
  Proof. intros. unfold zcount. lia. Qed.

  Lemma syms_in_U : (forall x, In x syms -> In (sym_lcode x) (bt_U s TL) /\ (ism x = true -> In (sdc x) (bt_U s TD))) /\ In 256 (bt_U s TL).
  Proof.
    pose proof (bt_U_facts s TL) as (_ & _ & _ & _ & INL & _). pose proof (bt_U_facts s TD) as (_ & _ & _ & _ & IND & _).
    split.
    - intros x Hx. pose proof (lcode_range x Hx) as (R1 & R2 & R3). split.
      + enough (NZ : Freq s TL (sym_lcode x) <> 0) by exact (proj1 (INL (sym_lcode x) ltac:(unfold sd_elems, L_CODES; lia) NZ)).
        rewrite (fbs_freq_l _ _ _ _ _ FB) by (unfold L_CODES; lia).
        pose proof (zcount_pos (fun dl => sym_lcode dl =? sym_lcode x) syms x Hx ltac:(apply Z.eqb_refl)). destruct (_ =? END_BLOCK); lia.
      + intros Hm. specialize (R2 Hm). enough (NZ : Freq s TD (sdc x) <> 0) by exact (proj1 (IND (sdc x) ltac:(unfold sd_elems, D_CODES; lia) NZ)).
        rewrite (fbs_freq_d _ _ _ _ _ FB) by (unfold D_CODES; lia).
        pose proof (zcount_pos (fun dl => match sym_dcode dl with Some j' => j' =? sdc x | None => false end) syms x Hx) as P.
        enough (E : match sym_dcode x with Some j' => j' =? sdc x | None => false end = true) by (specialize (P E); lia).
        destruct x as [d lc]. unfold sym_dcode, sdc, ism in *. cbn [fst] in *. destruct (d =? 0); [discriminate| apply Z.eqb_refl].
    - enough (NZ : Freq s TL 256 <> 0) by exact (proj1 (INL 256 ltac:(unfold sd_elems, L_CODES; lia) NZ)).
      rewrite (fbs_freq_l _ _ _ _ _ FB) by (unfold L_CODES; lia).
      unfold END_BLOCK. rewrite Z.eqb_refl. pose proof (zcount_nonneg (fun dl => sym_lcode dl =? 256) syms). lia.
  Qed.

  Lemma static_cost_sum :
    zsum (map (fun j => bt_F s TL j * (stree_Len TL j + xbits TL j)) (bt_U s TL)) - bt_slpad s TL
    + (zsum (map (fun j => bt_F s TD j * (stree_Len TD j + xbits TD j)) (bt_U s TD)) - bt_slpad s TD)
    = Sstat syms.
  Proof.
    unfold bt_F, bt_U, bt_slpad, sl_pad. rewrite !sum_UP. cbn [sd_elems]. unfold L_CODES, D_CODES.
    change (Z.to_nat 286) with 286%nat. change (Z.to_nat 30) with 30%nat.
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TL) j * _) (fun c => Freq s TL c * (stree_Len TL c + xbits TL c))) by (intros; reflexivity).
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TD) j * _) (fun c => Freq s TD c * (stree_Len TD c + xbits TD c))) by (intros; reflexivity).
    rewrite sumL_syms, sumD_syms.
    pose proof (pads_small TL (tree_fc s TL)) as [_ PL]. pose proof (pads_small TD (tree_fc s TD)) as [_ PD].
    assert (XL : zsum (map (fun j => stree_Len TL j + xbits TL j) (pads (tree_fc s TL) TL)) = zsum (map (stree_Len TL) (pads (tree_fc s TL) TL))).
    { apply zsum_map_ext. intros j Hj. specialize (PL j Hj). rewrite xbits_TL. replace (257 <=? j) with false by (symmetry; apply Z.leb_gt; lia). lia. }
    assert (XD : zsum (map (fun j => stree_Len TD j + xbits TD j) (pads (tree_fc s TD) TD)) = zsum (map (stree_Len TD) (pads (tree_fc s TD) TD))).
    { apply zsum_map_ext. intros j Hj. specialize (PD j Hj). rewrite xbits_TD by lia.
      rewrite (proj1 (table_range extra_dbits_a 0 0 3 ltac:(vm_compute; reflexivity) j ltac:(lia))) || (pose proof (table_range extra_dbits_a 0 0 3 ltac:(vm_compute; reflexivity) j ltac:(lia)); lia). }
    rewrite XL, XD. unfold Sstat.
    cbn [stree_Len]. rewrite (static_ltree_len 256) by lia. rewrite (xbits_TL 256).
    change (257 <=? 256) with false. change (256 <? 144) with false. change (256 <? 256) with false. change (256 <? 280) with true. cbv iota.
    enough (E : csum (fun x => arr_get static_ltree_dl (sym_lcode x) + xbits TL (sym_lcode x)) syms
               + csum (fun x => if ism x then arr_get static_dtree_dl (sdc x) + xbits TD (sdc x) else 0) syms = csum scost syms) by lia.
    assert (G : forall l, (forall x, In x l -> In x syms) ->
      csum (fun x => arr_get static_ltree_dl (sym_lcode x) + xbits TL (sym_lcode x)) l
      + csum (fun x => if ism x then arr_get static_dtree_dl (sdc x) + xbits TD (sdc x) else 0) l = csum scost l).
    { induction l as [|x l IH]; intros Hl; cbn [csum]; [lia|].
      specialize (IH ltac:(intros; apply Hl; right; assumption)).
      pose proof (lcode_range x (Hl x (or_introl eq_refl))) as (R1 & R2 & R3).
      enough (arr_get static_ltree_dl (sym_lcode x) + xbits TL (sym_lcode x) + (if ism x then arr_get static_dtree_dl (sdc x) + xbits TD (sdc x) else 0) = scost x) by lia.
      destruct x as [d lc]. unfold scost, sym_lcode, ism, sdc in *. cbn [fst] in *.
      pose proof (proj1 (Forall_forall _ _) (fbs_syms_valid _ _ _ _ _ FB) _ (Hl _ (or_introl eq_refl))) as V. unfold sym_valid in V.
      destruct (Z.eqb_spec d 0); cbn [negb] in *.
      - rewrite xbits_TL. replace (257 <=? lc) with false by (symmetry; apply Z.leb_gt; lia). lia.
      - specialize (R2 eq_refl). rewrite xbits_TL. replace (257 <=? arr_get length_code_a lc + LITERALS + 1) with true by (symmetry; apply Z.leb_le; lia).
        rewrite xbits_TD by lia. rewrite static_dtree_len by lia. unfold LITERALS. replace (arr_get length_code_a lc + 256 + 1 - 257) with (arr_get length_code_a lc) by lia. lia. }
    apply G. auto.
  Qed.

  Lemma Sstat_bound : 7 <= Sstat syms <= 31 * nS + 7.
  Proof.
    unfold Sstat, nS. pose proof (fbs_syms_valid _ _ _ _ _ FB) as V. rewrite Forall_forall in V.
    pose proof (csum_le scost (fun _ => 31) syms ltac:(intros x Hx; cbn beta; pose proof (scost_bound x (V x Hx)); lia)).
    pose proof (csum_le (fun _ => 1) scost syms ltac:(intros x Hx; cbn beta; pose proof (scost_bound x (V x Hx)); lia)).
    rewrite csum_const1, csum_constk in *. lia.
  Qed.

  Lemma pads_sum_bounds : forall t (g : Z -> Z) lo hi,
    (forall j, In j (pads (tree_fc s t) t) -> lo <= g j <= hi) ->
    lo * bt_npad s t <= zsum (map g (pads (tree_fc s t) t)) <= hi * bt_npad s t.
  Proof.
    intros t g lo hi Hg. unfold bt_npad.
    assert (G : forall l, (forall j, In j l -> lo <= g j <= hi) -> lo * zlen l <= zsum (map g l) <= hi * zlen l).
    { induction l as [|j l IH]; intros Hl; [unfold zlen; cbn; lia|]. cbn [map zsum]. rewrite zlen_cons.
      pose proof (Hl j (or_introl eq_refl)). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
    apply G. exact Hg.
  Qed.

  Lemma dyn_cost_sum : forall (LzL LzD : Z -> Z),
    (forall j, In j (bt_U s TL) -> 1 <= LzL j <= 15) -> (forall j, In j (bt_U s TD) -> 1 <= LzD j <= 15) ->
    let OLL := zsum (map (fun j => bt_F s TL j * (LzL j + xbits TL j)) (bt_U s TL)) - bt_npad s TL in
    let OLD := zsum (map (fun j => bt_F s TD j * (LzD j + xbits TD j)) (bt_U s TD)) - bt_npad s TD in
    csum (dcost LzL LzD) syms + LzL 256 <= OLL + OLD <= csum (dcost LzL LzD) syms + LzL 256 + 56
    /\ 0 <= csum (dcost LzL LzD) syms <= 48 * nS /\ 1 <= LzL 256 <= 15.
  Proof.
    intros LzL LzD HL HD. cbv zeta.
    pose proof (pads_small TL (tree_fc s TL)) as [ZPL PL]. pose proof (pads_small TD (tree_fc s TD)) as [ZPD PD].
    assert (XL : forall j, In j (pads (tree_fc s TL) TL) -> 1 <= (fun j0 : Z => LzL j0 + xbits TL j0) j <= 15).
    { intros j Hj. cbn beta. pose proof (PL j Hj) as [Rj _]. rewrite xbits_TL.
      replace (257 <=? j) with false by (symmetry; apply Z.leb_gt; lia).
      pose proof (HL j ltac:(unfold bt_U, UP; apply in_app_iff; right; exact Hj)). lia. }
    assert (XD : forall j, In j (pads (tree_fc s TD) TD) -> 1 <= (fun j0 : Z => LzD j0 + xbits TD j0) j <= 15).
    { intros j Hj. cbn beta. pose proof (PD j Hj) as [Rj _]. rewrite xbits_TD by lia.
      pose proof (table_range extra_dbits_a 0 0 3 ltac:(vm_compute; reflexivity) j ltac:(lia)).
      pose proof (HD j ltac:(unfold bt_U, UP; apply in_app_iff; right; exact Hj)). lia. }
    pose proof (pads_sum_bounds TL (fun j => LzL j + xbits TL j) 1 15 XL) as BL.
    pose proof (pads_sum_bounds TD (fun j => LzD j + xbits TD j) 1 15 XD) as BD. clear XL XD.
    pose proof (bt_U_facts s TL) as (_ & _ & _ & _ & _ & _ & NPL & _). pose proof (bt_U_facts s TD) as (_ & _ & _ & _ & _ & _ & NPD & _).
    destruct syms_in_U as [SU S256]. pose proof (HL 256 S256) as L256.
    assert (DC : forall x, In x syms -> 1 <= dcost LzL LzD x <= 48).
    { intros x Hx. destruct (SU x Hx) as [I1 I2]. pose proof (lcode_range x Hx) as (R1 & R2 & R3). unfold dcost.
      pose proof (HL _ I1). rewrite xbits_TL.
      destruct (ism x).
      - specialize (I2 eq_refl). specialize (R2 eq_refl). pose proof (HD _ I2). rewrite xbits_TD by lia.
        replace (257 <=? sym_lcode x) with true by (symmetry; apply Z.leb_le; lia).
        pose proof (extra_lbits_range (sym_lcode x - 257) ltac:(lia)). pose proof (extra_dbits_range (sdc x) ltac:(lia)). lia.
      - specialize (R3 eq_refl). replace (257 <=? sym_lcode x) with false by (symmetry; apply Z.leb_gt; lia). lia. }
    assert (UB0 : forall x, In x syms -> dcost LzL LzD x <= (fun _ => 48) x) by (intros x Hx; cbn beta; pose proof (DC x Hx); lia).
    pose proof (csum_le (dcost LzL LzD) (fun _ => 48) syms UB0) as UB.
    assert (LB0 : forall x, In x syms -> 0 <= dcost LzL LzD x) by (intros x Hx; pose proof (DC x Hx); lia).
    pose proof (csum_nonneg (dcost LzL LzD) syms LB0) as LB.
    rewrite csum_constk in UB. fold nS in UB.
    unfold bt_F, bt_U. rewrite !sum_UP. cbn [sd_elems]. unfold L_CODES, D_CODES.
    change (Z.to_nat 286) with 286%nat. change (Z.to_nat 30) with 30%nat.
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TL) j * _) (fun c => Freq s TL c * (LzL c + xbits TL c))) by (intros; reflexivity).
    rewrite (zsum_map_ext (fun j => arr_get (tree_fc s TD) j * _) (fun c => Freq s TD c * (LzD c + xbits TD c))) by (intros; reflexivity).
    rewrite sumL_syms, sumD_syms.
    assert (SPLIT : csum (dcost LzL LzD) syms = csum (fun x => LzL (sym_lcode x) + xbits TL (sym_lcode x)) syms
                                             + csum (fun x => if ism x then LzD (sdc x) + xbits TD (sdc x) else 0) syms).
    { unfold dcost. assert (G : forall l : list (Z * Z),
        csum (fun x => LzL (sym_lcode x) + xbits TL (sym_lcode x) + (if ism x then LzD (sdc x) + xbits TD (sdc x) else 0)) l
        = csum (fun x => LzL (sym_lcode x) + xbits TL (sym_lcode x)) l + csum (fun x => if ism x then LzD (sdc x) + xbits TD (sdc x) else 0) l)
        by (induction l; cbn [csum]; lia).
      apply G. }
    rewrite (xbits_TL 256). change (257 <=? 256) with false. cbv iota.
    unfold nS in *. lia.
  Qed.

  Lemma wsum_zsum : forall w b, wsum w b = zsum (map (fun y => arr_get b y * w y) (ziota 0 19)).
  Proof. intros. reflexivity. Qed.


  Record flush_rec (LL LzL LD LzD LB LzB : Z -> Z) (b4 : arr) : Prop := FLUSH_REC {
    ff_B1 : bt_post fs0 TL fY1 LL LzL;
    ff_B2 : bt_post fY1 TD fY2 LD LzD;
    ff_FC1D : tree_fc fY1 TD = tree_fc s TD;
    ff_B5 : bt_post fY4 TB fY5 LB LzB;
    ff_FC4B : tree_fc fY4 TB = b4;
    ff_Lb4 : arr_len b4 = 39;
    ff_NN4 : bnn b4;
    ff_BS316 : bsum b4 <= 316;
    ff_LENS : forall j, In j (bt_U s TL) -> Len fY5 TL j = LzL j /\ 1 <= LzL j <= 15;
    ff_ZL : forall j, 0 <= j <= bt_mc s TL -> ~ In j (bt_U s TL) -> Len fY5 TL j = 0;
    ff_GL : Len fY5 TL (bt_mc s TL + 1) = 65535;
    ff_LEND : forall j, In j (bt_U s TD) -> Len fY5 TD j = LzD j /\ 1 <= LzD j <= 15;
    ff_ZD : forall j, 0 <= j <= bt_mc s TD -> ~ In j (bt_U s TD) -> Len fY5 TD j = 0;
    ff_GD : Len fY5 TD (bt_mc s TD + 1) = 65535;
    ff_LENB : forall y, In y (bt_U fY4 TB) -> Len fY5 TB y = LzB y /\ 1 <= LzB y <= 7;
    ff_ZB : forall y, 0 <= y < 19 -> ~ In y (bt_U fY4 TB) -> Len fY5 TB y = 0 /\ arr_get b4 y = 0;
    ff_MCL : ds_l_max_code fY5 = bt_mc s TL;
    ff_MCD : ds_d_max_code fY5 = bt_mc s TD;
    ff_RL : 0 <= bt_mc s TL <= 285;
    ff_RD : 0 <= bt_mc s TD <= 29;
    ff_SU : forall x, In x syms -> In (sym_lcode x) (bt_U s TL) /\ (ism x = true -> In (sdc x) (bt_U s TD));
    ff_S256 : In 256 (bt_U s TL);
    ff_EY3 : fY3 = scan_tree fY2 TL (bt_mc s TL);
    ff_EY4 : fY4 = scan_tree fY3 TD (bt_mc s TD);
    ff_LQ2 : forall i, 0 <= i <= bt_mc s TL + 1 -> Len fY5 TL i = Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL i;
    ff_LQ3 : forall i, 0 <= i <= bt_mc s TD + 1 -> Len fY5 TD i = Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD i;
    ff_BL2 : ds_bl_tree_fc fY2 = ds_bl_tree_fc s;
    ff_BL4 : ds_bl_tree_fc fY4 = b4;
    ff_B0 : forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc s) y = 0;
    ff_TL2 : tree_lens fY2;
    ff_TL3 : tree_lens fY3;
    ff_TL5 : tree_lens fY5;
    ff_SL : ds_static_len fY6 = Sstat syms;
    ff_TBnn : 0 <= wsum (fun y => Len fY5 TB y + blx y) b4;
    ff_OLlo : csum (dcost LzL LzD) syms + LzL 256 + wsum (fun y => Len fY5 TB y + blx y) b4 + 3 * (fmb + 1) + 14 <= ds_opt_len fY6;
    ff_OLhi : ds_opt_len fY6 <= 48 * nS + 4600;
    ff_K6 : kproj fY6 = kproj fs0;
    ff_PB6 : ds_pending_buf fY6 = ds_pending_buf s;
    ff_PD6 : ds_pending fY6 = 0;
    ff_BV6 : ds_bi_valid fY6 = ds_bi_valid s;
    ff_BB6 : ds_bi_buf fY6 = ds_bi_buf s;
    ff_DL6L : tree_dl fY6 TL = tree_dl fY5 TL;
    ff_DL6D : tree_dl fY6 TD = tree_dl fY5 TD;
    ff_DL6B : tree_dl fY6 TB = tree_dl fY5 TB;
    ff_FC6L : tree_fc fY6 TL = tree_fc fY5 TL;
    ff_FC6D : tree_fc fY6 TD = tree_fc fY5 TD;
    ff_TL4 : tree_lens fY4;
    ff_P1 : bt_pre fs0 TL;
    ff_P2 : bt_pre fY1 TD;
    ff_P5 : bt_pre fY4 TB;
    ff_MCL2 : ds_l_max_code fY2 = bt_mc s TL;
    ff_MCD3 : ds_d_max_code fY3 = bt_mc s TD }.

  Theorem flush_facts : exists LL LzL LD LzD LB LzB b4, flush_rec LL LzL LD LzD LB LzB b4.
  Proof.
    pose proof fs0_fields as (Fpb & Fpd & Fbv & Fbb & Flb & Fsn & Fbc & Fhp & Fdp & Fol & Fsl & Flv & Fst & Fwi & Fbl & Fse).
    pose proof L_range as [LR NR].
    destruct (flush_trees fs0 fs0_flush_pre fY1 fY2 fY3 fY4 fY5 EfY1 EfY2 EfY3 EfY4 EfY5)
      as (LL & LzL & LD & LzD & LB & LzB & b3 & b4 & B1 & B2 & FC1D & BL2 & B5 & FC4B & EY3 & EY4 & NN3 & NN4 & Lb4 & MONb & BS4
          & LenL & ZL & GL & LenD & ZD & GD & MCL & MCD & MCB & OL5 & SL5 & TL5 & TL2 & TL3 & TL4 & MCL2 & MCD3 & LQ2 & LQ3 & ZB & P1 & P2 & P5).
    destruct (bt_same s fs0 TL (fs0_tree_fc TL)) as (UL & FL & MCLq & NPL & SPL & FTL).
    destruct (bt_same s fs0 TD (fs0_tree_fc TD)) as (UD & FD & MCDq & NPD & SPD & FTD).
    pose proof B1 as (_ & L1ge & _ & _ & _ & _ & LzL1 & _ & _ & _ & _ & _ & _ & _ & _ & (FC1 & DL1 & HP1 & DP1 & BC1 & E1 & LFC1 & LDL1 & LHP1 & LDP1 & LBC1)).
    pose proof B2 as (_ & L2ge & _ & _ & _ & _ & LzD2 & _ & _ & _ & _ & _ & _ & _ & _ & (FC2 & DL2 & HP2 & DP2 & BC2 & E2 & LFC2 & LDL2 & LHP2 & LDP2 & LBC2)).
    pose proof B5 as (_ & L5ge & _ & _ & _ & _ & LzB5 & ZB5 & _ & _ & _ & _ & _ & _ & _ & (FC5 & DL5 & HP5 & DP5 & BC5 & E5 & LFC5 & LDL5 & LHP5 & LDP5 & LBC5)).
    destruct (bt_same s fY1 TD ltac:(rewrite FC1D; apply fs0_tree_fc)) as (UD1 & FD1 & MCD1 & NPD1 & SPD1 & FTD1).
    rewrite UL, MCLq in *. rewrite UD, MCDq in *. rewrite FL, NPL, SPL, FD, NPD, SPD in *. rewrite UD1 in *.
    
    pose proof (bt_U_facts s TL) as (NDL & RGL & MCinL & U2L & INL & PADL & NPLr & _).
    pose proof (bt_U_facts s TD) as (NDD & RGD & MCinD & U2D & IND & PADD & NPDr & _).
    pose proof (bt_U_facts fY4 TB) as (NDB & RGB & MCinB & U2B & INB & PADB & NPBr & _).
    assert (RL : 0 <= bt_mc s TL <= 285) by (pose proof (RGL _ MCinL) as X; cbn [sd_elems] in X; unfold L_CODES in X; lia).
    assert (RD : 0 <= bt_mc s TD <= 29) by (pose proof (RGD _ MCinD) as X; cbn [sd_elems] in X; unfold D_CODES in X; lia).
    assert (B0 : forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc s) y = 0).
    { intros y Hy. change (arr_get (ds_bl_tree_fc s) y) with (Freq s TB y). apply (fbs_freq_b _ _ _ _ _ FB). unfold BL_CODES. lia. }
    assert (B4Z : forall y, 0 <= y < 19 -> ~ In y (bt_U fY4 TB) -> arr_get b4 y = 0).
    { intros y Hy Hny. destruct (Z.eq_dec (arr_get b4 y) 0) as [E|NE]; [exact E|]. exfalso. apply Hny.
      enough (NZ : Freq fY4 TB y <> 0) by exact (proj1 (INB y ltac:(cbn [sd_elems]; unfold BL_CODES; lia) NZ)).
      unfold Freq. rewrite FC4B. assumption. }
    assert (LENS : forall j, In j (bt_U s TL) -> Len fY5 TL j = LzL j /\ 1 <= LzL j <= 15).
    { intros j Hj. split; [apply LenL; exact Hj|]. pose proof (proj2 (LzL1 j Hj)) as X. cbn [sd_max_length] in X. unfold MAX_BITS in X. exact X. }
    assert (LEND : forall j, In j (bt_U s TD) -> Len fY5 TD j = LzD j /\ 1 <= LzD j <= 15).
    { intros j Hj. split; [apply LenD; exact Hj|]. pose proof (proj2 (LzD2 j Hj)) as X. cbn [sd_max_length] in X. unfold MAX_BITS in X. exact X. }
    assert (LENB : forall y, In y (bt_U fY4 TB) -> Len fY5 TB y = LzB y /\ 1 <= LzB y <= 7).
    { intros y Hy. pose proof (LzB5 y Hy) as [X1 X2]. cbn [sd_max_length] in X2. unfold MAX_BL_BITS in X2. auto. }
    assert (BS316 : bsum b4 <= 316).
    { rewrite Fbl in BS4. unfold bsum in BS4 |- *. rewrite (zsum_map_ext (arr_get (ds_bl_tree_fc s)) (fun _ => 0)) in BS4 by (intros y Hy; apply in_ziota in Hy; apply B0; lia).
      replace (zsum (map (fun _ : Z => 0) (ziota 0 19))) with 0 in BS4 by reflexivity. lia. }
    assert (LQ2' : forall i, 0 <= i <= bt_mc s TL + 1 -> Len fY5 TL i = Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL i).
    { intros i Hi. rewrite Len_set_Len by (rewrite (tree_lens_dl fY2 TL TL2); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TL + 1) i); [subst i; rewrite GL; reflexivity| symmetry; apply LQ2; lia]. }
    assert (LQ3' : forall i, 0 <= i <= bt_mc s TD + 1 -> Len fY5 TD i = Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD i).
    { intros i Hi. rewrite Len_set_Len by (rewrite (tree_lens_dl fY3 TD TL3); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TD + 1) i); [subst i; rewrite GD; reflexivity| symmetry; apply LQ3; lia]. }
    pose proof static_cost_sum as SCS. pose proof Sstat_bound as SB.
    destruct (dyn_cost_sum LzL LzD ltac:(intros j Hj; apply (proj2 (LENS j Hj))) ltac:(intros j Hj; apply (proj2 (LEND j Hj)))) as (DCS1 & DCS2 & DCS3).
    pose proof (sum_UP TB b4 (fun y => LzB y + xbits TB y)) as SB4.
    assert (PB : forall y, In y (pads b4 TB) -> 1 <= (fun y0 => LzB y0 + xbits TB y0) y <= 14).
    { intros y Hy. cbn beta. pose proof (pads_small TB b4) as [_ P]. pose proof (P y Hy) as [Ry _].
      rewrite xbits_TB by lia. assert (HU : In y (bt_U fY4 TB)) by (unfold bt_U; rewrite FC4B; unfold UP; apply in_app_iff; right; exact Hy).
      pose proof (proj2 (LENB y HU)). unfold blx, REP_3_6, REPZ_3_10, REPZ_11_138.
      destruct (y =? 16); [lia|]. destruct (y =? 17); [lia|]. destruct (y =? 18); lia. }
    pose proof (pads_sum_bounds' := I).
    assert (PSB : 1 * zlen (pads b4 TB) <= zsum (map (fun y => LzB y + xbits TB y) (pads b4 TB)) <= 14 * zlen (pads b4 TB)).
    { assert (G : forall l, (forall j, In j l -> 1 <= (fun y0 => LzB y0 + xbits TB y0) j <= 14) -> 1 * zlen l <= zsum (map (fun y => LzB y + xbits TB y) l) <= 14 * zlen l).
      { induction l as [|j l IH]; intros Hl; [unfold zlen; cbn; lia|]. cbn [map zsum]. rewrite zlen_cons.
        pose proof (Hl j (or_introl eq_refl)). cbn beta in H. specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
      apply G. exact PB. }
    assert (TBEQ : zsum (map (fun y => arr_get b4 y * (LzB y + xbits TB y)) (ziota 0 (Z.to_nat (sd_elems TB)))) = wsum (fun y => Len fY5 TB y + blx y) b4).
    { rewrite wsum_zsum. cbn [sd_elems]. unfold BL_CODES. change (Z.to_nat 19) with 19%nat. apply zsum_map_ext. intros y Hy. apply in_ziota in Hy.
      destruct (in_dec Z.eq_dec y (bt_U fY4 TB)) as [IN|NIN].
      - rewrite (proj1 (LENB y IN)), xbits_TB by lia. reflexivity.
      - rewrite (B4Z y ltac:(lia) NIN). lia. }
    assert (TBB : 0 <= wsum (fun y => Len fY5 TB y + blx y) b4 <= 14 * 316).
    { rewrite wsum_zsum.
      assert (G : forall l, (forall y, In y l -> 0 <= y < 19) -> 0 <= zsum (map (fun y => arr_get b4 y * (Len fY5 TB y + blx y)) l) <= 14 * zsum (map (arr_get b4) l)).
      { induction l as [|y l IH]; intros Hl; cbn [map zsum]; [lia|].
        specialize (IH ltac:(intros; apply Hl; right; assumption)). pose proof (Hl y (or_introl eq_refl)) as Ry.
        pose proof (NN4 y ltac:(lia)) as Ny.
        assert (W : 0 <= Len fY5 TB y + blx y <= 14).
        { unfold blx, REP_3_6, REPZ_3_10, REPZ_11_138. destruct (in_dec Z.eq_dec y (bt_U fY4 TB)) as [IN|NIN].
          - pose proof (LENB y IN) as [-> X]. destruct (y =? 16); [lia|]. destruct (y =? 17); [lia|]. destruct (y =? 18); lia.
          - rewrite (ZB y ltac:(lia) NIN). destruct (y =? 16); [lia|]. destruct (y =? 17); [lia|]. destruct (y =? 18); lia. }
        nia. }
      specialize (G (ziota 0 19) ltac:(intros y Hy; apply in_ziota in Hy; lia)). unfold bsum in *. lia. }
    assert (HNPB : bt_npad fY4 TB = zlen (pads b4 TB)) by (unfold bt_npad; rewrite FC4B; reflexivity).
    assert (GS : forall X v, ds_opt_len (set_opt_len X v) = v /\ ds_static_len (set_opt_len X v) = ds_static_len X
              /\ ds_pending_buf (set_opt_len X v) = ds_pending_buf X /\ ds_pending (set_opt_len X v) = ds_pending X
              /\ ds_bi_valid (set_opt_len X v) = ds_bi_valid X /\ ds_bi_buf (set_opt_len X v) = ds_bi_buf X
              /\ (forall t, tree_dl (set_opt_len X v) t = tree_dl X t) /\ (forall t, tree_fc (set_opt_len X v) t = tree_fc X t)).
    { intros X v. destruct X; repeat split; try reflexivity; intros [| |]; reflexivity. }
    destruct (GS fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb + 1) + 5 + 5 + 4))) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    assert (OLv : ds_opt_len fY6 = (zsum (map (fun j => bt_F s TL j * (LzL j + xbits TL j)) (bt_U s TL)) - bt_npad s TL)
                                  + (zsum (map (fun j => bt_F s TD j * (LzD j + xbits TD j)) (bt_U s TD)) - bt_npad s TD)
                                  + (wsum (fun y => Len fY5 TB y + blx y) b4 + zsum (map (fun y => LzB y + xbits TB y) (pads b4 TB)) - zlen (pads b4 TB))
                                  + 3 * (fmb + 1) + 14).
    { rewrite EfY6. rewrite G1.
      rewrite OL5, Fol, (fbs_opt_len _ _ _ _ _ FB). unfold bt_F at 3. unfold bt_U at 3. rewrite FC4B, SB4, TBEQ, HNPB.
      pose proof fmb_range. rewrite (wrap64_id (_ - zlen (pads b4 TB) + _)) by lia. rewrite wrap64_id by lia. lia. }
    assert (SLv : ds_static_len fY6 = Sstat syms).
    { rewrite EfY6. rewrite G2. rewrite SL5, Fsl, (fbs_static_len _ _ _ _ _ FB).
      rewrite Z.sub_0_l. replace (- bt_slpad s TL + zsum (map (fun j : Z => bt_F s TL j * (stree_Len TL j + xbits TL j)) (bt_U s TL)) - bt_slpad s TD + zsum (map (fun j : Z => bt_F s TD j * (stree_Len TD j + xbits TD j)) (bt_U s TD)))
        with (Sstat syms) by lia. apply wrap64_id. lia. }
    assert (K6 : kproj fY6 = kproj fs0).
    { rewrite EfY6, kp_set_opt_len, EfY5, kp_build_tree, EfY4, kp_scan_tree, EfY3, kp_scan_tree, EfY2, kp_build_tree, EfY1. apply kp_build_tree. }
    assert (GL' : forall X t i v, ds_pending_buf (set_Len X t i v) = ds_pending_buf X /\ ds_pending (set_Len X t i v) = ds_pending X
               /\ ds_bi_valid (set_Len X t i v) = ds_bi_valid X /\ ds_bi_buf (set_Len X t i v) = ds_bi_buf X) by (intros X [| |] i v; repeat split; reflexivity).
    assert (GB' : forall X b, ds_pending_buf (set_bl_tree_fc X b) = ds_pending_buf X /\ ds_pending (set_bl_tree_fc X b) = ds_pending X
               /\ ds_bi_valid (set_bl_tree_fc X b) = ds_bi_valid X /\ ds_bi_buf (set_bl_tree_fc X b) = ds_bi_buf X) by (intros X b; repeat split; reflexivity).
    assert (SH : ds_pending_buf fY5 = ds_pending_buf s /\ ds_pending fY5 = ds_pending s /\ ds_bi_valid fY5 = ds_bi_valid s /\ ds_bi_buf fY5 = ds_bi_buf s).
    { rewrite E5. autorewrite with btupd. rewrite EY4.
      destruct (GB' (set_Len fY3 TD (bt_mc s TD + 1) 65535) b4) as (A1 & A2 & A3 & A4). rewrite A1, A2, A3, A4.
      destruct (GL' fY3 TD (bt_mc s TD + 1) 65535) as (A5 & A6 & A7 & A8). rewrite A5, A6, A7, A8.
      rewrite EY3.
      destruct (GB' (set_Len fY2 TL (bt_mc s TL + 1) 65535) b3) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
      destruct (GL' fY2 TL (bt_mc s TL + 1) 65535) as (C5 & C6 & C7 & C8). rewrite C5, C6, C7, C8.
      rewrite E2. autorewrite with btupd. rewrite E1. autorewrite with btupd. rewrite Fpb, Fpd, Fbv, Fbb. repeat split; reflexivity. }
    destruct SH as (S1 & S2 & S3 & S4).
    pose proof (fbs_pending _ _ _ _ _ FB) as PD0. pose proof fmb_range as MBR. destruct syms_in_U as [SU S256].
    exists LL, LzL, LD, LzD, LB, LzB, b4. split.
    - exact B1. - exact B2. - rewrite FC1D; apply fs0_tree_fc. - exact B5. - exact FC4B. - exact Lb4. - exact NN4. - exact BS316.
    - exact LENS. - exact ZL. - exact GL. - exact LEND. - exact ZD. - exact GD. - exact LENB.
    - intros y Hy Hny; split; [apply ZB; assumption| apply B4Z; assumption].
    - exact MCL. - exact MCD. - exact RL. - exact RD. - exact SU. - exact S256.
    - rewrite EfY3, MCL2; reflexivity.
    - rewrite EfY4, MCD3; reflexivity.
    - exact LQ2'. - exact LQ3'.
    - rewrite BL2; exact Fbl.
    - rewrite EY4; reflexivity.
    - exact B0. - exact TL2. - exact TL3. - exact TL5. - exact SLv.
    - lia.
    - rewrite OLv; lia.
    - rewrite OLv; lia.
    - exact K6.
    - rewrite EfY6, G3, S1; reflexivity.
    - rewrite EfY6, G4, S2; exact PD0.
    - rewrite EfY6, G5, S3; reflexivity.
    - rewrite EfY6, G6, S4; reflexivity.
    - rewrite EfY6; apply G7.
    - rewrite EfY6; apply G7.
    - rewrite EfY6; apply G7.
    - rewrite EfY6; apply G8.
    - rewrite EfY6; apply G8.
    - exact TL4. - exact P1. - exact P2. - exact P5. - exact MCL2. - exact MCD3.
  Qed.
End FB.
