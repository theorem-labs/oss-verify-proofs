(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB5.

Module RefDeflSafeB6.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma build_tree_unfold : forall s t,
  build_tree s t =
  (let E := sd_elems t in
   let s0 := set_heap_max (set_heap_len s 0) HEAP_SIZE in
   let p1 := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
   let p2 := build_tree_loop2 2%nat (fst p1) t (snd p1) in
   let mc := snd p2 in
   let s3 := set_max_code (fst p2) t mc in
   let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
   let s5 := build_tree_loop4 573%nat s4 t E in
   let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
   let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
   gen_codes (gen_bitlen s7 t) t mc).
Proof.
  intros s t. unfold build_tree.
  destruct (build_tree_loop1 _ _ _ _ _ _) as [s1 mc1]. cbn [fst snd].
  destruct (build_tree_loop2 _ _ _ _) as [s2 mc]. reflexivity.
Qed.

Section BT6.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Hypothesis HP : bt_pre s t.

Lemma leaf_reindex : forall FC2 DL2 L mc FCf DLf HPf DPf (g : Z -> Z),
  heap_result t FC2 DL2 L mc FCf DLf HPf DPf ->
  zsum (fun i => zind (leafb t HPf i) * g (nd HPf i)) (HM L + 1) (Z.to_nat (572 - HM L))
  = zsum (fun c => zind (negb (arr_get FC2 c =? 0)) * g c) 0 (Z.to_nat E).
Proof.
  intros FC2 DL2 L mc FCf DLf HPf DPf g HR.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (elems_range t) as RE.
  transitivity (zsum (fun i => zsum (fun c => zind (leafb t HPf i && (nd HPf i =? c)) * g c) 0 (Z.to_nat E)) (HM L + 1) (Z.to_nat (572 - HM L))).
  - apply zsum_ext. intros i Hi. destruct (leafb t HPf i) eqn:Li; cbn [andb].
    + unfold leafb in Li. apply Z.ltb_lt in Li. pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)) as NC.
      rewrite (zsum_single (fun c => zind (nd HPf i =? c) * g c) 0 (Z.to_nat E) (nd HPf i)); [| lia |].
      * rewrite Z.eqb_refl. cbn [zind]. lia.
      * intros c Hc Nc. replace (nd HPf i =? c) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity.
    + cbn [zind]. rewrite Z.mul_0_l. symmetry. apply zsum_0. intros; reflexivity.
  - rewrite (zsum_swap (fun i c => zind (leafb t HPf i && (nd HPf i =? c)) * g c) 0 (Z.to_nat E) (HM L + 1) (Z.to_nat (572 - HM L))).
    apply zsum_ext. intros c Hc.
    transitivity (zsum (fun i => zind (leafb t HPf i && (nd HPf i =? c))) (HM L + 1) (Z.to_nat (572 - HM L)) * g c).
    { rewrite Z.mul_comm. rewrite <- zsum_scale. apply zsum_ext. intros; lia. }
    f_equal.
    destruct (Z.eqb_spec (arr_get FC2 c) 0) as [Fz|Fnz]; cbn [negb zind].
    + apply zsum_0. intros i Hi. destruct (leafb t HPf i) eqn:Li; cbn [andb]; [|reflexivity].
      destruct (Z.eqb_spec (nd HPf i) c) as [Ei|]; [|reflexivity]. exfalso.
      pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)) as [[A B]|A]; [| unfold leafb in Li; apply Z.ltb_lt in Li; lia].
      rewrite Ei in B. exact (B Fz).
    + destruct (hr_cov _ _ _ _ _ _ _ _ _ HR c ltac:(unfold Vj, V0, Vscan; left; lia)) as (p & Hp & Ep).
      assert (Np : p <> HM L) by (intros ->; unfold RefDeflSafeB3.HM in Ep; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Ep; lia).
      rewrite (zsum_single _ (HM L + 1) (Z.to_nat (572 - HM L)) p); [| unfold RefDeflSafeB3.HM in *; lia |].
      * unfold leafb, nd in *. rewrite Ep, Z.eqb_refl. replace (c <? E) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      * intros i Hi Ni. destruct (Z.eqb_spec (nd HPf i) c) as [Ei|]; [| rewrite Bool.andb_false_r; reflexivity].
        exfalso. apply Ni. apply (hr_inj _ _ _ _ _ _ _ _ _ HR i p); unfold RefDeflSafeB3.HM in *; try lia. unfold nd in Ei. rewrite Ei, Ep. reflexivity.
Qed.

Lemma xbits_small : forall c, 0 <= c <= 2 -> xbits t c = 0.
Proof.
  intros c Hc. unfold xbits. destruct t; cbn [sd_extra_base sd_extra_bits].
  - unfold LITERALS. replace (256 + 1 <=? c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
Qed.

Lemma zsum_list2 : forall (Fl : list Z) (w : Z -> Z) n,
  (length Fl <= 2)%nat -> NoDup Fl -> (forall f, In f Fl -> 0 <= f < Z.of_nat n) ->
  zsum (fun c => zind (existsb (Z.eqb c) Fl) * w c) 0 n = fold_right (fun f acc => w f + acc) 0 Fl.
Proof.
  intros Fl w n HL ND HIn. destruct Fl as [|a [|b [|c l]]]; cbn [fold_right existsb length] in *; [| | | lia].
  - apply zsum_0. intros; cbn [zind]; lia.
  - pose proof (HIn a (or_introl eq_refl)). rewrite (zsum_single _ 0 n a); [| lia |].
    + rewrite Z.eqb_refl. cbn [orb zind]. lia.
    + intros i Hi Ni. replace (i =? a) with false by (symmetry; apply Z.eqb_neq; exact Ni). cbn [orb zind]. lia.
  - pose proof (HIn a (or_introl eq_refl)). pose proof (HIn b (or_intror (or_introl eq_refl))).
    assert (Nab : a <> b). { intros ->. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. left. reflexivity. }
    rewrite (zsum_two _ 0 n a b); [| lia | lia | exact Nab |].
    + rewrite !Z.eqb_refl. replace (a =? b) with false by (symmetry; apply Z.eqb_neq; exact Nab).
      replace (b =? a) with false by (symmetry; apply Z.eqb_neq; congruence). cbn [orb zind]. lia.
    + intros i Hi N1 N2. replace (i =? a) with false by (symmetry; apply Z.eqb_neq; exact N1).
      replace (i =? b) with false by (symmetry; apply Z.eqb_neq; exact N2). cbn [orb zind]. lia.
Qed.

Lemma DLI_code : forall FC2 DL2 L mc FCf DLf HPf DPf DL' c,
  heap_result t FC2 DL2 L mc FCf DLf HPf DPf -> DLI t FC2 L HPf DL' -> 0 <= c < E ->
  (arr_get FC2 c = 0 -> arr_get DL' c = 0) /\ (arr_get FC2 c <> 0 -> 1 <= arr_get DL' c <= ML /\ c <= mc).
Proof.
  intros FC2 DL2 L mc FCf DLf HPf DPf DL' c HR HD Hc. split.
  - intros Z0. exact (dli_zero _ _ _ _ _ HD c Hc Z0).
  - intros NZ. split; [| apply (hr_mc_max _ _ _ _ _ _ _ _ _ HR); assumption].
    destruct (hr_cov _ _ _ _ _ _ _ _ _ HR c ltac:(unfold Vj, V0, Vscan; left; lia)) as (p & Hp & Ep).
    pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
    assert (Np : p <> 574 - 2 * L) by (intros ->; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Ep; lia).
    pose proof (dli_leaf _ _ _ _ _ HD p ltac:(unfold RefDeflSafeB3.HM; lia) ltac:(unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd; apply Z.ltb_lt; rewrite Ep; lia)) as X.
    unfold RefDeflSafeB3.nd in X. rewrite Ep in X. exact X.
Qed.

Theorem build_tree_facts :
  exists FCg DLg HPf DPf BCg L mc Fl SO SS,
    build_tree s t = bt_upd s t FCg DLg HPf 1 (574 - 2 * L) DPf BCg
                       (wrap64 (ds_opt_len s - Z.of_nat (length Fl) + SO))
                       (if stree_has t then wrap64 (ds_static_len s - fold_right (fun f acc => stree_Len t f + acc) 0 Fl + SS) else ds_static_len s) mc
    /\ 2 <= L <= E /\ 0 <= mc < E
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f <= 2 /\ f < E /\ arr_get (tree_fc s t) f = 0)
    /\ arr_len FCg = tsize t /\ arr_len DLg = tsize t /\ arr_len HPf = 573 /\ arr_len DPf = 573 /\ arr_len BCg = 16
    /\ (forall i, 0 <= arr_get FCg i < 65536) /\ (forall i, 0 <= arr_get DLg i < 65536)
    /\ (forall i, 0 <= arr_get DPf i < 256)
    /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BCg i <= 572)
    /\ (forall c, 0 <= c < E -> 0 <= arr_get DLg c <= ML)
    /\ (forall c, 0 <= c < E -> (arr_get (tree_fc s t) c <> 0 \/ In c Fl) -> 1 <= arr_get DLg c /\ c <= mc)
    /\ (forall c, 0 <= c < E -> arr_get (tree_fc s t) c = 0 -> ~ In c Fl -> arr_get DLg c = 0)
    /\ SO = zsum (fun c => arr_get (tree_fc s t) c * (arr_get DLg c + xbits t c)) 0 (Z.to_nat E)
            + fold_right (fun f acc => arr_get DLg f + xbits t f + acc) 0 Fl
    /\ SS = zsum (fun c => arr_get (tree_fc s t) c * (stree_Len t c + xbits t c)) 0 (Z.to_nat E)
            + fold_right (fun f acc => stree_Len t f + xbits t f + acc) 0 Fl
    /\ 0 <= zsum (fun c => arr_get (tree_fc s t) c * (arr_get DLg c + xbits t c)) 0 (Z.to_nat E) <= 2 ^ 31
    /\ 0 <= zsum (fun c => arr_get (tree_fc s t) c * (stree_Len t c + xbits t c)) 0 (Z.to_nat E) <= 2 ^ 31.
Proof.
  pose proof (elems_range t) as RE.
  pose proof (heap_phase_s s t HP) as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM.
  rewrite build_tree_unfold. cbv zeta. rewrite E7.
  set (p1 := build_tree_loop1 (Z.to_nat E) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t E 0 (-1)) in *.
  set (p2 := build_tree_loop2 2 (fst p1) t (snd p1)) in *.
  set (mc := snd p2) in *.
  set (FC := tree_fc s t) in *. set (FC2 := fc_forced Fl FC) in *.
  pose proof (LBC s t HP) as LB.
  assert (ROL : 0 <= ol_forced Fl (ds_opt_len s) < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_ol _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl (ds_static_len s) < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| apply (bp_sl _ _ HP)].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_sl _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_run t _ _ _ _ _ _ _ _ HR s (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) LB ROL RSL)
    as ((DL' & BC' & OL' & SL' & EG & HD & RO & RS & LB' & RBC) & _ & _).
  change (RefDeflSafeB3.HM L) with (574 - 2 * L) in EG. rewrite EG.
  set (X := bt_upd s t FCf DL' HPf 1 (574 - 2 * L) DPf BC' OL' SL' mc).
  assert (TLX : tree_lens X) by (subst X; apply bt_tree_lens; try assumption; [apply (bp_tl _ _ HP) | apply (hr_lfc _ _ _ _ _ _ _ _ _ HR) | apply (dli_len _ _ _ _ _ HD) | apply (hr_lhp _ _ _ _ _ _ _ _ _ HR) | apply (hr_ldp _ _ _ _ _ _ _ _ _ HR)]).
  unfold gen_codes. rewrite <- (stf_self X t).
  destruct (gen_codes_typed (Z.to_nat (mc + 1)) X t (tree_fc X t) (gen_codes_loop1 16 (ds_bl_count (set_tree_fc X t (tree_fc X t))) (arr_make (MAX_BITS + 1) 0) 0 1) mc 0)
    as (FCg & EC & LFCg & RFCg).
  { subst X. rewrite bt_tree_fc. apply (hr_lfc _ _ _ _ _ _ _ _ _ HR). }
  { subst X. rewrite bt_tree_fc. apply (hr_fcr _ _ _ _ _ _ _ _ _ HR). }
  rewrite EC. subst X. rewrite bt_set_tree_fc.
  set (SO := S_opt t FC2 L HPf DL'). set (SS := S_stat t FC2 L HPf).
  exists FCg, DL', HPf, DPf, BC', L, mc, Fl, SO, SS.
  assert (OLE : OL' = wrap64 (ds_opt_len s - Z.of_nat (length Fl) + SO)).
  { rewrite RO. subst SO. unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left length Z.of_nat] in *; [| | | lia].
    - f_equal. lia.
    - rewrite wrap64_add_l. try (f_equal; lia).
    - rewrite wrap64_add_l.
      replace (wrap64 (ds_opt_len s - 1) - 1 + S_opt t FC2 L HPf DL') with (wrap64 (ds_opt_len s - 1) + (S_opt t FC2 L HPf DL' - 1)) by lia.
      rewrite wrap64_add_l. try (f_equal; lia). }
  assert (SLE : SL' = (if stree_has t then wrap64 (ds_static_len s - fold_right (fun f acc => stree_Len t f + acc) 0 Fl + SS) else ds_static_len s)).
  { rewrite RS. subst SS. unfold sl_forced. destruct (stree_has t); [|reflexivity].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left fold_right length] in *; [| | | lia].
    - f_equal. lia.
    - rewrite wrap64_add_l. try (f_equal; lia).
    - rewrite wrap64_add_l.
      replace (wrap64 (ds_static_len s - stree_Len t a) - stree_Len t b + S_stat t FC2 L HPf) with (wrap64 (ds_static_len s - stree_Len t a) + (S_stat t FC2 L HPf - stree_Len t b)) by lia.
      rewrite wrap64_add_l. try (f_equal; lia). }
  assert (INFL : forall c, In c Fl <-> existsb (Z.eqb c) Fl = true).
  { intros c. rewrite existsb_exists. split.
    - intros Hc. exists c. split; [exact Hc | apply Z.eqb_refl].
    - intros (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. exact Hx. }
  assert (FC2E : forall c, arr_get FC2 c = if existsb (Z.eqb c) Fl then 1 else arr_get FC c) by exact FCE.
  assert (XB : forall c, 0 <= xbits t c <= 13).
  { intros c. unfold xbits. destruct (sd_extra_base t <=? c); [|lia]. destruct t; cbn [sd_extra_bits];
      [pose proof (extra_lbits_bound (c - sd_extra_base TL)) | pose proof (extra_dbits_bound (c - sd_extra_base TD)) | pose proof (extra_blbits_bound (c - sd_extra_base TB))]; lia. }
  assert (SLB : forall c, 0 <= stree_Len t c <= 9).
  { intros c. unfold stree_Len. destruct t; [pose proof (static_ltree_dl_bound c) | pose proof (static_dtree_dl_bound c) |]; lia. }
  assert (LEN : forall c, 0 <= c < E -> (arr_get FC2 c = 0 -> arr_get DL' c = 0) /\ (arr_get FC2 c <> 0 -> 1 <= arr_get DL' c <= ML /\ c <= mc)).
  { intros c Hc. exact (DLI_code _ _ _ _ _ _ _ _ DL' c HR HD Hc). }
  split; [rewrite OLE, SLE; reflexivity|].
  split; [exact RL|]. split; [lia|]. split; [exact LF|]. split; [exact ND|].
  split; [intros f Hf; destruct (FF f Hf) as (A & B & C0); lia|].
  split; [exact LFCg|]. split; [exact (dli_len _ _ _ _ _ HD)|]. split; [exact (hr_lhp _ _ _ _ _ _ _ _ _ HR)|]. split; [exact (hr_ldp _ _ _ _ _ _ _ _ _ HR)|]. split; [exact LB'|].
  split; [exact RFCg|]. split; [exact (dli_rng _ _ _ _ _ HD)|]. split; [exact (hr_dpr _ _ _ _ _ _ _ _ _ HR)|]. split; [exact RBC|].
  split.
  { intros c Hc. destruct (LEN c Hc) as [A B]. destruct (Z.eq_dec (arr_get FC2 c) 0) as [Z0|NZ]; [rewrite (A Z0); lia | pose proof (B NZ); lia]. }
  split.
  { intros c Hc HIn. destruct (LEN c Hc) as [_ B].
    assert (NZ : arr_get FC2 c <> 0).
    { rewrite FC2E. destruct HIn as [H1|H1]; [| apply INFL in H1; rewrite H1; lia]. destruct (existsb (Z.eqb c) Fl); [lia | exact H1]. }
    pose proof (B NZ). lia. }
  split.
  { intros c Hc Fz NIn. destruct (LEN c Hc) as [A _]. apply A. rewrite FC2E.
    destruct (existsb (Z.eqb c) Fl) eqn:Ex; [exfalso; apply NIn; apply INFL; exact Ex | exact Fz]. }
  assert (REIDX : forall (w : Z -> Z),
     zsum (fun i => zind (leafb t HPf i) * (arr_get FC2 (nd HPf i) * w (nd HPf i))) (HM L + 1) (Z.to_nat (572 - HM L))
     = zsum (fun c => arr_get FC c * w c) 0 (Z.to_nat E) + fold_right (fun f acc => w f + acc) 0 Fl).
  { intros w. rewrite (leaf_reindex _ _ _ _ _ _ _ _ (fun u => arr_get FC2 u * w u) HR).
    transitivity (zsum (fun c => arr_get FC c * w c + zind (existsb (Z.eqb c) Fl) * w c) 0 (Z.to_nat E)).
    - apply zsum_ext. intros c Hc. rewrite FC2E.
      destruct (existsb (Z.eqb c) Fl) eqn:Ex.
      + apply INFL in Ex. destruct (FF c Ex) as (A & B & _). rewrite B. cbn [Z.eqb negb zind]. lia.
      + destruct (Z.eqb_spec (arr_get FC c) 0) as [Z0|NZ]; cbn [negb zind]; [rewrite Z0; lia | lia].
    - rewrite zsum_add. f_equal. apply zsum_list2; [exact LF | exact ND | intros f Hf; destruct (FF f Hf); lia]. }
  split; [subst SO; unfold S_opt; exact (REIDX (fun u => arr_get DL' u + xbits t u))|].
  split; [subst SS; unfold S_stat, w_stat; apply (REIDX (fun u => stree_Len t u + xbits t u))|].
  split.
  { split.
    - apply zsum_nonneg. intros c Hc. pose proof (bp_fc _ _ HP c). pose proof (dli_rng _ _ _ _ _ HD c). pose proof (XB c). subst FC. nia.
    - apply (Z.le_trans _ (zsum (fun _ => 65535 * 28) 0 (Z.to_nat E))).
      + apply zsum_mono. intros c Hc. pose proof (bp_fc _ _ HP c). pose proof (XB c).
        destruct (LEN c ltac:(lia)) as [A B]. assert (0 <= arr_get DL' c <= 15) by (destruct (Z.eq_dec (arr_get FC2 c) 0) as [Z0|NZ]; [rewrite (A Z0); lia | pose proof (B NZ); lia]).
        subst FC. nia.
      + clear. assert (G : forall n lo, zsum (fun _ => 65535 * 28) lo n = Z.of_nat n * (65535 * 28)) by (induction n; intros; [reflexivity | rewrite zsum_snoc, IHn; lia]).
        rewrite G. pose proof (elems_range t). lia. }
  split.
  - apply zsum_nonneg. intros c Hc. pose proof (bp_fc _ _ HP c). pose proof (XB c). pose proof (SLB c). subst FC. nia.
  - apply (Z.le_trans _ (zsum (fun _ => 65535 * 22) 0 (Z.to_nat E))).
    + apply zsum_mono. intros c Hc. pose proof (bp_fc _ _ HP c). pose proof (XB c). pose proof (SLB c). subst FC. nia.
    + clear. assert (G : forall n lo, zsum (fun _ => 65535 * 22) lo n = Z.of_nat n * (65535 * 22)) by (induction n; intros; [reflexivity | rewrite zsum_snoc, IHn; lia]).
      rewrite G. pose proof (elems_range t). lia.
Qed.

End BT6.
End RefDeflSafeB6.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeB6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE1.

Module RefDeflSafeE2.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition trip_cnt (mn q p k x : Z) : Z :=
  if k <? mn then (if x =? q then k else 0)
  else if negb (q =? 0) then (if negb (q =? p) then zind (x =? q) else 0) + zind (x =? REP_3_6)
  else if k <=? 10 then zind (x =? REPZ_3_10)
  else zind (x =? REPZ_11_138).

Definition trip_cost (BD : Z -> Z) (mn q p k : Z) : Z :=
  if k <? mn then k * BD q
  else if negb (q =? 0) then (if negb (q =? p) then BD q else 0) + BD REP_3_6 + 2
  else if k <=? 10 then BD REPZ_3_10 + 3
  else BD REPZ_11_138 + 7.

Lemma trip_cnt_nonneg : forall mn q p k x, 0 <= k -> 0 <= trip_cnt mn q p k x.
Proof.
  intros. unfold trip_cnt. pose proof (zind_le1 (x =? q)). pose proof (zind_le1 (x =? REP_3_6)).
  pose proof (zind_le1 (x =? REPZ_3_10)). pose proof (zind_le1 (x =? REPZ_11_138)).
  destruct (k <? mn); [destruct (x =? q); lia|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); lia|]. destruct (k <=? 10); lia.
Qed.

Lemma trip_cnt_out : forall mn q p k x, x <> q -> x <> REP_3_6 -> x <> REPZ_3_10 -> x <> REPZ_11_138 -> trip_cnt mn q p k x = 0.
Proof.
  intros mn q p k x A B C D. unfold trip_cnt.
  replace (x =? q) with false by (symmetry; apply Z.eqb_neq; exact A).
  replace (x =? REP_3_6) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (x =? REPZ_3_10) with false by (symmetry; apply Z.eqb_neq; exact C).
  replace (x =? REPZ_11_138) with false by (symmetry; apply Z.eqb_neq; exact D). cbn [zind].
  destruct (k <? mn); [reflexivity|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); reflexivity|]. destruct (k <=? 10); reflexivity.
Qed.

Lemma trip_cnt_le : forall mn q p k x, 0 <= k -> trip_cnt mn q p k x <= (if k <? mn then k else 2).
Proof.
  intros. unfold trip_cnt. pose proof (zind_le1 (x =? q)). pose proof (zind_le1 (x =? REP_3_6)).
  pose proof (zind_le1 (x =? REPZ_3_10)). pose proof (zind_le1 (x =? REPZ_11_138)).
  destruct (k <? mn); [destruct (x =? q); lia|]. destruct (negb (q =? 0)); [destruct (negb (q =? p)); lia|]. destruct (k <=? 10); lia.
Qed.

Lemma trip_cost_cnt : forall BD mn q p k, 0 <= q <= 15 ->
  trip_cost BD mn q p k = zsum (fun x => trip_cnt mn q p k x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  intros BD mn q p k Hq.
  assert (XB : forall x, 0 <= x <= 15 -> arr_get extra_blbits_a x = 0).
  { intros x Hx. assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15) by lia.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H]; [reflexivity|] end. subst; reflexivity. }
  assert (X16 : arr_get extra_blbits_a REP_3_6 = 2) by reflexivity.
  assert (X17 : arr_get extra_blbits_a REPZ_3_10 = 3) by reflexivity.
  assert (X18 : arr_get extra_blbits_a REPZ_11_138 = 7) by reflexivity.
  unfold trip_cost, trip_cnt, REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (k <? mn).
  - rewrite (zsum_single (fun x => (if x =? q then k else 0) * (BD x + arr_get extra_blbits_a x)) 0 19 q) by
      (try lia; intros i Hi Ni; replace (i =? q) with false by (symmetry; apply Z.eqb_neq; exact Ni); lia).
    rewrite Z.eqb_refl, (XB q Hq). lia.
  - destruct (negb (q =? 0)).
    + transitivity (zsum (fun x => (if negb (q =? p) then zind (x =? q) else 0) * (BD x + arr_get extra_blbits_a x)
                              + zind (x =? 16) * (BD x + arr_get extra_blbits_a x)) 0 19); [| apply zsum_ext; intros; lia].
      rewrite zsum_add.
      rewrite (zsum_single (fun x => zind (x =? 16) * (BD x + arr_get extra_blbits_a x)) 0 19 16) by
        (try lia; intros i Hi Ni; replace (i =? 16) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
      rewrite Z.eqb_refl, X16. cbn [zind].
      destruct (negb (q =? p)).
      * rewrite (zsum_single (fun x => zind (x =? q) * (BD x + arr_get extra_blbits_a x)) 0 19 q) by
          (try lia; intros i Hi Ni; replace (i =? q) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, (XB q Hq). cbn [zind]. lia.
      * rewrite zsum_0 by (intros; lia). lia.
    + destruct (k <=? 10).
      * rewrite (zsum_single (fun x => zind (x =? 17) * (BD x + arr_get extra_blbits_a x)) 0 19 17) by
          (try lia; intros i Hi Ni; replace (i =? 17) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, X17. cbn [zind]. lia.
      * rewrite (zsum_single (fun x => zind (x =? 18) * (BD x + arr_get extra_blbits_a x)) 0 19 18) by
          (try lia; intros i Hi Ni; replace (i =? 18) with false by (symmetry; apply Z.eqb_neq; exact Ni); reflexivity).
        rewrite Z.eqb_refl, X18. cbn [zind]. lia.
Qed.

Lemma st_upd_cnt : forall mn b q p k x,
  0 <= q <= 15 -> 19 <= arr_len b -> 0 <= k ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) -> (forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p k y < 65536) ->
  arr_get (st_upd mn b q p k) x = arr_get b x + trip_cnt mn q p k x.
Proof.
  intros mn b q p k x Hq Hb Hk H0 HB.
  assert (G : forall a i v y, 0 <= i < arr_len a -> 0 <= v < 65536 ->
             arr_get (arr_set a i (wrap16 v)) y = if y =? i then v else arr_get a y).
  { intros a i v y Hi Hv. rewrite arr_get_set. unfold arr_inb.
    replace ((0 <=? i) && (i <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite (Z.eqb_sym i y). destruct (y =? i); cbn [andb]; [apply wrap16_id; lia | reflexivity]. }
  assert (T : forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p k y < 65536 /\ 0 <= arr_get b y) by (intros y Hy; split; [apply HB | apply H0]; exact Hy).
  unfold st_upd, trip_cnt in *. unfold REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (k <? mn) eqn:E1.
  - pose proof (T q ltac:(lia)) as Tq. rewrite Z.eqb_refl in Tq. rewrite G by lia. destruct (Z.eqb_spec x q) as [->|N]; lia.
  - destruct (negb (q =? 0)) eqn:E2.
    + pose proof (T 16 ltac:(lia)) as T16. rewrite Z.eqb_refl in T16.
      destruct (negb (q =? p)) eqn:E3.
      * pose proof (T q ltac:(lia)) as Tq. rewrite Z.eqb_refl in Tq.
        assert (Nq1 : (q =? 16) = false) by (apply Z.eqb_neq; lia). assert (Nq2 : (16 =? q) = false) by (apply Z.eqb_neq; lia).
        rewrite Nq1 in Tq. rewrite Nq2 in T16. cbn [zind Z.add] in Tq, T16.
        assert (I16 : arr_get (arr_set b q (wrap16 (arr_get b q + 1))) 16 = arr_get b 16) by (rewrite (G b q (arr_get b q + 1) 16) by lia; rewrite Nq2; reflexivity).
        rewrite (G (arr_set b q (wrap16 (arr_get b q + 1))) 16 _ x); [| rewrite arr_len_set; lia | rewrite I16; lia].
        rewrite I16. rewrite (G b q (arr_get b q + 1) x) by lia.
        destruct (Z.eqb_spec x 16) as [->|N16]; [rewrite Nq2; cbn [zind]; lia|].
        destruct (Z.eqb_spec x q) as [->|Nxq]; cbn [zind]; lia.
      * cbn [zind Z.add] in T16. rewrite G by lia. destruct (Z.eqb_spec x 16) as [->|N16]; cbn [zind]; lia.
    + destruct (k <=? 10) eqn:E4.
      * pose proof (T 17 ltac:(lia)) as T17. rewrite Z.eqb_refl in T17. cbn [zind] in T17. rewrite G by lia. destruct (Z.eqb_spec x 17) as [->|N]; cbn [zind]; lia.
      * pose proof (T 18 ltac:(lia)) as T18. rewrite Z.eqb_refl in T18. cbn [zind] in T18. rewrite G by lia. destruct (Z.eqb_spec x 18) as [->|N]; cbn [zind]; lia.
Qed.

Lemma st_calls_clen : forall s mn q p k, 1 <= k ->
  clen (st_calls s mn q p k) = trip_cost (fun x => Len s TB x) mn q p k.
Proof.
  intros s mn q p k Hk. unfold st_calls, trip_cost, blc.
  destruct (k <? mn); [rewrite clen_repeat; cbn [snd]; lia|].
  destruct (negb (q =? 0)); [destruct (negb (q =? p)); cbn [clen app]; lia|].
  destruct (k <=? 10); cbn [clen]; lia.
Qed.

Lemma st_calls_lens : forall s mn q p k,
  (forall x, 0 <= x < 19 -> 0 <= Len s TB x <= 16) -> 0 <= q <= 15 ->
  Forall (fun c => 0 <= snd c <= 16) (st_calls s mn q p k).
Proof.
  intros s mn q p k HB Hq. unfold st_calls, blc.
  destruct (k <? mn).
  - apply Forall_forall. intros c Hc. apply repeat_spec in Hc. subst c. cbn. apply HB. lia.
  - destruct (negb (q =? 0)).
    + destruct (negb (q =? p)); cbn [app]; repeat constructor; cbn; try lia; try (apply HB; unfold REP_3_6; lia).
    + destruct (k <=? 10); repeat constructor; cbn; try lia; apply HB; unfold REPZ_3_10, REPZ_11_138; lia.
Qed.


Fixpoint td_cnt (L : Z -> Z) (mc : Z) (fuel : nat) (n p q k mx mn : Z) (x : Z) : Z :=
  match fuel with
  | O => 0
  | S f =>
      if n <=? mc then
        let nl := L (n + 1) in
        let k' := k + 1 in
        if (k' <? mx) && (q =? nl) then td_cnt L mc f (n + 1) p nl k' mx mn x
        else let '(mx', mn') := tree_counts q nl in
             trip_cnt mn q p k' x + td_cnt L mc f (n + 1) q nl 0 mx' mn' x
      else 0
  end.

Fixpoint td_cost (BD L : Z -> Z) (mc : Z) (fuel : nat) (n p q k mx mn : Z) : Z :=
  match fuel with
  | O => 0
  | S f =>
      if n <=? mc then
        let nl := L (n + 1) in
        let k' := k + 1 in
        if (k' <? mx) && (q =? nl) then td_cost BD L mc f (n + 1) p nl k' mx mn
        else let '(mx', mn') := tree_counts q nl in
             trip_cost BD mn q p k' + td_cost BD L mc f (n + 1) q nl 0 mx' mn'
      else 0
  end.

Definition lens_ok (L : Z -> Z) (n mc : Z) : Prop := forall i, n < i <= mc -> 0 <= L i <= 15.

Lemma td_cnt_nonneg : forall L mc f n p q k mx mn x, 0 <= k -> 0 <= td_cnt L mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros; cbn [td_cnt]; [lia|].
  destruct (n <=? mc); [|lia]. cbv zeta. destruct (_ && _); [apply IH; lia|].
  destruct (tree_counts _ _). pose proof (trip_cnt_nonneg mn q p (k + 1) x ltac:(lia)). specialize (IH (n + 1) q (L (n + 1)) 0). pose proof (IH). 
  match goal with |- 0 <= _ + ?r => assert (0 <= r) by (apply IH; lia) end. lia.
Qed.

Lemma td_cnt_le : forall L mc f n p q k mx mn x, 0 <= k -> 0 <= n ->
  td_cnt L mc f n p q k mx mn x <= k + 2 * (Z.max 0 (mc + 1 - n)).
Proof.
  induction f as [|f IH]; intros n p q k mx mn x Hk Hn; cbn [td_cnt]; [lia|].
  destruct (Z.leb_spec n mc); [|lia]. cbv zeta. destruct (_ && _).
  - specialize (IH (n + 1) p (L (n + 1)) (k + 1) mx mn x ltac:(lia) ltac:(lia)). lia.
  - destruct (tree_counts _ _) as [mx' mn']. pose proof (trip_cnt_le mn q p (k + 1) x ltac:(lia)).
    specialize (IH (n + 1) q (L (n + 1)) 0 mx' mn' x ltac:(lia) ltac:(lia)).
    destruct (k + 1 <? mn); lia.
Qed.

Lemma td_cnt_out : forall L mc f n p q k mx mn x,
  lens_ok L n mc -> 0 <= q <= 15 -> (x < 0 \/ 19 <= x) -> td_cnt L mc f n p q k mx mn x = 0.
Proof.
  induction f as [|f IH]; intros n p q k mx mn x HL Hq Hx; cbn [td_cnt]; [reflexivity|].
  destruct (Z.leb_spec n mc); [|reflexivity]. cbv zeta.
  destruct (Z.eq_dec n mc) as [En|Nn].
  -
    destruct (_ && _).
    + cbn [td_cnt]. destruct f; [reflexivity|]. cbn [td_cnt]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + destruct (tree_counts _ _). rewrite trip_cnt_out by (unfold REP_3_6, REPZ_3_10, REPZ_11_138; lia).
      destruct f; [reflexivity|]. cbn [td_cnt]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - pose proof (HL (n + 1) ltac:(lia)) as Hl.
    destruct (_ && _).
    + apply IH; [intros i Hi; apply HL; lia | exact Hl | exact Hx].
    + destruct (tree_counts _ _). rewrite trip_cnt_out by (unfold REP_3_6, REPZ_3_10, REPZ_11_138; lia).
      rewrite IH; [lia | intros i Hi; apply HL; lia | exact Hl | exact Hx].
Qed.

Lemma td_cost_cnt : forall BD L mc f n p q k mx mn,
  lens_ok L n mc -> 0 <= q <= 15 ->
  td_cost BD L mc f n p q k mx mn = zsum (fun x => td_cnt L mc f n p q k mx mn x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  induction f as [|f IH]; intros n p q k mx mn HL Hq; cbn [td_cost td_cnt].
  - symmetry. apply zsum_0. intros; lia.
  - destruct (Z.leb_spec n mc); [| symmetry; apply zsum_0; intros; lia]. cbv zeta.
    destruct (Z.eq_dec n mc) as [En|Nn].
    +
      destruct (_ && _).
      * destruct f; cbn [td_cost td_cnt]; [symmetry; apply zsum_0; intros; lia|].
        replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). symmetry; apply zsum_0; intros; lia.
      * destruct (tree_counts _ _) as [mx' mn']. rewrite trip_cost_cnt by exact Hq.
        assert (R0 : td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' = 0 /\ forall x, td_cnt L mc f (n + 1) q (L (n + 1)) 0 mx' mn' x = 0).
        { destruct f; cbn [td_cost td_cnt]; [split; intros; reflexivity|].
          replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). split; intros; reflexivity. }
        destruct R0 as [A B]. rewrite A, Z.add_0_r. apply zsum_ext. intros x Hx. rewrite B. lia.
    + pose proof (HL (n + 1) ltac:(lia)) as Hl.
      assert (HL' : lens_ok L (n + 1) mc) by (intros i Hi; apply HL; lia).
      destruct (_ && _).
      * apply IH; assumption.
      * destruct (tree_counts _ _). rewrite trip_cost_cnt by exact Hq. rewrite (IH (n + 1) q (L (n + 1)) 0) by assumption.
        rewrite <- zsum_add. apply zsum_ext. intros; lia.
Qed.


Lemma scan_loop_cnt : forall f s0 b t mc n p q k mx mn,
  t <> TB -> lens_ok (fun i => Len s0 t i) n mc -> 0 <= q <= 15 -> 0 <= k -> 0 <= n -> 39 <= arr_len b ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) ->
  (forall y, 0 <= y < 19 -> arr_get b y + (k + 2 * Z.max 0 (mc + 1 - n)) < 65536) ->
  exists b', scan_tree_loop f (set_bl_tree_fc s0 b) t mc n p q k mx mn = set_bl_tree_fc s0 b'
    /\ arr_len b' = arr_len b
    /\ forall x, arr_get b' x = arr_get b x + td_cnt (fun i => Len s0 t i) mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros s0 b t mc n p q k mx mn Ht HL Hq Hk Hn Hb H0 HB.
  - exists b. rewrite scan_loop_0. split; [reflexivity|]. split; [reflexivity|]. intros; cbn; lia.
  - rewrite scan_loop_S. cbn [td_cnt]. destruct (Z.leb_spec n mc); [| exists b; split; [reflexivity|]; split; [reflexivity|]; intros; lia]. cbv zeta.
    destruct (Z.eq_dec n mc) as [En|Nn].
    +
      destruct (_ && _).
      * exists b. rewrite scan_loop_out by lia. split; [reflexivity|]. split; [reflexivity|]. intros x.
        destruct f; cbn [td_cnt]; [lia|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). lia.
      * destruct (tree_counts _ _) as [mx' mn'].
        exists (st_upd mn b q p (k + 1)). rewrite scan_loop_out by lia. split; [reflexivity|]. split; [apply st_upd_len|]. intros x.
        rewrite st_upd_cnt; [| lia | lia | lia | exact H0 |].
        2:{ intros y Hy. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        destruct f; cbn [td_cnt]; [lia|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). lia.
    + pose proof (HL (n + 1) ltac:(lia)) as Hl. assert (HL' : lens_ok (fun i => Len s0 t i) (n + 1) mc) by (intros i Hi; apply HL; lia).
      destruct (_ && _).
      * apply IH; try assumption; try lia. intros y Hy. pose proof (HB y Hy). lia.
      * destruct (tree_counts _ _) as [mx' mn'].
        assert (TB' : forall y, 0 <= y < 19 -> arr_get b y + trip_cnt mn q p (k + 1) y < 65536).
        { intros y Hy. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        destruct (IH s0 (st_upd mn b q p (k + 1)) t mc (n + 1) q (Len s0 t (n + 1)) 0 mx' mn' Ht HL' Hl ltac:(lia) ltac:(lia)) as (b' & E & Lb & Gb).
        { rewrite st_upd_len. lia. }
        { intros y Hy. rewrite st_upd_cnt; try lia; try assumption. pose proof (H0 y Hy). pose proof (trip_cnt_nonneg mn q p (k + 1) y ltac:(lia)). lia. }
        { intros y Hy. rewrite st_upd_cnt; try lia; try assumption. pose proof (trip_cnt_le mn q p (k + 1) y ltac:(lia)). pose proof (HB y Hy). destruct (k + 1 <? mn); lia. }
        exists b'. split; [exact E|]. rewrite st_upd_len in Lb. split; [exact Lb|]. intros x. rewrite Gb, st_upd_cnt; try lia; try assumption.
Qed.


Lemma send_loop_facts : forall f (L BD : Z -> Z) s t mc n p q k mx mn,
  (forall i, Len s t i = L i) -> (forall x, Len s TB x = BD x) ->
  1 <= mn -> 0 <= k -> lens_ok L n mc -> 0 <= q <= 15 ->
  (forall x, 0 <= x < 19 -> 0 <= BD x <= 16) -> 0 <= ds_bi_valid s <= 16 ->
  let s' := send_tree_loop f s t mc n p q k mx mn in
  ov_W s' = ov_W s + td_cost BD L mc f n p q k mx mn
  /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s')
  /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
  /\ (forall PBL, ov_W s' <= 8 * PBL -> send_tree_ok PBL f s t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros L BD s t mc n p q k mx mn ELn EBD Hmn Hk HL Hq HB Hbv s'; subst s'.
  - rewrite send_loop_0. cbn [td_cost send_tree_ok]. repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end.
  - rewrite send_loop_S by exact Hmn. cbn [td_cost send_tree_ok].
    destruct (Z.leb_spec n mc); [| repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end]. cbv zeta.
    rewrite !ELn.
    assert (HBs : forall x, 0 <= x < 19 -> 0 <= Len s TB x <= 16) by (intros x Hx; rewrite EBD; apply HB; exact Hx).
    assert (TRIP : forall mx' mn', 1 <= mn' -> 0 <= L (n + 1) <= 15 \/ n = mc ->
      let cs := st_calls s mn q p (k + 1) in
      let s1 := sbs_run s cs in
      let s' := send_tree_loop f s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn' in
      ov_W s' = ov_W s + (trip_cost BD mn q p (k + 1) + td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn')
      /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
      /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
      /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
      /\ (PBB s -> PBB s')
      /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
      /\ (forall PBL, ov_W s' <= 8 * PBL -> sbs_ok PBL s cs /\ send_tree_ok PBL f s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn')).
    { intros mx' mn' Hmn' Hl cs s1 s'. subst s'.
      pose proof (st_calls_lens s mn q p (k + 1) HBs Hq) as CL. fold cs in CL.
      pose proof (st_calls_clen s mn q p (k + 1) ltac:(lia)) as CC. fold cs in CC.
      assert (CC' : clen cs = trip_cost BD mn q p (k + 1)).
      { rewrite CC. unfold trip_cost. rewrite !EBD. reflexivity. }
      pose proof (sbs_W cs s) as W1. pose proof (sbs_nb_view cs s) as V1. pose proof (sbs_biv cs s Hbv CL) as B1.
      pose proof (sbs_pbl cs s) as P1. pose proof (sbs_pending_mono cs s) as M1. fold s1 in W1, V1, B1, P1, M1.
      pose proof (nb_view_facts _ _ V1) as (_ & _ & _ & _ & _ & _ & Vfc & Vdl & _).
      assert (EL : forall t' i, Len s1 t' i = Len s t' i) by (intros; unfold Len; rewrite Vdl; reflexivity).
      destruct (Z.eq_dec n mc) as [En|Nn].
      - rewrite !send_loop_out by lia.
        assert (TC0 : td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' = 0).
        { destruct f; cbn [td_cost]; [reflexivity|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite TC0. rewrite CC' in W1. split; [lia|]. split; [exact V1|]. split; [exact B1|]. split; [exact P1|]. split; [exact M1|].
        split; [intros i Hi; apply sbs_frame; exact Hi|]. split; [intros HP; apply sbs_PBB; exact HP|].
        split; [intros; apply sbs_bib; assumption|].
        intros PBL HW. split; [| destruct f; cbn [send_tree_ok]; [exact I|]; replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia); exact I].
        apply sbs_ok_of_bound; [exact Hbv | exact CL | lia].
      - destruct Hl as [Hl|Hl]; [|lia].
        assert (HL1 : lens_ok L (n + 1) mc) by (intros i Hi; apply HL; lia).
        specialize (IH L BD s1 t mc (n + 1) q (L (n + 1)) 0 mx' mn' ltac:(intros; rewrite EL; apply ELn) ltac:(intros; rewrite EL; apply EBD) Hmn' ltac:(lia) HL1 Hl HB B1).
        cbv zeta in IH.
        destruct IH as (IW & IV & IB & IP & IM & IF & IPB & IBB & IOK).
        rewrite W1, CC' in IW. split; [lia|]. split; [rewrite IV; exact V1|]. split; [exact IB|]. split; [rewrite IP; exact P1|]. split; [lia|].
        split; [intros i Hi; rewrite IF by lia; apply (sbs_frame cs s i); fold s1; lia|].
        split; [intros HP; apply IPB; apply sbs_PBB; exact HP|].
        split; [intros; apply IBB; apply sbs_bib; assumption|].
        intros PBL HW. split.
        + apply sbs_ok_of_bound; [exact Hbv | exact CL |].
          pose proof (td_cost_cnt BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn' HL1 Hl) as TCC.
          assert (0 <= td_cost BD L mc f (n + 1) q (L (n + 1)) 0 mx' mn').
          { rewrite TCC. apply zsum_nonneg. intros x Hx. pose proof (td_cnt_nonneg L mc f (n + 1) q (L (n + 1)) 0 mx' mn' x ltac:(lia)).
            pose proof (HB x ltac:(lia)). pose proof (extra_blbits_bound x). nia. }
          lia.
        + apply IOK. exact HW. }
    destruct ((k + 1 <? mx) && (q =? L (n + 1))) eqn:EC.
    + apply andb_prop in EC. destruct EC as [_ EC]. apply Z.eqb_eq in EC.
      destruct (Z.eq_dec n mc) as [En|Nn].
      * rewrite !send_loop_out by lia.
        assert (TC0 : td_cost BD L mc f (n + 1) p (L (n + 1)) (k + 1) mx mn = 0).
        { destruct f; cbn [td_cost]; [reflexivity|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        rewrite TC0. repeat split; intros; try reflexivity; try lia; try assumption; try (match goal with HP : PBB _ |- _ => apply HP; assumption end).
        destruct f; cbn [send_tree_ok]; [exact I|]. replace (n + 1 <=? mc) with false by (symmetry; apply Z.leb_gt; lia); exact I.
      * apply (IH L BD s t mc (n + 1) p (L (n + 1)) (k + 1) mx mn ELn EBD Hmn ltac:(lia)); try assumption.
        { intros i Hi; apply HL; lia. }
        { rewrite <- EC. exact Hq. }
    + destruct (tree_counts q (L (n + 1))) as [mx' mn'] eqn:ET.
      pose proof (tree_counts_range _ _ _ _ ET) as [_ Rmn'].
      apply (TRIP mx' mn' ltac:(lia)).
      destruct (Z.eq_dec n mc) as [En|Nn]; [right; exact En | left; apply HL; lia].
Qed.


Definition cnts0 (q : Z) : Z * Z := if q =? 0 then (138, 3) else (7, 4).

Definition TDcnt (L : Z -> Z) (mc : Z) (x : Z) : Z :=
  let '(mx, mn) := cnts0 (L 0) in td_cnt L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 mx mn x.
Definition TDcost (BD L : Z -> Z) (mc : Z) : Z :=
  let '(mx, mn) := cnts0 (L 0) in td_cost BD L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 mx mn.

Lemma cnts0_range : forall q, 1 <= snd (cnts0 q) /\ (fst (cnts0 q) = 138 \/ fst (cnts0 q) = 7) /\ (snd (cnts0 q) = 3 \/ snd (cnts0 q) = 4).
Proof. intros q. unfold cnts0. destruct (q =? 0); cbn; lia. Qed.

Lemma TDcost_cnt : forall BD L mc, (forall i, 0 <= i <= mc -> 0 <= L i <= 15) ->
  TDcost BD L mc = zsum (fun x => TDcnt L mc x * (BD x + arr_get extra_blbits_a x)) 0 19.
Proof.
  intros BD L mc HL. unfold TDcost, TDcnt. destruct (cnts0 (L 0)) as [mx mn].
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc].
  - replace (Z.to_nat (mc + 1)) with 0%nat by lia. cbn [td_cost td_cnt]. symmetry. apply zsum_0. intros; lia.
  - apply td_cost_cnt; [intros i Hi; apply HL; lia | apply HL; lia].
Qed.

Lemma TDcnt_nonneg : forall L mc x, 0 <= TDcnt L mc x.
Proof. intros. unfold TDcnt. destruct (cnts0 (L 0)). apply td_cnt_nonneg. lia. Qed.

Lemma TDcnt_le : forall L mc x, 0 <= mc -> TDcnt L mc x <= 2 * (mc + 1).
Proof. intros. unfold TDcnt. destruct (cnts0 (L 0)). pose proof (td_cnt_le L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 z z0 x ltac:(lia) ltac:(lia)). lia. Qed.

Lemma TDcnt_out : forall L mc x, (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> (x < 0 \/ 19 <= x) -> TDcnt L mc x = 0.
Proof.
  intros L mc x HL Hx. unfold TDcnt. destruct (cnts0 (L 0)).
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc]; [replace (Z.to_nat (mc + 1)) with 0%nat by lia; reflexivity|].
  apply td_cnt_out; [intros i Hi; apply HL; lia | apply HL; lia | exact Hx].
Qed.

Lemma set_Len_sbf : forall s0 b t i v, t <> TB -> set_Len (set_bl_tree_fc s0 b) t i v = set_bl_tree_fc (set_Len s0 t i v) b.
Proof. intros s0 b [| |] i v H; [ | | exfalso; apply H; reflexivity]; unfold set_Len, set_Dad; destruct s0; reflexivity. Qed.

Lemma ds_bl_tree_fc_set_Len : forall s0 t i v, t <> TB -> ds_bl_tree_fc (set_Len s0 t i v) = ds_bl_tree_fc s0.
Proof. intros s0 [| |] i v H; [ | | exfalso; apply H; reflexivity]; unfold set_Len, set_Dad; destruct s0; reflexivity. Qed.

Lemma scan_tree_cnt : forall s0 b t mc,
  t <> TB -> 0 <= mc -> mc + 1 < arr_len (tree_dl s0 t) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s0 t i <= 15) -> 39 <= arr_len b ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get b y) -> (forall y, 0 <= y < 19 -> arr_get b y + 2 * (mc + 1) < 65536) ->
  let s0' := set_Len s0 t (mc + 1) 65535 in
  exists b', scan_tree (set_bl_tree_fc s0 b) t mc = set_bl_tree_fc s0' b'
    /\ arr_len b' = arr_len b
    /\ (forall x, arr_get b' x = arr_get b x + TDcnt (fun i => Len s0' t i) mc x)
    /\ (forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i) /\ Len s0' t (mc + 1) = 65535.
Proof.
  intros s0 b t mc Ht Hmc Hlen HL Hb H0 HB s0'.
  assert (EL : forall i, Len s0' t i = if mc + 1 =? i then 65535 else Len s0 t i).
  { intros i. subst s0'. rewrite Len_set_Len by lia. destruct (mc + 1 =? i); [apply wrap16_id; lia | reflexivity]. }
  assert (EL' : forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i).
  { intros i Hi. rewrite EL. replace (mc + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  unfold scan_tree. rewrite sbf_Len. rewrite (set_Len_sbf s0 b t) by exact Ht. fold s0'.
  unfold TDcnt, cnts0. rewrite (EL' 0) by lia.
  assert (GO : forall mx mn : Z,
    exists b', scan_tree_loop (Z.to_nat (mc + 1)) (set_bl_tree_fc s0' b) t mc 0 (-1) (Len s0 t 0) 0 mx mn = set_bl_tree_fc s0' b'
      /\ arr_len b' = arr_len b
      /\ (forall x, arr_get b' x = arr_get b x + td_cnt (fun i => Len s0' t i) mc (Z.to_nat (mc + 1)) 0 (-1) (Len s0 t 0) 0 mx mn x)
      /\ (forall i, 0 <= i <= mc -> Len s0' t i = Len s0 t i) /\ Len s0' t (mc + 1) = 65535).
  { intros mx mn.
    destruct (scan_loop_cnt (Z.to_nat (mc + 1)) s0' b t mc 0 (-1) (Len s0 t 0) 0 mx mn Ht
                ltac:(intros i Hi; rewrite EL' by lia; apply HL; lia) ltac:(apply HL; lia) ltac:(lia) ltac:(lia) Hb H0
                ltac:(intros y Hy; pose proof (HB y Hy); lia)) as (b' & E & Lb & Gb).
    exists b'. split; [exact E|]. split; [exact Lb|]. split; [exact Gb|]. split; [exact EL'|].
    rewrite EL, Z.eqb_refl. reflexivity. }
  destruct (Len s0 t 0 =? 0); apply GO.
Qed.

Lemma send_tree_facts : forall (L BD : Z -> Z) s t mc,
  (forall i, Len s t i = L i) -> (forall x, Len s TB x = BD x) ->
  (forall i, 0 <= i <= mc -> 0 <= L i <= 15) ->
  (forall x, 0 <= x < 19 -> 0 <= BD x <= 16) -> 0 <= ds_bi_valid s <= 16 ->
  let s' := send_tree s t mc in
  ov_W s' = ov_W s + TDcost BD L mc
  /\ nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 16
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s) /\ ds_pending s <= ds_pending s'
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s')
  /\ (0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf s' < 2 ^ 16)
  /\ (forall PBL, ov_W s' <= 8 * PBL ->
        send_tree_ok PBL (Z.to_nat (mc + 1)) s t mc 0 (-1) (Len s t 0) 0 (fst (cnts0 (Len s t 0))) (snd (cnts0 (Len s t 0)))).
Proof.
  intros L BD s t mc EL EBD HL HB Hbv s'.
  destruct (Z_lt_le_dec mc 0) as [Hmc|Hmc].
  { subst s'. unfold send_tree, TDcost. rewrite EL. unfold cnts0.
    replace (Z.to_nat (mc + 1)) with 0%nat by lia.
    destruct (L 0 =? 0); rewrite send_loop_0; cbn [td_cost send_tree_ok fst snd];
      (repeat split; intros; try reflexivity; try lia; try assumption; match goal with HP : PBB _ |- _ => apply HP; assumption end). }
  pose proof (send_loop_facts (Z.to_nat (mc + 1)) L BD s t mc 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0))) EL EBD
                (proj1 (cnts0_range (L 0))) ltac:(lia) ltac:(intros i Hi; apply HL; lia) ltac:(apply HL; lia) HB Hbv) as F.
  cbv zeta in F.
  assert (ES : send_tree s t mc = send_tree_loop (Z.to_nat (mc + 1)) s t mc 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0)))).
  { unfold send_tree. rewrite EL. unfold cnts0. destruct (L 0 =? 0); reflexivity. }
  assert (EC : TDcost BD L mc = td_cost BD L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 (fst (cnts0 (L 0))) (snd (cnts0 (L 0)))).
  { unfold TDcost. destruct (cnts0 (L 0)); reflexivity. }
  subst s'. rewrite ES, EC, EL. exact F.
Qed.
End RefDeflSafeE2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.RefDeflSafeE2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma detect_loop1_range : forall f s n m r, detect_loop1 f s n m = Some r -> r = Z_BINARY.
Proof.
  induction f as [|f IH]; intros s n m r H; cbn [detect_loop1] in H; [discriminate|].
  destruct (Z.leb n 31); [|discriminate].
  destruct (_ && _); [injection H; intros <-; reflexivity | exact (IH _ _ _ _ H)].
Qed.

Lemma detect_loop2_range : forall f s n r, detect_loop2 f s n = Some r -> r = Z_TEXT.
Proof.
  induction f as [|f IH]; intros s n r H; cbn [detect_loop2] in H; [discriminate|].
  destruct (Z.ltb n LITERALS); [|discriminate].
  destruct (negb _); [injection H; intros <-; reflexivity | exact (IH _ _ _ H)].
Qed.

Lemma detect_data_type_range : forall s, 0 <= detect_data_type s <= 1.
Proof.
  intros s. unfold detect_data_type.
  destruct (detect_loop1 32 s 0 4093624447) eqn:E1; [apply detect_loop1_range in E1; subst; unfold Z_BINARY; lia|].
  destruct (_ || _); [unfold Z_TEXT; lia|].
  destruct (detect_loop2 224 s 32) eqn:E2; [apply detect_loop2_range in E2; subst|]; unfold Z_BINARY, Z_TEXT; lia.
Qed.

Lemma tfb_X0_eq : forall s, exists dt,
  tfb_X0 s = set_strm s (cset_data_type (ds_strm s) dt) /\ (dt = cs_data_type (ds_strm s) \/ 0 <= dt <= 1).
Proof.
  intros s. unfold tfb_X0.
  destruct ((0 <? ds_level s) && (cs_data_type (ds_strm s) =? Z_UNKNOWN)).
  - exists (detect_data_type s). split; [reflexivity | right; apply detect_data_type_range].
  - exists (cs_data_type (ds_strm s)). split; [| left; reflexivity]. destruct s; cbn; match goal with |- context [cset_data_type ?c _] => destruct c; reflexivity end.
Qed.

Definition nt_view (s : deflate_state) :=
  (ds_pending_buf s, ds_pending s, ds_bi_buf s, ds_bi_valid s, ds_lit_bufsize s, ds_sym_next s, ds_pending_out s,
   (ds_level s, ds_strategy s, ds_block_start s, ds_strstart s, ds_matches s, ds_window s, ds_w_size s, ds_lookahead s, ds_match_length s)).

Lemma nt_view_facts : forall a b, nt_view b = nt_view a ->
  ds_pending_buf b = ds_pending_buf a /\ ds_pending b = ds_pending a /\ ds_bi_buf b = ds_bi_buf a /\ ds_bi_valid b = ds_bi_valid a
  /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_sym_next b = ds_sym_next a /\ ds_pending_out b = ds_pending_out a
  /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_block_start b = ds_block_start a /\ ds_strstart b = ds_strstart a
  /\ ds_matches b = ds_matches a /\ ds_window b = ds_window a /\ ds_w_size b = ds_w_size a /\ ds_lookahead b = ds_lookahead a
  /\ ds_match_length b = ds_match_length a.
Proof. intros a b E. unfold nt_view in E. injection E. intros. repeat split; assumption. Qed.

Lemma nt_view_set_strm : forall s c, nt_view (set_strm s c) = nt_view s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma nt_view_bt_upd : forall s t FC DL HP HL HM DP BC OL SL MC, nt_view (bt_upd s t FC DL HP HL HM DP BC OL SL MC) = nt_view s.
Proof. intros; destruct s, t; reflexivity. Qed.
Lemma nt_view_sbf : forall s b, nt_view (set_bl_tree_fc s b) = nt_view s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma nt_view_set_Len : forall s t i v, nt_view (set_Len s t i v) = nt_view s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma nt_view_set_opt_len : forall s v, nt_view (set_opt_len s v) = nt_view s.
Proof. intros; destruct s; reflexivity. Qed.

Lemma strm_bt_upd : forall s t FC DL HP HL HM DP BC OL SL MC, ds_strm (bt_upd s t FC DL HP HL HM DP BC OL SL MC) = ds_strm s.
Proof. intros; destruct s, t; reflexivity. Qed.
Lemma strm_sbf : forall s b, ds_strm (set_bl_tree_fc s b) = ds_strm s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma strm_set_Len : forall s t i v, ds_strm (set_Len s t i v) = ds_strm s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma strm_set_opt_len : forall s v, ds_strm (set_opt_len s v) = ds_strm s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma strm_set_strm : forall s c, ds_strm (set_strm s c) = c.
Proof. intros; destruct s; reflexivity. Qed.

Lemma tree_fc_set_strm : forall s c t, tree_fc (set_strm s c) t = tree_fc s t.
Proof. intros s c [| |]; destruct s; reflexivity. Qed.
Lemma tree_dl_set_strm : forall s c t, tree_dl (set_strm s c) t = tree_dl s t.
Proof. intros s c [| |]; destruct s; reflexivity. Qed.
Lemma depth_set_strm : forall s c, ds_depth (set_strm s c) = ds_depth s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma opt_len_set_strm : forall s c, ds_opt_len (set_strm s c) = ds_opt_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma static_len_set_strm : forall s c, ds_static_len (set_strm s c) = ds_static_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma tree_lens_set_strm : forall s c, tree_lens s -> tree_lens (set_strm s c).
Proof. intros s c H. unfold tree_lens in *. destruct s; exact H. Qed.
Lemma bl_count_set_strm : forall s c, ds_bl_count (set_strm s c) = ds_bl_count s.
Proof. intros; destruct s; reflexivity. Qed.

Lemma max_code_set_strm : forall x c t, max_code (set_strm x c) t = max_code x t.
Proof. intros x c [| |]; destruct x; reflexivity. Qed.
Lemma max_code_bt_upd : forall x t FC DL HP HL HM DP BC OL SL MC, max_code (bt_upd x t FC DL HP HL HM DP BC OL SL MC) t = MC.
Proof. intros x [| |]; intros; destruct x; reflexivity. Qed.
Lemma max_code_bt_other : forall s t t' FC DL HP HL HM DP BC OL SL MC, t' <> t ->
  max_code (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' = max_code s t'.
Proof. intros s [| |] [| |] FC DL HP HL HM DP BC OL SL MC H; try (exfalso; apply H; reflexivity); destruct s; reflexivity. Qed.
Lemma max_code_sbf : forall s b t, max_code (set_bl_tree_fc s b) t = max_code s t.
Proof. intros s b [| |]; destruct s; reflexivity. Qed.
Lemma max_code_set_Len : forall s t i v t', max_code (set_Len s t i v) t' = max_code s t'.
Proof. intros s [| |] i v [| |]; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma depth_sbf : forall s b, ds_depth (set_bl_tree_fc s b) = ds_depth s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma depth_set_Len : forall s t i v, ds_depth (set_Len s t i v) = ds_depth s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma opt_len_sbf : forall s b, ds_opt_len (set_bl_tree_fc s b) = ds_opt_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma opt_len_set_Len : forall s t i v, ds_opt_len (set_Len s t i v) = ds_opt_len s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma static_len_sbf : forall s b, ds_static_len (set_bl_tree_fc s b) = ds_static_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma static_len_set_Len : forall s t i v, ds_static_len (set_Len s t i v) = ds_static_len s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma bl_count_sbf : forall s b, ds_bl_count (set_bl_tree_fc s b) = ds_bl_count s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma bl_count_set_Len : forall s t i v, ds_bl_count (set_Len s t i v) = ds_bl_count s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma tree_dl_set_Len_other : forall s t i v t', t' <> t -> tree_dl (set_Len s t i v) t' = tree_dl s t'.
Proof. intros s [| |] i v [| |] H; try (exfalso; apply H; reflexivity); unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma tree_lens_sbf : forall s b, tree_lens s -> arr_len b = 39 -> tree_lens (set_bl_tree_fc s b).
Proof. intros s b H L. unfold tree_lens in *. destruct s; cbn in *. rewrite L. tauto. Qed.
Lemma tree_lens_set_Len : forall s t i v, tree_lens s -> tree_lens (set_Len s t i v).
Proof.
  intros s t i v H. unfold tree_lens in *. unfold set_Len, set_Dad. destruct t; destruct s; cbn in *; rewrite arr_len_set; exact H.
Qed.
Lemma tree_lens_set_opt_len : forall s v, tree_lens s -> tree_lens (set_opt_len s v).
Proof. intros s v H. unfold tree_lens in *. destruct s; exact H. Qed.

Lemma tree_dl_set_Len_typed : forall s t i v t',
  (forall j, 0 <= arr_get (tree_dl s t') j < 65536) -> forall j, 0 <= arr_get (tree_dl (set_Len s t i v) t') j < 65536.
Proof.
  intros s t i v t' H j. unfold set_Len, set_Dad.
  destruct t, t'; destruct s; cbn [tree_dl set_tree_dl] in *; dsred; rewrite ?arr_get_set;
    first [apply H | destruct (_ && _); [apply wrap16_range | apply H]].
Qed.

Lemma xbits_small' : forall t c, 0 <= c <= 2 -> xbits t c = 0.
Proof.
  intros t c Hc. unfold xbits. destruct t; cbn [sd_extra_base sd_extra_bits].
  - unfold LITERALS. replace (256 + 1 <=? c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
Qed.

Lemma fold_ge_len : forall (Fl : list Z) (g : Z -> Z),
  (forall f, In f Fl -> 1 <= g f) -> Z.of_nat (length Fl) <= fold_right (fun f acc => g f + acc) 0 Fl.
Proof.
  induction Fl as [|a l IH]; intros g H; cbn [length fold_right]; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH g ltac:(intros f Hf; apply H; right; exact Hf)). lia.
Qed.

Lemma fold_split : forall (Fl : list Z) (g h : Z -> Z),
  fold_right (fun f acc => g f + h f + acc) 0 Fl = fold_right (fun f acc => g f + acc) 0 Fl + fold_right (fun f acc => h f + acc) 0 Fl.
Proof. induction Fl as [|a l IH]; intros; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma fold_zero : forall (Fl : list Z) (h : Z -> Z),
  (forall f, In f Fl -> h f = 0) -> fold_right (fun f acc => h f + acc) 0 Fl = 0.
Proof.
  induction Fl as [|a l IH]; intros h H; cbn [fold_right]; [lia|].
  rewrite (H a (or_introl eq_refl)), IH by (intros f Hf; apply H; right; exact Hf). lia.
Qed.

Lemma fold_nonneg : forall (Fl : list Z) (h : Z -> Z),
  (forall f, In f Fl -> 0 <= h f) -> 0 <= fold_right (fun f acc => h f + acc) 0 Fl.
Proof.
  induction Fl as [|a l IH]; intros h H; cbn [fold_right]; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH h ltac:(intros f Hf; apply H; right; exact Hf)). lia.
Qed.

Lemma if_stree_TL : forall (x y : Z), (if stree_has TL then x else y) = x. Proof. reflexivity. Qed.
Lemma if_stree_TD : forall (x y : Z), (if stree_has TD then x else y) = x. Proof. reflexivity. Qed.
Lemma if_stree_TB : forall (x y : Z), (if stree_has TB then x else y) = y. Proof. reflexivity. Qed.

Lemma Len_eq : forall x t i, Len x t i = arr_get (tree_dl x t) i. Proof. reflexivity. Qed.
Lemma max_code_TL : forall x, max_code x TL = ds_l_max_code x. Proof. reflexivity. Qed.
Lemma max_code_TD : forall x, max_code x TD = ds_d_max_code x. Proof. reflexivity. Qed.
Lemma tree_fc_TL : forall x, tree_fc x TL = ds_dyn_ltree_fc x. Proof. reflexivity. Qed.
Lemma tree_fc_TD : forall x, tree_fc x TD = ds_dyn_dtree_fc x. Proof. reflexivity. Qed.
Lemma tree_fc_TB : forall x, tree_fc x TB = ds_bl_tree_fc x. Proof. reflexivity. Qed.
Lemma tree_dl_TL : forall x, tree_dl x TL = ds_dyn_ltree_dl x. Proof. reflexivity. Qed.
Lemma tree_dl_TD : forall x, tree_dl x TD = ds_dyn_dtree_dl x. Proof. reflexivity. Qed.
Lemma tree_dl_TB : forall x, tree_dl x TB = ds_bl_tree_dl x. Proof. reflexivity. Qed.


Record TPF (s : deflate_state) : Prop := {
  tp_nt6 : nt_view (ov_X6 s) = nt_view s;
  tp_strm6 : ds_strm (ov_X6 s) = ds_strm (ov_X0 s);
  tp_X0 : exists dt, ov_X0 s = set_strm s (cset_data_type (ds_strm s) dt) /\ (dt = cs_data_type (ds_strm s) \/ 0 <= dt <= 1);
  tp_tl6 : tree_lens (ov_X6 s);
  tp_fc6 : forall t i, 0 <= arr_get (tree_fc (ov_X6 s) t) i < 65536;
  tp_dl6 : forall t i, 0 <= arr_get (tree_dl (ov_X6 s) t) i < 65536;
  tp_depth6 : forall i, 0 <= arr_get (ds_depth (ov_X6 s)) i < 256;
  tp_blc6 : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count (ov_X6 s)) i < 65536;
  tp_lmax : 0 <= ds_l_max_code (ov_X6 s) < L_CODES;
  tp_dmax : 0 <= ds_d_max_code (ov_X6 s) < D_CODES;
  tp_LD : forall i, 0 <= i <= ds_l_max_code (ov_X6 s) -> 0 <= Len (ov_X6 s) TL i <= 15;
  tp_DD : forall i, 0 <= i <= ds_d_max_code (ov_X6 s) -> 0 <= Len (ov_X6 s) TD i <= 15;
  tp_LDall : forall i, 0 <= i < L_CODES -> i <> ds_l_max_code (ov_X6 s) + 1 -> 0 <= Len (ov_X6 s) TL i <= 15;
  tp_DDall : forall i, 0 <= i < D_CODES -> i <> ds_d_max_code (ov_X6 s) + 1 -> 0 <= Len (ov_X6 s) TD i <= 15;
  tp_BD : forall x, 0 <= x < 19 -> 0 <= Len (ov_X6 s) TB x <= 7;
  tp_LDu : forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc s) c <> 0 -> 1 <= Len (ov_X6 s) TL c <= 15 /\ c <= ds_l_max_code (ov_X6 s);
  tp_DDu : forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc s) d <> 0 -> 1 <= Len (ov_X6 s) TD d <= 15 /\ d <= ds_d_max_code (ov_X6 s);
  tp_mb : 2 <= ov_mb s <= 18;
  tp_BC : forall x, 0 <= x < 19 ->
    arr_get (ov_BC s) x = TDcnt (fun i => Len (ov_X6 s) TL i) (ds_l_max_code (ov_X6 s)) x + TDcnt (fun i => Len (ov_X6 s) TD i) (ds_d_max_code (ov_X6 s)) x;
  tp_opt : 0 <= ds_opt_len (ov_X6 s) < 2 ^ 40;
  tp_opt_ge : 14 + 3 * (ov_mb s + 1)
              + zsum (fun x => arr_get (ov_BC s) x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x)) 0 19
              + zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c)) 0 (Z.to_nat L_CODES)
              + zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d)) 0 (Z.to_nat D_CODES)
              <= ds_opt_len (ov_X6 s);
  tp_stat : ds_static_len (ov_X6 s) =
              zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (stree_Len TL c + xbits TL c)) 0 (Z.to_nat L_CODES)
            + zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (stree_Len TD d + xbits TD d)) 0 (Z.to_nat D_CODES);
  tp_stat_range : 0 <= ds_static_len (ov_X6 s) < 2 ^ 40;
  tp_h1 : bt_safe (ov_X0 s) TL;
  tp_h2 : bt_safe (ov_X1 s) TD;
  tp_h3 : ds_l_max_code (ov_X2 s) = ds_l_max_code (ov_X6 s);
  tp_h4 : forall i, 0 <= i <= ds_l_max_code (ov_X2 s) -> 0 <= Len (ov_X2 s) TL i <= 15;
  tp_h5 : forall i, 0 <= arr_get (tree_dl (ov_X2 s) TL) i < 65536;
  tp_h6 : forall i, 0 <= arr_get (ds_bl_tree_fc (ov_X2 s)) i < 65536;
  tp_h7 : ds_d_max_code (ov_X3 s) = ds_d_max_code (ov_X6 s);
  tp_h8 : forall i, 0 <= i <= ds_d_max_code (ov_X3 s) -> 0 <= Len (ov_X3 s) TD i <= 15;
  tp_h9 : forall i, 0 <= arr_get (tree_dl (ov_X3 s) TD) i < 65536;
  tp_h10 : forall i, 0 <= arr_get (ds_bl_tree_fc (ov_X3 s)) i < 65536;
  tp_h11 : bt_safe (ov_X4 s) TB;
  tp_h12 : forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 16;
  tp_h12' : forall i, 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 65536;
  tp_h13 : 0 <= ds_opt_len (ov_X5 s) < 2 ^ 63 /\ 0 <= ds_static_len (ov_X5 s) < 2 ^ 63;
  tp_h14 : ds_strategy (ov_X5 s) = ds_strategy s;
  tp_h15 : ds_l_max_code (ov_X5 s) = ds_l_max_code (ov_X6 s) /\ ds_d_max_code (ov_X5 s) = ds_d_max_code (ov_X6 s)
           /\ ds_opt_len (ov_X6 s) = ds_opt_len (ov_X5 s) + 3 * (ov_mb s + 1) + 14
           /\ ds_static_len (ov_X6 s) = ds_static_len (ov_X5 s);
  tp_bp1 : bt_pre (ov_X1 s) TD;
  tp_bp4 : bt_pre (ov_X4 s) TB;
  tp_fc0L : tree_fc (ov_X0 s) TL = ds_dyn_ltree_fc s;
  tp_fc1D : tree_fc (ov_X1 s) TD = ds_dyn_dtree_fc s;
  tp_fc4B : tree_fc (ov_X4 s) TB = ov_BC s;
  tp_len1 : forall i, i <> ds_l_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TL i = arr_get (tree_dl (ov_X1 s) TL) i;
  tp_len2 : forall i, i <> ds_d_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TD i = arr_get (tree_dl (ov_X2 s) TD) i;
  tp_len5 : forall i, Len (ov_X6 s) TB i = arr_get (tree_dl (ov_X5 s) TB) i;
  tp_guard1 : Len (ov_X6 s) TL (ds_l_max_code (ov_X6 s) + 1) = 65535;
  tp_guard2 : Len (ov_X6 s) TD (ds_d_max_code (ov_X6 s) + 1) = 65535;
  tp_mc1 : max_code (ov_X1 s) TL = ds_l_max_code (ov_X6 s);
  tp_mc2 : max_code (ov_X2 s) TD = ds_d_max_code (ov_X6 s) }.

Section TreePhase.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.

Let TLs : tree_lens s := op_tl _ OP.

Lemma bt_pre_X0 : bt_pre (ov_X0 s) TL.
Proof.
  destruct (tfb_X0_eq s) as (dt & E & _). unfold ov_X0. rewrite E. constructor.
  - apply tree_lens_set_strm. exact TLs.
  - intros i. rewrite tree_fc_set_strm. apply (op_fc _ OP).
  - intros i. rewrite tree_dl_set_strm. apply (op_dl _ OP).
  - intros i. rewrite depth_set_strm. apply (op_depth _ OP).
  - rewrite opt_len_set_strm, (op_optlen _ OP). lia.
  - rewrite static_len_set_strm, (op_statlen _ OP). lia.
Qed.

Lemma zsum_bound : forall f lo n B, 0 <= B -> (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i <= B) -> 0 <= zsum f lo n <= Z.of_nat n * B.
Proof.
  intros f lo n B HB H. split; [apply zsum_nonneg; intros; apply H; assumption|].
  pose proof (zsum_mono f (fun _ => B) lo n ltac:(intros; apply H; assumption)) as M.
  assert (G : forall m l, zsum (fun _ => B) l m = Z.of_nat m * B) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
  rewrite G in M. lia.
Qed.

Theorem tree_phase : TPF s.
Proof.
  pose proof OP as [Rlbs Lpb Bpb P0 Rbv Rlv Rst SN RN SY FH OL0 SL0 TL0 TFC TDL TDP].
  destruct FH as (FHL & FHD & FHB).
  destruct (tfb_X0_eq s) as (dt & EX0 & Rdt). change (tfb_X0 s) with (ov_X0 s) in EX0.
  pose proof bt_pre_X0 as BP0.
  destruct (build_tree_facts (ov_X0 s) TL BP0) as (FC1 & DL1 & HP1 & DP1 & BC1 & L1 & mc1 & Fl1 & SO1 & SS1 & EX1 & RL1 & Rmc1 & LF1 & ND1 & FF1 & LFC1 & LDL1 & LHP1 & LDP1 & LBC1 & TFC1 & TDL1 & TDP1 & RBC1 & Len1 & Use1 & Unu1 & ESO1 & ESS1 & RSO1 & RSS1).
  change (build_tree (ov_X0 s) TL) with (ov_X1 s) in EX1. rewrite if_stree_TL in EX1.
  cbn [sd_elems sd_max_length tsize] in RL1, Rmc1, FF1, LFC1, LDL1, Len1, Use1, Unu1, ESO1, ESS1, RSO1, RSS1.
  assert (FC0L : tree_fc (ov_X0 s) TL = ds_dyn_ltree_fc s) by (rewrite EX0, tree_fc_set_strm; reflexivity).
  rewrite FC0L in FF1, Use1, Unu1, ESO1, ESS1, RSO1, RSS1. rewrite EX0 in EX1. rewrite opt_len_set_strm, static_len_set_strm, OL0, SL0 in EX1.
  assert (BP1 : bt_pre (ov_X1 s) TD).
  { rewrite EX1. constructor.
    - apply bt_tree_lens; try assumption. all: apply tree_lens_set_strm; exact TLs.
    - intros i. rewrite bt_tree_fc_other by discriminate. rewrite tree_fc_set_strm. apply TFC.
    - intros i. rewrite bt_tree_dl_other by discriminate. rewrite tree_dl_set_strm. apply TDL.
    - intros i. rewrite bt_depth. apply TDP1.
    - rewrite bt_opt_len. apply wrap64_range.
    - rewrite bt_static_len. apply wrap64_range. }
  destruct (build_tree_facts (ov_X1 s) TD BP1) as (FC2 & DL2 & HP2 & DP2 & BC2 & L2 & mc2 & Fl2 & SO2 & SS2 & EX2 & RL2 & Rmc2 & LF2 & ND2 & FF2 & LFC2 & LDL2 & LHP2 & LDP2 & LBC2 & TFC2 & TDL2 & TDP2 & RBC2 & Len2 & Use2 & Unu2 & ESO2 & ESS2 & RSO2 & RSS2).
  change (build_tree (ov_X1 s) TD) with (ov_X2 s) in EX2. rewrite if_stree_TD in EX2.
  cbn [sd_elems sd_max_length tsize] in RL2, Rmc2, FF2, LFC2, LDL2, Len2, Use2, Unu2, ESO2, ESS2, RSO2, RSS2.
  assert (FC1D : tree_fc (ov_X1 s) TD = ds_dyn_dtree_fc s) by (rewrite EX1, bt_tree_fc_other, tree_fc_set_strm by discriminate; reflexivity).
  rewrite FC1D in FF2, Use2, Unu2, ESO2, ESS2, RSO2, RSS2.
  assert (EX2' : ov_X2 s = bt_upd (bt_upd (set_strm s (cset_data_type (ds_strm s) dt)) TL FC1 DL1 HP1 1 (574 - 2 * L1) DP1 BC1
                                  (wrap64 (0 - Z.of_nat (length Fl1) + SO1)) (wrap64 (0 - fold_right (fun f acc => stree_Len TL f + acc) 0 Fl1 + SS1)) mc1)
                      TD FC2 DL2 HP2 1 (574 - 2 * L2) DP2 BC2
                      (wrap64 (ds_opt_len (ov_X1 s) - Z.of_nat (length Fl2) + SO2)) (wrap64 (ds_static_len (ov_X1 s) - fold_right (fun f acc => stree_Len TD f + acc) 0 Fl2 + SS2)) mc2).
  { rewrite EX2, EX1. reflexivity. }
  assert (P2dlL : tree_dl (ov_X2 s) TL = DL1) by (rewrite EX2', bt_tree_dl_other, bt_tree_dl by discriminate; reflexivity).
  assert (P2dlD : tree_dl (ov_X2 s) TD = DL2) by (rewrite EX2', bt_tree_dl; reflexivity).
  assert (P2dlB : tree_dl (ov_X2 s) TB = tree_dl s TB) by (rewrite EX2', bt_tree_dl_other, bt_tree_dl_other, tree_dl_set_strm by discriminate; reflexivity).
  assert (P2fcL : tree_fc (ov_X2 s) TL = FC1) by (rewrite EX2', bt_tree_fc_other, bt_tree_fc by discriminate; reflexivity).
  assert (P2fcD : tree_fc (ov_X2 s) TD = FC2) by (rewrite EX2', bt_tree_fc; reflexivity).
  assert (P2fcB : ds_bl_tree_fc (ov_X2 s) = ds_bl_tree_fc s) by (rewrite <- !tree_fc_TB, EX2', !bt_tree_fc_other, tree_fc_set_strm by discriminate; reflexivity).
  assert (P2mcL : ds_l_max_code (ov_X2 s) = mc1) by (rewrite <- max_code_TL, EX2', max_code_bt_other, max_code_bt_upd by discriminate; reflexivity).
  assert (P2mcD : ds_d_max_code (ov_X2 s) = mc2) by (rewrite <- max_code_TD, EX2', max_code_bt_upd; reflexivity).
  assert (P2dp : ds_depth (ov_X2 s) = DP2) by (rewrite EX2', bt_depth; reflexivity).
  assert (P2tl : tree_lens (ov_X2 s)).
  { rewrite EX2. apply bt_tree_lens; try assumption. exact (bp_tl _ _ BP1). }
  assert (P2nt : nt_view (ov_X2 s) = nt_view s) by (rewrite EX2', !nt_view_bt_upd, nt_view_set_strm; reflexivity).
  assert (P2st : ds_strm (ov_X2 s) = ds_strm (ov_X0 s)) by (rewrite EX2', !strm_bt_upd, EX0; reflexivity).
  pose proof (elems_range TL) as REL. pose proof (elems_range TD) as RED. cbn [sd_elems tsize sd_max_length] in REL, RED.
  assert (LdlL : arr_len (tree_dl (ov_X2 s) TL) = 573) by (rewrite P2dlL; exact LDL1).
  assert (HL15 : forall i, 0 <= i <= mc1 -> 0 <= Len (ov_X2 s) TL i <= 15).
  { intros i Hi. unfold Len. rewrite P2dlL. pose proof (Len1 i ltac:(unfold L_CODES; lia)) as X. unfold MAX_BITS in X. lia. }
  assert (Bz : forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc (ov_X2 s)) y = 0).
  { intros y Hy. rewrite P2fcB. apply FHB. unfold BL_CODES. exact Hy. }
  assert (Lb : arr_len (ds_bl_tree_fc (ov_X2 s)) = 39) by (pose proof P2tl as X; unfold tree_lens in X; tauto).
  destruct (scan_tree_cnt (ov_X2 s) (ds_bl_tree_fc (ov_X2 s)) TL mc1 ltac:(discriminate) ltac:(lia) ltac:(rewrite LdlL; unfold L_CODES in Rmc1; lia) HL15 ltac:(lia)
              ltac:(intros y Hy; rewrite Bz by exact Hy; lia) ltac:(intros y Hy; rewrite Bz by exact Hy; unfold L_CODES in Rmc1; lia))
    as (b3 & EX3 & Lb3 & Gb3 & EL3 & GL3).
  rewrite sbf_self in EX3.
  assert (D3 : ov_X3 s = scan_tree (ov_X2 s) TL mc1) by (unfold ov_X3; rewrite P2mcL; reflexivity).
  rewrite <- D3 in EX3. clear D3.
  set (s03 := set_Len (ov_X2 s) TL (mc1 + 1) 65535) in *.
  assert (LdlD : arr_len (tree_dl s03 TD) = 61) by (subst s03; rewrite tree_dl_set_Len_other, P2dlD by discriminate; exact LDL2).
  assert (HD15 : forall i, 0 <= i <= mc2 -> 0 <= Len s03 TD i <= 15).
  { intros i Hi. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. pose proof (Len2 i ltac:(unfold D_CODES; lia)) as X. unfold MAX_BITS in X. lia. }
  assert (B3r : forall y, 0 <= y < 19 -> 0 <= arr_get b3 y <= 2 * (mc1 + 1)).
  { intros y Hy. rewrite Gb3, Bz by exact Hy. pose proof (TDcnt_nonneg (fun i => Len s03 TL i) mc1 y). pose proof (TDcnt_le (fun i => Len s03 TL i) mc1 y ltac:(lia)). lia. }
  destruct (scan_tree_cnt s03 b3 TD mc2 ltac:(discriminate) ltac:(lia) ltac:(rewrite LdlD; unfold D_CODES in Rmc2; lia) HD15 ltac:(lia)
              ltac:(intros y Hy; pose proof (B3r y Hy); lia) ltac:(intros y Hy; pose proof (B3r y Hy); unfold L_CODES in Rmc1; unfold D_CODES in Rmc2; lia))
    as (b4 & EX4 & Lb4 & Gb4 & EL4 & GL4).
  assert (P3mcD : ds_d_max_code (ov_X3 s) = mc2).
  { rewrite <- max_code_TD, EX3, max_code_sbf. subst s03. rewrite max_code_set_Len, max_code_TD. exact P2mcD. }
  rewrite <- EX3 in EX4.
  assert (D4 : ov_X4 s = scan_tree (ov_X3 s) TD mc2) by (unfold ov_X4; rewrite P3mcD; reflexivity).
  rewrite <- D4 in EX4. clear D4.
  set (s04 := set_Len s03 TD (mc2 + 1) 65535) in *.
  assert (P4dlL : forall i, Len (ov_X4 s) TL i = Len s03 TL i).
  { intros i. unfold Len. rewrite EX4, sbf_tree_dl. unfold s04. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P4dlD : forall i, Len (ov_X4 s) TD i = Len s04 TD i) by (intros i; unfold Len; rewrite EX4, sbf_tree_dl; reflexivity).
  assert (P4dlB : tree_dl (ov_X4 s) TB = tree_dl s TB).
  { rewrite EX4, sbf_tree_dl. unfold s04, s03. rewrite !tree_dl_set_Len_other by discriminate. exact P2dlB. }
  assert (P4fcB : tree_fc (ov_X4 s) TB = b4) by (rewrite EX4, tree_fc_TB; apply sbf_get).
  assert (P4tl : tree_lens (ov_X4 s)).
  { rewrite EX4. apply tree_lens_sbf; [| rewrite Lb4, Lb3; exact Lb]. unfold s04, s03. apply tree_lens_set_Len, tree_lens_set_Len. exact P2tl. }
  assert (P4nt : nt_view (ov_X4 s) = nt_view s) by (rewrite EX4, nt_view_sbf; unfold s04, s03; rewrite !nt_view_set_Len; exact P2nt).
  assert (P4st : ds_strm (ov_X4 s) = ds_strm (ov_X0 s)) by (rewrite EX4, strm_sbf; unfold s04, s03; rewrite !strm_set_Len; exact P2st).
  assert (P4dp : ds_depth (ov_X4 s) = DP2) by (rewrite EX4, depth_sbf; unfold s04, s03; rewrite !depth_set_Len; exact P2dp).
  assert (P4ol : ds_opt_len (ov_X4 s) = ds_opt_len (ov_X2 s)) by (rewrite EX4, opt_len_sbf; unfold s04, s03; rewrite !opt_len_set_Len; reflexivity).
  assert (P4sl : ds_static_len (ov_X4 s) = ds_static_len (ov_X2 s)) by (rewrite EX4, static_len_sbf; unfold s04, s03; rewrite !static_len_set_Len; reflexivity).
  assert (P4mcL : ds_l_max_code (ov_X4 s) = mc1).
  { rewrite <- max_code_TL, EX4, max_code_sbf. unfold s04, s03. rewrite !max_code_set_Len, max_code_TL. exact P2mcL. }
  assert (P4mcD : ds_d_max_code (ov_X4 s) = mc2).
  { rewrite <- max_code_TD, EX4, max_code_sbf. unfold s04, s03. rewrite !max_code_set_Len, max_code_TD. exact P2mcD. }
  assert (T4dl : forall t i, 0 <= arr_get (tree_dl (ov_X4 s) t) i < 65536).
  { intros t i. rewrite EX4, sbf_tree_dl. unfold s04, s03. apply tree_dl_set_Len_typed. apply tree_dl_set_Len_typed.
    intros j. destruct t; [rewrite P2dlL; apply TDL1 | rewrite P2dlD; apply TDL2 | rewrite P2dlB; apply TDL]. }
  assert (HLs03 : forall j, 0 <= j <= mc1 -> 0 <= Len s03 TL j <= 15) by (intros j Hj; rewrite (EL3 j Hj); apply HL15; exact Hj).
  assert (HDs04 : forall j, 0 <= j <= mc2 -> 0 <= Len s04 TD j <= 15) by (intros j Hj; rewrite (EL4 j Hj); apply HD15; exact Hj).
  assert (TbB : forall i, 0 <= arr_get (ds_bl_tree_fc s) i < 65536) by (intros i; rewrite <- tree_fc_TB; apply TFC).
  assert (T4fcB : forall i, 0 <= arr_get b4 i < 65536).
  { intros i. rewrite (Gb4 i), (Gb3 i). destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [| destruct (Z_lt_le_dec i 19) as [Hi'|Hi']].
    - rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), (TDcnt_out (fun j => Len s04 TD j) mc2 i HDs04 ltac:(lia)).
      rewrite P2fcB. pose proof (TbB i). lia.
    - rewrite Bz by lia. pose proof (TDcnt_nonneg (fun j => Len s03 TL j) mc1 i). pose proof (TDcnt_le (fun j => Len s03 TL j) mc1 i ltac:(lia)).
      pose proof (TDcnt_nonneg (fun j => Len s04 TD j) mc2 i). pose proof (TDcnt_le (fun j => Len s04 TD j) mc2 i ltac:(lia)). unfold L_CODES, D_CODES in Rmc1, Rmc2. lia.
    - rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), (TDcnt_out (fun j => Len s04 TD j) mc2 i HDs04 ltac:(lia)).
      rewrite P2fcB. pose proof (TbB i). lia. }
  assert (BP4 : bt_pre (ov_X4 s) TB).
  { constructor.
    - exact P4tl.
    - intros i. rewrite P4fcB. apply T4fcB.
    - intros i. apply T4dl.
    - intros i. rewrite P4dp. apply TDP2.
    - rewrite P4ol, EX2', bt_opt_len. apply wrap64_range.
    - rewrite P4sl, EX2', bt_static_len. apply wrap64_range. }
  destruct (build_tree_facts (ov_X4 s) TB BP4) as (FC5 & DL5 & HP5 & DP5 & BC5 & L5 & mc5 & Fl5 & SO5 & SS5 & EX5 & RL5 & Rmc5 & LF5 & ND5 & FF5 & LFC5 & LDL5 & LHP5 & LDP5 & LBC5 & TFC5 & TDL5 & TDP5 & RBC5 & Len5 & Use5 & Unu5 & ESO5 & ESS5 & RSO5 & RSS5).
  change (build_tree (ov_X4 s) TB) with (ov_X5 s) in EX5. rewrite if_stree_TB in EX5.
  cbn [sd_elems sd_max_length tsize] in RL5, Rmc5, FF5, LFC5, LDL5, Len5, Use5, Unu5, ESO5, ESS5, RSO5, RSS5.
  rewrite P4fcB in FF5, Use5, Unu5, ESO5, ESS5, RSO5, RSS5.
  pose proof (build_bl_tree_loop_range 17 (ov_X5 s) 18 ltac:(lia)) as Rmb. change (build_bl_tree_loop 17 (ov_X5 s) 18) with (ov_mb s) in Rmb.
  assert (EX6 : ov_X6 s = bt_upd (ov_X4 s) TB FC5 DL5 HP5 1 (574 - 2 * L5) DP5 BC5
                           (wrap64 (wrap64 (ds_opt_len (ov_X4 s) - Z.of_nat (length Fl5) + SO5) + 3 * (ov_mb s + 1) + 5 + 5 + 4)) (ds_static_len (ov_X4 s)) mc5).
  { unfold ov_X6, tfb_X6. change (tfb_mb (ov_X5 s)) with (ov_mb s). rewrite EX5, bt_set_opt_len, bt_opt_len. reflexivity. }
  assert (EL3' : forall i, i <> mc1 + 1 -> Len s03 TL i = Len (ov_X2 s) TL i).
  { intros i Hi. subst s03. rewrite Len_set_Len by (rewrite LdlL; unfold L_CODES in Rmc1; lia).
    replace (mc1 + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (EL4' : forall i, i <> mc2 + 1 -> Len s04 TD i = Len (ov_X2 s) TD i).
  { intros i Hi. unfold s04. rewrite Len_set_Len by (rewrite LdlD; unfold D_CODES in Rmc2; lia).
    replace (mc2 + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). subst s03. unfold Len. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P4fcL : tree_fc (ov_X4 s) TL = FC1).
  { rewrite EX4, sbf_tree_fc by discriminate. unfold s04, s03. rewrite !tree_fc_set_Len. exact P2fcL. }
  assert (P4fcD : tree_fc (ov_X4 s) TD = FC2).
  { rewrite EX4, sbf_tree_fc by discriminate. unfold s04, s03. rewrite !tree_fc_set_Len. exact P2fcD. }
  assert (P6dlL : tree_dl (ov_X6 s) TL = tree_dl s03 TL).
  { rewrite EX6, bt_tree_dl_other, EX4, sbf_tree_dl by discriminate. unfold s04. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P6dlD : tree_dl (ov_X6 s) TD = tree_dl s04 TD) by (rewrite EX6, bt_tree_dl_other, EX4, sbf_tree_dl by discriminate; reflexivity).
  assert (P6dlB : tree_dl (ov_X6 s) TB = DL5) by (rewrite EX6, bt_tree_dl; reflexivity).
  assert (P6fcL : tree_fc (ov_X6 s) TL = FC1) by (rewrite EX6, bt_tree_fc_other by discriminate; exact P4fcL).
  assert (P6fcD : tree_fc (ov_X6 s) TD = FC2) by (rewrite EX6, bt_tree_fc_other by discriminate; exact P4fcD).
  assert (P6fcB : tree_fc (ov_X6 s) TB = FC5) by (rewrite EX6, bt_tree_fc; reflexivity).
  assert (P6mcL : ds_l_max_code (ov_X6 s) = mc1) by (rewrite <- max_code_TL, EX6, max_code_bt_other, max_code_TL by discriminate; exact P4mcL).
  assert (P6mcD : ds_d_max_code (ov_X6 s) = mc2) by (rewrite <- max_code_TD, EX6, max_code_bt_other, max_code_TD by discriminate; exact P4mcD).
  assert (P6nt : nt_view (ov_X6 s) = nt_view s) by (rewrite EX6, nt_view_bt_upd; exact P4nt).
  assert (P6LD : forall i, Len (ov_X6 s) TL i = Len s03 TL i) by (intros i; unfold Len; rewrite P6dlL; reflexivity).
  assert (P6DD : forall i, Len (ov_X6 s) TD i = Len s04 TD i) by (intros i; unfold Len; rewrite P6dlD; reflexivity).
  assert (P6BD : forall x, Len (ov_X6 s) TB x = arr_get DL5 x) by (intros x; unfold Len; rewrite P6dlB; reflexivity).
  assert (XB : forall t c, 0 <= xbits t c <= 13).
  { intros t c. unfold xbits. destruct (sd_extra_base t <=? c); [|lia]. destruct t; cbn [sd_extra_bits];
      [pose proof (extra_lbits_bound (c - sd_extra_base TL)) | pose proof (extra_dbits_bound (c - sd_extra_base TD)) | pose proof (extra_blbits_bound (c - sd_extra_base TB))]; lia. }
  assert (F1 : Z.of_nat (length Fl1) <= fold_right (fun f acc => arr_get DL1 f + xbits TL f + acc) 0 Fl1).
  { apply (fold_ge_len Fl1 (fun f => arr_get DL1 f + xbits TL f)). intros f Hf. destruct (FF1 f Hf) as (A & B & C0).
    pose proof (Use1 f ltac:(lia) (or_intror Hf)). pose proof (XB TL f). lia. }
  assert (F2 : Z.of_nat (length Fl2) <= fold_right (fun f acc => arr_get DL2 f + xbits TD f + acc) 0 Fl2).
  { apply (fold_ge_len Fl2 (fun f => arr_get DL2 f + xbits TD f)). intros f Hf. destruct (FF2 f Hf) as (A & B & C0).
    pose proof (Use2 f ltac:(lia) (or_intror Hf)). pose proof (XB TD f). lia. }
  assert (F5 : Z.of_nat (length Fl5) <= fold_right (fun f acc => arr_get DL5 f + xbits TB f + acc) 0 Fl5).
  { apply (fold_ge_len Fl5 (fun f => arr_get DL5 f + xbits TB f)). intros f Hf. destruct (FF5 f Hf) as (A & B & C0).
    pose proof (Use5 f ltac:(lia) (or_intror Hf)). pose proof (XB TB f). lia. }
  assert (LF1' : Z.of_nat (length Fl1) <= 2) by lia. assert (LF2' : Z.of_nat (length Fl2) <= 2) by lia. assert (LF5' : Z.of_nat (length Fl5) <= 2) by lia.
  assert (FB1 : fold_right (fun f acc => arr_get DL1 f + xbits TL f + acc) 0 Fl1 <= 2 * 28).
  { rewrite (fold_split Fl1 (fun f => arr_get DL1 f) (xbits TL)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl1 (fun f => arr_get DL1 f) 15 ltac:(intros f Hf; destruct (FF1 f Hf) as (A & B & C0); pose proof (Len1 f ltac:(lia)) as X; unfold MAX_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl1 (xbits TL) 13 ltac:(intros f Hf; pose proof (XB TL f); lia) ltac:(lia)). lia. }
  assert (FB2 : fold_right (fun f acc => arr_get DL2 f + xbits TD f + acc) 0 Fl2 <= 2 * 28).
  { rewrite (fold_split Fl2 (fun f => arr_get DL2 f) (xbits TD)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl2 (fun f => arr_get DL2 f) 15 ltac:(intros f Hf; destruct (FF2 f Hf) as (A & B & C0); pose proof (Len2 f ltac:(lia)) as X; unfold MAX_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl2 (xbits TD) 13 ltac:(intros f Hf; pose proof (XB TD f); lia) ltac:(lia)). lia. }
  assert (FB5 : fold_right (fun f acc => arr_get DL5 f + xbits TB f + acc) 0 Fl5 <= 2 * 28).
  { rewrite (fold_split Fl5 (fun f => arr_get DL5 f) (xbits TB)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl5 (fun f => arr_get DL5 f) 7 ltac:(intros f Hf; destruct (FF5 f Hf) as (A & B & C0); pose proof (Len5 f ltac:(lia)) as X; unfold MAX_BL_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl5 (xbits TB) 13 ltac:(intros f Hf; pose proof (XB TB f); lia) ltac:(lia)). lia. }
  set (DATL := zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (arr_get DL1 c + xbits TL c)) 0 (Z.to_nat L_CODES)) in *.
  set (DATD := zsum (fun c => arr_get (ds_dyn_dtree_fc s) c * (arr_get DL2 c + xbits TD c)) 0 (Z.to_nat D_CODES)) in *.
  set (DATB := zsum (fun c => arr_get b4 c * (arr_get DL5 c + xbits TB c)) 0 (Z.to_nat BL_CODES)) in *.
  set (STL := zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (stree_Len TL c + xbits TL c)) 0 (Z.to_nat L_CODES)) in *.
  set (STD := zsum (fun c => arr_get (ds_dyn_dtree_fc s) c * (stree_Len TD c + xbits TD c)) 0 (Z.to_nat D_CODES)) in *.
  assert (OL1 : ds_opt_len (ov_X1 s) = SO1 - Z.of_nat (length Fl1)).
  { rewrite EX1, bt_opt_len. rewrite wrap64_id by lia. lia. }
  assert (SLv1 : ds_static_len (ov_X1 s) = STL).
  { rewrite EX1, bt_static_len, ESS1. rewrite (fold_split Fl1 (stree_Len TL) (xbits TL)).
    rewrite (fold_zero Fl1 (xbits TL)) by (intros f Hf; destruct (FF1 f Hf) as (A & _); apply xbits_small'; exact A).
    rewrite wrap64_id by lia. lia. }
  assert (OL2 : ds_opt_len (ov_X2 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2))).
  { rewrite EX2, bt_opt_len, OL1. rewrite wrap64_id by lia. lia. }
  assert (SLv2 : ds_static_len (ov_X2 s) = STL + STD).
  { rewrite EX2, bt_static_len, SLv1, ESS2. rewrite (fold_split Fl2 (stree_Len TD) (xbits TD)).
    rewrite (fold_zero Fl2 (xbits TD)) by (intros f Hf; destruct (FF2 f Hf) as (A & _); apply xbits_small'; exact A).
    rewrite wrap64_id by lia. lia. }
  assert (OL5 : ds_opt_len (ov_X5 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2)) + (SO5 - Z.of_nat (length Fl5))).
  { rewrite EX5, bt_opt_len, P4ol, OL2. rewrite wrap64_id by lia. lia. }
  assert (OL6 : ds_opt_len (ov_X6 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2)) + (SO5 - Z.of_nat (length Fl5)) + 3 * (ov_mb s + 1) + 14).
  { rewrite EX6, bt_opt_len, P4ol, OL2. rewrite (wrap64_id (SO1 - _ + _ - _ + _)) by lia. rewrite wrap64_id by lia. lia. }
  assert (SL6 : ds_static_len (ov_X6 s) = STL + STD) by (rewrite EX6, bt_static_len, P4sl; exact SLv2).
  assert (SL5 : ds_static_len (ov_X5 s) = STL + STD) by (rewrite EX5, bt_static_len, P4sl; exact SLv2).
  constructor.
  - exact P6nt.
  - rewrite EX6, strm_bt_upd. exact P4st.
  - exists dt. split; [exact EX0 | exact Rdt].
  - rewrite EX6. apply bt_tree_lens; try assumption.
  - intros t i. destruct t; [rewrite P6fcL; apply TFC1 | rewrite P6fcD; apply TFC2 | rewrite P6fcB; apply TFC5].
  - intros t i. destruct t; [rewrite P6dlL | rewrite P6dlD | rewrite P6dlB; apply TDL5].
    + subst s03. apply tree_dl_set_Len_typed. intros j. rewrite P2dlL. apply TDL1.
    + unfold s04, s03. apply tree_dl_set_Len_typed. apply tree_dl_set_Len_typed. intros j. rewrite P2dlD. apply TDL2.
  - intros i. rewrite EX6, bt_depth. apply TDP5.
  - intros i Hi. rewrite EX6, bt_bl_count. pose proof (RBC5 i Hi). lia.
  - rewrite P6mcL. unfold L_CODES. lia.
  - rewrite P6mcD. unfold D_CODES. lia.
  - intros i Hi. rewrite P6mcL in Hi. rewrite P6LD, EL3 by lia. apply HL15. lia.
  - intros i Hi. rewrite P6mcD in Hi. rewrite P6DD, EL4 by lia. apply HD15. lia.
  - intros i Hi Ni. rewrite P6mcL in Ni. rewrite P6LD, EL3' by lia. unfold Len. rewrite P2dlL. pose proof (Len1 i ltac:(unfold L_CODES in Hi; lia)) as X. unfold MAX_BITS in X. lia.
  - intros i Hi Ni. rewrite P6mcD in Ni. rewrite P6DD, EL4' by lia. unfold Len. rewrite P2dlD. pose proof (Len2 i ltac:(unfold D_CODES in Hi; lia)) as X. unfold MAX_BITS in X. lia.
  - intros x Hx. rewrite P6BD. pose proof (Len5 x Hx) as X. unfold MAX_BL_BITS in X. lia.
  - intros c Hc Hf. rewrite P6mcL. pose proof (Use1 c ltac:(unfold L_CODES in Hc; lia) (or_introl Hf)) as [A B].
    rewrite P6LD, EL3 by lia. unfold Len. rewrite P2dlL. pose proof (Len1 c ltac:(unfold L_CODES in Hc; lia)) as X. unfold MAX_BITS in X. lia.
  - intros d Hd Hf. rewrite P6mcD. pose proof (Use2 d ltac:(unfold D_CODES in Hd; lia) (or_introl Hf)) as [A B].
    rewrite P6DD, EL4 by lia. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. pose proof (Len2 d ltac:(unfold D_CODES in Hd; lia)) as X. unfold MAX_BITS in X. lia.
  - exact Rmb.
  - intros x Hx. unfold ov_BC. rewrite <- tree_fc_TB, P4fcB, Gb4, Gb3, Bz by exact Hx. rewrite P6mcL, P6mcD.
    unfold Len. rewrite P6dlL, P6dlD. lia.
  - rewrite OL6. pose proof RSO1 as Q1. pose proof RSO2 as Q2. pose proof RSO5 as Q5. rewrite ESO1, ESO2, ESO5. clearbody DATL DATD DATB. lia.
  - unfold ov_BC. rewrite <- tree_fc_TB, P4fcB, OL6, ESO1, ESO2, ESO5. fold DATL DATD DATB.
    assert (EB : zsum (fun x => arr_get b4 x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x)) 0 19 = DATB).
    { subst DATB. apply zsum_ext. intros x Hx. rewrite P6BD. unfold xbits. cbn [sd_extra_base sd_extra_bits]. replace (0 <=? x) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r. reflexivity. }
    assert (ELs : zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c)) 0 (Z.to_nat L_CODES) = DATL).
    { subst DATL. apply zsum_ext. intros c Hc. rewrite P6LD.
      destruct (Z.eq_dec (arr_get (ds_dyn_ltree_fc s) c) 0) as [Z0|NZ]; [rewrite Z0; lia|].
      pose proof (Use1 c ltac:(unfold L_CODES in Hc; lia) (or_introl NZ)) as [A B].
      rewrite EL3 by lia. unfold Len. rewrite P2dlL. reflexivity. }
    assert (EDs : zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d)) 0 (Z.to_nat D_CODES) = DATD).
    { subst DATD. apply zsum_ext. intros d Hd. rewrite P6DD.
      destruct (Z.eq_dec (arr_get (ds_dyn_dtree_fc s) d) 0) as [Z0|NZ]; [rewrite Z0; lia|].
      pose proof (Use2 d ltac:(unfold D_CODES in Hd; lia) (or_introl NZ)) as [A B].
      rewrite EL4 by lia. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. reflexivity. }
    rewrite EB, ELs, EDs. lia.
  - rewrite SL6. reflexivity.
  - rewrite SL6. pose proof RSS1 as Q6. pose proof RSS2 as Q7. clearbody STL STD. lia.
  - exact (bt_safe_intro _ _ BP0).
  - exact (bt_safe_intro _ _ BP1).
  - rewrite P2mcL, P6mcL. reflexivity.
  - rewrite P2mcL. exact HL15.
  - intros i. rewrite P2dlL. apply TDL1.
  - intros i. rewrite P2fcB. apply TbB.
  - rewrite P3mcD, P6mcD. reflexivity.
  - intros i Hi. rewrite P3mcD in Hi. pose proof (HD15 i Hi) as X. rewrite Len_eq in X. rewrite Len_eq, EX3, sbf_tree_dl. exact X.
  - intros i. rewrite EX3, sbf_tree_dl. subst s03. apply tree_dl_set_Len_typed. intros j. rewrite P2dlD. apply TDL2.
  - intros i. rewrite EX3, sbf_get, Gb3. destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [| destruct (Z_lt_le_dec i 19) as [Hi'|Hi']].
    + rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), P2fcB. pose proof (TbB i). lia.
    + rewrite Bz by lia. pose proof (TDcnt_nonneg (fun j => Len s03 TL j) mc1 i). pose proof (TDcnt_le (fun j => Len s03 TL j) mc1 i ltac:(lia)). unfold L_CODES in Rmc1. lia.
    + rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), P2fcB. pose proof (TbB i). lia.
  - exact (bt_safe_intro _ _ BP4).
  - intros i Hi. rewrite <- tree_dl_TB, EX5, bt_tree_dl. pose proof (Len5 i Hi) as X. unfold MAX_BL_BITS in X. lia.
  - intros i. rewrite <- tree_dl_TB, EX5, bt_tree_dl. apply TDL5.
  - rewrite OL5, SL5. pose proof RSO1 as Q1. pose proof RSO2 as Q2. pose proof RSO5 as Q5. pose proof RSS1 as Q6. pose proof RSS2 as Q7. rewrite ESO1, ESO2, ESO5. clearbody DATL DATD DATB STL STD. lia.
  - assert (V5 : nt_view (ov_X5 s) = nt_view s) by (rewrite EX5, nt_view_bt_upd; exact P4nt).
    pose proof (nt_view_facts _ _ V5) as V. destruct V as (_ & _ & _ & _ & _ & _ & _ & _ & V9 & _). exact V9.
  - split; [| split; [| split]].
    + rewrite <- !max_code_TL, EX5, EX6, !max_code_bt_other by discriminate. reflexivity.
    + rewrite <- !max_code_TD, EX5, EX6, !max_code_bt_other by discriminate. reflexivity.
    + rewrite OL6, OL5. lia.
    + rewrite SL6, SL5. reflexivity.
  - exact BP1.
  - exact BP4.
  - exact FC0L.
  - exact FC1D.
  - unfold ov_BC. rewrite tree_fc_TB. reflexivity.
  - intros i Ni. rewrite P6mcL in Ni. rewrite P6LD, EL3' by lia. unfold Len. rewrite P2dlL, EX1, bt_tree_dl. reflexivity.
  - intros i Ni. rewrite P6mcD in Ni. rewrite P6DD, EL4' by lia. reflexivity.
  - intros i. rewrite P6BD, EX5, bt_tree_dl. reflexivity.
  - rewrite P6mcL, P6LD. subst s03. rewrite Len_set_Len by (rewrite LdlL; unfold L_CODES in Rmc1; lia). rewrite Z.eqb_refl. reflexivity.
  - rewrite P6mcD, P6DD. unfold s04. rewrite Len_set_Len by (rewrite LdlD; unfold D_CODES in Rmc2; lia). rewrite Z.eqb_refl. reflexivity.
  - rewrite EX1, max_code_bt_upd. symmetry. exact P6mcL.
  - rewrite P6mcD, max_code_TD. exact P2mcD.
Qed.
End TreePhase.
