(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
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
