(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild HuffBuild2 HuffFib HuffSpec HuffFlush HuffSend DeflRoom OverlayFBS OverlayRace OverlayCmp OverlayHdr OverlayFlush DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel ScanModel SendModel CompressModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma send_tree_ok_of_sbs : forall PBL f s t mc n p q c mx mn, (mn = 3 \/ mn = 4) ->
  sbs_ok PBL s (flat_map (em_calls s) (emits f (Len s t) mc n p q c mx mn)) ->
  send_tree_ok PBL f s t mc n p q c mx mn.
Proof.
  intros PBL. induction f as [|f IH]; intros s t mc n p q c mx mn Hmn OK; [exact I|].
  cbn [send_tree_ok]. cbn [emits] in OK. destruct (n <=? mc); [|exact I]. cbv zeta. cbv zeta in OK.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))).
  - apply IH; [exact Hmn| exact OK].
  - destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:TC. cbn [flat_map] in OK.
    apply sbs_ok_app in OK. destruct OK as [OK1 OK2]. unfold em_calls at 1 in OK1.
    split; [exact OK1|]. apply IH; [apply (tree_counts_range _ _ _ _ TC)|].
    rewrite (emits_ext _ (Len (sbs_run s (st_calls s mn q p (c + 1))) t) (Len s t)) by (intros; apply sbs_Len).
    assert (EMC : forall E, flat_map (em_calls (sbs_run s (st_calls s mn q p (c + 1)))) E = flat_map (em_calls s) E).
    { induction E as [|e E IHE]; cbn; [reflexivity|]. rewrite IHE. f_equal.
      destruct e as [[[mn0 cu] pr] ct]. unfold em_calls, st_calls, blc. rewrite !sbs_Code, !sbs_Len. reflexivity. }
    rewrite EMC. exact OK2.
Qed.

Definition sat_calls (s : deflate_state) (blcodes rank : Z) : list (Z * Z) :=
  map (fun r => (Len s TB (arr_get bl_order_a r), 3)) (ziota rank (Z.to_nat (blcodes - rank))).

Lemma sat_calls_lens_ok : forall s b r, lens_ok (sat_calls s b r).
Proof. intros. unfold sat_calls, lens_ok. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & _). cbn. lia. Qed.

Lemma send_tree_tabs : forall X t mc t',
  tree_dl (send_tree X t mc) t' = tree_dl X t' /\ tree_fc (send_tree X t mc) t' = tree_fc X t'.
Proof.
  intros X t mc t'. unfold send_tree. destruct (Len X t 0 =? 0).
  - destruct (send_loop_tree_fc (Z.to_nat (mc + 1)) X t mc 0 (-1) (Len X t 0) 0 138 3 t' ltac:(lia)) as (A & B & _). split; [exact B| exact A].
  - destruct (send_loop_tree_fc (Z.to_nat (mc + 1)) X t mc 0 (-1) (Len X t 0) 0 7 4 t' ltac:(lia)) as (A & B & _). split; [exact B| exact A].
Qed.

Lemma sat_tabs : forall X lc dc bc t',
  tree_dl (send_all_trees X lc dc bc) t' = tree_dl X t' /\ tree_fc (send_all_trees X lc dc bc) t' = tree_fc X t'.
Proof.
  intros X lc dc bc t'. unfold send_all_trees.
  destruct (send_tree_tabs (send_tree (send_all_trees_loop 19 (send_bits (send_bits (send_bits X (lc - 257) 5) (dc - 1) 5) (bc - 4) 4) bc 0) TL (lc - 1)) TD (dc - 1) t') as [A B].
  rewrite A, B.
  destruct (send_tree_tabs (send_all_trees_loop 19 (send_bits (send_bits (send_bits X (lc - 257) 5) (dc - 1) 5) (bc - 4) 4) bc 0) TL (lc - 1) t') as [C D].
  rewrite C, D. rewrite sat_loop_sbs by lia. rewrite sbs_tree_dl, sbs_tree_fc, !sb_tree_dl, !sb_tree_fc. split; reflexivity.
Qed.

Lemma dl_projL : forall X, ds_dyn_ltree_dl X = tree_dl X TL. Proof. reflexivity. Qed.
Lemma dl_projD : forall X, ds_dyn_dtree_dl X = tree_dl X TD. Proof. reflexivity. Qed.
Lemma fc_projL : forall X, ds_dyn_ltree_fc X = tree_fc X TL. Proof. reflexivity. Qed.
Lemma fc_projD : forall X, ds_dyn_dtree_fc X = tree_fc X TD. Proof. reflexivity. Qed.
Lemma Len_proj : forall X t n, arr_get (tree_dl X t) n = Len X t n. Proof. reflexivity. Qed.

Lemma sumlen_cons : forall v l r, sumlen ((v, l) :: r) = l + sumlen r.
Proof. reflexivity. Qed.


Section FB2.
  Variable syms : list (Z * Z).
  Variable s : deflate_state.
  Variable buf : option Z.
  Variables len last : Z.
  Hypothesis FB : FBS syms s buf len last.

  Local Notation nS := (nS syms).
  Local Notation LS := (LS s).
  Local Notation fs0 := (fs0 s).
  Variables fY1 fY2 fY3 fY4 fY5 fY6 : deflate_state.
  Local Notation fmb := (fmb fY5).
  Hypothesis EfY1 : fY1 = build_tree fs0 TL.
  Hypothesis EfY2 : fY2 = build_tree fY1 TD.
  Hypothesis EfY3 : fY3 = scan_tree fY2 TL (ds_l_max_code fY2).
  Hypothesis EfY4 : fY4 = scan_tree fY3 TD (ds_d_max_code fY3).
  Hypothesis EfY5 : fY5 = build_tree fY4 TB.
  Hypothesis EfY6 : fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb + 1) + 5 + 5 + 4)).
  Definition PBL : Z := arr_len (ds_pending_buf s).

  Variables fX7 fXh fXe : deflate_state.
  Hypothesis EfX7 : fX7 = send_bits fY6 (Z.shiftl DYN_TREES 1 + last) 3.
  Hypothesis EfXh : fXh = send_all_trees fX7 (ds_l_max_code fX7 + 1) (ds_d_max_code fX7 + 1) (fmb + 1).
  Hypothesis EfXe : fXe = compress_block fXh (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh).
  Definition THDR : Z := vsize fXh - vsize fX7.
  Definition dyncost : Z * Z -> Z := cost_of (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh).

  Local Ltac get_ff :=
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4' P1' P2' P5' MCL2' MCD3']).

  Lemma PBL4 : PBL = 4 * LS.
  Proof. unfold PBL, LS. pose proof (fbs_pbl _ _ _ _ _ FB) as E. exact E. Qed.

  Lemma fY6_frames :
    ds_lit_bufsize fY6 = LS /\ ds_sym_next fY6 = 3 * nS /\ arr_len (ds_pending_buf fY6) = PBL
    /\ ds_l_max_code fX7 = ds_l_max_code fY6 /\ ds_d_max_code fX7 = ds_d_max_code fY6
    /\ 0 <= ds_bi_valid fY6 <= 16 /\ 0 <= ds_bi_buf fY6 < 2 ^ 16 /\ ds_pending fY6 = 0
    /\ ds_strategy fY6 = ds_strategy s /\ ds_level fY6 = ds_level s.
  Proof.
    get_ff.
    pose proof (fs0_fields syms s buf len last FB) as (Fpb & Fpd & Fbv & Fbb & Flb & Fsn & Fbc & Fhp & Fdp & Fol & Fsl & Flv & Fst & Fwi & Fbl & Fse).
    split; [rewrite (kp_lit_bufsize _ _ K6), Flb; reflexivity|].
    split; [rewrite (kp_sym_next _ _ K6), Fsn; apply (fbs_sym_next _ _ _ _ _ FB)|].
    split; [rewrite PB6; reflexivity|].
    split; [rewrite EfX7, send_bits_shape; destruct fY6; reflexivity|].
    split; [rewrite EfX7, send_bits_shape; destruct fY6; reflexivity|].
    split; [rewrite BV6; apply (fbs_bi_valid _ _ _ _ _ FB)|].
    split; [rewrite BB6; apply (fbs_bi_buf _ _ _ _ _ FB)|].
    split; [exact PD6|].
    split; [rewrite (kp_strategy _ _ K6), Fst; reflexivity| rewrite (kp_level _ _ K6), Flv; reflexivity].
  Qed.

  Lemma sbs_tabs : forall cs, let X := sbs_run fX7 cs in
    (forall t n, Len X t n = Len fY5 t n) /\ (forall n, Code X TB n = Code fY6 TB n)
    /\ (forall t, tree_dl X t = tree_dl fY5 t) /\ tree_fc X TL = tree_fc fY5 TL /\ tree_fc X TD = tree_fc fY5 TD
    /\ ds_lit_bufsize X = LS /\ ds_sym_next X = 3 * nS /\ arr_len (ds_pending_buf X) = PBL
    /\ ds_l_max_code X = bt_mc s TL /\ ds_d_max_code X = bt_mc s TD.
  Proof.
    intros cs. cbv zeta. get_ff.
    pose proof fY6_frames as (F1 & F2 & F3 & F4 & F5 & _).
    assert (DL : forall t, tree_dl (sbs_run fX7 cs) t = tree_dl fY5 t).
    { intros t. rewrite sbs_tree_dl. rewrite EfX7. rewrite sb_tree_dl. destruct t; [exact DL6L| exact DL6D| exact DL6B]. }
    split; [intros t n; unfold Len; rewrite DL; reflexivity|].
    split; [intros n; rewrite sbs_Code; rewrite EfX7; rewrite sb_Code; reflexivity|].
    split; [exact DL|].
    split; [rewrite sbs_tree_fc; rewrite EfX7; rewrite sb_tree_fc; exact FC6L|].
    split; [rewrite sbs_tree_fc; rewrite EfX7; rewrite sb_tree_fc; exact FC6D|].
    assert (K : kproj (sbs_run fX7 cs) = kproj fY6).
    { clear - EfX7. induction cs as [|[v l] cs IH] using rev_ind; [rewrite EfX7; apply kp_send_bits|].
      rewrite sbs_run_app. cbn [sbs_run]. rewrite kp_send_bits. exact IH. }
    split; [rewrite (kp_lit_bufsize _ _ K); exact F1|]. split; [rewrite (kp_sym_next _ _ K); exact F2|].
    split; [rewrite (kp_len_pending_buf _ _ K); exact F3|].
    assert (MC : forall X v l, ds_l_max_code (send_bits X v l) = ds_l_max_code X /\ ds_d_max_code (send_bits X v l) = ds_d_max_code X).
    { intros X v l. rewrite send_bits_shape. destruct X; split; reflexivity. }
    assert (MCs : forall cs0 X, ds_l_max_code (sbs_run X cs0) = ds_l_max_code X /\ ds_d_max_code (sbs_run X cs0) = ds_d_max_code X).
    { induction cs0 as [|[v l] cs0 IH]; intros X; [split; reflexivity|]. cbn [sbs_run]. destruct (IH (send_bits X v l)) as [A B]. rewrite A, B. apply MC. }
    destruct (MCs cs fX7) as [A B]. rewrite A, B, F4, F5.
    assert (G : forall X v, ds_l_max_code (set_opt_len X v) = ds_l_max_code X /\ ds_d_max_code (set_opt_len X v) = ds_d_max_code X) by (intros X v; destruct X; split; reflexivity).
    rewrite EfY6. destruct (G fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb + 1) + 5 + 5 + 4))) as [G1 G2]. rewrite G1, G2, MCL, MCD. split; reflexivity.
  Qed.

  Lemma dyncost_dcost : forall LL LzL LD LzD LB LzB b4, flush_rec syms s fY1 fY2 fY3 fY4 fY5 fY6 LL LzL LD LzD LB LzB b4 ->
    forall x, In x syms -> dyncost x = dcost LzL LzD x /\ lens_ok (calls_of (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh) x)
      /\ (fst x = 0 -> 1 <= arr_get (ds_dyn_ltree_dl fXh) (snd x) <= 15)
      /\ (fst x <> 0 -> 1 <= arr_get (ds_dyn_ltree_dl fXh) (arr_get length_code_a (snd x) + LITERALS + 1) <= 15
                      /\ 1 <= arr_get (ds_dyn_dtree_dl fXh) (d_code (fst x - 1)) <= 15).
  Proof.
    intros LL LzL LD LzD LB LzB b4 F x Hx.
    destruct F as [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4' P1' P2' P5' MCL2' MCD3'].
    pose proof (sbs_tabs nil) as ST. cbn [sbs_run] in ST. destruct ST as (TLn & _ & TDL & _).
    unfold dyncost. pose proof (lcode_range syms s buf len last FB x Hx) as (R1 & R2 & R3). destruct (SU x Hx) as [I1 I2].
    rewrite (dl_projL fXh), (dl_projD fXh).
    destruct (sat_tabs fX7 (ds_l_max_code fX7 + 1) (ds_d_max_code fX7 + 1) (fmb + 1) TL) as [SL _].
    destruct (sat_tabs fX7 (ds_l_max_code fX7 + 1) (ds_d_max_code fX7 + 1) (fmb + 1) TD) as [SD _].
    rewrite <- EfXh in SL, SD. rewrite SL, SD. rewrite EfX7. rewrite !sb_tree_dl, DL6L, DL6D.
    pose proof (Len_proj fY5 TL) as TL'. pose proof (Len_proj fY5 TD) as TD'.
    destruct x as [d lc]. unfold dcost, ism, sdc, sym_lcode in *. cbn [fst] in *.
    destruct (Z.eqb_spec d 0) as [->|Hd]; cbn [negb] in *.
    - rewrite cost_of_lit. unfold calls_of. rewrite Z.eqb_refl. rewrite TL'. pose proof (LENS lc I1) as [E R]. rewrite E.
      rewrite xbits_TL. specialize (R3 eq_refl). replace (257 <=? lc) with false by (symmetry; apply Z.leb_gt; lia).
      split; [lia|]. split; [constructor; [cbn [snd]; lia| constructor]|]. cbn [fst snd]. split; [intros _; rewrite TL', E; lia| intros X; exfalso; apply X; reflexivity].
    - specialize (R2 eq_refl). specialize (I2 eq_refl).
      rewrite cost_of_match by exact Hd. unfold calls_of. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd). cbv zeta.
      rewrite !TL', !TD'. pose proof (LENS _ I1) as [E R]. pose proof (LEND _ I2) as [E2 Rd]. rewrite E, E2.
      rewrite xbits_TL, xbits_TD by lia. replace (257 <=? arr_get length_code_a lc + LITERALS + 1) with true by (symmetry; apply Z.leb_le; lia).
      unfold LITERALS in *. replace (arr_get length_code_a lc + 256 + 1 - 257) with (arr_get length_code_a lc) by lia.
      split; [lia|].
      pose proof (extra_lbits_range (arr_get length_code_a lc) ltac:(lia)). pose proof (extra_dbits_range (d_code (d - 1)) ltac:(lia)).
      split.
      + apply lens_ok_app; [constructor; [cbn [snd]; lia| constructor]|].
        apply lens_ok_app; [destruct (negb (arr_get extra_lbits_a (arr_get length_code_a lc) =? 0)); [constructor; [cbn [snd]; lia| constructor]| constructor]|].
        apply lens_ok_app; [constructor; [cbn [snd]; lia| constructor]|].
        destruct (negb (arr_get extra_dbits_a (d_code (d - 1)) =? 0)); [constructor; [cbn [snd]; lia| constructor]| constructor].
      + cbn [fst snd]. split; [intros X; exfalso; exact (Hd X)|]. intros _. lia.
  Qed.

  Definition HDR3 : list (Z * Z) := [(bt_mc s TL + 1 - 257, 5); (bt_mc s TD + 1 - 1, 5); (fmb + 1 - 4, 4)].

  Lemma header_sbs : exists EL ED,
    let HDR := HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED in
    fXh = sbs_run fX7 HDR /\ lens_ok HDR /\ sumlen HDR = THDR /\ 14 <= THDR <= 2283
    /\ csum dyncost syms + Len fY5 TL 256 + THDR <= ds_opt_len fY6 /\ 1 <= Len fY5 TL 256 <= 15
    /\ 0 <= csum dyncost syms <= 48 * nS
    /\ (forall X, (forall t n, Len X t n = Len fY5 t n) -> (forall n, Code X TB n = Code fY6 TB n) ->
          flat_map (em_calls X) EL = flat_map (em_calls fX7) EL /\ flat_map (em_calls X) ED = flat_map (em_calls fX7) ED
          /\ sat_calls X (fmb + 1) 0 = sat_calls fX7 (fmb + 1) 0
          /\ send_tree X TL (bt_mc s TL) = sbs_run X (flat_map (em_calls X) EL)
          /\ send_tree X TD (bt_mc s TD) = sbs_run X (flat_map (em_calls X) ED)
          /\ (forall P, sbs_ok P X (flat_map (em_calls X) EL) ->
                send_tree_ok P (Z.to_nat (bt_mc s TL + 1 - 0)) X TL (bt_mc s TL) 0 (-1) (Len X TL 0) 0
                  (fst (if Len X TL 0 =? 0 then (138, 3) else (7, 4))) (snd (if Len X TL 0 =? 0 then (138, 3) else (7, 4))))
          /\ (forall P, sbs_ok P X (flat_map (em_calls X) ED) ->
                send_tree_ok P (Z.to_nat (bt_mc s TD + 1 - 0)) X TD (bt_mc s TD) 0 (-1) (Len X TD 0) 0
                  (fst (if Len X TD 0 =? 0 then (138, 3) else (7, 4))) (snd (if Len X TD 0 =? 0 then (138, 3) else (7, 4)))))
    /\ THDR = 14 + 3 * (fmb + 1) + wsum (fun y => Len fY5 TB y + blx y) (ds_bl_tree_fc fY4).
  Proof.
    get_ff. pose proof fY6_frames as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
    pose proof (fbs_lens _ _ _ _ _ FB) as TL0. pose proof (fbs_cty _ _ _ _ _ FB) as CT.
    assert (BNN0 : bnn (ds_bl_tree_fc s)).
    { intros i Hi. apply (proj1 (ct_bfc _ CT i ltac:(unfold fbs_tree_lens in TL0; lia))). }
    assert (L2v : forall i, 0 <= i <= bt_mc s TL -> Len fY2 TL i = Len fY5 TL i).
    { intros i Hi. rewrite (LQ2 i) by lia. rewrite Len_set_Len by (rewrite (tree_lens_dl fY2 TL TL2); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TL + 1) i); [lia| reflexivity]. }
    assert (L3v : forall i, 0 <= i <= bt_mc s TD -> Len fY3 TD i = Len fY5 TD i).
    { intros i Hi. rewrite (LQ3 i) by lia. rewrite Len_set_Len by (rewrite (tree_lens_dl fY3 TD TL3); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TD + 1) i); [lia| reflexivity]. }
    assert (L5L : forall i, 0 <= i <= bt_mc s TL -> 0 <= Len fY5 TL i <= 15).
    { intros i Hi. destruct (in_dec Z.eq_dec i (bt_U s TL)) as [IN|NIN]; [pose proof (LENS i IN); lia| rewrite ZL by assumption; lia]. }
    assert (L5D : forall i, 0 <= i <= bt_mc s TD -> 0 <= Len fY5 TD i <= 15).
    { intros i Hi. destruct (in_dec Z.eq_dec i (bt_U s TD)) as [IN|NIN]; [pose proof (LEND i IN); lia| rewrite ZD by assumption; lia]. }
    assert (BS0 : bsum (ds_bl_tree_fc s) = 0).
    { unfold bsum. rewrite (zsum_map_ext _ (fun _ => 0)) by (intros y Hy; apply in_ziota in Hy; apply B0; lia). reflexivity. }
    destruct (scan_send fY2 TL (bt_mc s TL) ltac:(lia) ltac:(rewrite (tree_lens_dl fY2 TL TL2); cbn [tsize]; lia) TL2
                ltac:(rewrite BL2; exact BNN0) ltac:(intros i Hi; rewrite L2v by exact Hi; apply L5L; exact Hi) ltac:(rewrite BL2, BS0; lia))
      as (b3 & SC3 & Lb3 & NN3 & BS3 & M3 & SENDL). set (EL := scan_E fY2 TL (bt_mc s TL)) in *.
    assert (BL3 : ds_bl_tree_fc fY3 = b3) by (rewrite EY3, SC3; reflexivity).
    destruct (scan_send fY3 TD (bt_mc s TD) ltac:(lia) ltac:(rewrite (tree_lens_dl fY3 TD TL3); cbn [tsize]; lia) TL3
                ltac:(rewrite BL3; exact NN3) ltac:(intros i Hi; rewrite L3v by exact Hi; apply L5D; exact Hi) ltac:(rewrite BL3, BL2, BS0 in *; lia))
      as (b4' & SC4 & Lb4' & NN4' & BS4' & M4 & SENDD). set (ED := scan_E fY3 TD (bt_mc s TD)) in *.
    assert (Eb4 : b4' = b4) by (rewrite <- BL4, EY4, SC4; reflexivity). subst b4'.
    exists EL, ED. cbv zeta.
    assert (AGREE : forall X, (forall t n, Len X t n = Len fY5 t n) -> (forall n, Code X TB n = Code fY6 TB n) ->
              flat_map (em_calls X) EL = flat_map (em_calls fX7) EL /\ flat_map (em_calls X) ED = flat_map (em_calls fX7) ED
              /\ sat_calls X (fmb + 1) 0 = sat_calls fX7 (fmb + 1) 0).
    { intros X HL HC. pose proof (sbs_tabs nil) as S0. cbn [sbs_run] in S0. destruct S0 as (XL & XC & _).
      assert (EMC : forall E, flat_map (em_calls X) E = flat_map (em_calls fX7) E).
      { induction E as [|e E IHE]; cbn; [reflexivity|]. rewrite IHE. f_equal.
        destruct e as [[[mn0 cu] pr] ct]. unfold em_calls, st_calls, blc. rewrite !HL, !HC, !XL, !XC. reflexivity. }
      split; [apply EMC|]. split; [apply EMC|]. unfold sat_calls. apply map_ext. intros r. rewrite HL, XL. reflexivity. }
    pose proof (sbs_tabs nil) as S0. cbn [sbs_run] in S0. destruct S0 as (XL7 & XC7 & DL7 & FCL7 & FCD7 & LB7 & SN7 & PBL7 & MCL7 & MCD7).
    destruct (send_all_trees_sbs fX7 (bt_mc s TL + 1) (bt_mc s TD + 1) (fmb + 1) EL ED ltac:(pose proof (fmb_range fY5); lia)) as [SAT SUM].
    { intros X1 HL HC.
      assert (HL5 : forall t n, Len X1 t n = Len fY5 t n) by (intros; rewrite HL; apply XL7).
      split.
      - replace (bt_mc s TL + 1 - 1) with (bt_mc s TL) by lia. apply (proj1 (SENDL X1 ltac:(intros i Hi; rewrite HL5; apply LQ2; exact Hi))).
      - replace (bt_mc s TD + 1 - 1) with (bt_mc s TD) by lia. apply (proj1 (SENDD X1 ltac:(intros i Hi; rewrite HL5; apply LQ3; exact Hi))). }
    assert (EH : fXh = sbs_run fX7 (HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED)).
    { rewrite EfXh, MCL7, MCD7. rewrite SAT. unfold HDR3, sat_calls. rewrite Z.sub_0_r. reflexivity. }
    destruct (SENDL fX7 ltac:(intros i Hi; rewrite XL7; apply LQ2; exact Hi)) as [_ SUML].
    destruct (SENDD fX7 ltac:(intros i Hi; rewrite XL7; apply LQ3; exact Hi)) as [_ SUMD].
    rewrite BL3 in SUMD. rewrite BL2 in SUML.
    assert (W0 : wsum (fun y : Z => Len fX7 TB y + blx y) (ds_bl_tree_fc s) = 0).
    { unfold wsum. rewrite (zsum_map_ext _ (fun _ => 0)) by (intros y Hy; apply in_ziota in Hy; rewrite B0 by lia; lia). reflexivity. }
    assert (WE : wsum (fun y : Z => Len fX7 TB y + blx y) b4 = wsum (fun y => Len fY5 TB y + blx y) b4).
    { unfold wsum. apply zsum_map_ext. intros y Hy. rewrite XL7. reflexivity. }
    assert (ST : sumlen (HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED)
                 = 14 + 3 * (fmb + 1) + wsum (fun y => Len fY5 TB y + blx y) b4).
    { unfold HDR3, sat_calls. rewrite Z.sub_0_r. rewrite SUM, SUML, SUMD. lia. }
    assert (TH : THDR = 14 + 3 * (fmb + 1) + wsum (fun y => Len fY5 TB y + blx y) b4).
    { unfold THDR. rewrite EH, sbs_size, ST. lia. }
    assert (BL7 : forall y, 0 <= y <= 18 -> 0 <= Len fX7 TB y <= 7).
    { intros y Hy. rewrite XL7. destruct (in_dec Z.eq_dec y (bt_U fY4 TB)) as [IN|NIN]; [pose proof (LENB y IN); lia|].
      rewrite (proj1 (ZB y ltac:(lia) NIN)). lia. }
    assert (L2s : forall i, 0 <= i <= bt_mc s TL -> 0 <= Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL i <= 15).
    { intros i Hi. rewrite <- LQ2 by lia. apply L5L. exact Hi. }
    assert (L3s : forall i, 0 <= i <= bt_mc s TD -> 0 <= Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD i <= 15).
    { intros i Hi. rewrite <- LQ3 by lia. apply L5D. exact Hi. }
    assert (MN2 : (if Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0 then 3 else 4) = 3 \/ (if Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0 then 3 else 4) = 4).
    { destruct (Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0); lia. }
    assert (MN3 : (if Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0 then 3 else 4) = 3 \/ (if Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0 then 3 else 4) = 4).
    { destruct (Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0); lia. }
    pose proof (send_tree_bits_le fX7 BL7 (Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL) (bt_mc s TL)
                  (if Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0 then 138 else 7)
                  (if Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0 then 3 else 4)
                  ltac:(lia) MN2 L2s) as [STL LOL].
    pose proof (send_tree_bits_le fX7 BL7 (Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD) (bt_mc s TD)
                  (if Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0 then 138 else 7)
                  (if Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0 then 3 else 4)
                  ltac:(lia) MN3 L3s) as [STD LOD].
    change (emits _ _ _ _ _ _ _ _ _) with EL in STL, LOL. change (emits _ _ _ _ _ _ _ _ _) with ED in STD, LOD.
    split; [exact EH|].
    split. { apply lens_ok_app; [unfold HDR3; repeat constructor; cbn; lia|]. apply lens_ok_app; [apply sat_calls_lens_ok|]. apply lens_ok_app; assumption. }
    split; [rewrite TH; exact ST|].
    split. { rewrite TH. pose proof (fmb_range fY5). rewrite SUML, SUMD, W0 in *. rewrite <- WE. lia. }
    assert (CE : csum dyncost syms = csum (dcost LzL LzD) syms).
    { assert (G : forall l, (forall x, In x l -> In x syms) -> csum dyncost l = csum (dcost LzL LzD) l).
      { induction l as [|x l IH]; intros Hl; cbn [csum]; [reflexivity|].
        rewrite (proj1 (dyncost_dcost LL LzL LD LzD LB LzB b4 ltac:(split; assumption) x (Hl x (or_introl eq_refl)))).
        rewrite IH by (intros; apply Hl; right; assumption). reflexivity. }
      apply G. auto. }
    destruct (dyn_cost_sum syms s buf len last FB LzL LzD ltac:(intros j Hj; apply (proj2 (LENS j Hj))) ltac:(intros j Hj; apply (proj2 (LEND j Hj)))) as (_ & DCS2 & _).
    split. { rewrite TH. pose proof (LENS 256 S256) as [E256 _]. rewrite E256, CE. lia. }
    split; [pose proof (LENS 256 S256); lia|].
    split; [rewrite CE; exact DCS2|].
    split; [|rewrite BL4; exact TH].
    intros X HL HC. destruct (AGREE X HL HC) as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    assert (HLQ2 : forall i, 0 <= i <= bt_mc s TL + 1 -> Len X TL i = Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL i) by (intros i Hi; rewrite HL; apply LQ2; exact Hi).
    assert (HLQ3 : forall i, 0 <= i <= bt_mc s TD + 1 -> Len X TD i = Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD i) by (intros i Hi; rewrite HL; apply LQ3; exact Hi).
    split; [apply (proj1 (SENDL X HLQ2))|]. split; [apply (proj1 (SENDD X HLQ3))|].
    split.
    - intros P OK. apply send_tree_ok_of_sbs; [destruct (Len X TL 0 =? 0); cbn; lia|].
      replace (Z.to_nat (bt_mc s TL + 1 - 0)) with (Z.to_nat (bt_mc s TL + 1)) by lia.
      rewrite (emits_ext_upto _ (Len X TL) (Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL)) by (lia || (intros; apply HLQ2; lia)).
      rewrite (HLQ2 0) by lia. revert OK. subst EL. unfold scan_E. cbv zeta.
      destruct (Len (set_Len fY2 TL (bt_mc s TL + 1) 65535) TL 0 =? 0); cbn [fst snd]; intros OK; exact OK.
    - intros P OK. apply send_tree_ok_of_sbs; [destruct (Len X TD 0 =? 0); cbn; lia|].
      replace (Z.to_nat (bt_mc s TD + 1 - 0)) with (Z.to_nat (bt_mc s TD + 1)) by lia.
      rewrite (emits_ext_upto _ (Len X TD) (Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD)) by (lia || (intros; apply HLQ3; lia)).
      rewrite (HLQ3 0) by lia. revert OK. subst ED. unfold scan_E. cbv zeta.
      destruct (Len (set_Len fY3 TD (bt_mc s TD + 1) 65535) TD 0 =? 0); cbn [fst snd]; intros OK; exact OK.
  Qed.


  Lemma init_block_bits : forall X,
    ds_pending (init_block X) = ds_pending X /\ ds_bi_valid (init_block X) = ds_bi_valid X
    /\ ds_bi_buf (init_block X) = ds_bi_buf X /\ ds_pending_buf (init_block X) = ds_pending_buf X /\ ds_strm (init_block X) = ds_strm X.
  Proof. intros X. destruct X; repeat split; reflexivity. Qed.

  Lemma bi_windup_bits : forall P X, BINV P X -> ds_pending X + 2 <= P ->
    BINV P (bi_windup X) /\ ds_bi_valid (bi_windup X) = 0 /\ ds_bi_buf (bi_windup X) = 0
    /\ ds_pending X <= ds_pending (bi_windup X) <= ds_pending X + 2 /\ vsize (bi_windup X) <= vsize X + 7
    /\ arr_len (ds_pending_buf (bi_windup X)) = arr_len (ds_pending_buf X) /\ ds_strm (bi_windup X) = ds_strm X.
  Proof.
    intros P X (B1 & B2 & B3) R. unfold bi_windup, put_short, put_byte, BINV, vsize. 
    destruct (Z.ltb_spec 8 (ds_bi_valid X)); [|destruct (Z.ltb_spec 0 (ds_bi_valid X))]; dsred; rewrite ?arr_len_set; repeat split; try lia.
  Qed.

  Definition fX10 : deflate_state := sbs_run fX7 HDR3.
  Definition fX11 : deflate_state := send_all_trees_loop 19 fX10 (fmb + 1) 0.
  Definition fX12 : deflate_state := send_tree fX11 TL (bt_mc s TL).

  Theorem dyn_branch :
    ds_opt_len fY6 <= ds_static_len fY6 ->
    vsize fXh + excess dyncost syms <= 8 * LS + 7 ->
       BINV PBL fY6 /\ sb_room PBL fY6 3
    /\ sb_room PBL fX7 5 /\ sb_room PBL (send_bits fX7 (bt_mc s TL + 1 - 257) 5) 5
    /\ sb_room PBL (send_bits (send_bits fX7 (bt_mc s TL + 1 - 257) 5) (bt_mc s TD + 1 - 1) 5) 4
    /\ fX10 = send_bits (send_bits (send_bits fX7 (bt_mc s TL + 1 - 257) 5) (bt_mc s TD + 1 - 1) 5) (fmb + 1 - 4) 4
    /\ sbs_ok PBL fX10 (sat_calls fX10 (fmb + 1) 0)
    /\ (forall i, 0 <= i <= bt_mc s TL -> 0 <= Len fX11 TL i <= 15) /\ (forall c, 0 <= c < 19 -> 0 <= Len fX11 TB c <= 7)
    /\ send_tree_ok PBL (Z.to_nat (bt_mc s TL + 1 - 0)) fX11 TL (bt_mc s TL) 0 (-1) (Len fX11 TL 0) 0
         (fst (if Len fX11 TL 0 =? 0 then (138, 3) else (7, 4))) (snd (if Len fX11 TL 0 =? 0 then (138, 3) else (7, 4)))
    /\ (forall i, 0 <= i <= bt_mc s TD -> 0 <= Len fX12 TD i <= 15) /\ (forall c, 0 <= c < 19 -> 0 <= Len fX12 TB c <= 7)
    /\ send_tree_ok PBL (Z.to_nat (bt_mc s TD + 1 - 0)) fX12 TD (bt_mc s TD) 0 (-1) (Len fX12 TD 0) 0
         (fst (if Len fX12 TD 0 =? 0 then (138, 3) else (7, 4))) (snd (if Len fX12 TD 0 =? 0 then (138, 3) else (7, 4)))
    /\ send_tree fX12 TD (bt_mc s TD) = fXh
    /\ cty fX11 /\ cty fX12 /\ cty fXh
    /\ compress_block_ok PBL fXh (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh)
    /\ ds_sym_next fXh = 3 * nS /\ ds_lit_bufsize fXh = LS
    /\ BINV PBL fXe /\ vsize fXe <= ds_bi_valid s + 3 + ds_static_len fY6 /\ cty fXe
    /\ arr_len (ds_pending_buf fXe) = PBL
    /\ vsize fXe <= ds_bi_valid s + 3 + ds_opt_len fY6.
  Proof.
    intros DYN RACE. get_ff. pose proof fY6_frames as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof PBL4 as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT. pose proof (fbs_lens _ _ _ _ _ FB) as TLS.
    destruct header_sbs as (EL & ED & HH). cbv zeta in HH. destruct HH as (EH & LOK & SUMH & THR & OPT & L256 & CSB & AGREE & THE).
    pose proof (sbs_tabs nil) as S7. cbn [sbs_run] in S7. destruct S7 as (XL7 & XC7 & DL7 & FCL7 & FCD7 & LB7 & SN7 & PBL7 & MCL7 & MCD7).
    assert (V6 : vsize fY6 = ds_bi_valid s) by (unfold vsize; rewrite PD6, BV6; lia).
    assert (V7 : vsize fX7 = ds_bi_valid s + 3) by (rewrite EfX7; rewrite send_bits_size, V6; reflexivity).
    assert (VH : vsize fXh = ds_bi_valid s + 3 + THDR) by (unfold THDR; lia).
    assert (BINV6 : BINV PBL fY6) by (unfold BINV; rewrite PD6; pose proof P4; lia).
    pose proof (Sstat_bound syms s buf len last FB) as SB. rewrite <- SLv in SB.
    set (HDR := HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED) in *.
    assert (EHDR : HDR = HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED) by reflexivity.
    clearbody HDR.
    assert (TOT : vsize fY6 + sumlen ((Z.shiftl DYN_TREES 1 + last, 3) :: HDR) <= 8 * PBL).
    { rewrite sumlen_cons, SUMH, V6. pose proof (fbs_bi_valid _ _ _ _ _ FB). pose proof P4. lia. }
    assert (LOK' : lens_ok ((Z.shiftl DYN_TREES 1 + last, 3) :: HDR)) by (constructor; [cbn; lia| exact LOK]).
    pose proof (sbs_ok_of_total PBL _ fY6 BINV6 LOK' TOT) as OKall.
    cbn [sbs_ok] in OKall. destruct OKall as (_ & R6 & OKH0).
    assert (OKH : sbs_ok PBL fX7 HDR) by (rewrite EfX7; exact OKH0). clear OKH0.
    assert (BINV7 : BINV PBL fX7) by (rewrite EfX7; apply send_bits_BINV; [exact BINV6| lia| exact R6]).
    pose proof OKH as OKH'. rewrite EHDR in OKH.
    apply sbs_ok_app in OKH. destruct OKH as [OK3 OKr0].
    assert (OKr : sbs_ok PBL fX10 (sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED)) by exact OKr0. clear OKr0.
    apply sbs_ok_app in OKr. destruct OKr as [OKs OKr].
    destruct (sbs_tabs HDR3) as (XL10 & XC10 & _).
    destruct (AGREE fX10 XL10 XC10) as (_ & _ & SC10 & _).
    assert (E11 : fX11 = sbs_run fX10 (sat_calls fX7 (fmb + 1) 0)).
    { unfold fX11. rewrite sat_loop_sbs by lia. rewrite <- SC10. unfold sat_calls. rewrite Z.sub_0_r.
      pose proof (fmb_range fY5). replace (Nat.min 19 (Z.to_nat (fmb + 1))) with (Z.to_nat (fmb + 1)) by lia. reflexivity. }
    rewrite <- E11 in OKr. apply sbs_ok_app in OKr. destruct OKr as [OKL OKr].
    destruct (sbs_tabs (HDR3 ++ sat_calls fX7 (fmb + 1) 0)) as (XL11 & XC11 & DL11 & _).
    assert (E11' : sbs_run fX7 (HDR3 ++ sat_calls fX7 (fmb + 1) 0) = fX11) by (rewrite sbs_run_app, E11; unfold fX10; reflexivity).
    rewrite E11' in XL11, XC11, DL11.
    destruct (AGREE fX11 XL11 XC11) as (EL11 & ED11 & _ & ST11 & _ & SOK11 & _).
    rewrite <- EL11 in OKL.
    assert (E12 : fX12 = sbs_run fX11 (flat_map (em_calls fX11) EL)) by (unfold fX12; exact ST11).
    rewrite <- EL11, <- E12 in OKr.
    destruct (sbs_tabs (HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL)) as (XL12 & XC12 & DL12 & _).
    assert (E12' : sbs_run fX7 (HDR3 ++ sat_calls fX7 (fmb + 1) 0 ++ flat_map (em_calls fX7) EL) = fX12).
    { rewrite app_assoc, sbs_run_app, E11', E12, EL11. reflexivity. }
    rewrite E12' in XL12, XC12, DL12.
    destruct (AGREE fX12 XL12 XC12) as (EL12 & ED12 & _ & _ & ST12 & _ & SOK12).
    rewrite <- ED12 in OKr.
    assert (E13 : send_tree fX12 TD (bt_mc s TD) = fXh).
    { rewrite ST12, ED12, EH, EHDR. rewrite <- E12'. rewrite <- !sbs_run_app. rewrite <- !app_assoc. reflexivity. }
    assert (CT0 : cty fs0).
    { unfold OverlayFlush.fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); [apply cty_set_strm_dt; exact CT| exact CT]. }
    assert (CT6 : cty fY6).
    { rewrite EfY6. apply cty_set_opt_len. rewrite EfY5. apply cty_build_tree. rewrite EfY4. apply cty_scan_tree.
      rewrite EfY3. apply cty_scan_tree. rewrite EfY2. apply cty_build_tree. rewrite EfY1. apply cty_build_tree. exact CT0. }
    assert (CT7 : cty fX7) by (rewrite EfX7; apply cty_send_bits; exact CT6).
    assert (CT10 : cty fX10) by (unfold fX10, HDR3; cbn [sbs_run]; do 3 apply cty_send_bits; exact CT7).
    assert (CT11 : cty fX11) by (unfold fX11; apply cty_send_all_trees_loop; exact CT10).
    assert (CT12 : cty fX12) by (unfold fX12; apply cty_send_tree; exact CT11).
    assert (CTh : cty fXh) by (rewrite <- E13; apply cty_send_tree; exact CT12).
    assert (BL19 : forall X, (forall t n, Len X t n = Len fY5 t n) -> forall c, 0 <= c < 19 -> 0 <= Len X TB c <= 7).
    { intros X HL c Hc. rewrite HL. destruct (in_dec Z.eq_dec c (bt_U fY4 TB)) as [IN|NIN]; [pose proof (LENB c IN); lia|].
      rewrite (proj1 (ZB c ltac:(lia) NIN)). lia. }
    assert (L5L : forall X, (forall t n, Len X t n = Len fY5 t n) -> forall i, 0 <= i <= bt_mc s TL -> 0 <= Len X TL i <= 15).
    { intros X HL i Hi. rewrite HL. destruct (in_dec Z.eq_dec i (bt_U s TL)) as [IN|NIN]; [pose proof (LENS i IN); lia| rewrite ZL by assumption; lia]. }
    assert (L5D : forall X, (forall t n, Len X t n = Len fY5 t n) -> forall i, 0 <= i <= bt_mc s TD -> 0 <= Len X TD i <= 15).
    { intros X HL i Hi. rewrite HL. destruct (in_dec Z.eq_dec i (bt_U s TD)) as [IN|NIN]; [pose proof (LEND i IN); lia| rewrite ZD by assumption; lia]. }
    destruct (sbs_tabs HDR) as (XLh & XCh & DLh & FCLh & FCDh & LBh & SNh & PBLh & _).
    rewrite <- EH in XLh, XCh, DLh, FCLh, FCDh, LBh, SNh, PBLh.
    pose proof (sbs_fp HDR fX7 LOK (proj1 BINV7)) as FP.
    cbv zeta in FP. rewrite <- EH in FP. destruct FP as (PDh & ALh & PRh & _ & _ & BVh & VSh).
    pose proof (sbs_BINV_total PBL HDR fX7 BINV7 LOK ltac:(rewrite V7; cbn [sumlen] in TOT; lia)) as [BINVh _]. rewrite <- EH in BINVh.
    pose proof (send_bits_fp fY6 (Z.shiftl DYN_TREES 1 + last) 3) as FP7. cbv zeta in FP7.
    destruct FP7 as (PD7 & AL7 & PR7 & _).
    assert (PD7' : ds_pending fX7 <= 2) by (rewrite EfX7; rewrite PD6 in PD7; lia).
    assert (PRIS : forall i, ds_pending fXh <= i -> arr_get (ds_pending_buf fXh) i = arr_get (ds_pending_buf s) i).
    { intros i Hi. rewrite PRh by lia. rewrite <- PB6. pose proof (PDh) as X. rewrite EfX7 in X |- *. apply PR7. rewrite PD6 in PD7 |- *. lia. }
    assert (VAL := fbs_syms_valid _ _ _ _ _ FB).
    assert (DR : Forall (fun dl : Z * Z => 0 <= fst dl < 65536) syms).
    { apply Forall_forall. intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) VAL _ Hx) as V. unfold sym_valid, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V. cbn [fst]. lia. }
    assert (DM : Forall (fun dl : Z * Z => fst dl <= 32768) syms).
    { apply Forall_forall. intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) VAL _ Hx) as V. unfold sym_valid, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V. cbn [fst]. lia. }
    assert (LENSX : forall dl, In dl syms -> lens_ok (calls_of (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh) dl)).
    { intros dl Hdl. apply (proj1 (proj2 (dyncost_dcost LL LzL LD LzD LB LzB b4 ltac:(split; assumption) dl Hdl))). }
    assert (RACEk : forall k, (k < length syms)%nat -> vsize fXh + csum dyncost (firstn k syms) <= 8 * (ds_lit_bufsize fXh + 3 * Z.of_nat k) + 7).
    { intros k Hk. rewrite LBh. apply (cb_race_suff (vsize fXh) LS dyncost syms RACE k Hk). }
    assert (BYTES : forall i d lc, nth_error syms i = Some (d, lc) -> sym_at fXh (3 * Z.of_nat i) d lc).
    { intros i d lc Hi. pose proof (fbs_sym_bytes _ _ _ _ _ FB i d lc Hi) as (Y1 & Y2 & Y3). unfold fbs_L in Y1, Y2, Y3.
      assert (Hlen : (i < length syms)%nat) by (apply (proj1 (nth_error_Some syms i)); rewrite Hi; discriminate).
      pose proof (RACEk 0%nat ltac:(lia)) as R0. rewrite firstn_O in R0. cbn [csum] in R0. rewrite LBh in R0.
      pose proof (pending_le_vsize fXh ltac:(lia)).
      unfold sym_at. rewrite LBh. rewrite !PRIS by lia. unfold OverlayFlush.LS.
      split; [exact Y1|]. split; [exact Y2| exact Y3]. }
    assert (E256 : arr_get (ds_dyn_ltree_dl fXh) END_BLOCK = Len fY5 TL 256).
    { rewrite (dl_projL fXh), (Len_proj fXh). apply XLh. }
    assert (ROOM : vsize fXh + csum dyncost syms + arr_get (ds_dyn_ltree_dl fXh) END_BLOCK <= 8 * PBL).
    { rewrite E256, VH, P4. pose proof (fbs_bi_valid _ _ _ _ _ FB). lia. }
    assert (ROOM' : vsize fXh + csum dyncost syms <= 8 * PBL) by (pose proof L256; rewrite E256 in ROOM; lia).
    pose proof (fbs_sym_next _ _ _ _ _ FB) as SN0. unfold fbs_n in SN0.
    assert (TABS : Forall (tabs_ok (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_dl fXh)) syms).
    { apply Forall_forall. intros dl Hdl. destruct (dyncost_dcost LL LzL LD LzD LB LzB b4 ltac:(split; assumption) dl Hdl) as (_ & _ & T1 & T2).
      split; [intros E0; specialize (T1 E0); lia| intros E0; specialize (T2 E0); lia]. }
    assert (SYMN : ds_sym_next fXh = 3 * Z.of_nat (length syms)) by (rewrite SNh; reflexivity).
    assert (SYMROOM : ds_lit_bufsize fXh + 3 * Z.of_nat (length syms) <= PBL) by (rewrite LBh, P4; unfold OverlayFlush.nS in NR; lia).
    destruct (cb_race_ok fXh (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh) syms
                SYMN BYTES DR ltac:(lia) LENSX RACEk PBL PBLh ROOM' SYMROOM BINVh DM TABS (ct_pb _ CTh) ltac:(rewrite E256; lia) ROOM)
      as (CBOK & CBE & CBV & CBB & CBP & CBPR & CBL).
    split; [(exact BINV6)|]. split; [(exact R6)|].
    cbn [sbs_ok HDR3] in OK3. destruct OK3 as ([_ _] & R7 & [_ _] & R8 & [_ _] & R9 & _).
    split; [(exact R7)|]. split; [(exact R8)|]. split; [(exact R9)|].
    split; [reflexivity|].
    split; [(rewrite SC10; exact OKs)|].
    split; [(exact (L5L fX11 XL11))|]. split; [(exact (BL19 fX11 XL11))|].
    split; [(apply SOK11; exact OKL)|].
    split; [(exact (L5D fX12 XL12))|]. split; [(exact (BL19 fX12 XL12))|].
    split; [(apply SOK12; exact OKr)|].
    split; [(exact E13)|]. split; [(exact CT11)|]. split; [(exact CT12)|]. split; [(exact CTh)|].
    split; [(exact CBOK)|]. split; [(rewrite SNh; reflexivity)|]. split; [(exact LBh)|].
    rewrite EfXe. split; [exact CBB|]. split; [rewrite CBV, E256, VH; unfold dyncost in OPT; lia|].
    split; [apply cty_compress_block; exact CTh|]. split; [exact CBL|].
    rewrite CBV, E256, VH; unfold dyncost in OPT; lia.
  Qed.
End FB2.
