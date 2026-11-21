(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild HuffBuild2 HuffFib HuffSpec HuffFlush HuffSend DeflRoom OverlayFBS OverlayRace OverlayCmp OverlayHdr OverlayFlush OverlayDyn DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel ScanModel SendModel CompressModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dyn_need (syms : list (Z * Z)) (s : deflate_state) (last : Z) : Prop :=
  forall fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh : deflate_state,
    fY1 = build_tree (fs0 s) TL ->
    fY2 = build_tree fY1 TD ->
    fY3 = scan_tree fY2 TL (ds_l_max_code fY2) ->
    fY4 = scan_tree fY3 TD (ds_d_max_code fY3) ->
    fY5 = build_tree fY4 TB ->
    fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb fY5 + 1) + 5 + 5 + 4)) ->
    fX7 = send_bits fY6 (Z.shiftl DYN_TREES 1 + last) 3 ->
    fXh = send_all_trees fX7 (ds_l_max_code fX7 + 1) (ds_d_max_code fX7 + 1) (fmb fY5 + 1) ->
    ds_opt_len fY6 < ds_static_len fY6 ->
    vsize fXh + excess (dyncost fXh) syms <= 8 * LS s + 7.


Lemma zcount_mono : forall (p q : Z * Z -> bool) l, (forall x, In x l -> p x = true -> q x = true) -> zcount p l <= zcount q l.
Proof.
  intros p q l H. unfold zcount. induction l as [|x l IH]; cbn [filter length]; [lia|].
  specialize (IH ltac:(intros; apply H; [right|]; assumption)).
  destruct (p x) eqn:Px.
  - rewrite (H x (or_introl eq_refl) Px). cbn [length]. lia.
  - destruct (q x); cbn [length]; lia.
Qed.

Lemma zsum_map_zero : forall (l : list Z), zsum (map (fun _ => 0) l) = 0.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map zsum]. rewrite IH. reflexivity. Qed.

Section NEED.
  Variable syms : list (Z * Z).
  Variable s : deflate_state.
  Variable buf : option Z.
  Variables len last : Z.
  Hypothesis FB : FBS syms s buf len last.
  Local Set Warnings "-notation-for-abbreviation".
  Local Notation nS := (nS syms).
  Local Notation LS := (LS s).
  Variables fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh fXe : deflate_state.
  Hypothesis EfY1 : fY1 = build_tree (fs0 s) TL.
  Hypothesis EfY2 : fY2 = build_tree fY1 TD.
  Hypothesis EfY3 : fY3 = scan_tree fY2 TL (ds_l_max_code fY2).
  Hypothesis EfY4 : fY4 = scan_tree fY3 TD (ds_d_max_code fY3).
  Hypothesis EfY5 : fY5 = build_tree fY4 TB.
  Hypothesis EfY6 : fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb fY5 + 1) + 5 + 5 + 4)).
  Hypothesis EfX7 : fX7 = send_bits fY6 (Z.shiftl DYN_TREES 1 + last) 3.
  Hypothesis EfXh : fXh = send_all_trees fX7 (ds_l_max_code fX7 + 1) (ds_d_max_code fX7 + 1) (fmb fY5 + 1).
  Hypothesis EfXe : fXe = compress_block fXh (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh).

  Definition PENt (t : tree_id) (L : Z -> Z) : Z :=
    zsum (map (fun j => bt_F s t j * Z.max 0 (Len fY5 t j - L j)) (bt_U s t)).

  Definition optcode (t : tree_id) (L : Z -> Z) (H : Z) : Prop :=
    (forall j, In j (bt_U s t) -> 1 <= L j <= H) /\ 0 <= H
    /\ zsum (map (fun j => 2 ^ (H - L j)) (bt_U s t)) <= 2 ^ H
    /\ (forall Hh c, dep_ok Hh c -> kraft Hh c <= 2 ^ Hh -> (forall e, In e c -> 0 <= ew e) ->
          Permutation (map ew c) (map (bt_F s t) (bt_U s t)) -> zsum (map (fun j => bt_F s t j * L j) (bt_U s t)) <= ccost c).

  Theorem need_chain : forall LL LD HL HD, optcode TL LL HL -> optcode TD LD HD ->
    vsize fXh + excess (dyncost fXh) syms <= ds_bi_valid s + 3 + 2283 + (nS + 3) + (nS + 2) + PENt TL LL + PENt TD LD.
  Proof.
    intros LL LD HL HD (LLH & HL0 & KLL & OPTL) (LDH & HD0 & KLD & OPTD).
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6) as (LL' & LzL & LD' & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    destruct (header_sbs syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6 fX7 fXh EfX7 EfXh) as (EL & ED & HH).
    cbv zeta in HH. destruct HH as (EH & LOK & SUMH & THR & _).
    pose proof (sbs_tabs syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6 fX7 EfX7
                  (HDR3 s fY5 ++ sat_calls fX7 (fmb fY5 + 1) 0 ++ flat_map (em_calls fX7) EL ++ flat_map (em_calls fX7) ED)) as ST.
    cbv zeta in ST. rewrite <- EH in ST. destruct ST as (XLh & _).
    assert (V6 : vsize fY6 = ds_bi_valid s) by (unfold vsize; rewrite PD6, BV6; lia).
    assert (V7 : vsize fX7 = ds_bi_valid s + 3) by (rewrite EfX7; rewrite send_bits_size, V6; reflexivity).
    assert (VH : vsize fXh = ds_bi_valid s + 3 + THDR fX7 fXh) by (unfold THDR; lia).
    pose proof (bt_U_facts s TL) as (NDL & RNGL & MCinL & U2L & INL & PADL & NPL & ULN).
    pose proof (bt_U_facts s TD) as (NDD & RNGD & MCinD & U2D & IND & PADD & NPD & UDN).
    pose proof (bt_Ftot_TL syms s buf len last FB) as [FTL NPL2]. pose proof (bt_Ftot_TD syms s buf len last FB) as [FTD NPD2].
    pose proof (fbs_syms_valid _ _ _ _ _ FB) as VAL.
    pose proof (fbs_lens _ _ _ _ _ FB) as TLS. unfold fbs_tree_lens in TLS.
    assert (FLnn : forall j, In j (bt_U s TL) -> 0 <= bt_F s TL j).
    { intros j Hj. pose proof (RNGL j Hj) as R. cbn [sd_elems] in R. unfold L_CODES in R. unfold bt_F, FP. destruct (existsb _ _); [lia|].
      apply (proj1 (ct_lfc s (fbs_cty _ _ _ _ _ FB) j ltac:(lia))). }
    assert (FDnn : forall j, In j (bt_U s TD) -> 0 <= bt_F s TD j).
    { intros j Hj. pose proof (RNGD j Hj) as R. cbn [sd_elems] in R. unfold D_CODES in R. unfold bt_F, FP. destruct (existsb _ _); [lia|].
      apply (proj1 (ct_dfc s (fbs_cty _ _ _ _ _ FB) j ltac:(lia))). }
    assert (M256 : 256 <= bt_mc s TL) by (pose proof (RNGL 256 S256); lia).
    assert (TABL : forall j, arr_get (ds_dyn_ltree_dl fXh) j = Len fY5 TL j).
    { intros j. rewrite (dl_projL fXh), (Len_proj fXh). apply XLh. }
    assert (TABD : forall j, arr_get (ds_dyn_dtree_dl fXh) j = Len fY5 TD j).
    { intros j. rewrite (dl_projD fXh), (Len_proj fXh). apply XLh. }
    assert (LAM : forall lc, 0 <= lc <= 255 -> arr_get (ds_dyn_ltree_dl fXh) lc <= 24).
    { intros lc Hlc. rewrite TABL. destruct (in_dec Z.eq_dec lc (bt_U s TL)) as [IN|NIN]; [pose proof (LENS lc IN); lia| rewrite ZL by (lia || assumption); lia]. }
    assert (CNTL : forall j, In j (bt_U s TL) -> zcount (fun x => ism x && (sym_lcode x =? j)) syms <= bt_F s TL j).
    { intros j Hj. pose proof (RNGL j Hj) as R. cbn [sd_elems] in R.
      pose proof (fbs_freq_l _ _ _ _ _ FB j ltac:(unfold L_CODES in *; lia)) as FQ.
      pose proof (zcount_mono (fun x => ism x && (sym_lcode x =? j)) (fun dl => sym_lcode dl =? j) syms
                    ltac:(intros x _ Hx; apply andb_prop in Hx; tauto)) as ZM.
      destruct (Z.eq_dec (Freq s TL j) 0) as [Z0|NZ].
      - rewrite (PADL j Hj Z0). rewrite Z0 in FQ. pose proof (zcount_nonneg (fun dl => sym_lcode dl =? j) syms). destruct (j =? END_BLOCK); lia.
      - rewrite (proj2 (INL j ltac:(cbn [sd_elems]; unfold L_CODES in *; lia) NZ)). rewrite FQ. destruct (j =? END_BLOCK); lia. }
    assert (CNTD : forall i, In i (bt_U s TD) -> zcount (fun x => ism x && (sdc x =? i)) syms <= bt_F s TD i).
    { intros i Hi. pose proof (RNGD i Hi) as R. cbn [sd_elems] in R.
      pose proof (fbs_freq_d _ _ _ _ _ FB i ltac:(unfold D_CODES in *; lia)) as FQ.
      pose proof (zcount_mono (fun x => ism x && (sdc x =? i)) (fun dl => match sym_dcode dl with Some j' => j' =? i | None => false end) syms) as ZM.
      specialize (ZM ltac:(intros [d lc] _ Hx; apply andb_prop in Hx; destruct Hx as [H1 H2]; unfold ism, sdc, sym_dcode in *; cbn [fst] in *;
                        destruct (d =? 0); [discriminate| exact H2])).
      destruct (Z.eq_dec (Freq s TD i) 0) as [Z0|NZ].
      - rewrite (PADD i Hi Z0). rewrite Z0 in FQ.
        pose proof (zcount_nonneg (fun dl => match sym_dcode dl with Some jq => jq =? i | None => false end) syms). lia.
      - rewrite (proj2 (IND i ltac:(cbn [sd_elems]; unfold D_CODES in *; lia) NZ)). rewrite FQ. lia. }
    pose proof (excess_bound (ds_dyn_ltree_fc fXh) (ds_dyn_ltree_dl fXh) (ds_dyn_dtree_fc fXh) (ds_dyn_dtree_dl fXh) syms
                  (bt_U s TL) (bt_U s TD) (bt_F s TL) (bt_F s TD) LL LD HL HD
                  VAL LAM NDL NDD
                  ltac:(intros j Hj; pose proof (RNGL j Hj) as R; cbn [sd_elems] in R; unfold L_CODES in R; lia)
                  ltac:(intros i Hi; pose proof (RNGD i Hi) as R; cbn [sd_elems] in R; unfold D_CODES in R; lia)
                  ltac:(intros x Hx _; apply (proj1 (SU x Hx))) ltac:(intros x Hx Hm; apply (proj2 (SU x Hx) Hm))
                  CNTL CNTD FLnn FDnn LLH LDH HL0 HD0 KLL KLD OPTL OPTD) as EB.
    unfold dyncost.
    assert (PL : PEN (bt_U s TL) (bt_F s TL) (arr_get (ds_dyn_ltree_dl fXh)) LL = PENt TL LL).
    { unfold PEN, PENt. apply zsum_map_ext. intros j Hj. rewrite TABL. reflexivity. }
    assert (PD : PEN (bt_U s TD) (bt_F s TD) (arr_get (ds_dyn_dtree_dl fXh)) LD = PENt TD LD).
    { unfold PEN, PENt. apply zsum_map_ext. intros j Hj. rewrite TABD. reflexivity. }
    rewrite PL, PD in EB.
    change (zsum (map (bt_F s TL) (bt_U s TL))) with (bt_Ftot s TL) in EB.
    change (zsum (map (bt_F s TD) (bt_U s TD))) with (bt_Ftot s TD) in EB.
    lia.
  Qed.

  Theorem need_noovf : nS <= 2580 ->
    vsize fXh + excess (dyncost fXh) syms <= ds_bi_valid s + 3 + 2283 + (nS + 3) + (nS + 2).
  Proof.
    intros NS.
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    pose proof (bt_Ftot_TL syms s buf len last FB) as [FTL NPL2]. pose proof (bt_Ftot_TD syms s buf len last FB) as [FTD NPD2].
    destruct (bt_same s (fs0 s) TL (fs0_tree_fc syms s buf len last FB TL)) as (UL & FL & MCLq & NPL & SPL & FTLq).
    destruct (bt_same s fY1 TD ltac:(rewrite FC1D; reflexivity)) as (UD & FD & MCDq & NPD & SPD & FTDq).
    unfold bt_post in B1, B2. cbv zeta in B1, B2. rewrite UL, FL, FTLq in B1. rewrite UD, FD, FTDq in B2.
    destruct B1 as (_ & L1 & NOV1 & OPT1 & _ & EQ1 & LZ1 & _ & KR1 & _).
    destruct B2 as (_ & L2 & NOV2 & OPT2 & _ & EQ2 & LZ2 & _ & KR2 & _).
    cbn [sd_max_length] in *.
    assert (F18 : fibZ (MAX_BITS + 3) = 2584) by (vm_compute; reflexivity).
    rewrite F18 in NOV1, NOV2.
    specialize (NOV1 ltac:(clear -FTL NPL2 NS; lia)). specialize (NOV2 ltac:(clear -FTD NS; lia)).
    unfold MAX_BITS in NOV1, NOV2, L1, L2, OPT1, OPT2, EQ1, EQ2, KR1, KR2, LZ1, LZ2.
    specialize (EQ1 NOV1). specialize (EQ2 NOV2).
    assert (OC1 : optcode TL LL 15).
    { split; [intros j Hj; pose proof (L1 j Hj); pose proof (NOV1 j Hj); lia|]. split; [lia|]. split.
      - rewrite (zsum_map_ext _ (fun j => 2 ^ (15 - LzL j))) by (intros j Hj; rewrite (EQ1 j Hj); reflexivity). lia.
      - exact OPT1. }
    assert (OC2 : optcode TD LD 15).
    { split; [intros j Hj; pose proof (L2 j Hj); pose proof (NOV2 j Hj); lia|]. split; [lia|]. split.
      - rewrite (zsum_map_ext _ (fun j => 2 ^ (15 - LzD j))) by (intros j Hj; rewrite (EQ2 j Hj); reflexivity). lia.
      - exact OPT2. }
    pose proof (need_chain LL LD 15 15 OC1 OC2) as NC.
    assert (P1z : PENt TL LL = 0).
    { unfold PENt. rewrite (zsum_map_ext _ (fun _ => 0)); [apply zsum_map_zero|].
      intros j Hj. rewrite (proj1 (LENS j Hj)), (EQ1 j Hj). lia. }
    assert (P2z : PENt TD LD = 0).
    { unfold PENt. rewrite (zsum_map_ext _ (fun _ => 0)); [apply zsum_map_zero|].
      intros j Hj. rewrite (proj1 (LEND j Hj)), (EQ2 j Hj). lia. }
    clear -NC P1z P2z. lia.
  Qed.
  Theorem need_ovf :
    vsize fXh + excess (dyncost fXh) syms <= ds_bi_valid s + 3 + 2283 + (nS + 3) + (nS + 2) + (nS + 3) + (nS + 2).
  Proof.
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    pose proof (bt_Ftot_TL syms s buf len last FB) as [FTL NPL2]. pose proof (bt_Ftot_TD syms s buf len last FB) as [FTD NPD2].
    destruct (bt_same s (fs0 s) TL (fs0_tree_fc syms s buf len last FB TL)) as (UL & FL & MCLq & NPL & SPL & FTLq).
    destruct (bt_same s fY1 TD ltac:(rewrite FC1D; reflexivity)) as (UD & FD & MCDq & NPD & SPD & FTDq).
    unfold bt_post in B1, B2. cbv zeta in B1, B2. rewrite UL, FL, FTLq in B1. rewrite UD, FD, FTDq in B2.
    destruct B1 as (_ & L1 & _ & _ & _ & _ & LZ1 & _ & _ & _ & _ & _ & _ & _ & PEN1 & _).
    destruct B2 as (_ & L2 & _ & _ & _ & _ & LZ2 & _ & _ & _ & _ & _ & _ & _ & PEN2 & _).
    destruct PEN1 as (LP1 & bs1 & _ & _ & OPT1 & _ & RNG1 & _ & _ & _ & _ & KR1 & PB1 & _).
    destruct PEN2 as (LP2 & bs2 & _ & _ & OPT2 & _ & RNG2 & _ & _ & _ & _ & KR2 & PB2 & _).
    cbn [sd_max_length] in PB1, PB2. unfold MAX_BITS in PB1, PB2. specialize (PB1 eq_refl). specialize (PB2 eq_refl).
    pose proof (bt_U_facts s TL) as (_ & _ & _ & U2L & _). pose proof (bt_U_facts s TD) as (_ & _ & _ & U2D & _).
    assert (OC1 : optcode TL LP1 (zlen (bt_U s TL))).
    { split; [intros j Hj; pose proof (RNG1 j Hj) as X; clear -X; lia|]. split; [clear -U2L; lia|]. split; [exact KR1| exact OPT1]. }
    assert (OC2 : optcode TD LP2 (zlen (bt_U s TD))).
    { split; [intros j Hj; pose proof (RNG2 j Hj) as X; clear -X; lia|]. split; [clear -U2D; lia|]. split; [exact KR2| exact OPT2]. }
    pose proof (need_chain LP1 LP2 _ _ OC1 OC2) as NC.
    assert (Q1 : PENt TL LP1 <= nS + 3).
    { unfold PENt. rewrite (zsum_map_ext _ (fun j => bt_F s TL j * Z.max 0 (LzL j - LP1 j))) by (intros j Hj; rewrite (proj1 (LENS j Hj)); reflexivity).
      change (zsum (map (bt_F s TL) (bt_U s TL))) with (bt_Ftot s TL) in PB1. clear -PB1 FTL NPL2. lia. }
    assert (Q2 : PENt TD LP2 <= nS + 2).
    { unfold PENt. rewrite (zsum_map_ext _ (fun j => bt_F s TD j * Z.max 0 (LzD j - LP2 j))) by (intros j Hj; rewrite (proj1 (LEND j Hj)); reflexivity).
      change (zsum (map (bt_F s TD) (bt_U s TD))) with (bt_Ftot s TD) in PB2. clear -PB2 FTD. lia. }
    clear -NC Q1 Q2. lia.
  Qed.
End NEED.

Theorem dyn_need_mid : forall syms s buf len last, FBS syms s buf len last ->
  383 <= LS s -> nS syms <= 2580 -> dyn_need syms s last.
Proof.
  intros syms s buf len last FB HL HN. unfold dyn_need. intros fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh E1 E2 E3 E4 E5 E6 E7 Eh DYN.
  pose proof (need_noovf syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh E1 E2 E3 E4 E5 E6 E7 Eh HN) as NC.
  pose proof (fbs_bi_valid _ _ _ _ _ FB). pose proof (L_range syms s buf len last FB). lia.
Qed.

Theorem dyn_need_big : forall syms s buf len last, FBS syms s buf len last ->
  577 <= LS s -> dyn_need syms s last.
Proof.
  intros syms s buf len last FB HL. unfold dyn_need. intros fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh E1 E2 E3 E4 E5 E6 E7 Eh DYN.
  pose proof (need_ovf syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 fX7 fXh E1 E2 E3 E4 E5 E6 E7 Eh) as NC.
  pose proof (fbs_bi_valid _ _ _ _ _ FB). pose proof (L_range syms s buf len last FB). lia.
Qed.

Theorem dyn_need_ge512 : forall syms s buf len last, FBS syms s buf len last ->
  512 <= LS s -> dyn_need syms s last.
Proof.
  intros syms s buf len last FB HL.
  destruct (Z_lt_le_dec (LS s) 577).
  - apply (dyn_need_mid syms s buf len last FB); [lia|]. pose proof (L_range syms s buf len last FB). lia.
  - apply (dyn_need_big syms s buf len last FB). lia.
Qed.
