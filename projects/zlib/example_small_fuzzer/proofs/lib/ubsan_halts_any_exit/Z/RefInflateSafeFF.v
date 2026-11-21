(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeF2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Strategy 100 [dodist dolen fast_trip dodist_ok dolen_ok trip_ok].

Definition fin (r : InflateFast.fstep) : Z := match r with FCont f' => f_in f' | FBreak f' _ _ => f_in f' end.



Section FF.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
Variable usedL : Z.
Variable usedD : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis Xdm : x_dmask x = zmask (is_distbits s).
  Hypothesis Xlm : x_lmask x = zmask (is_lenbits s).
  Hypothesis HTL : TBLg LENS (code_at s (is_lencode s)) (is_lenbits s) usedL.
  Hypothesis HTD : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) usedD.
  Hypothesis HLC : usedL <= ctab_len (is_lencode s).
  Hypothesis HDC : usedD <= ctab_len (is_distcode s).
  Hypothesis Xsane : x_sane x = 1.
  Hypothesis Xwh : 0 <= x_whave x <= x_wsize x.
  Hypothesis Xws : x_wsize x <> 0 -> x_wnext x < x_wsize x /\ WN = x_wsize x.
  Hypothesis Xws0 : x_wsize x = 0 -> x_whave x = 0.

  Lemma window_ok_true : forall f,
    1 <= f_op f <= x_whave x -> 0 <= f_len f -> f_out f + f_len f <= ON ->
    window_ok x ON WN f = true.
  Proof.
    intros f Hop Hlen Hroom.
    assert (WS : x_wsize x <> 0) by (intros Z0; pose proof (Xws0 Z0); lia).
    destruct (Xws WS) as [WN1 WN2].
    unfold window_ok. cbv zeta.
    rewrite (proj2 (Z.leb_le _ _) Hroom). cbn [andb].
    destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0].
    - rewrite (proj2 (Z.leb_le (f_op f) (x_wsize x))) by lia. cbn [andb].
      destruct (Z.ltb_spec (f_op f) (f_len f)); apply Z.leb_le; lia.
    - destruct (Z.ltb_spec (x_wnext x) (f_op f)) as [W1|W1].
      + rewrite (proj2 (Z.leb_le (f_op f) (x_wsize x + x_wnext x))) by lia. cbn [andb].
        destruct (Z.ltb_spec (f_op f - x_wnext x) (f_len f)) as [W2|W2].
        * rewrite (proj2 (Z.leb_le (x_wsize x + x_wnext x - f_op f + (f_op f - x_wnext x)) WN)) by lia. cbn [andb].
          destruct (Z.ltb_spec (x_wnext x) (f_len f - (f_op f - x_wnext x))); apply Z.leb_le; lia.
        * apply Z.leb_le; lia.
      + destruct (Z.ltb_spec (f_op f) (f_len f)); apply Z.leb_le; lia.
  Qed.


  Lemma dodist_ok_S : forall k here f,
    dodist_ok x s IN ON WN (S k) here f =
      let op := code_bits here in
      (op <=? f_bits f) &&
      let f := fdrop f op in
      let op := code_op here in
      if negb (Z.land op 16 =? 0) then
        let f := fset_dist f (code_val here) in
        let op := Z.land op 15 in
        (if f_bits f <? op then (f_in f + 1 <=? IN) && (if f_bits f + 8 <? op then f_in f + 2 <=? IN else true) else true) &&
        let f := if f_bits f <? op then
                   let f := fpull x f in
                   if f_bits f <? op then fpull x f else f
                 else f in
        (op <=? f_bits f) &&
        let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
        let f := fdrop f op in
        (1 <=? f_dist f) && (3 <=? f_len f) && (f_out f + f_len f <=? ON) &&
        let op := wrap32 (f_out f - x_beg x) in
        if op <? f_dist f then
          let op := wrap32 (f_dist f - op) in
          if (x_whave x <? op) && negb (x_sane x =? 0) then true
          else window_ok x ON WN (fset_op f op)
        else true
      else if Z.land op 64 =? 0 then
        (op <? 16) &&
        let i := code_val here + Z.land (f_hold f) (zmask op) in
        (i <? ctab_len (is_distcode s)) && dodist_ok x s IN ON WN k (code_at s (is_distcode s) i) f
      else true.
  Proof. intros. cbn [dodist_ok]. lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end. Qed.

  Lemma COPIED_in : forall n f f', COPIED n f f' -> f_in f' = f_in f.
  Proof. intros n f f' H. exact (proj1 H). Qed.

  Lemma dodist_ok_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    ((exists sy, 0 <= sy < 32 /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
    fin (dodist (S k) x s here f) <= IN ->
    dodist_ok x s IN ON WN (S k) here f = true.
  Proof.
    intros k here f HF Hcb Hcf Hlen Hbeg Hroom Hsh HIN. rewrite dodist_ok_S. rewrite dodist_S in HIN. cbv zeta. cbv zeta in HIN.
    rewrite (proj2 (Z.leb_le _ _) Hcf). cbn [andb].
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *.
    pose proof HF as (B1 & B2 & B3 & B4 & B5). pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. reflexivity. }
    pose proof (dists_sym_cases sy Hsy) as SC. destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv in *. destruct SC as [(O1 & O2 & O3)|[O1 O2]].
    2:{ rewrite O1. reflexivity. }
    destruct (dist_op_facts op O1) as (F1 & F2 & F3 & F4).
    replace (negb (Z.land op 16 =? 0)) with true in * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
    rewrite F3 in *. set (e := op - 16) in *.
    assert (He : 0 <= e <= 13) by lia.
    pose proof (pow2_le e 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13. pose proof (pow2_pos e ltac:(lia)) as P0.
    set (f1d := fset_dist f1 v) in *.
    assert (HF1d : FB ON f1d /\ f_in f1d = f_in f /\ f_out f1d = f_out f /\ f_bits f1d = f_bits f - code_bits here /\ f_len f1d = f_len f /\ f_dist f1d = v
                   /\ 0 <= f_hold f1d).
    { subst f1d. unfold FB. facc. repeat split; first [assumption | reflexivity | lia]. }
    clearbody f1d. clear HF1 E1i E1o E1b E1h E1l E1d E1ob C1 C2 C3 C4 C5 f1.
    destruct HF1d as (HF1 & E1i & E1o & E1b & E1l & E1d & E1h0).
    match goal with |- context [e <=? f_bits ?F] => set (f2 := F) in * end.
    assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ f_len f2 = f_len f /\ f_dist f2 = v /\ e <= f_bits f2 /\ f_bits f2 <= 32 /\
                  f_in f2 = f_in f + (if f_bits f1d <? e then if f_bits f1d + 8 <? e then 2 else 1 else 0)).
    { subst f2. destruct (Z.ltb_spec (f_bits f1d) e) as [L1|L1].
      - destruct (FB_fpull x ON Xin f1d HF1 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
        rewrite P1b. destruct (Z.ltb_spec (f_bits f1d + 8) e) as [L2|L2].
        + destruct (FB_fpull x ON Xin (fpull x f1d) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & P2d & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2d, P1o, P1l, P1d, P2b, P1b, P2i, P1i, E1i. unfold FB in HP2. repeat split; first [assumption | lia].
        + split; [exact HP1|]. rewrite P1o, P1l, P1d, P1b, P1i, E1i. unfold FB in HP1. repeat split; first [assumption | lia].
      - split; [exact HF1|]. rewrite E1i. unfold FB in HF1. repeat split; first [assumption | lia]. }
    clearbody f2. destruct HF2 as (HF2 & E2o & E2l & E2d & E2e & E2b32 & E2i).
    pose proof HF2 as (D1 & D2 & D3 & D4 & D5).
    rewrite (land_wrap32_zmask (f_hold f2) e) in * by lia.
    pose proof (mod_pow2_range (f_hold f2) e ltac:(lia)) as MR.
    rewrite E2d in *. rewrite (wrap32_id (v + _)) in * by lia.
    set (dist := v + f_hold f2 mod 2 ^ e) in *.
    destruct (FB_fdrop ON (fset_dist f2 dist) e ltac:(unfold FB in *; facc; repeat split; try lia; exact D5) ltac:(facc; lia))
      as (HF3 & E3i & E3o & E3b & E3h & E3l & E3d & E3ob).
    set (f3 := fdrop (fset_dist f2 dist) e) in *. revert E3i E3o E3b E3l E3d. facc. intros E3i E3o E3b E3l E3d.
    rewrite ?E3o, ?E3d, ?E3l, ?E2o, ?E2l in *. rewrite (wrap32_id (f_out f - x_beg x)) in * by lia.
    assert (HIN2 : f_in f2 <= IN).
    { rewrite <- E3i. revert HIN.
      destruct (Z.ltb_spec (f_out f - x_beg x) dist) as [Cw|Cw].
      - rewrite (wrap32_id (dist - _)) by lia.
        destruct ((x_whave x <? dist - (f_out f - x_beg x)) && negb (x_sane x =? 0)).
        + cbn [fin]. facc. intros X; exact X.
        + cbn [fin]. set (f4 := fset_op f3 (dist - (f_out f - x_beg x))).
          destruct (win_place_spec x f4 ltac:(subst f4; facc; lia) ltac:(subst f4; facc; lia) Xwn) as (n & CPw & Hn & Hl5 & En).
          apply COPIED_op_l in CPw.
          pose proof (dist_tailcopy_spec x (win_place x f4) ltac:(subst f4; revert Hl5 En; facc; rewrite ?E3l; intros; lia)) as CPt.
          rewrite (COPIED_in _ _ _ CPt), (COPIED_in _ _ _ CPw). intros X; exact X.
      - cbn [fin]. pose proof (out_copy_spec x f3 ltac:(rewrite E3l; lia)) as CP. rewrite (COPIED_in _ _ _ CP). intros X; exact X. }
    assert (CK1 : (if f_bits f1d <? e then (f_in f1d + 1 <=? IN) && (if f_bits f1d + 8 <? e then f_in f1d + 2 <=? IN else true) else true) = true).
    { rewrite E1i. destruct (f_bits f1d <? e); [|reflexivity]. destruct (f_bits f1d + 8 <? e).
      - rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
      - rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    rewrite CK1. cbn [andb].
    rewrite (proj2 (Z.leb_le e (f_bits f2)) E2e). cbn [andb].
    rewrite (proj2 (Z.leb_le 1 dist)) by lia. rewrite (proj2 (Z.leb_le 3 (f_len f))) by lia. rewrite (proj2 (Z.leb_le _ _) Hroom). cbn [andb].
    destruct (Z.ltb_spec (f_out f - x_beg x) dist) as [Cw|Cw]; [|reflexivity].
    rewrite (wrap32_id (dist - _)) by lia. rewrite Xsane. change (negb (1 =? 0)) with true. rewrite Bool.andb_true_r.
    destruct (Z.ltb_spec (x_whave x) (dist - (f_out f - x_beg x))) as [Wf|Wf]; [reflexivity|].
    apply window_ok_true; facc; rewrite ?E3l; lia.
  Qed.

  Lemma dodist_ok_root : forall k f,
    FB ON f -> 15 <= f_bits f -> 3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    fin (dodist (S (S k)) x s (code_at s (is_distcode s) (f_hold f mod 2 ^ is_distbits s)) f) <= IN ->
    dodist_ok x s IN ON WN (S (S k)) (code_at s (is_distcode s) (f_hold f mod 2 ^ is_distbits s)) f = true.
  Proof.
    intros k f HF Hb Hlen Hbeg Hroom HIN. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HTD) as HR15.
    pose proof (ridx_range _ _ _ _ HTD (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HTD _ XR) as (Hbits & RL & RN).
    set (getD := code_at s (is_distcode s)) in *. set (root := is_distbits s) in *.
    set (here := getD (f_hold f mod 2 ^ root)) in *.
    destruct (is_linkb here) eqn:HL.
    - destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dodist_ok_S. rewrite dodist_S in HIN. cbv zeta. cbv zeta in HIN.
      rewrite (land16_small (code_op here)) in * by lia. rewrite (land64_small (code_op here)) in * by lia. cbn [Z.eqb negb]. cbn [Z.eqb negb] in HIN.
      rewrite (proj2 (Z.leb_le (code_bits here) (f_bits f))) by lia. rewrite (proj2 (Z.ltb_lt (code_op here) 16)) by lia. cbn [andb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h in *. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) in * by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here) in *.
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      pose proof (pow2_pos (code_op here) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (code_val here + y) (ctab_len (is_distcode s)))) by lia. cbn [andb].
      destruct (sub_cell _ _ _ _ HTD (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getD root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getD. fold getD in HIN.
      exact (dodist_ok_term k (getD (code_val here + y)) f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia) ltac:(rewrite E1l; exact Hlen)
               ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o, E1l; exact Hroom) SSh HIN).
    - destruct (RN eq_refl) as [Hbr SH].
      exact (dodist_ok_term (S k) here f HF ltac:(lia) ltac:(lia) Hlen Hbeg Hroom SH HIN).
  Qed.


  Lemma dolen_ok_S : forall k here f,
    dolen_ok x s IN ON WN (S k) here f =
      let op := code_bits here in
      (op <=? f_bits f) &&
      let f := fdrop f op in
      let op := code_op here in
      if op =? 0 then f_out f <? ON
      else if negb (Z.land op 16 =? 0) then
        let f := fset_len f (code_val here) in
        let op := Z.land op 15 in
        (if negb (op =? 0) then if f_bits f <? op then (f_in f + 1 <=? IN) && (op <=? f_bits f + 8) else true else true) &&
        let f := len_extra x op f in
        pull2_ok IN f &&
        let f := fpull2_if x f in
        let i := Z.land (f_hold f) (x_dmask x) in
        (i <? ctab_len (is_distcode s)) && dodist_ok x s IN ON WN 4 (code_at s (is_distcode s) i) f
      else if Z.land op 64 =? 0 then
        (op <? 16) &&
        let i := code_val here + Z.land (f_hold f) (zmask op) in
        (i <? ctab_len (is_lencode s)) && dolen_ok x s IN ON WN k (code_at s (is_lencode s) i) f
      else true.
  Proof. intros. unfold len_extra. cbn [dolen_ok]. lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end. Qed.

  Lemma dodist_fin_ge : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    ((exists sy, 0 <= sy < 32 /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
    f_in f <= fin (dodist (S k) x s here f).
  Proof.
    intros k here f HF Hcb Hcf Hlen Hbeg Hroom Hsh.
    pose proof (dodist_term x s ON Xin Xwn Xbeg HON k here f HF Hcb Hcf Hlen Hbeg Hroom Hsh) as DT.
    destruct (dodist (S k) x s here f) as [f'|f' m msg]; cbn [fin].
    - destruct DT as [[_ (p & e & Hp & _ & Ei & _)] _]. lia.
    - destruct DT as [[_ (p & e & Hp & _ & Ei & _)] _]. lia.
  Qed.

  Lemma dodist_root_fin_ge : forall k f,
    FB ON f -> 15 <= f_bits f -> 3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    f_in f <= fin (dodist (S (S k)) x s (code_at s (is_distcode s) (f_hold f mod 2 ^ is_distbits s)) f).
  Proof.
    intros k f HF Hb Hlen Hbeg Hroom.
    destruct (dodist_root x s ON usedD Xin Xwn Xbeg HON HTD k f HF Hb Hlen Hbeg Hroom) as (c & Hc & DT).
    destruct (dodist (S (S k)) x s _ f) as [f'|f' m msg]; cbn [fin].
    - destruct DT as [[_ (p & e & Hp & _ & Ei & _)] _]. lia.
    - destruct DT as [[_ (p & e & Hp & _ & Ei & _)] _]. lia.
  Qed.

  Lemma dolen_ok_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    x_beg x <= f_out f -> f_out f + 258 <= ON ->
    ((exists sy, 0 <= sy < 288 /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    fin (dolen (S k) x s here f) <= IN ->
    dolen_ok x s IN ON WN (S k) here f = true.
  Proof.
    intros k here f HF Hcb Hcf Hbeg Hroom Hsh HIN. rewrite dolen_ok_S. rewrite dolen_S in HIN. cbv zeta. cbv zeta in HIN.
    rewrite (proj2 (Z.leb_le _ _) Hcf). cbn [andb].
    pose proof HF as (B1 & B2 & B3 & B4 & B5).
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *. pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. reflexivity. }
    pose proof (lens_sym_cases sy Hsy) as SC. destruct (sym_entry LENS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv in *. destruct SC as [[O1 O2]|[[O1 O2]|[(O1 & O2 & O3)|[O1|O1]]]].
    - rewrite O1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
    - rewrite O1. reflexivity.
    -
      destruct (len_op_facts op O1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia).
      replace (negb (Z.land op 16 =? 0)) with true in * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
      rewrite F3 in *. set (e := op - 16) in *.
      assert (He : 0 <= e <= 5) by lia.
      pose proof (pow2_le e 5 ltac:(lia)) as P5. change (2 ^ 5) with 32 in P5. pose proof (pow2_pos e ltac:(lia)) as P0.
      set (f1v := fset_len f1 v) in *.
      assert (HF1v : FB ON f1v /\ f_len f1v = v /\ f_in f1v = f_in f /\ f_out f1v = f_out f /\ f_bits f1v = f_bits f - code_bits here)
        by (subst f1v; unfold FB in *; facc; repeat split; first [assumption | reflexivity | lia]).
      clearbody f1v. destruct HF1v as (HF1v & Vl & Vi & Vo & Vb).
      set (f2 := len_extra x e f1v) in *.
      assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ 3 <= f_len f2 <= 258 /\ f_bits f2 <= 32 /\
                    f_in f2 = f_in f + (if negb (e =? 0) then if f_bits f1v <? e then 1 else 0 else 0)).
      { subst f2. unfold len_extra. destruct (Z.eqb_spec e 0) as [E0|E0]; cbn [negb].
        - split; [exact HF1v|]. rewrite Vo, Vl, Vi. unfold FB in HF1v. repeat split; lia.
        - cbv zeta. destruct (Z.ltb_spec (f_bits f1v) e) as [L1|L1].
          + destruct (FB_fpull x ON Xin f1v HF1v ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
            destruct (FB_fdrop ON (fset_len (fpull x f1v) (wrap32 (f_len (fpull x f1v) + Z.land (wrap32 (f_hold (fpull x f1v))) (zmask e)))) e
                        ltac:(unfold FB in *; facc; rewrite ?arr_len_set; repeat split; try lia) ltac:(facc; lia)) as (HQ & Qi & Qo & Qb & Qh & Ql & Qd & Qob).
            split; [exact HQ|]. revert Qi Qo Qb Ql. facc. intros Qi Qo Qb Ql. rewrite Qo, Ql, Qb, Qi, P1o, P1i, P1b, Vo, Vi.
            rewrite (land_wrap32_zmask (f_hold (fpull x f1v)) e) by (unfold FB in HP1; lia).
            pose proof (mod_pow2_range (f_hold (fpull x f1v)) e ltac:(lia)). rewrite wrap32_id by lia. rewrite P1l, Vl. repeat split; lia.
          + destruct (FB_fdrop ON (fset_len f1v (wrap32 (f_len f1v + Z.land (wrap32 (f_hold f1v)) (zmask e)))) e
                        ltac:(unfold FB in *; facc; repeat split; try lia) ltac:(facc; lia)) as (HQ & Qi & Qo & Qb & Qh & Ql & Qd & Qob).
            split; [exact HQ|]. revert Qi Qo Qb Ql. facc. intros Qi Qo Qb Ql. rewrite Qo, Ql, Qb, Qi, Vo, Vi.
            rewrite (land_wrap32_zmask (f_hold f1v) e) by (unfold FB in HF1v; lia).
            pose proof (mod_pow2_range (f_hold f1v) e ltac:(lia)). rewrite wrap32_id by lia. rewrite Vl. repeat split; lia. }
      clearbody f2. destruct HF2 as (HF2 & E2o & E2l & E2b32 & E2i).
      set (f3 := fpull2_if x f2) in *. pose proof HF2 as (D1 & D2 & D3 & D4 & D5).
      assert (HF3 : FB ON f3 /\ f_out f3 = f_out f /\ f_len f3 = f_len f2 /\ 15 <= f_bits f3 /\
                    f_in f3 = f_in f2 + (if f_bits f2 <? 15 then 2 else 0)).
      { subst f3. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f2) 15) as [L|L].
        - destruct (FB_fpull x ON Xin f2 HF2 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & _ & _).
          destruct (FB_fpull x ON Xin (fpull x f2) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & _ & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2b, P2i, P1o, P1l, P1b, P1i. repeat split; cbv beta iota; first [assumption | lia].
        - split; [exact HF2|]. repeat split; cbv beta iota; first [assumption | lia]. }
      clearbody f3. destruct HF3 as (HF3 & E3o & E3l & E3b & E3i).
      rewrite Xdm in *. rewrite land_zmask in * by (pose proof (T_root _ _ _ _ HTD); unfold FB in HF3; lia).
      pose proof (dodist_root_fin_ge 2 f3 HF3 E3b ltac:(lia) ltac:(lia) ltac:(lia)) as GE. change (S (S 2)) with 4%nat in GE.
      assert (HIN3 : f_in f3 <= IN) by lia.
      assert (CK1 : (if negb (e =? 0) then if f_bits f1v <? e then (f_in f1v + 1 <=? IN) && (e <=? f_bits f1v + 8) else true else true) = true).
      { destruct (negb (e =? 0)); [|reflexivity]. destruct (Z.ltb_spec (f_bits f1v) e); [|reflexivity].
        rewrite Vi. rewrite (proj2 (Z.leb_le _ _)) by (destruct (f_bits f2 <? 15); lia). apply Z.leb_le. unfold FB in HF1v. lia. }
      rewrite CK1. cbn [andb].
      assert (CK2 : pull2_ok IN f2 = true).
      { unfold pull2_ok. destruct (Z.ltb_spec (f_bits f2) 15); [|reflexivity]. apply Z.leb_le. lia. }
      rewrite CK2. cbn [andb].
      pose proof (ridx_range _ _ _ _ HTD (f_hold f3)) as XR. pose proof (T_used _ _ _ _ HTD).
      rewrite (proj2 (Z.ltb_lt (f_hold f3 mod 2 ^ is_distbits s) (ctab_len (is_distcode s)))) by lia. cbn [andb].
      apply dodist_ok_root; first [exact HF3 | exact E3b | lia | exact HIN].
    - rewrite O1. reflexivity.
    - rewrite O1. reflexivity.
  Qed.

  Lemma dolen_ok_root : forall k f,
    FB ON f -> 15 <= f_bits f -> x_beg x <= f_out f -> f_out f + 258 <= ON ->
    fin (dolen (S (S k)) x s (code_at s (is_lencode s) (f_hold f mod 2 ^ is_lenbits s)) f) <= IN ->
    dolen_ok x s IN ON WN (S (S k)) (code_at s (is_lencode s) (f_hold f mod 2 ^ is_lenbits s)) f = true.
  Proof.
    intros k f HF Hb Hbeg Hroom HIN. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HTL) as HR15.
    pose proof (ridx_range _ _ _ _ HTL (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HTL _ XR) as (Hbits & RL & RN).
    set (getL := code_at s (is_lencode s)) in *. set (root := is_lenbits s) in *.
    set (here := getL (f_hold f mod 2 ^ root)) in *.
    destruct (is_linkb here) eqn:HL.
    - destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dolen_ok_S. rewrite dolen_S in HIN. cbv zeta. cbv zeta in HIN.
      replace (code_op here =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia).
      rewrite (land16_small (code_op here)) in * by lia. rewrite (land64_small (code_op here)) in * by lia. cbn [Z.eqb negb]. cbn [Z.eqb negb] in HIN.
      rewrite (proj2 (Z.leb_le (code_bits here) (f_bits f))) by lia. rewrite (proj2 (Z.ltb_lt (code_op here) 16)) by lia. cbn [andb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h in *. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) in * by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here) in *.
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      pose proof (pow2_pos (code_op here) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (code_val here + y) (ctab_len (is_lencode s)))) by lia. cbn [andb].
      destruct (sub_cell _ _ _ _ HTL (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getL root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getL. fold getL in HIN.
      exact (dolen_ok_term k (getL (code_val here + y)) f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia)
               ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o; exact Hroom) SSh HIN).
    - destruct (RN eq_refl) as [Hbr SH].
      exact (dolen_ok_term (S k) here f HF ltac:(lia) ltac:(lia) Hbeg Hroom SH HIN).
  Qed.


  Hypothesis Xlast : x_last x + 5 = IN.
  Hypothesis Xend : x_end x + 257 = ON.

  Lemma trip_ok_true : forall f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= IN -> f_out f + 258 <= ON ->
    trip_ok x s IN ON WN f = true.
  Proof.
    intros f HF Hbeg Hin Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (fast_trip_spec x s ON usedL usedD Xin Xwn Xbeg HON Xdm Xlm HTL HTD f HF Hbeg Hroom) as TS.
    cbv zeta in TS. destruct TS as (Hmod & Hc & T1 & _).
    assert (HIN : fin (fast_trip x s f) <= IN).
    { destruct (fast_trip x s f) as [f'|f' m msg]; cbn [fin]; destruct T1 as (_ & Hi & _); lia. }
    clear T1. unfold fast_trip in HIN. cbv zeta in HIN.
    unfold trip_ok.
    assert (P2 : pull2_ok IN f = true).
    { unfold pull2_ok. destruct (Z.ltb_spec (f_bits f) 15); [apply Z.leb_le; lia|reflexivity]. }
    rewrite P2. cbn [andb]. cbv zeta.
    set (f1 := fpull2_if x f) in *.
    assert (HF1 : FB ON f1 /\ f_out f1 = f_out f /\ 15 <= f_bits f1).
    { subst f1. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f) 15) as [L|L].
      - destruct (FB_fpull x ON Xin f HF ltac:(lia)) as (HP1 & P1i & P1o & P1b & _).
        destruct (FB_fpull x ON Xin (fpull x f) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _).
        split; [exact HP2|]. rewrite P2o, P2b, P1o, P1b. split; [reflexivity|lia].
      - split; [exact HF|]. split; [reflexivity|lia]. }
    destruct HF1 as (HF1 & E1o & E1b).
    rewrite Xlm in *. rewrite land_zmask in * by (pose proof (T_root _ _ _ _ HTL); unfold FB in HF1; lia).
    pose proof (ridx_range _ _ _ _ HTL (f_hold f1)) as XR. pose proof (T_used _ _ _ _ HTL).
    rewrite (proj2 (Z.ltb_lt (f_hold f1 mod 2 ^ is_lenbits s) (ctab_len (is_lencode s)))) by lia. cbn [andb].
    change 4%nat with (S (S 2%nat)) in HIN |- *.
    apply dolen_ok_root; first [exact HF1 | exact E1b | lia | exact HIN].
  Qed.

  Lemma ff_loop_ok_nat : forall m in0 f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= IN -> f_out f + 258 <= ON -> 0 <= in0 <= f_in f ->
    (f_bits f - 8 * (f_in f - in0) < 8 \/ f_bits f - 8 * (f_in f - in0) < lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold (fpull2_if x f))) ->
    8 * (IN - f_in f) + f_bits f + (ON - f_out f) < Z.of_nat m ->
    InffastSafe.loop_ok x s IN ON WN (Z.of_nat m) f = true.
  Proof.
    induction m as [|m IH]; intros in0 f HF Hbeg Hin Hout Hin0 HD HM.
    { exfalso. unfold FB in HF. cbn in HM. lia. }
    unfold InffastSafe.loop_ok. rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    fold (InffastSafe.loop_ok x s IN ON WN (Z.of_nat m)).
    cbv beta. rewrite (trip_ok_true f HF Hbeg Hin Hout).
    pose proof (fast_trip_spec x s ON usedL usedD Xin Xwn Xbeg HON Xdm Xlm HTL HTD f HF Hbeg Hout) as TS.
    cbv zeta in TS. destruct TS as (Hmod & Hc & T1 & _).
    assert (EXIT : forall f', FB ON f' -> f_in f <= f_in f' ->
              lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold (fpull2_if x f)) <= 8 * (f_in f' - f_in f) + f_bits f - f_bits f' ->
              exit_ok f' = true).
    { intros f' HF' Hi' Hcons. unfold exit_ok. apply Z.leb_le. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold FB in HF'.
      assert (LT : f_bits f' / 8 < f_in f' + 1); [|lia].
      apply Z.div_lt_upper_bound; [lia|]. destruct HD as [HD|HD]; lia. }
    destruct (fast_trip x s f) as [f'|f' md msg].
    - destruct T1 as (HF' & Hi' & Ho' & Hcons).
      destruct (Z.ltb_spec (f_in f') (x_last x)); destruct (Z.ltb_spec (f_out f') (x_end x)); cbn [andb].
      + apply (IH in0); try assumption; unfold FB in HF'; destruct HD as [HD|HD]; lia.
      + exact (EXIT f' HF' ltac:(lia) Hcons).
      + exact (EXIT f' HF' ltac:(lia) Hcons).
      + exact (EXIT f' HF' ltac:(lia) Hcons).
    - destruct T1 as (HF' & Hi' & Ho' & Hcons). exact (EXIT f' HF' ltac:(lia) Hcons).
  Qed.

  Lemma ff_loop_ok : forall n in0 f,
    FB ON f -> x_beg x <= f_out f -> f_in f + 6 <= IN -> f_out f + 258 <= ON -> 0 <= in0 <= f_in f ->
    (f_bits f - 8 * (f_in f - in0) < 8 \/ f_bits f - 8 * (f_in f - in0) < lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold (fpull2_if x f))) ->
    8 * (IN - f_in f) + f_bits f + (ON - f_out f) < n ->
    InffastSafe.loop_ok x s IN ON WN n f = true.
  Proof.
    intros n in0 f HF Hbeg Hin Hout Hin0 HD HM.
    assert (Hn : 0 <= n) by (unfold FB in HF; lia).
    rewrite <- (Z2Nat.id n) by exact Hn. apply (ff_loop_ok_nat _ in0); try assumption. rewrite Z2Nat.id by exact Hn. exact HM.
  Qed.
End FF.


Theorem ff_ok_LEN : forall s c r,
  WINV (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
  ff_ok (w_s (RESTORE (mkW s c r))) (w_c (RESTORE (mkW s c r))) (w_r (RESTORE (mkW s c r))) = true.
Proof.
  intros s c r HW E Hh6 Hl258.
  winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb). pose proof (CORE_length s HC) as HL0.
  pose proof HC as (CW1 & CW2 & CW3 & CW4 & CW5 & CW6 & CW7 & CW8 & CW9 & CW10 & CW11 & CW12 & CW13 & CW14).
  destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (usedL & HTL & HUL).
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (usedD & HTD & HUD).
  pose proof (T_root _ _ _ _ HTL) as RL15. pose proof (T_root _ _ _ _ HTD) as RD15.
  assert (HLC : usedL <= ctab_len (is_lencode s)) by (clear - HUL; destruct (is_lencode s); cbn [ctab_len]; lia).
  assert (HDC : usedD <= ctab_len (is_distcode s)) by (clear - HUD; destruct (is_distcode s); cbn [ctab_len]; lia).
  assert (Hb14 : ir_bits r <= 14).
  { destruct Hbx as [Hbx|Hbx]; [clear - Hbx; lia|]. rewrite lneed_lneedg in Hbx. pose proof (lneedg_range _ _ _ _ HTL (ir_hold r)). clear - Hbx H. lia. }
  unfold RESTORE. cbn [w_s w_c w_r].
  set (sR := iset_bits (iset_hold s (ir_hold r)) (ir_bits r)).
  set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)).
  unfold ff_ok.
  set (x := ffx_of sR cR r).
  set (ON := arr_len (ic_outbuf c)) in *. set (IN := arr_len (ic_input c)) in *.
  assert (HX : x_input x = ic_input c /\ x_last x = IN - 5 /\ x_beg x = 0 /\ x_end x = ON - 257
               /\ x_wnext x = is_wnext s /\ x_dmask x = zmask (is_distbits sR) /\ x_lmask x = zmask (is_lenbits sR)
               /\ x_sane x = is_sane s /\ x_whave x = is_whave s /\ x_wsize x = is_wsize s).
  { subst x sR cR. unfold ffx_of. cbn [x_input x_last x_beg x_end x_wnext x_dmask x_lmask x_sane x_whave x_wsize]. sacc.
    rewrite !wrap32_id by (clear - Hh6 Hl258 RNH RPL RN RP RL RNI RNO HWF; lia). clear - RNH RPL HWF. repeat split; try reflexivity; lia. }
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (HTL' : TBLg LENS (code_at sR (is_lencode sR)) (is_lenbits sR) usedL) by exact HTL.
  assert (HTD' : TBLg DISTS (code_at sR (is_distcode sR)) (is_distbits sR) usedD) by exact HTD.
  assert (EsR : is_lencode sR = is_lencode s /\ is_distcode sR = is_distcode s /\ arr_len (is_window sR) = arr_len (is_window s))
    by (subst sR; repeat split; reflexivity).
  destruct EsR as (EsRL & EsRD & EsRW).
  assert (EcR : ic_input cR = ic_input c /\ ic_outbuf cR = ic_outbuf c /\ ic_avail_in cR = ir_have r /\ ic_avail_out cR = ir_left r)
    by (subst cR; repeat split; reflexivity).
  destruct EcR as (EcI & EcO & EcA & EcB). rewrite EcI, EcO, EcA, EcB, EsRW. fold IN ON.
  assert (F0 : f_in (ff0_of sR cR) = ir_next r /\ f_out (ff0_of sR cR) = ir_put r /\ f_bits (ff0_of sR cR) = ir_bits r
               /\ f_hold (ff0_of sR cR) = ir_hold r /\ f_ob (ff0_of sR cR) = ic_outbuf c) by (subst sR cR; repeat split; reflexivity).
  destruct F0 as (F0i & F0o & F0b & F0h & F0ob).
  assert (HF0 : FB ON (ff0_of sR cR)).
  { unfold FB. rewrite F0i, F0o, F0b, F0h, F0ob. fold ON. clear - RN RP RB RHO Hb14. repeat split; lia. }
  assert (XWH : 0 <= x_whave x <= x_wsize x).
  { rewrite X9, X10. clear - CW4 CW6 CW7. destruct (Z.eq_dec (is_wsize s) 0) as [Z0|Z0]; [pose proof (CW6 Z0); lia | pose proof (CW7 Z0); lia]. }
  assert (XWS : x_wsize x <> 0 -> x_wnext x < x_wsize x /\ arr_len (is_window s) = x_wsize x).
  { rewrite X10, X5. intros Z0. destruct (CW7 Z0) as [A _]. split; [exact A|].
    assert (Hblk : is_window_blk s <> None) by (intros N; exact (Z0 (CW1 N))).
    destruct (CW2 Hblk) as [L _]. rewrite L. symmetry. exact (CW3 Z0). }
  assert (XWS0 : x_wsize x = 0 -> x_whave x = 0) by (rewrite X10, X9; intros Z0; exact (proj1 (CW6 Z0))).
  pose proof (fpull2_if_mod x ON _ ltac:(rewrite X1; exact RIN) HF0) as HM. rewrite F0b, F0h in HM.
  assert (HD : f_bits (ff0_of sR cR) - 8 * (f_in (ff0_of sR cR) - ir_next r) < 8
               \/ f_bits (ff0_of sR cR) - 8 * (f_in (ff0_of sR cR) - ir_next r) < lneedg (code_at sR (is_lencode sR)) (is_lenbits sR) (f_hold (fpull2_if x (ff0_of sR cR)))).
  { rewrite F0b, F0i. replace (ir_next r - ir_next r) with 0 by lia. rewrite Z.mul_0_r, Z.sub_0_r.
    destruct Hbx as [Hbx|Hbx]; [left; exact Hbx|right].
    rewrite lneed_lneedg in Hbx.
    exact (lneedg_mono LENS _ _ usedL HTL (ir_hold r) _ (ir_bits r) ltac:(clear -RB; lia) ltac:(rewrite HM; symmetry; apply Z.mod_small; clear - RB RHO; lia) Hbx). }
  apply (ff_loop_ok x sR IN ON (arr_len (is_window s)) usedL usedD
           ltac:(rewrite X1; exact RIN) ltac:(rewrite X5; exact CW5) ltac:(rewrite X3; apply Z.le_refl) ltac:(clear - RNO; lia) X6 X7 HTL' HTD'
           ltac:(rewrite EsRL; exact HLC) ltac:(rewrite EsRD; exact HDC) ltac:(rewrite X8; exact CW13) XWH XWS XWS0
           ltac:(rewrite X2; apply Z.sub_add) ltac:(rewrite X4; apply Z.sub_add)
           _ (ir_next r) _ HF0); rewrite ?F0i, ?F0o, ?F0b, ?F0h.
  - rewrite X3. exact RP.
  - clear - RNH Hh6. lia.
  - clear - RPL Hl258. lia.
  - clear - RN. lia.
  - exact HD.
  - clear - RNH RPL RN RH RP RL RB Hb14. lia.
Qed.
