(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_CODELENS11.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeF3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeOK2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeTY2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS3.

Module RefInflateSafeT1spec.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition IT_SAFE_INTRO : Prop :=
  forall (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr),
    0 <= codes <= 288 -> codes <= arr_len work -> arr_len work <= 65536 ->
    0 <= lens_ofs -> lens_ofs + codes <= arr_len lens ->
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
    ty_ok ty (lens_list lens lens_ofs codes) bits ->
    1 <= bits <= 15 -> 0 <= table -> table + it_room ty <= arr_len tbl ->
    it_safe ty lens lens_ofs codes tbl table bits work = true.
End RefInflateSafeT1spec.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeOK3.RefInflateSafeT1spec.

Module RefInflateSafeIT.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeOK3.RefInflateSafeT1spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac bsplit := repeat (apply andb_true_intro; split).
Local Ltac blia := first [apply Z.leb_le | apply Z.ltb_lt | apply Z.eqb_eq]; lia.

Lemma it_step_min : forall x st,
  match it_step x st with ItCont s' | ItBreak s' | ItFail s' => t_min s' end = shl32 1 (t_curr st).
Proof.
  intros x st. unfold it_step.
  destruct (if arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x) then _ else _) as [hop hval].
  cbv zeta.
  destruct ((wrap16 (arr_get (t_count st) (t_len st) - 1) =? 0) && (t_len st =? x_max x)); [reflexivity|].
  destruct ((x_root x <? _) && negb _); [| reflexivity].
  destruct (it_not_enough (x_ty x) _); reflexivity.
Qed.

Section T1.
  Variable ty : codetype.
Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
Variable table : Z.
Variable bits : Z.
Variable tbl : arr.
Variable work : arr.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hty : ty_ok ty ll bits.
  Hypothesis Hbits : 1 <= bits <= 15.
  Hypothesis HWN : codes <= arr_len work.
  Hypothesis HWN2 : arr_len work <= 65536.
  Hypothesis Hofs : 0 <= lens_ofs.
  Hypothesis HLN : lens_ofs + codes <= arr_len lens.
  Hypothesis Htable : 0 <= table.
  Hypothesis HTN : table + it_room ty <= arr_len tbl.

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let Hll' := OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation MINL := (MINL wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation hf := (hf wl).
  Local Notation wsym := (wsym wl ll).

  Lemma NC_ll' : NC ll = codes.
  Proof. exact (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl). Qed.

  Lemma Hty' : ty = CODES -> codes <= 19.
  Proof. intros ->. cbn [ty_ok] in Hty. rewrite NC_ll' in Hty. lia. Qed.

  Lemma NZC : NZ <= codes.
  Proof. exact (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl). Qed.

  Lemma room2 : 2 <= it_room ty <= 852.
  Proof. destruct ty; cbn [it_room]; unfold ENOUGH_LENS, ENOUGH_DISTS; lia. Qed.

  Lemma match_ok : forall w, 0 <= w < codes ->
    (if w + 1 <? it_match ty then true
     else if it_match ty <=? w then w - it_match ty <? it_ext_len ty (arr_len work) else true) = true.
  Proof.
    intros w Hw. pose proof Hty as T. pose proof NC_ll' as E. destruct ty; cbn [it_match it_ext_len ty_ok] in *.
    - rewrite E in T. destruct (Z.ltb_spec (w + 1) 20); [reflexivity | lia].
    - rewrite E in T. destruct (Z.ltb_spec (w + 1) 257); [reflexivity|]. destruct (Z.leb_spec 257 w); [| reflexivity]. blia.
    - rewrite E in T. destruct (Z.ltb_spec (w + 1) 0); [reflexivity|]. destruct (Z.leb_spec 0 w); [| reflexivity]. blia.
  Qed.

  Lemma sort_ok : forall O, arr_len O = 16 -> (forall l, 1 <= l <= 15 -> arr_get O l = OFF wl l) ->
    it_sort_ok lens lens_ofs codes O (arr_len work) = true.
  Proof.
    intros O HOL HO. unfold it_sort_ok. pose proof NZC as NZC0. pose proof Hll' as FL.
    enough (G : (fun sym st =>
                   arr_len (fst st) = 16 /\
                   (forall l, 1 <= l <= 15 -> arr_get (fst st) l = OFF wl l + countz l (firstn (Z.to_nat sym) ll)) /\
                   snd st = true) codes
                (forZ 0 codes (fun sym st => let '(offs, ok) := st in
                   let l := arr_get lens (lens_ofs + sym) in
                   if negb (l =? 0) then
                     let o := arr_get offs l in (arr_set offs l (wrap16 (o + 1)), ok && ((0 <=? o) && (o <? arr_len work)))
                   else (offs, ok)) (O, true))).
    { cbn beta in G. destruct G as [_ [_ G]]. exact G. }
    apply forZ_ind.
    - intros i [offs ok] Hi [L [G E]]. cbn [fst snd] in L, G, E. cbn zeta. subst ok.
      pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl i) by lia.
      rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl i) in R by lia.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      destruct (Z.eqb_spec (LofS ll i) 0) as [Z0|NZ0]; cbn [negb fst snd].
      + split; [exact L|]. split; [|reflexivity]. intros l Hl.
        rewrite countz_firstn_S by (rewrite (ll_length lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl); lia).
        replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity. rewrite Z0.
        destruct (Z.eqb_spec l 0); [lia|]. rewrite G by lia. lia.
      + pose proof (sidx_range ll FL i ltac:(rewrite NC_ll'; lia) NZ0) as [SR LR].
        unfold sidx in SR. rewrite <- Ewl in SR. rewrite <- G in SR by lia.
        pose proof (OFF_mono wl HW HL (LofS ll i + 1) 16 ltac:(lia)) as M. rewrite (NZ_eq wl HW HL) in NZC0.
        pose proof (OFF_nonneg wl HW HL (LofS ll i)) as ON.
        split; [rewrite arr_len_set; exact L|]. split.
        * intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite L.
          rewrite countz_firstn_S by (rewrite (ll_length lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl); lia).
          replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity.
          destruct (Z.eqb_spec (LofS ll i) l) as [EQ|NE].
          -- rewrite <- EQ. destruct (Z.leb_spec 0 (LofS ll i)); [|lia]. destruct (Z.ltb_spec (LofS ll i) 16); [|lia]. cbn [andb].
             rewrite Z.eqb_refl. rewrite wrap16_small by lia. rewrite G by lia. lia.
          -- cbn [andb]. destruct (Z.eqb_spec l (LofS ll i)); [congruence|]. rewrite G by lia. lia.
        * cbn [andb]. apply andb_true_intro. split; blia.
    - cbn [fst snd]. split; [exact HOL|]. split; [|reflexivity]. intros l Hl. rewrite HO by lia.
      change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. lia.
    - lia.
  Qed.

  Section Loop.
    Variable root : Z.
    Hypothesis Hroot : MINL <= root <= MAXL.
    Hypothesis HM1 : 1 <= MAXL.
    Hypothesis HK : TM wl MAXL <= 2 ^ MAXL.
    Hypothesis Eroot : root = ROOT wl bits.
    Hypothesis NE0 : it_not_enough ty (2 ^ root) = false.

    Local Notation noff := (noff wl root).
    Local Notation curr := (curr wl root).
    Local Notation used := (used wl root).
    Local Notation drop := (drop wl root).
    Local Notation low := (low wl root).
    Local Notation Pfx := (Pfx wl root).
    Local Notation islong := (islong wl root).
    Local Notation newtable := (newtable wl root).
    Local Notation XX := (X ty lens lens_ofs wl table root).
    Local Notation SM := (StM ll wl table root).

    Lemma codes_flat : forall k, ty = CODES -> 0 <= k < NZ -> islong k = false /\ used k = 2 ^ root /\ root <= 7.
    Proof.
      intros k Hc Hk. subst ty.
      destruct (codes_short wl ll bits Hll' Ewl Hbits Hty HM1) as [E7 M7]. rewrite <- Eroot in E7.
      pose proof (len_at_range wl HW HL k Hk) as LR.
      assert (HS : islong k = false) by (unfold ItDefs.islong; apply Z.ltb_ge; lia).
      destruct (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI HS) as [_ [_ U]].
      split; [exact HS|]. split; [exact U | lia].
    Qed.

    Lemma root_room : 2 ^ root <= it_room ty.
    Proof.
      pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (NZ_pos wl HW HL HM1) as NP.
      destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (E : ty = CODES) by (destruct ty; cbn in TC; congruence).
        destruct (codes_flat 0 E ltac:(lia)) as (_ & _ & R7). rewrite E. cbn [it_room].
        change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
      - apply (room_enough wl ll bits Hll' Ewl Hbits ty); [exact NE0 | destruct ty; cbn in TC; congruence].
    Qed.

    Lemma used_room : forall k, 0 <= k < NZ -> it_not_enough ty (used k) = false -> used k <= it_room ty.
    Proof.
      intros k Hk Hne. destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (E : ty = CODES) by (destruct ty; cbn in TC; congruence).
        destruct (codes_flat k E Hk) as (_ & U & _). rewrite U. exact root_room.
      - apply (room_enough wl ll bits Hll' Ewl Hbits ty); [exact Hne | destruct ty; cbn in TC; congruence].
    Qed.

    Lemma trip_ok : forall k st, 0 <= k < NZ -> SM k st -> 0 <= t_min st <= 32768 ->
      it_not_enough ty (used k) = false ->
      it_trip_ok XX (arr_len work) (arr_len lens) (arr_len tbl) st = true.
    Proof.
      intros k st Hk SMk Hmin Hne.
      pose proof (trip_spec ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k st Hk SMk) as TS.
      pose proof (root_range wl HW HL root Hroot HM1) as RR.
      pose proof (len_at_spec wl HW HL k Hk) as [L1 _].
      pose proof (rank_at_spec wl HW HL k Hk) as RK.
      pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [CR1 [CR2 CR3]].
      pose proof (used_eq wl HW HL root Hroot HM1 k Hk) as UE.
      pose proof (used_room k Hk Hne) as UR. pose proof room2 as R2. pose proof root_room as RRm.
      pose proof (hf_div_bound wl root HW HL Hroot HM1 HK k Hk) as HB.
      pose proof (rev_bound (len_at k) (code wl k) ltac:(lia)) as HFB. rewrite <- (hf_spec wl HW HL HK k Hk) in HFB.
      pose proof (pow2_le_15 (len_at k) ltac:(lia)) as P1. pose proof (pow2_le_15 (curr k) ltac:(lia)) as P2.
      pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k Hk) as [WR WL].
      pose proof NZC as NZC0.
      assert (Hdrop : 0 <= drop k <= root /\ drop k <= len_at k).
      { unfold ItDefs.drop. destruct (islong k) eqn:E; [unfold ItDefs.islong in E; apply Z.ltb_lt in E; lia | lia]. }
      assert (WB : W (len_at k) <= NZ).
      { pose proof (OFF_mono wl HW HL (len_at k + 1) 16 ltac:(lia)) as M. rewrite (OFF_step wl HW HL) in M by lia.
        pose proof (OFF_nonneg wl HW HL (len_at k)). rewrite <- (NZ_eq wl HW HL) in M. lia. }
      destruct st as [huff sym len next cur drp lw usd mn cnt tb wk].
      destruct SMk as (Eh & Es & El & En & Ec & Ed & Elw & Eu & Lc & Hc & Hw).
      cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in *.
      subst huff sym len next cur drp lw usd.
      assert (CC : (if (W (len_at k) - rank_at k - 1 =? 0) && negb (len_at k =? MAXL)
                    then (k + 1 <? arr_len work) && (0 <=? arr_get wk (k + 1)) && (0 <=? lens_ofs + arr_get wk (k + 1))
                         && (lens_ofs + arr_get wk (k + 1) <? arr_len lens)
                         && ((1 <=? arr_get lens (lens_ofs + arr_get wk (k + 1))) && (arr_get lens (lens_ofs + arr_get wk (k + 1)) <=? 15))
                    else true) = true).
      { destruct (Z.eqb_spec (W (len_at k) - rank_at k - 1) 0) as [Hc0|Hc0]; [| reflexivity].
        destruct (Z.eqb_spec (len_at k) MAXL) as [HlM|HlM]; cbn [andb negb]; [reflexivity|].
        pose proof (last_iff wl HW HL k Hk) as LI.
        assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
        rewrite (Hw (k + 1)) by lia.
        pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' (k + 1) ltac:(lia)) as [WR1 WL1].
        rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl (wsym (k + 1))) by lia.
        rewrite WL1. pose proof (len_at_spec wl HW HL (k + 1) ltac:(lia)) as [L2 _].
        bsplit; blia. }
      unfold it_trip_ok. cbv zeta.
      lazymatch goal with |- context [it_step ?x ?s] => destruct (it_step x s) as [st'|st'|st'] end.
      all: cbv beta iota delta [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                               x_ty x_lens x_lens_ofs x_table x_root x_max x_mask OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim2.X].
      all: rewrite (Hw k Hk).
      all: rewrite (Hc (len_at k)) by lia.
      all: rewrite (REM_self ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k Hk).
      all: rewrite (wrap16_small (W (len_at k) - rank_at k - 1)) by lia.
      all: rewrite Z.shiftr_div_pow2 by lia. all: rewrite !Z.shiftl_1_l.
      all: rewrite (match_ok (wsym k) WR).
      all: rewrite CC.
      1: { destruct TS as (Hk1 & Hfa & SM' & _ & _).
           destruct st' as [huff' sym' len' next' cur' drp' lw' usd' mn' cnt' tb' wk'].
           destruct SM' as (_ & _ & _ & En' & Ec' & _ & Elw' & _).
           cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in *.
           subst next' cur' lw'.
           pose proof (curr_range wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as [CS1 _].
           destruct (newtable (k + 1)) eqn:HN.
           - pose proof (lay_S_new wl HW HL root Hroot HM1 k ltac:(lia) HN) as [En1 _].
             pose proof (drop_low_new ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k HN) as [_ Elo1].
             rewrite En1, Elo1.
             pose proof (rev_bound root (Pfx (k + 1)) ltac:(lia)) as RB.
             match goal with |- _ && (if ?c then _ else _) = true => destruct c end; bsplit; try blia; reflexivity.
           - pose proof (lay_same_proj wl HW HL root Hroot HM1 k ltac:(lia) HN) as [En1 _].
             pose proof (drop_low_same ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k ltac:(lia) Hk1 HN) as [_ Elo1].
             rewrite En1, Elo1, !Z.eqb_refl. cbn [negb orb]. bsplit; try blia; reflexivity. }
      all: bsplit; try blia; try reflexivity.
      all: match goal with |- ?g => idtac "TRIPLEFT" g end.
    Qed.
  
    Hypothesis Hinc : 0 < LEFT wl -> codetype_eqb ty CODES = false /\ MAXL = 1.

    Lemma loop_ok : forall n k st, 0 <= k < NZ -> SM k st -> 0 <= t_min st <= 32768 ->
      it_not_enough ty (used k) = false ->
      (forall j, 0 <= j < k -> fails_at wl root ty j = false) ->
      NZ - k <= Z.of_nat n ->
      it_loop_ok n XX (arr_len work) (arr_len lens) (arr_len tbl) st = true.
    Proof.
      induction n as [|n IH]; intros k st Hk SMk Hmin Hne Hnf Hf; [change (Z.of_nat 0%nat) with 0 in Hf; lia|].
      rewrite it_loop_ok_S. rewrite (trip_ok k st Hk SMk Hmin Hne). cbn [andb].
      pose proof (trip_spec ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty' k st Hk SMk) as TS.
      pose proof (it_step_min XX st) as TMIN.
      pose proof (root_range wl HW HL root Hroot HM1) as RR.
      pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [CR1 _].
      pose proof SMk as (_ & _ & _ & _ & Ec & _).
      destruct (it_step XX st) as [st'|st'|st'].
      -
        destruct TS as (Hk1 & Hfa & SM' & _ & _).
        apply (IH (k + 1)); [lia | exact SM' | | | | rewrite Nat2Z.inj_succ in Hf; lia].
        + rewrite TMIN, Ec, shl32_pow2 by lia. pose proof (pow2_le_15 (curr k) ltac:(lia)). lia.
        + unfold ItDefs.fails_at in Hfa. destruct (Z.ltb_spec (k + 1) NZ); [|lia]. cbn [andb] in Hfa.
          destruct (newtable (k + 1)) eqn:HN; cbn [andb] in Hfa; [exact Hfa|].
          pose proof (lay_same_proj wl HW HL root Hroot HM1 k ltac:(lia) HN) as (_ & _ & EU). rewrite EU. exact Hne.
        + intros j Hj. destruct (Z.eq_dec j k) as [->|NE]; [exact Hfa | apply Hnf; lia].
      -
        destruct TS as (Hk1 & Eh & _ & _ & En & _ & _ & _). rewrite Eh, En.
        destruct (Z.eqb_spec (hf NZ) 0) as [Z0|Z0]; cbn [negb]; [reflexivity|].
        pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
        destruct (Z.eq_dec (LEFT wl) 0) as [HC0|HC0].
        { exfalso. apply Z0. apply (hf_NZ_complete wl root ty HW HL Hroot HM1 HK (proj1 LS2 HC0)); [| exact NE0].
          intros j Hj. apply Hnf. lia. }
        assert (HLp : 0 < LEFT wl) by lia.
        destruct (Hinc HLp) as [TC HMx].
        destruct (incomplete_facts wl ll bits Hll' Ewl Hbits HLp HMx) as (Emin & W1 & NZ1 & R1 & _).
        rewrite <- Eroot in R1.
        assert (Ek : k = 0) by lia. subst k.
        pose proof (len_at_0 wl HW HL HM1) as EL. rewrite Emin in EL.
        assert (Ehf1 : hf 1 = 1).
        { unfold ItDefs.hf. cbn [Z.eqb]. change (1 - 1) with 0. rewrite (code_0 wl HW HL HM1), EL. reflexivity. }
        rewrite NZ1, Ehf1. unfold ItDefs.noff. rewrite (lay_0 wl HW HL root Hroot HM1). cbn [fst].
        pose proof room2 as R2. bsplit; blia.
      - reflexivity.
    Qed.
  End Loop.

  Theorem it_safe_main : it_safe ty lens lens_ofs codes tbl table bits work = true.
  Proof.
    pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [CL CC].
    set (C := CNT lens lens_ofs codes) in CL, CC.
    pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof room2 as R2. pose proof NZC as NZC0.
    unfold it_safe, itm_count. change (it_count lens lens_ofs codes (it_zero_count (arr_make 16 0))) with C.
    cbv zeta. unfold itm_max. rewrite (find_max_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    replace ((0 <=? codes) && (codes <=? arr_len work) && (arr_len work <=? 65536)) with true by (symmetry; bsplit; blia).
    cbn [andb].
    destruct (Z.eqb_spec MAXL 0) as [HM0|HM0]; [bsplit; blia|].
    assert (HM1 : 1 <= MAXL) by lia.
    unfold itm_min. rewrite (find_min_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC HM1).
    unfold itm_reject. rewrite (left_check_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HL0|HL0]; [reflexivity|].
    assert (HK : TM wl MAXL <= 2 ^ MAXL) by lia.
    destruct ((0 <? LEFT wl) && (codetype_eqb ty CODES || negb (MAXL =? 1))) eqn:Hrej; [reflexivity|].
    assert (Hinc : 0 < LEFT wl -> codetype_eqb ty CODES = false /\ MAXL = 1).
    { intros HLp. destruct (Z.ltb_spec 0 (LEFT wl)); [|lia]. cbn [andb] in Hrej.
      apply Bool.orb_false_iff in Hrej as [A B]. apply Bool.negb_false_iff in B. apply Z.eqb_eq in B. split; assumption. }
    pose proof (offs_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as [OL OC].
    unfold itm_offs. change (it_offs C (arr_make 16 0)) with (OFS C). set (O := OFS C) in OL, OC |- *.
    rewrite (sort_ok O OL OC). cbn [andb].
    assert (ER : itm_root bits MAXL MINL = ROOT wl bits).
    { pose proof (MINL_spec wl HW HL HM1) as [A _]. unfold itm_root, ROOT.
      destruct (Z.ltb_spec MAXL bits); [destruct (Z.ltb_spec MAXL MINL) | destruct (Z.ltb_spec bits MINL)]; lia. }
    rewrite ER. pose proof (ROOT_range ty lens lens_ofs codes ll wl bits Hcodes Hlens Ell Ewl Hty' Hbits HM1) as RR.
    set (root := ROOT wl bits) in *.
    pose proof (root_range wl HW HL root RR HM1) as RR2.
    unfold itm_used. rewrite shl32_pow2 by lia.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [reflexivity|].
    pose proof (root_room root RR HM1 eq_refl NE0) as RRm.
    replace ((0 <=? table) && (table + 2 ^ root <=? arr_len tbl)) with true by (symmetry; bsplit; blia). cbn [andb].
    unfold itm_ctx, itm_used. rewrite shl32_pow2 by lia.
    change (mkItCtx ty lens lens_ofs table root MAXL (2 ^ root - 1)) with (X ty lens lens_ofs wl table root).
    unfold itm_work, itm_st0, itm_used. rewrite (sort_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl O work OL OC).
    rewrite shl32_pow2 by lia.
    pose proof (NZ_pos wl HW HL HM1) as NP.
    apply (loop_ok root RR HM1 HK eq_refl NE0 Hinc (Z.to_nat (codes + 1)) 0); [lia | | | | intros j Hj; lia | rewrite Z2Nat.id by lia; lia].
    - unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
      pose proof (lay_inv wl HW HL root RR HM1 0 ltac:(lia)) as [LI _].
      assert (HS : islong wl root 0 = false).
      { unfold islong. rewrite (len_at_0 wl HW HL HM1). apply Z.ltb_ge. lia. }
      destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold ItDefs.drop, ItDefs.low. rewrite HS.
      rewrite (len_at_0 wl HW HL HM1).
      repeat split; try reflexivity; try lia.
      + intros l Hl. rewrite CC by lia. unfold REM. rewrite (len_at_0 wl HW HL HM1).
        pose proof (MINL_spec wl HW HL HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW HL HM1).
        rewrite (OFF_below_MINL wl HW HL MINL) by lia.
        destruct (Z.ltb_spec l MINL); [apply D; lia|]. destruct (Z.eqb_spec l MINL); [subst; lia | reflexivity].
      + intros j Hj. rewrite Ewl in Hj |- *. apply (sorted_work ll Hll'); [|exact Hj].
        pose proof (NZ_le_NC ll Hll') as NN. rewrite NC_ll' in NN. lia.
    - cbn [t_min]. clear; lia.
    - unfold ItDefs.used. rewrite (lay_0 wl HW HL root RR HM1). cbn [snd]. exact NE0.
  Qed.
End T1.

Theorem it_safe_intro : IT_SAFE_INTRO.
Proof.
  intros ty lens lens_ofs codes tbl table bits work Hcodes HWN HWN2 Hofs HLN Hlens Hty Hbits Htable HTN.
  exact (it_safe_main ty lens lens_ofs codes (lens_list lens lens_ofs codes) (wl_of (lens_list lens lens_ofs codes))
           table bits tbl work Hcodes Hlens eq_refl eq_refl Hty Hbits HWN HWN2 Hofs HLN Htable HTN).
Qed.
End RefInflateSafeIT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeOK3.RefInflateSafeIT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [inflate_table lenlens_while1 lenlens_while2 ll2 codelens_while codelens_body NEEDBITS_k DECODE_k].


Lemma ll_post_ok_intro : forall tbl next lenbits work,
  arr_len tbl = 1444 -> arr_len work = 288 -> 0 <= next <= 1444 -> 0 <= lenbits < 2 ^ 32 ->
  ty32 tbl -> ty16 work -> ll_post_ok tbl next lenbits work = true.
Proof.
  intros tbl next lenbits work L1 L2 Hn Hb T1 T2. unfold ll_post_ok.
  rewrite L1, L2, !Z.eqb_refl. rewrite (proj2 (Z.leb_le 0 next)) by lia. rewrite (proj2 (Z.leb_le next 1444)) by lia.
  rewrite (proj2 (Z.leb_le 0 lenbits)) by lia. rewrite (proj2 (Z.ltb_lt lenbits (2 ^ 32))) by lia. cbn [andb].
  rewrite (proj2 (forallb_forall _ _)).
  2:{ intros k _. cbv beta. pose proof (T1 (Z.of_nat k)) as X. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite (proj2 (forallb_forall _ _)).
  2:{ intros k _. cbv beta. pose proof (T2 (Z.of_nat k)) as X. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  reflexivity.
Qed.

Lemma lens15b_intro : forall lens lo hi, (forall i, lo <= i < hi -> arr_get lens i <= 15) -> lens15b lens lo hi = true.
Proof.
  intros lens lo hi H. unfold lens15b. apply (proj2 (forallb_forall _ _)). intros k _. cbv beta zeta.
  destruct (Z.ltb_spec (Z.of_nat k) lo); [reflexivity|]. destruct (Z.leb_spec hi (Z.of_nat k)); [reflexivity|]. cbn [orb].
  apply Z.leb_le. apply H. lia.
Qed.

Lemma inflate_table_fail : forall ty lens lens_ofs codes tbl table bits work,
  let '(ret, tbl', toff, bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  ret <> 0 -> toff = table /\ bits' = bits.
Proof.
  intros ty lens lens_ofs codes tbl table bits work. unfold inflate_table. cbv zeta.
  destruct (it_find_max _ =? 0); [intros X; exfalso; exact (X eq_refl)|].
  destruct (it_left_check _) as [lft|]; [|intros _; split; reflexivity].
  destruct ((0 <? lft) && _); [intros _; split; reflexivity|].
  destruct (it_sort lens lens_ofs codes _) as [offs' work1].
  destruct (it_not_enough _ _); [intros _; split; reflexivity|].
  destruct (it_loop _ _ _) as [st'|st']; [intros X; exfalso; exact (X eq_refl) | intros _; split; reflexivity].
Qed.

Lemma decode_okb_one : forall two ty s c r p root used,
  TBLg ty (code_at s p) root used -> used <= ctab_size p -> REGS c r ->
  (forall op, two op = false) ->
  decode_okb two s c r p root = true.
Proof.
  intros two ty s c r p root used HT HU HR Htwo.
  pose proof (T_root _ _ _ _ HT) as R15. pose proof (T_used _ _ _ _ HT) as RU.
  pose proof HR as (_ & _ & _ & _ & _ & _ & [Bb Bh] & _).
  unfold decode_okb. cbv zeta.
  rewrite (proj2 (Z.leb_le 0 root)) by lia. rewrite (proj2 (Z.leb_le root 15)) by lia. cbn [andb].
  assert (I1 : forall h, 0 <= h -> 0 <= dec_idx1 root h < ctab_size p).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)). lia. }
  assert (N1 : forall h, 0 <= h -> 1 <= code_bits (code_at s p (dec_idx1 root h)) <= 15).
  { intros h Hh. unfold dec_idx1. pose proof (BITSv_range h root Hh ltac:(lia)).
    exact (proj1 (root_cell _ _ _ _ HT (BITSv h root) ltac:(lia))). }
  destruct (dchk_ok c 8 (dec_idx1 root) code_bits (ctab_size p) (code_at s p) r HR I1 N1 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
    as (r1 & E1 & HR1). rewrite E1.
  rewrite Htwo. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma ll2_eq : forall k s c r s2,
  lenlens_while2 k (mkW s c r) = ARun tt (mkW s2 c r) -> ll2 k s = s2.
Proof.
  intros k s c r s2 E. rewrite lenlens_while2_run in E.
  apply (f_equal (fun x => match x with ARun _ w => w_s w | _ => s end)) in E. cbn [w_s] in E. exact E.
Qed.


Section Lenlens.
  Variable s : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HW : WINV (mkW s c r).
  Hypothesis HA : ATY s.
  Hypothesis E : is_mode s = LENLENS.

  Lemma lenlens_facts :
    is_ncode s <= 19 /\
    match lenlens_while1 19 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) =>
        c1 = c /\
        exists lens19,
          ll2 19 s1 = iset_have (iset_lens s1 lens19) 19 /\ arr_len lens19 = 320
          /\ (forall i, 0 <= i < 19 -> 0 <= arr_get lens19 i <= 7) /\ ty16 lens19
          /\ CORE s1 /\ REGS c r1 /\ common s1 /\ ir_bits r1 < 8
          /\ 257 <= is_nlen s1 <= 286 /\ 1 <= is_ndist s1 <= 30
          /\ ir_out r1 = arr_len (ic_outbuf c) /\ (is_wbits s1 = 0 -> ir_put r1 = 0)
          /\ ATY s1
    | _ => True
    end.
  Proof.
    pose proof HW as HW0. winv_open2 HW0 E HC HR.
    destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
    split; [lia|].
    assert (HLL : LL s c r) by (unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    pose proof (lenlens_while1_spec c 19 s r HLL ltac:(cbn; lia)) as W1.
    pose proof (lenlens_while1_aty 19 (mkW s c r) HA) as A1.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact I|exact I].
    unfold ATYr, wof in A1. cbn [w_s] in A1.
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & P1 & Ep1 & Q1 & Ecd & Ewk).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    split; [reflexivity|].
    destruct (lenlens_while2_spec c 19 s1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    pose proof (lenlens_while2_aty 19 (mkW s1 c r1) A1) as A2. rewrite EQ2 in A2. unfold ATYr, wof in A2. cbn [w_s] in A2.
    exists lens19. split; [exact (ll2_eq _ _ _ _ _ EQ2)|]. split; [exact HL19|].
    split; [intros i Hi; destruct (order_a_onto i Hi) as [j [Hj <-]]; apply HLs19; exact Hj|].
    split; [exact (proj1 A2)|].
    repeat (split; [first [assumption | lia]|]). exact A1.
  Qed.

  Theorem WINV_lenlens_okb : lenlens_okb (mkW s c r) = true.
  Proof.
    pose proof lenlens_facts as F. unfold lenlens_okb. cbn [w_s].
    destruct F as [Hnc F]. rewrite (proj2 (Z.leb_le _ _) Hnc). cbn [andb].
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity].
    destruct F as (-> & lens19 & EL2 & HL19 & HLs & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
    rewrite EL2. unfold ll_call_ok. sacc.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    rewrite (proj2 (forallb_forall _ _)).
    2:{ intros k Hk. cbv beta. apply in_seq in Hk. apply Z.leb_le. pose proof (HLs (Z.of_nat k) ltac:(lia)). lia. }
    rewrite (it_safe_intro CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
               ltac:(lia) ltac:(rewrite CB2; lia) ltac:(rewrite CB2; lia) ltac:(lia) ltac:(rewrite HL19; lia)
               ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    pose proof (inflate_table_typed CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    pose proof (inflate_table_fail CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as TF.
    destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
    destruct TC as [[TC5 TC6] TC]. destruct TT as [TT1 TT2]. cbn [it_room] in TC. cbv beta iota.
    apply ll_post_ok_intro; [rewrite TC5, CB3; reflexivity | rewrite TC6, CB2; reflexivity | | | exact TT1 | exact TT2].
    - destruct (Z.eq_dec ret 0) as [R0|R0]; [destruct (TC R0) as (_ & X & _); pose proof (pow2_pos lb ltac:(lia)); lia | destruct (TF R0) as [-> _]; lia].
    - destruct (Z.eq_dec ret 0) as [R0|R0]; [destruct (TC R0) as (X & _); lia | destruct (TF R0) as [_ ->]; lia].
  Qed.

  Theorem lenlens_next_WINV : forall w2, lenlens_next (mkW s c r) = Some w2 ->
    WINV w2 /\ ATY (w_s w2) /\ is_mode (w_s w2) = CODELENS.
  Proof.
    intros w2 HN. pose proof lenlens_facts as [Hnc F]. unfold lenlens_next in HN.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
    destruct F as (-> & lens19 & EL2 & HL19 & HLs & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
    cbv zeta in HN. rewrite EL2 in HN. sacc_in HN.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs i ltac:(lia)); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    pose proof (inflate_table_typed CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
    destruct TC as [[TC5 TC6] TC]. destruct TT as [TT1 TT2]. cbn [it_room] in TC.
    destruct (Z.eqb_spec ret 0) as [R0|R0]; [|discriminate HN].
    specialize (TC R0). destruct TC as (TC1 & TC2 & TC3 & TC4).
    apply some_inj in HN. subst w2. unfold ll_s2, ll_tab. cbn [w_s].
    split; [|split].
    - winv_split.
      + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [left; exact Hb1|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros i Hi; exfalso; lia|].
        cbn [cpok]. split; [lia|]. exists (nxt - 0). split; [lia|]. exact TC3.
      + exact HWF1.
      + exact HWB1.
    - unfold ATY. sacc. split; [exact HT19|]. split; [exact TT2|exact TT1].
    - sacc. reflexivity.
  Qed.
End Lenlens.


Section Codelens.
  Variable c : icall.

  Lemma clw_chk_CL : forall k s r, CL s c r -> clw_chk k s c r = true.
  Proof.
    induction k as [|k IH]; intros s r HCL; [reflexivity|].
    cbn [clw_chk]. destruct (Z.ltb_spec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE]; [|reflexivity].
    pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & HU).
    rewrite (decode_okb_one cl_two CODES s c r (is_lencode s) (is_lenbits s) used HTg).
    2:{ destruct (is_lencode s) as [ofs| |]; cbn [ctab_size]; lia. }
    2:{ exact HR. }
    2:{ intros op. reflexivity. }
    cbn [andb].
    pose proof (codelens_body_spec c s r HCL LT) as B.
    destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity|reflexivity].
    destruct B as (-> & HCL1 & _). apply IH. exact HCL1.
  Qed.
End Codelens.

Section Codelens2.
  Variable flush : Z.
Variable s : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HW : WINV (mkW s c r).
  Hypothesis HA : ATY s.
  Hypothesis E : is_mode s = CODELENS.

  Lemma codelens_facts :
    CL s c r /\ is_have s < is_nlen s + is_ndist s /\
    match codelens_while 321 (mkW s c r) with
    | ARun _ (mkW s1 c1 r1) =>
        is_mode s1 = BAD
        \/ (c1 = c /\ CL s1 c r1 /\ is_have s1 = is_nlen s1 + is_ndist s1 /\ ir_bits r1 < 8 /\ ATY s1)
    | _ => True
    end.
  Proof.
    pose proof HW as HW0. winv_open2 HW0 E HC HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    assert (HCL : CL s c r) by (unfold CL; repeat (split; [first [assumption | lia]|]); exact HWB).
    split; [exact HCL|]. split; [lia|].
    pose proof (codelens_while_spec c 321 s r HCL ltac:(cbn; lia)) as W.
    pose proof (codelens_while_aty 321 (mkW s c r) HA) as A1.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact I|exact I].
    unfold ATYr, wof in A1. cbn [w_s] in A1.
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & P1 & Ep1 & Q1 & _)|(Hm1 & _)].
    - right. destruct (Q1 ltac:(lia)) as [_ Hb1]. split; [reflexivity|]. split; [exact HCL1|]. split; [exact Hh1|]. split; [exact Hb1|exact A1].
    - left. exact Hm1.
  Qed.

  Theorem WINV_codelens_okb : codelens_okb (mkW s c r) = true.
  Proof.
    pose proof codelens_facts as (HCL & Hlt & F). unfold codelens_okb. cbn [w_s w_c w_r].
    pose proof HCL as (_ & _ & _ & _ & _ & Hnl & Hnd & _).
    rewrite (proj2 (Z.leb_le _ 320)) by lia. rewrite (clw_chk_CL c 321 s r HCL). cbn [andb].
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|reflexivity|reflexivity].
    destruct F as [Hm1 | (-> & HCL1 & Hh1 & Hb1 & HA1)]; [rewrite Hm1; reflexivity|].
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    rewrite E1. change (CODELENS =? BAD) with false. cbv iota.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    unfold cl_post_ok. destruct (arr_get (is_lens s1) 256 =? 0); [reflexivity|].
    rewrite (lens15b_intro (is_lens s1) 0 (is_nlen s1)) by (intros i Hi; pose proof (HLs1 i ltac:(lia)); lia).
    rewrite (it_safe_intro LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
               ltac:(lia) ltac:(rewrite CB2; lia) ltac:(rewrite CB2; lia) ltac:(lia) ltac:(rewrite CB1; lia)
               ltac:(intros i Hi; apply HLs1; lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    pose proof (inflate_table_typed LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) (proj2 (proj2 HA1)) (proj1 (proj2 HA1))) as TT.
    pose proof (inflate_table_fail LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as TF.
    destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[retL tblL] nextL] lenbitsL] workL].
    destruct TL as [[TL5 TL6] TL]. destruct TT as [TT1 TT2]. cbn [it_room] in TL. unfold ENOUGH_LENS in TL. cbv beta iota.
    rewrite (ll_post_ok_intro tblL nextL lenbitsL workL ltac:(rewrite TL5, CB3; reflexivity) ltac:(rewrite TL6, CB2; reflexivity)
               ltac:(destruct (Z.eq_dec retL 0) as [R0|R0]; [destruct (TL R0) as (_ & X & _); pose proof (pow2_pos lenbitsL ltac:(lia)); lia | destruct (TF R0) as [-> _]; lia])
               ltac:(destruct (Z.eq_dec retL 0) as [R0|R0]; [destruct (TL R0) as (X & _); lia | destruct (TF R0) as [_ ->]; lia])
               TT1 TT2).
    cbn [andb].
    destruct (Z.eqb_spec retL 0) as [RL0|RL0]; [|reflexivity].
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). pose proof (pow2_pos lenbitsL ltac:(lia)) as PL.
    unfold cl_tab1. sacc.
    rewrite (lens15b_intro (is_lens s1) (is_nlen s1) (is_nlen s1 + is_ndist s1)) by (intros i Hi; pose proof (HLs1 i ltac:(lia)); lia).
    rewrite (it_safe_intro DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
               ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(rewrite TL6, CB2; lia) ltac:(lia) ltac:(rewrite CB1; lia)
               ltac:(intros i Hi; apply HLs1; lia)
               ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia)
               ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)).
    cbn [andb].
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    pose proof (inflate_table_typed DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL TT1 TT2) as TTD.
    pose proof (inflate_table_fail DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as TFD.
    destruct (inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as [[[[retD tblD] nextD] distbitsD] workD].
    destruct TD as [[TD5 TD6] TD]. destruct TTD as [TTD1 TTD2]. cbn [it_room] in TD. unfold ENOUGH_DISTS in TD. cbv beta iota.
    apply ll_post_ok_intro; [rewrite TD5, TL5, CB3; reflexivity | rewrite TD6, TL6, CB2; reflexivity | | | exact TTD1 | exact TTD2].
    - destruct (Z.eq_dec retD 0) as [R0|R0]; [destruct (TD R0) as (_ & X & _); pose proof (pow2_pos distbitsD ltac:(lia)); lia | destruct (TFD R0) as [-> _]; lia].
    - destruct (Z.eq_dec retD 0) as [R0|R0]; [destruct (TD R0) as (X & _); lia | destruct (TFD R0) as [_ ->]; lia].
  Qed.

  Theorem codelens_next_WINV : forall w2, codelens_next flush (mkW s c r) = Some w2 ->
    WINV w2 /\ is_mode (w_s w2) = LEN_.
  Proof.
    intros w2 HN. pose proof codelens_facts as (HCL & Hlt & F). rewrite codelens_next_eq in HN.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
    destruct F as [Hm1 | (-> & HCL1 & Hh1 & Hb1 & HA1)]; [rewrite Hm1 in HN; discriminate HN|].
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    rewrite E1 in HN. change (CODELENS =? BAD) with false in HN. cbv iota in HN.
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    unfold cl_post_next in HN. destruct (arr_get (is_lens s1) 256 =? 0); [discriminate HN|].
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[retL tblL] nextL] lenbitsL] workL].
    destruct TL as [[TL5 TL6] TL].
    destruct (Z.eqb_spec retL 0) as [RL0|RL0]; cbn [negb] in HN; [|discriminate HN].
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    cbv zeta in HN. unfold cl_tab1 in HN. sacc_in HN.
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    destruct (inflate_table DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL) as [[[[retD tblD] nextD] distbitsD] workD].
    destruct TD as [[TD5 TD6] TD].
    destruct (Z.eqb_spec retD 0) as [RD0|RD0]; cbn [negb] in HN; [|discriminate HN].
    destruct (flush =? Z_TREES); [discriminate HN|].
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    apply some_inj in HN. subst w2. unfold cl_tab2. cbn [w_s]. split.
    - winv_split.
      + core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [exact Hb1|]. unfold tables. sacc. split.
        * cbn [cpok]. split; [lia|]. exists (nextL - 0). split; [lia|].
          apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        * cbn [cpok]. split; [lia|]. exists (nextD - nextL). split; [lia|]. exact TD3.
      + exact HWF1.
      + exact HWB1.
    - sacc. reflexivity.
  Qed.
End Codelens2.


Theorem WINV_codelens_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = CODELENS ->
  codelens_chain flush w = true.
Proof.
  intros flush [s c r] HW HA E. cbn [w_s] in HA, E. unfold codelens_chain.
  rewrite (WINV_codelens_okb s c r HW HA E).
  destruct (codelens_next flush (mkW s c r)) as [w2|] eqn:HN; [|reflexivity].
  destruct (codelens_next_WINV flush s c r HW HA E w2 HN) as [HW2 E2]. exact (WINV_len__chain w2 HW2 E2).
Qed.

Theorem WINV_lenlens_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = LENLENS ->
  lenlens_chain flush w = true.
Proof.
  intros flush [s c r] HW HA E. cbn [w_s] in HA, E. unfold lenlens_chain.
  rewrite (WINV_lenlens_okb s c r HW HA E).
  destruct (lenlens_next (mkW s c r)) as [w2|] eqn:HN; [|reflexivity].
  destruct (lenlens_next_WINV s c r HW HA E w2 HN) as (HW2 & HA2 & E2). exact (WINV_codelens_chain flush w2 HW2 HA2 E2).
Qed.

Lemma table_next_ATY : forall w w2, ATY (w_s w) -> table_next w = Some w2 -> ATY (w_s w2).
Proof.
  intros w w2 HA HN. unfold table_next in HN.
  pose proof (NEEDBITS_aty 14 w HA) as A1.
  destruct (NEEDBITS 14 w) as [u [s1 c1 r1] | w1 | rc w1]; [|discriminate HN|discriminate HN].
  unfold ATYr, wof in A1. cbn [w_s] in A1.
  destruct (_ || _); [discriminate HN|]. apply some_inj in HN. subst w2. unfold tb_s2, tb_s. cbn [w_s].
  apply (ATY_same s1 _ A1); reflexivity.
Qed.

Theorem WINV_table_chain : forall flush w, WINV w -> ATY (w_s w) -> is_mode (w_s w) = TABLE ->
  table_chain flush w = true.
Proof.
  intros flush w HW HA E. unfold table_chain.
  destruct (table_next w) as [w2|] eqn:HN; [|reflexivity].
  destruct (table_next_WINV w w2 HW E HN) as [HW2 E2].
  exact (WINV_lenlens_chain flush w2 HW2 (table_next_ATY w w2 HA HN) E2).
Qed.


Theorem okL_WINV : forall flush w, WINV w -> ATY (w_s w) -> RefInflateArms.okL flush w = true.
Proof.
  intros flush w HW HA. unfold RefInflateArms.okL. cbv zeta.
  destruct (Z.eqb_spec (is_mode (w_s w)) DICT) as [E1|N1]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) MEM) as [E2|N2]; [reflexivity|].
  destruct (Z.eqb_spec (is_mode (w_s w)) SYNC) as [E3|N3]; [reflexivity|]. cbn [orb].
  rewrite (WINV_leave_okb w HW N1 N2). cbn [andb].
  destruct (Z.eqb_spec (is_mode (w_s w)) DISTEXT) as [E4|N4]; [exact (WINV_distext_chain w HW E4)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) DIST) as [E5|N5]; [exact (WINV_dist_chain w HW E5)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LENEXT) as [E6|N6]; [exact (WINV_lenext_chain w HW E6)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) MATCH) as [E7|N7]; [exact (WINV_match_okb w HW E7)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LEN) as [E8|N8]; [exact (WINV_len_chain w HW E8)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LEN_) as [E9|N9]; [exact (WINV_len__chain w HW E9)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) TABLE) as [E10|N10]; [exact (WINV_table_chain flush w HW HA E10)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) LENLENS) as [E11|N11]; [exact (WINV_lenlens_chain flush w HW HA E11)|].
  destruct (Z.eqb_spec (is_mode (w_s w)) CODELENS) as [E12|N12]; [exact (WINV_codelens_chain flush w HW HA E12)|].
  reflexivity.
Qed.

Theorem inflate_safe_proof : forall st zc flush,
  RefInflateRel.ireach st -> RefInflateRel.zcall_wf zc -> 0 <= flush < 16 ->
  RefInflateCtx.loop_ok RefInflateArms.okL flush (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.W0 st zc) = true.
Proof.
  intros st zc flush HR Hz _. exact (inflate_safe_gen2 RefInflateArms.okL flush (okL_WINV flush) st zc HR Hz).
Qed.
