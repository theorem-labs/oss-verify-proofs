(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSimPre.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSim1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSim2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT1spec.
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
  Let Hll' := ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

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
                               x_ty x_lens x_lens_ofs x_table x_root x_max x_mask ItSim2.X].
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
