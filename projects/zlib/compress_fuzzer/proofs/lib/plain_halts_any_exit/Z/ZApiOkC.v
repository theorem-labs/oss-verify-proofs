(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prelim ZApi ZApiL ZHarnessL ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeI1 RefDeflSafeI5b RefDeflSafeI6 DeflateTaintRel DeflateTaintCall DeflateTaintTop RefCompress2Spec RefDeflProgress.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall ZApiInst.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi RefInflateRel RefInflate_runA RefInflateSafeD RefInflateSafeS2 RefInflateEqS RefInflateEqU RefInflateEqB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFrameIn InflateCall BoundArith ZTaint ZTaintI.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC InflateStallCS HarnessCompress ZApiInstC ZTaintC InflateCallsC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac pz := change (@Prelim.zlength) with (@ZIface.zlength) in *; change (@Prelim.ztake) with (@zfirstn Z) in *; change (@Prelim.zdrop) with (@zskipn Z) in *.

Lemma zlength_nonneg' : forall A (l : list A), 0 <= zlength l.
Proof. intros A l. unfold zlength. lia. Qed.

Lemma zlength_zfirstn_min : forall (l : list Z) n, 0 <= n -> zlength (zfirstn n l) = Z.min n (zlength l).
Proof. intros l n Hn. unfold zfirstn, zlength. rewrite length_firstn. lia. Qed.

Lemma zlength_zskipn' : forall (l : list Z) n, 0 <= n <= zlength l -> zlength (zskipn n l) = zlength l - n.
Proof. intros l n Hn. unfold zskipn, zlength in *. rewrite length_skipn. lia. Qed.

Lemma zlength_rev_append : forall (l acc : list Z), zlength (rev_append l acc) = zlength l + zlength acc.
Proof.
  induction l as [|a l IH]; intros acc; [cbn; unfold zlength; cbn; lia|].
  cbn [rev_append]. rewrite IH. unfold zlength. cbn [length]. lia.
Qed.

Section C2.
  Local Abbreviation c2L := (ZHarnessC.c2L zinstC).

  Lemma dzC_scalars : forall level, 0 <= level <= 9 ->
    zs_total_in (dzC level) = 0 /\ zs_total_out (dzC level) = 0 /\ zstrm_okP (dzC level).
  Proof.
    intros level Hl. rewrite (dzC_of level Hl). unfold dinitC_zr.
    pose proof (dinitC_fields (fun _ => g0) level Hl) as F. cbv zeta in F.
    destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & TO & AD).
    unfold zret_of_cs, zstrm_of_cs. cbn [zr_strm zs_total_in zs_total_out zs_adler zs_data_type].
    split; [exact TI|]. split; [exact TO|]. unfold zstrm_okP. cbn [zs_total_in zs_total_out zs_adler zs_data_type]. rewrite TI, TO, AD.
    assert (C : level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5 \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
    destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; cbn; unfold Z_UNKNOWN; lia.
  Qed.

  Definition CI (N : Z) (x : c2L) : Prop :=
    let ds := ZHarnessC.c2_ds zinstC x in
    DCALL (dz_s ds) (dz_s ds) /\ zstrm_okP (dz_z ds) /\ bytes_okP (ZHarnessC.c2_rest zinstC x)
    /\ 0 <= ZHarnessC.c2_ain zinstC x /\ 0 <= ZHarnessC.c2_slen zinstC x
    /\ ZHarnessC.c2_slen zinstC x + ZHarnessC.c2_ain zinstC x = zlength (ZHarnessC.c2_rest zinstC x)
    /\ zlength (ZHarnessC.c2_rest zinstC x) <= ZApiC.ZC_UMAX
    /\ 0 <= ZHarnessC.c2_aout zinstC x /\ 0 <= ZHarnessC.c2_left zinstC x
    /\ zs_total_out (dz_z ds) + ZHarnessC.c2_aout zinstC x + ZHarnessC.c2_left zinstC x = N
    /\ zs_total_out (dz_z ds) = zlength (ZHarnessC.c2_orev zinstC x)
    /\ 0 <= zs_total_out (dz_z ds).

  Definition CM (x : c2L) : Z :=
    ZHarnessC.c2_left zinstC x + ZHarnessC.c2_slen zinstC x + ZHarnessC.c2_ain zinstC x + ZHarnessC.c2_aout zinstC x.

  Lemma CI_init : forall N src level, 0 <= N <= ZHarnessC.ZBC_MAX -> zlength src <= ZHarnessC.ZBC_MAX -> bytes_okP src -> 0 <= level <= 9 ->
    CI N (ZHarnessC.c2_x0 zinstC N src level) /\ CM (ZHarnessC.c2_x0 zinstC N src level) = N + zlength src.
  Proof.
    intros N src level HN Hs Hb Hl. unfold CI, CM, ZHarnessC.c2_x0.
    cbn [ZHarnessC.c2_ds ZHarnessC.c2_rest ZHarnessC.c2_ain ZHarnessC.c2_slen ZHarnessC.c2_aout ZHarnessC.c2_left ZHarnessC.c2_orev ZApiC.dc_init zinstC].
    pz. destruct (dzC_scalars level Hl) as (TI & TO & ZOK). unfold zdc_init. cbn [dz_s dz_z]. rewrite TO.
    pose proof (zlength_nonneg' _ src). unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX, ZApiC.ZC_UMAX in *.
    split; [| lia].
    split; [rewrite (dsC_of level Hl); exact (DCALL_initC _ _ level Hl)|]. split; [exact ZOK|]. split; [exact Hb|].
    repeat (split; [first [reflexivity | lia] |]). cbn. lia.
  Qed.

  Lemma c2_step : forall N x, 0 <= N <= ZHarnessC.ZBC_MAX -> CI N x ->
    match ZHarnessC.c2_stepP zinstC x with
    | inl x' => CI N x' /\ 0 <= CM x' < CM x
    | inr (Some (x', _)) => zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) = zlength (ZHarnessC.c2_orev zinstC x')
                            /\ zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) <= N
    | inr None => False
    end.
  Proof.
    intros N x HN (HD & ZOK & HB & Hain & Hslen & Hsum & Hrl & Haout & Hleft & Htot & Horev & Htout0).
    unfold ZHarnessC.c2_stepP, ZHarnessC.c2_refill. cbn [ZApiC.dc_deflate ZApiC.dc_total_out zinstC].
    set (ds := ZHarnessC.c2_ds zinstC x) in *. set (rest := ZHarnessC.c2_rest zinstC x) in *.
    set (ain := ZHarnessC.c2_ain zinstC x) in *. set (slen := ZHarnessC.c2_slen zinstC x) in *.
    set (aout := ZHarnessC.c2_aout zinstC x) in *. set (left := ZHarnessC.c2_left zinstC x) in *.
    set (orev := ZHarnessC.c2_orev zinstC x) in *.
    unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX, ZApiC.ZC_UMAX in *.

    set (ao := if aout =? 0 then (if 4294967295 <? left then 4294967295 else left) else aout).
    set (lf := if aout =? 0 then left - (if 4294967295 <? left then 4294967295 else left) else left).
    set (ai := if ain =? 0 then (if 4294967295 <? slen then 4294967295 else slen) else ain).
    set (sl := if ain =? 0 then slen - (if 4294967295 <? slen then 4294967295 else slen) else slen).
    assert (ER : (let '(ao0, lf0) := if aout =? 0 then (if 4294967295 <? left then 4294967295 else left, left - (if 4294967295 <? left then 4294967295 else left)) else (aout, left) in
                  let '(ai0, sl0) := if ain =? 0 then (if 4294967295 <? slen then 4294967295 else slen, slen - (if 4294967295 <? slen then 4294967295 else slen)) else (ain, slen) in
                  (ao0, lf0, ai0, sl0)) = (ao, lf, ai, sl)).
    { subst ao lf ai sl. destruct (aout =? 0); destruct (ain =? 0); reflexivity. }
    rewrite ER. clear ER.
    assert (Hao : 0 <= ao /\ 0 <= lf /\ ao + lf = aout + left /\ ao < 2 ^ 32).
    { subst ao lf. destruct (Z.eqb_spec aout 0) as [E|E]; [| lia]. destruct (Z.ltb_spec 4294967295 left); lia. }
    assert (Hai : 0 <= ai /\ 0 <= sl /\ ai + sl = ain + slen /\ ai <= zlength rest /\ (sl <> 0 -> 0 < ai)).
    { subst ai sl. destruct (Z.eqb_spec ain 0) as [E|E]; [| lia]. destruct (Z.ltb_spec 4294967295 slen); lia. }
    destruct Hao as (Ao1 & Ao2 & Ao3 & Ao4). destruct Hai as (Ai1 & Ai2 & Ai3 & Ai4 & Ai5).
    pz.
    set (inp := zfirstn ai rest).
    assert (Linp : zlength inp = ai) by (subst inp; rewrite zlength_zfirstn_min by exact Ai1; lia).
    set (flush := ZHarnessC.c2_flush sl).
    assert (HFL : flush = Z_FINISH \/ (flush = Z_NO_FLUSH /\ 0 < zlength inp)).
    { subst flush. unfold ZHarnessC.c2_flush. destruct (Z.eqb_spec sl 0) as [E|E]; [left; reflexivity | right]. split; [reflexivity|]. rewrite Linp. exact (Ai5 E). }
    assert (Hfl16 : 0 <= flush < 16) by (destruct HFL as [-> |[-> _]]; unfold Z_FINISH, Z_NO_FLUSH; lia).
    assert (Hfl2 : flush = Z_NO_FLUSH \/ flush = Z_FINISH) by (destruct HFL as [F|[F _]]; [right | left]; exact F).
    assert (Hzc : dcall_wf (mkZCall inp ao (dz_z ds))).
    { unfold dcall_wf. cbn [zc_strm zc_avail_out zc_input]. split; [exact ZOK|]. split; [lia|]. split; [rewrite Linp; lia|].
      subst inp. apply bytes_okP_zfirstn. exact HB. }

    pose proof (DREL_facts (dz_s ds) ds HD) as (HR & HDD & HINV & _).
    pose proof (deflate_m_facts (dz_s ds) (mkZCall inp ao (dz_z ds)) flush HR Hzc Hfl16) as MF. cbv zeta in MF. destruct MF as (ZOK' & OUT & CON & TOT & BY).
    pose proof (deflate_progress (dz_s ds) (mkZCall inp ao (dz_z ds)) flush HINV HR Hzc HFL) as PRG.
    pose proof (DREL_zdc (dz_s ds) inp ds ao flush HD Hzc Hfl2) as DZ.
    unfold zdc_deflate in DZ |- *.
    cbn [zc_strm zc_avail_out zc_input] in OUT, CON, TOT, PRG.
    destruct (deflate_m (dz_s ds) (mkZCall inp ao (dz_z ds)) flush) as [s' zr]. cbn [fst snd] in *.
    destruct DZ as (HD' & Estrm & _ & _ & _).
    rewrite Linp in CON.
    assert (TOT' : zs_total_out (zr_strm zr) = zs_total_out (dz_z ds) + zlength (zr_output zr)).
    { rewrite TOT. apply wrap64_id. lia. }

    unfold ZHarnessC.c_step_ok. cbn [ZApiC.dc_total_out zinstC dz_z]. pz.
    replace (0 <=? zr_consumed zr) with true by (symmetry; apply Z.leb_le; lia).
    replace (zr_consumed zr <=? ai) with true by (symmetry; apply Z.leb_le; lia).
    replace (zlength (zr_output zr) <=? ao) with true by (symmetry; apply Z.leb_le; lia).
    replace (zs_total_out (zr_strm zr) =? zs_total_out (dz_z ds) + zlength (zr_output zr)) with true by (symmetry; apply Z.eqb_eq; exact TOT').
    cbn [andb].
    destruct (Z.eqb_spec (zr_rc zr) ZApi.Z_OK) as [E0|E0].
    -
      specialize (PRG E0).
      split.
      + unfold CI. cbn [ZHarnessC.c2_ds ZHarnessC.c2_rest ZHarnessC.c2_ain ZHarnessC.c2_slen ZHarnessC.c2_aout ZHarnessC.c2_left ZHarnessC.c2_orev dz_s dz_z]. pz.
        split; [exact HD'|]. split; [exact ZOK'|]. split; [apply bytes_okP_zskipn'; exact HB|].
        unfold ZApiC.ZC_UMAX. rewrite zlength_zskipn' by lia. rewrite zlength_rev_append. rewrite TOT'.
        pose proof (zlength_nonneg' _ (zr_output zr)). repeat split; lia.
      + unfold CM. cbn [ZHarnessC.c2_ain ZHarnessC.c2_slen ZHarnessC.c2_aout ZHarnessC.c2_left]. subst ao lf ai sl. fold aout left ain slen. lia.
    -
      cbn [ZHarnessC.c2_ds ZHarnessC.c2_orev dz_z]. rewrite TOT', zlength_rev_append. split; [lia|]. pose proof (zlength_nonneg' _ (zr_output zr)). lia.
  Qed.

  Lemma c2_loop_nat : forall N n x, 0 <= N <= ZHarnessC.ZBC_MAX -> CI N x -> CM x < Z.of_nat n ->
    match ZHarnessL.iterNL n (ZHarnessC.c2_stepP zinstC) x with
    | inl _ => False
    | inr None => False
    | inr (Some (x', _)) => zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) = zlength (ZHarnessC.c2_orev zinstC x')
                            /\ zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) <= N
    end.
  Proof.
    intros N n. induction n as [|n IH]; intros x HN HX HM.
    { exfalso. unfold CM in HM. destruct HX as (_ & _ & _ & A1 & A2 & _ & _ & A3 & A4 & _). cbn in HM. lia. }
    cbn [ZHarnessL.iterNL]. pose proof (c2_step N x HN HX) as ST.
    destruct (ZHarnessC.c2_stepP zinstC x) as [x'|[[x' e]|]]; [| exact ST | exact ST].
    destruct ST as [HX' HM']. apply IH; [exact HN | exact HX' | lia].
  Qed.

  Theorem c2_total : forall N src level, 0 <= N <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    0 <= level <= 9 -> ZHarnessC.c2_pure zinstC N src level <> None.
  Proof.
    intros N src level HN Hs Hb Hl. pz. unfold ZHarnessC.c2_pure, ZHarnessC.c2_loop. rewrite ZHarnessL.iterZL_nat.
    destruct (CI_init N src level HN Hs Hb Hl) as [HX0 HM0].
    assert (HM : CM (ZHarnessC.c2_x0 zinstC N src level) < Z.of_nat (Z.to_nat (ZHarnessC.C2_FUEL N (Prelim.zlength src)))).
    { rewrite HM0. unfold ZHarnessC.C2_FUEL. pz. pose proof (zlength_nonneg' _ src). rewrite Z2Nat.id by lia. lia. }
    pose proof (c2_loop_nat N _ _ HN HX0 HM) as L.
    destruct (ZHarnessL.iterNL _ _ _) as [x'|[[x' e]|]]; [destruct L | | destruct L].
    destruct L as [E1 E2]. cbn [ZApiC.dc_total_out zinstC]. pz. rewrite zlength_rev_append.
    replace (zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) =? zlength (ZHarnessC.c2_orev zinstC x') + zlength (@nil Z)) with true
      by (symmetry; apply Z.eqb_eq; change (zlength (@nil Z)) with 0; lia).
    replace (zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x')) <=? N) with true by (symmetry; apply Z.leb_le; exact E2).
    cbn [andb]. intros H; discriminate H.
  Qed.
End C2.

Section U2.
  Local Abbreviation u2L := (ZHarnessC.u2L zinstC).

  Definition UI (dlen : Z) (x : u2L) : Prop :=
    JC (ZHarnessC.u2_is zinstC x) /\ bytes_okP (ZHarnessC.u2_rest zinstC x)
    /\ 0 <= ZHarnessC.u2_ain zinstC x /\ 0 <= ZHarnessC.u2_len zinstC x
    /\ ZHarnessC.u2_len zinstC x + ZHarnessC.u2_ain zinstC x = zlength (ZHarnessC.u2_rest zinstC x)
    /\ zlength (ZHarnessC.u2_rest zinstC x) <= ZApiC.ZC_UMAX
    /\ 0 <= ZHarnessC.u2_aout zinstC x /\ 0 <= ZHarnessC.u2_left zinstC x
    /\ ZHarnessC.u2_aout zinstC x + ZHarnessC.u2_left zinstC x <= dlen.

  Definition UM (x : u2L) : Z :=
    ZHarnessC.u2_left zinstC x + ZHarnessC.u2_len zinstC x + ZHarnessC.u2_ain zinstC x + ZHarnessC.u2_aout zinstC x.

  Lemma UI_init : forall dlen src, 0 < dlen <= ZHarnessC.ZBC_MAX -> zlength src <= ZHarnessC.ZBC_MAX -> bytes_okP src ->
    UI dlen (ZHarnessC.u2_x0 zinstC dlen src) /\ UM (ZHarnessC.u2_x0 zinstC dlen src) = dlen + zlength src.
  Proof.
    intros dlen src Hd Hs Hb. unfold UI, UM, ZHarnessC.u2_x0.
    cbn [ZHarnessC.u2_is ZHarnessC.u2_rest ZHarnessC.u2_ain ZHarnessC.u2_len ZHarnessC.u2_aout ZHarnessC.u2_left ZApiC.ic_init zinstC]. pz.
    pose proof (zlength_nonneg' _ src). unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX, ZApiC.ZC_UMAX in *.
    split; [| lia]. split; [exact JC_init|]. split; [exact Hb|]. repeat split; lia.
  Qed.

  Lemma u2_step : forall dlen x ok, 0 < dlen <= ZHarnessC.ZBC_MAX -> UI dlen x ->
    match ZHarnessC.u2_stepP zinstC ok x with
    | inl x' => UI dlen x' /\ 0 <= UM x' < UM x
    | inr (Some _) => True
    | inr None => False
    end.
  Proof.
    intros dlen x ok Hd (HJ & HB & Hain & Hlen & Hsum & Hrl & Haout & Hleft & Hle).
    unfold ZHarnessC.u2_stepP, ZHarnessC.u2_refill. cbn [ZApiC.ic_inflate zinstC].
    set (is := ZHarnessC.u2_is zinstC x) in *. set (rest := ZHarnessC.u2_rest zinstC x) in *.
    set (ain := ZHarnessC.u2_ain zinstC x) in *. set (len := ZHarnessC.u2_len zinstC x) in *.
    set (aout := ZHarnessC.u2_aout zinstC x) in *. set (left := ZHarnessC.u2_left zinstC x) in *.
    unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX, ZApiC.ZC_UMAX in *.
    set (ao := if aout =? 0 then (if 4294967295 <? left then 4294967295 else left) else aout).
    set (lf := if aout =? 0 then left - (if 4294967295 <? left then 4294967295 else left) else left).
    set (ai := if ain =? 0 then (if 4294967295 <? len then 4294967295 else len) else ain).
    set (ln := if ain =? 0 then len - (if 4294967295 <? len then 4294967295 else len) else len).
    assert (ER : (let '(ao0, lf0) := if aout =? 0 then (if 4294967295 <? left then 4294967295 else left, left - (if 4294967295 <? left then 4294967295 else left)) else (aout, left) in
                  let '(ai0, ln0) := if ain =? 0 then (if 4294967295 <? len then 4294967295 else len, len - (if 4294967295 <? len then 4294967295 else len)) else (ain, len) in
                  (ao0, lf0, ai0, ln0)) = (ao, lf, ai, ln)).
    { subst ao lf ai ln. destruct (aout =? 0); destruct (ain =? 0); reflexivity. }
    rewrite ER. clear ER.
    assert (Hao : 0 <= ao /\ 0 <= lf /\ ao + lf = aout + left).
    { subst ao lf. destruct (Z.eqb_spec aout 0) as [E|E]; [| lia]. destruct (Z.ltb_spec 4294967295 left); lia. }
    assert (Hai : 0 <= ai /\ 0 <= ln /\ ai + ln = ain + len /\ ai <= zlength rest).
    { subst ai ln. destruct (Z.eqb_spec ain 0) as [E|E]; [| lia]. destruct (Z.ltb_spec 4294967295 len); lia. }
    destruct Hao as (Ao1 & Ao2 & Ao3). destruct Hai as (Ai1 & Ai2 & Ai3 & Ai4).
    pz.
    set (inp := zfirstn ai rest).
    assert (Linp : zlength inp = ai) by (subst inp; rewrite zlength_zfirstn_min by exact Ai1; lia).
    assert (Hz : ZC (mkZCall inp ao (iz_z is))).
    { unfold ZC. cbn [zc_avail_out zc_input]. split; [lia|]. split; [rewrite Linp; lia|]. subst inp. apply bytes_okP_zfirstn. exact HB. }
    pose proof (JC_facts is HJ) as (HI & HUS & HQ).
    pose proof (ic_call_facts is inp ao ok HJ Hz) as CF.
    pose proof (inflate_p_pure (wans ok) (iz_s is) (mkZCall inp ao (iz_z is)) Z_NO_FLUSH (INV_check _ HI)) as EP.
    pose proof (inflate_m_post Z_NO_FLUSH (iz_s is) (mkZCall inp ao (iz_z is)) (wans ok) _ HI Hz EP) as [P1 _].
    pose proof (inflate_m_post2 Z_NO_FLUSH (iz_s is) (mkZCall inp ao (iz_z is)) (wans ok) _ HI Hz EP) as [Q1 _].
    unfold zic_inflate in CF |- *.
    destruct (inflate_p (wans ok) (iz_s is) (mkZCall inp ao (iz_z is)) Z_NO_FLUSH) as [[s' zr] asked]. cbn [fst snd] in *.
    cbn [zc_avail_out zc_input zc_strm] in P1, Q1. rewrite Linp in Q1.
    destruct CF as (HJ' & _ & _ & _).
    unfold ZHarnessC.u_step_ok. pz.
    replace (zlength (zr_output zr) <=? ao) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.eqb_spec (zr_rc zr) ZApi.Z_OK) as [E0|E0].
    - destruct (Q1 E0) as (C1 & C2 & C3). cbn [negb orb].
      replace (0 <=? zr_consumed zr) with true by (symmetry; apply Z.leb_le; lia).
      replace (zr_consumed zr <=? ai) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      split.
      + unfold UI. cbn [ZHarnessC.u2_is ZHarnessC.u2_rest ZHarnessC.u2_ain ZHarnessC.u2_len ZHarnessC.u2_aout ZHarnessC.u2_left]. pz.
        split; [exact HJ'|]. split; [apply bytes_okP_zskipn'; exact HB|].
        unfold ZApiC.ZC_UMAX. rewrite zlength_zskipn' by lia. repeat split; lia.
      + unfold UM. cbn [ZHarnessC.u2_ain ZHarnessC.u2_len ZHarnessC.u2_aout ZHarnessC.u2_left]. subst ao lf ai ln. fold aout left ain len. lia.
    - cbn [negb orb]. exact I.
  Qed.

  Lemma u2_loop_nat : forall dlen n x, 0 < dlen <= ZHarnessC.ZBC_MAX -> UI dlen x -> UM x < Z.of_nat n ->
    match ZHarnessL.iterNL n (ZHarnessC.u2_stepP zinstC true) x with
    | inl _ => False
    | inr None => False
    | inr (Some _) => True
    end.
  Proof.
    intros dlen n. induction n as [|n IH]; intros x Hd HX HM.
    { exfalso. unfold UM in HM. destruct HX as (_ & _ & A1 & A2 & _ & _ & A3 & A4 & _). cbn in HM. lia. }
    cbn [ZHarnessL.iterNL]. pose proof (u2_step dlen x true Hd HX) as ST.
    destruct (ZHarnessC.u2_stepP zinstC true x) as [x'|[[x' e]|]]; [| exact I | exact ST].
    destruct ST as [HX' HM']. apply IH; [exact Hd | exact HX' | lia].
  Qed.

  Theorem u2_total : forall dlen src, 0 < dlen <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    ZHarnessC.u2_pure zinstC dlen src <> None.
  Proof.
    intros dlen src Hd Hs Hb. pz. unfold ZHarnessC.u2_pure, ZHarnessC.u2_loop. rewrite ZHarnessL.iterZL_nat.
    destruct (UI_init dlen src Hd Hs Hb) as [HX0 HM0].
    assert (HM : UM (ZHarnessC.u2_x0 zinstC dlen src) < Z.of_nat (Z.to_nat (ZHarnessC.U2_FUEL dlen (Prelim.zlength src)))).
    { rewrite HM0. unfold ZHarnessC.U2_FUEL. pz. pose proof (zlength_nonneg' _ src). rewrite Z2Nat.id by lia. lia. }
    pose proof (u2_loop_nat dlen _ _ Hd HX0 HM) as L.
    destruct (ZHarnessL.iterNL _ _ _) as [x'|[[x' e]|]]; [destruct L | intros H; discriminate H | destruct L].
  Qed.

  Lemma u2_iter_UI : forall dlen k y x, 0 < dlen <= ZHarnessC.ZBC_MAX -> UI dlen y ->
    ZHarnessL.iterNL k (ZHarnessC.u2_stepP zinstC true) y = inl x -> UI dlen x.
  Proof.
    intros dlen k. induction k as [|k IH]; intros y x Hd HY Hk.
    - cbn [ZHarnessL.iterNL] in Hk. injection Hk as <-. exact HY.
    - cbn [ZHarnessL.iterNL] in Hk. pose proof (u2_step dlen y true Hd HY) as ST.
      destruct (ZHarnessC.u2_stepP zinstC true y) as [y'|r]; [| destruct r; discriminate Hk].
      exact (IH y' x Hd (proj1 ST) Hk).
  Qed.

  Lemma u2_reach_UI : forall dlen src x, 0 < dlen <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    ZHarnessC.u2_reach zinstC dlen src x -> UI dlen x.
  Proof.
    intros dlen src x Hd Hs Hb [k Hk]. pz.
    exact (u2_iter_UI dlen k _ x Hd (proj1 (UI_init dlen src Hd Hs Hb)) Hk).
  Qed.

  Theorem u2_nomem : forall dlen src x, 0 < dlen <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    ZHarnessC.u2_reach zinstC dlen src x -> ZHarnessC.u2_wants zinstC x = true ->
    exists x', ZHarnessC.u2_stepP zinstC false x = inr (Some (x', ZApi.Z_MEM_ERROR)).
  Proof.
    intros dlen src x Hd Hs Hb HR HW.
    pose proof (u2_reach_UI dlen src x Hd Hs Hb HR) as HX.
    pose proof (u2_step dlen x false Hd HX) as ST.
    revert HW ST. unfold ZHarnessC.u2_wants, ZHarnessC.u2_inp, ZHarnessC.u2_ao, ZHarnessC.u2_stepP.
    cbn [ZApiC.ic_inflate ZApiC.ic_wants_window zinstC].
    destruct (ZHarnessC.u2_refill zinstC x) as [[[ao lf] ai] ln].
    unfold zic_wants_window, zic_inflate.
    intros HW. pose proof (inflate_p_refused_zr 6%N g0 (iz_s (ZHarnessC.u2_is zinstC x))
                             (mkZCall (Prelim.ztake ai (ZHarnessC.u2_rest zinstC x)) ao (iz_z (ZHarnessC.u2_is zinstC x))) Z_NO_FLUSH HW) as RZ.
    cbv zeta in RZ. destruct RZ as (_ & _ & _ & RC). change (wans false) with (@None (blk * (Z -> Z))).
    destruct (inflate_p None _ _ Z_NO_FLUSH) as [[s' zr] asked]. cbn [fst snd] in RC |- *.
    rewrite RC. intros ST.
    destruct (ZHarnessC.u_step_ok ai ao (zr_consumed zr) (zr_output zr) Z_MEM_ERROR); [| destruct ST].
    change (Z_MEM_ERROR =? ZApi.Z_OK) with false. cbv iota. eexists. reflexivity.
  Qed.
End U2.

Theorem zinstC_ok : ZHarnessC.zapiC_ok zinstC.
Proof.
  constructor.
  -   cbn [ZApiC.zc_dstate ZApiC.zc_dwin ZApiC.zc_dprev ZApiC.zc_dhead ZApiC.zc_dpend ZApiC.zc_isize ZApiC.zc_wsize zinstC].
    repeat constructor; lia.
  -   intros n Hn. cbn [ZApiC.zc_bound zinstC]. unfold ZHarnessC.ZBC_MAX in *. unfold ZApiC.ZC_MAX in *.
    unfold compressBound_m, sat_bound64. pose proof (cbound_range n ltac:(lia)) as R. unfold cbound in R.
    assert (A : Z.shiftr n 12 <= 256) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; lia).
    assert (B : Z.shiftr n 14 <= 64) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; lia).
    assert (C : Z.shiftr n 25 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
    rewrite wrap64_id by lia.
    (* zlib 1.4 (zl14cmp-r1): compressBound saturates; on this range the sum is at least n, so it does not *)
    assert (S12 : 0 <= Z.shiftr n 12) by (apply Z.shiftr_nonneg; lia).
    assert (S14 : 0 <= Z.shiftr n 14) by (apply Z.shiftr_nonneg; lia).
    match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end; lia.
  -   exact c2_total.
  -   exact u2_total.
  -   intros dlen src x1 ok Hd Hs Hb. unfold ZHarnessC.ZBC_MAX in *. unfold ZApiC.ZC_MAX in *. apply u2_two_trips; [unfold ZApiC.ZC_UMAX; lia | unfold ZApiC.ZC_UMAX; lia | exact Hb].
  -   exact u2_nomem.
Qed.
