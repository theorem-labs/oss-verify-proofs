(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prelim ZApi ZApiL ZHarnessL ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate HarnessSmall ZApiInst.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi RefInflateRel RefInflateSafeD RefInflateSafeS2 RefInflateEqS RefInflateEqU RefInflateEqB InflateCall ZTaintI.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintTop HarnessCompress ZApiInstC InflateCallsC ZApiOkC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac pz := change (@Prelim.zlength) with (@ZIface.zlength) in *; change (@Prelim.ztake) with (@zfirstn Z) in *; change (@Prelim.zdrop) with (@zskipn Z) in *.

Lemma zskipn_zskipn : forall (l : list Z) a b, 0 <= a -> 0 <= b -> zskipn a (zskipn b l) = zskipn (b + a) l.
Proof. intros l a b Ha Hb. unfold zskipn. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma zfirstn_all_of_len : forall (l : list Z) n, zlength l <= n -> zfirstn n l = l.
Proof. intros l n H. unfold zfirstn. apply firstn_all2. unfold zlength in H. lia. Qed.

Lemma ic_inflate_factsC : forall inp (x : istream) aout ok,
  INV (iz_s x) -> bytes_ok inp -> zlength inp < 2 ^ 32 -> 0 <= aout < 2 ^ 32 ->
  let '(x', consumed, bs, rc) := zic_inflate inp x aout ok in
  INV (iz_s x') /\ 0 <= zlength bs <= aout
  /\ (rc = Z_OK \/ rc = Z_STREAM_END -> zs_total_out (iz_z x') = wrap64 (zs_total_out (iz_z x) + zlength bs))
  /\ (rc = Z_OK -> 0 <= consumed <= zlength inp /\ zs_total_in (iz_z x') = wrap64 (zs_total_in (iz_z x) + consumed)).
Proof.
  intros inp x aout ok HI Hb Hl Ha. unfold zic_inflate.
  set (zc := mkZCall inp aout (iz_z x)).
  assert (Hz : ZC zc) by (unfold ZC, zc; cbn [zc_avail_out zc_input]; repeat split; try lia; exact Hb).
  pose proof (inflate_p_pure (wans ok) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
  destruct (inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked] eqn:EIP. cbn [fst] in EP.
  pose proof (inflate_m_post Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz EP) as (P1 & P2).
  pose proof (inflate_m_post2 Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz EP) as (Q1 & _).
  cbn [fst snd iz_s iz_z] in *.
  split; [exact (inflate_INV' (iz_s x) zc Z_NO_FLUSH (wans ok) s' zr HI Hz EP)|].
  split; [exact P1|]. split; [exact P2|].
  intros E. destruct (Q1 E) as (C1 & C2 & _). split; [exact C1| exact C2].
Qed.

(* compress #16582 carry, k3 (cmpcarry-pu): a Z_BUF_ERROR return consumed a count in [0, input length] *)
Lemma ic_inflate_bufC : forall inp (x : istream) aout ok,
  INV (iz_s x) -> bytes_ok inp -> zlength inp < 2 ^ 32 -> 0 <= aout < 2 ^ 32 ->
  let '(x', consumed, bs, rc) := zic_inflate inp x aout ok in
  rc = Z_BUF_ERROR -> 0 <= consumed <= zlength inp.
Proof.
  intros inp x aout ok HI Hb Hl Ha. unfold zic_inflate.
  set (zc := mkZCall inp aout (iz_z x)).
  assert (Hz : ZC zc) by (unfold ZC, zc; cbn [zc_avail_out zc_input]; repeat split; try lia; exact Hb).
  pose proof (inflate_p_pure (wans ok) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
  destruct (inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked] eqn:EIP. cbn [fst] in EP.
  pose proof (inflate_m_bufc Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz EP) as Q.
  cbn [fst snd iz_s iz_z] in *.
  exact Q.
Qed.

Lemma JC_INV : forall x, JC x -> INV (iz_s x).
Proof. intros x HJ. exact (proj1 (JC_facts x HJ)). Qed.

Section U2.
  Local Abbreviation u2L := (ZHarnessC.u2L zinstC).
  Variables (src : list Z) (dlen : Z).

  Definition UT (x : u2L) : Prop :=
    let tin := zs_total_in (iz_z (ZHarnessC.u2_is zinstC x)) in
    let tout := zs_total_out (iz_z (ZHarnessC.u2_is zinstC x)) in
    0 <= tin /\ tin + zlength (ZHarnessC.u2_rest zinstC x) = zlength src
    /\ ZHarnessC.u2_rest zinstC x = zskipn tin src
    /\ tout = zlength (ZHarnessC.u2_orev zinstC x)
    /\ ZHarnessC.u2_aout zinstC x + ZHarnessC.u2_left zinstC x + zlength (ZHarnessC.u2_orev zinstC x) = dlen
    /\ (ZHarnessC.u2_len zinstC x = 0 \/ ZHarnessC.u2_ain zinstC x = 0)
    /\ (ZHarnessC.u2_left zinstC x = 0 \/ ZHarnessC.u2_aout zinstC x = 0).

  Lemma UT_init : UT (ZHarnessC.u2_x0 zinstC dlen src).
  Proof.
    unfold UT, ZHarnessC.u2_x0.
    cbn [ZHarnessC.u2_is ZHarnessC.u2_rest ZHarnessC.u2_ain ZHarnessC.u2_len ZHarnessC.u2_aout ZHarnessC.u2_left ZHarnessC.u2_orev ZApiC.ic_init zinstC]. pz.
    change (zs_total_in (iz_z zi_init)) with 0. change (zs_total_out (iz_z zi_init)) with 0.
    change (zlength (@nil Z)) with 0. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; right; reflexivity.
  Qed.

  Lemma u2_refill_shape : forall x, 0 < dlen <= ZHarnessC.ZBC_MAX -> UI dlen x -> UT x ->
    let tin := zs_total_in (iz_z (ZHarnessC.u2_is zinstC x)) in
    let tout := zs_total_out (iz_z (ZHarnessC.u2_is zinstC x)) in
    let '(ao, lf, ai, ln) := ZHarnessC.u2_refill zinstC x in
    ai = zlength src - tin /\ ln = 0 /\ ao = dlen - tout /\ lf = 0
    /\ Prelim.ztake ai (ZHarnessC.u2_rest zinstC x) = zskipn tin src
    /\ 0 <= tin <= zlength src /\ 0 <= tout <= dlen.
  Proof.
    intros x Hd (HJ & HB & Hain & Hlen & Hsum & Hrl & Haout & Hleft & Hle) (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    unfold ZHarnessC.u2_refill.
    set (is := ZHarnessC.u2_is zinstC x) in *. set (rest := ZHarnessC.u2_rest zinstC x) in *.
    set (ain := ZHarnessC.u2_ain zinstC x) in *. set (len := ZHarnessC.u2_len zinstC x) in *.
    set (aout := ZHarnessC.u2_aout zinstC x) in *. set (left := ZHarnessC.u2_left zinstC x) in *.
    set (orev := ZHarnessC.u2_orev zinstC x) in *.
    unfold ZApiC.ZC_UMAX in *. pz. pose proof (zlength_nonneg' _ orev) as LO. pose proof (zlength_nonneg' _ rest) as LR.
    assert (AI : (if ain =? 0 then (if 4294967295 <? len then 4294967295 else len, len - (if 4294967295 <? len then 4294967295 else len)) else (ain, len))
                 = (zlength src - zs_total_in (iz_z is), 0)).
    { destruct (Z.eqb_spec ain 0) as [E|E].
      - replace (4294967295 <? len) with false by (symmetry; apply Z.ltb_ge; lia). f_equal; lia.
      - destruct T6 as [L0|A0]; [| exfalso; exact (E A0)]. f_equal; lia. }
    assert (AO : (if aout =? 0 then (if 4294967295 <? left then 4294967295 else left, left - (if 4294967295 <? left then 4294967295 else left)) else (aout, left))
                 = (dlen - zs_total_out (iz_z is), 0)).
    { destruct (Z.eqb_spec aout 0) as [E|E].
      - assert (HL : left <= 4294967295) by (unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX in *; lia).
        replace (4294967295 <? left) with false by (symmetry; apply Z.ltb_ge; lia). f_equal; lia.
      - destruct T7 as [L0|A0]; [| exfalso; exact (E A0)]. f_equal; lia. }
    rewrite AI, AO. cbv zeta.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [| lia]. rewrite T3. rewrite zfirstn_all_of_len; [reflexivity|]. rewrite <- T3. lia.
  Qed.

  Lemma u2_step_UT : forall x ok x', 0 < dlen <= ZHarnessC.ZBC_MAX -> zlength src <= ZHarnessC.ZBC_MAX -> UI dlen x -> UT x ->
    ZHarnessC.u2_stepP zinstC ok x = inl x' -> UT x'.
  Proof.
    intros x ok x' Hd Hs HX HT.
    pose proof (u2_refill_shape x Hd HX HT) as RS.
    destruct HX as (HJ & HB & Hain & Hlen & Hsum & Hrl & Haout & Hleft & Hle). destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    unfold ZHarnessC.u2_stepP. cbn [ZApiC.ic_inflate zinstC].
    destruct (ZHarnessC.u2_refill zinstC x) as [[[ao lf] ai] ln]. cbv zeta in RS. destruct RS as (Eai & Eln & Eao & Elf & Einp & Htin & Htout).
    set (is := ZHarnessC.u2_is zinstC x) in *. set (rest := ZHarnessC.u2_rest zinstC x) in *.
    set (orev := ZHarnessC.u2_orev zinstC x) in *.
    rewrite Einp. pz.
    set (inp := zskipn (zs_total_in (iz_z is)) src) in *.
    assert (Linp : zlength inp = ai) by (subst inp; rewrite zlength_zskipn' by lia; lia).
    pose proof (JC_facts is HJ) as (HI & _ & _).
    assert (HBi : bytes_ok inp) by (rewrite <- T3; exact HB).
    unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX, ZApiC.ZC_UMAX in *.
    pose proof (ic_inflate_factsC inp is ao ok HI HBi ltac:(lia) ltac:(lia)) as CF.
    destruct (zic_inflate inp is ao ok) as [[[is' consumed] bs] rc]. destruct CF as (HI' & Hbs & HTO & HOK).
    unfold ZHarnessC.u_step_ok. pz.
    destruct (Z.eqb_spec rc ZApi.Z_OK) as [E0|E0].
    - destruct (HOK E0) as (C1 & C2). specialize (HTO (or_introl E0)).
      replace (zlength bs <=? ao) with true by (symmetry; apply Z.leb_le; lia).
      replace (0 <=? consumed) with true by (symmetry; apply Z.leb_le; lia).
      replace (consumed <=? ai) with true by (symmetry; apply Z.leb_le; lia). cbn [andb orb negb].
      intros H. injection H as <-.
      unfold UT. cbn [ZHarnessC.u2_is ZHarnessC.u2_rest ZHarnessC.u2_ain ZHarnessC.u2_len ZHarnessC.u2_aout ZHarnessC.u2_left ZHarnessC.u2_orev]. pz.
      cbn [iz_z]. rewrite C2, HTO.
      pose proof (zlength_nonneg' _ orev) as LO. pose proof (zlength_nonneg' _ rest) as LR.
      rewrite (wrap64_id (zs_total_in (iz_z is) + consumed)) by lia.
      rewrite (wrap64_id (zs_total_out (iz_z is) + zlength bs)) by lia.
      subst inp. rewrite T3. rewrite zskipn_zskipn by lia.
      rewrite zlength_rev_append. rewrite (zlength_zskipn' src (zs_total_in (iz_z is) + consumed)) by lia.
      split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; left; assumption.
    - cbn [andb orb negb]. destruct (zlength bs <=? ao); cbn [andb]; intros H; discriminate H.
  Qed.

  Lemma u2_iter_UT : forall k y x, 0 < dlen <= ZHarnessC.ZBC_MAX -> zlength src <= ZHarnessC.ZBC_MAX -> UI dlen y -> UT y ->
    ZHarnessL.iterNL k (ZHarnessC.u2_stepP zinstC true) y = inl x -> UI dlen x /\ UT x.
  Proof.
    intros k. induction k as [|k IH]; intros y x Hd Hs UY TY Hk.
    - cbn [ZHarnessL.iterNL] in Hk. injection Hk as <-. split; assumption.
    - cbn [ZHarnessL.iterNL] in Hk. pose proof (u2_step dlen y true Hd UY) as ST.
      destruct (ZHarnessC.u2_stepP zinstC true y) as [y'|r] eqn:ES; [| destruct r; discriminate Hk].
      exact (IH y' x Hd Hs (proj1 ST) (u2_step_UT y true y' Hd Hs UY TY ES) Hk).
  Qed.

  Lemma u2_reach_UT : forall x, 0 < dlen <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    ZHarnessC.u2_reach zinstC dlen src x -> UI dlen x /\ UT x.
  Proof.
    intros x Hd Hs Hb [k Hk].
    pz. exact (u2_iter_UT k _ x Hd Hs (proj1 (UI_init dlen src Hd Hs Hb)) UT_init Hk).
  Qed.
End U2.

Section C2.
  Local Abbreviation c2L := (ZHarnessC.c2L zinstC).
  Variables (src : list Z) (N : Z).

  Definition CT (x : c2L) : Prop :=
    ZHarnessC.c2_rest zinstC x = zskipn (zlength src - zlength (ZHarnessC.c2_rest zinstC x)) src
    /\ zlength (ZHarnessC.c2_rest zinstC x) <= zlength src
    /\ (ZHarnessC.c2_slen zinstC x = 0 \/ ZHarnessC.c2_ain zinstC x = 0)
    /\ (ZHarnessC.c2_left zinstC x = 0 \/ ZHarnessC.c2_aout zinstC x = 0).

  Lemma CT_init : forall level, CT (ZHarnessC.c2_x0 zinstC N src level).
  Proof.
    intros level. unfold CT, ZHarnessC.c2_x0.
    cbn [ZHarnessC.c2_rest ZHarnessC.c2_ain ZHarnessC.c2_slen ZHarnessC.c2_aout ZHarnessC.c2_left]. pz.
    rewrite Z.sub_diag. split; [reflexivity|]. split; [lia|]. split; [right; reflexivity| right; reflexivity].
  Qed.

  Lemma c2_refill_shape : forall x, 0 <= N <= ZHarnessC.ZBC_MAX -> CI N x -> CT x ->
    let rest := ZHarnessC.c2_rest zinstC x in
    let tout := zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x)) in
    let '(ao, lf, ai, sl) := ZHarnessC.c2_refill zinstC x in
    ai = zlength rest /\ sl = 0 /\ ao = N - tout /\ lf = 0
    /\ Prelim.ztake ai rest = rest /\ ZHarnessC.c2_flush sl = Z_FINISH
    /\ rest = zskipn (zlength src - zlength rest) src /\ 0 <= zlength src - zlength rest <= zlength src
    /\ 0 <= tout <= N /\ zlength rest <= ZApiC.ZC_UMAX.
  Proof.
    intros x HN (HDC & ZOK & HB & Hain & Hslen & Hsum & Hrl & Haout & Hleft & Htot & Hto & Hto0) (T1 & T2 & T3 & T4).
    unfold ZHarnessC.c2_refill.
    set (rest := ZHarnessC.c2_rest zinstC x) in *.
    set (ain := ZHarnessC.c2_ain zinstC x) in *. set (slen := ZHarnessC.c2_slen zinstC x) in *.
    set (aout := ZHarnessC.c2_aout zinstC x) in *. set (left := ZHarnessC.c2_left zinstC x) in *.
    set (tout := zs_total_out (dz_z (ZHarnessC.c2_ds zinstC x))) in *.
    unfold ZApiC.ZC_UMAX in *. pz. pose proof (zlength_nonneg' _ rest) as LR.
    assert (AI : (if ain =? 0 then (if 4294967295 <? slen then 4294967295 else slen, slen - (if 4294967295 <? slen then 4294967295 else slen)) else (ain, slen))
                 = (zlength rest, 0)).
    { destruct (Z.eqb_spec ain 0) as [E|E].
      - replace (4294967295 <? slen) with false by (symmetry; apply Z.ltb_ge; lia). f_equal; lia.
      - destruct T3 as [L0|A0]; [| exfalso; exact (E A0)]. f_equal; lia. }
    assert (AO : (if aout =? 0 then (if 4294967295 <? left then 4294967295 else left, left - (if 4294967295 <? left then 4294967295 else left)) else (aout, left))
                 = (N - tout, 0)).
    { destruct (Z.eqb_spec aout 0) as [E|E].
      - assert (HL : left <= 4294967295) by (unfold ZHarnessC.ZBC_MAX, ZApiC.ZC_MAX in *; lia).
        replace (4294967295 <? left) with false by (symmetry; apply Z.ltb_ge; lia). f_equal; lia.
      - destruct T4 as [L0|A0]; [| exfalso; exact (E A0)]. f_equal; lia. }
    rewrite AI, AO. cbv zeta.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply zfirstn_all_of_len; lia|]. split; [reflexivity|]. split; [exact T1|]. split; [lia|]. split; [lia|]. unfold ZApiC.ZC_UMAX. lia.
  Qed.

  Lemma c2_step_CT : forall x x', 0 <= N <= ZHarnessC.ZBC_MAX -> CI N x -> CT x ->
    ZHarnessC.c2_stepP zinstC x = inl x' -> CT x'.
  Proof.
    intros x x' HN HX HT.
    pose proof (c2_refill_shape x HN HX HT) as RS.
    destruct HT as (T1 & T2 & T3 & T4).
    unfold ZHarnessC.c2_stepP.
    destruct (ZHarnessC.c2_refill zinstC x) as [[[ao lf] ai] sl]. cbv zeta in RS.
    destruct RS as (Eai & Esl & Eao & Elf & Einp & _ & Erest & Hoff & _ & _).
    set (rest := ZHarnessC.c2_rest zinstC x) in *.
    rewrite Einp.
    destruct (ZApiC.dc_deflate zinstC rest (ZHarnessC.c2_ds zinstC x) ao (ZHarnessC.c2_flush sl)) as [[[ds' consumed] bs] rc].
    destruct (ZHarnessC.c_step_ok zinstC ai ao (ZHarnessC.c2_ds zinstC x) ds' consumed bs) eqn:OK; [| intros H; discriminate H].
    destruct (rc =? ZApi.Z_OK); [| intros H; discriminate H].
    intros H. injection H as <-.
    unfold ZHarnessC.c_step_ok in OK. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [O1 O2].
    apply Z.leb_le in O1. apply Z.leb_le in O2.
    unfold CT. cbn [ZHarnessC.c2_rest ZHarnessC.c2_ain ZHarnessC.c2_slen ZHarnessC.c2_aout ZHarnessC.c2_left]. pz.
    pose proof (zlength_nonneg' _ rest) as LR.
    rewrite (zlength_zskipn' rest consumed) by lia.
    split.
    - rewrite Erest at 1. rewrite zskipn_zskipn by lia. f_equal. lia.
    - split; [lia|]. split; left; assumption.
  Qed.

  Lemma c2_iter_CT : forall k y x, 0 <= N <= ZHarnessC.ZBC_MAX -> CI N y -> CT y ->
    ZHarnessL.iterNL k (ZHarnessC.c2_stepP zinstC) y = inl x -> CI N x /\ CT x.
  Proof.
    intros k. induction k as [|k IH]; intros y x HN UY TY Hk.
    - cbn [ZHarnessL.iterNL] in Hk. injection Hk as <-. split; assumption.
    - cbn [ZHarnessL.iterNL] in Hk. pose proof (c2_step N y HN UY) as ST.
      destruct (ZHarnessC.c2_stepP zinstC y) as [y'|r] eqn:ES; [| destruct r as [[? ?]|]; [discriminate Hk| destruct ST]].
      exact (IH y' x HN (proj1 ST) (c2_step_CT y y' HN UY TY ES) Hk).
  Qed.

  Lemma c2_reach_CT : forall level x, 0 <= N <= ZHarnessC.ZBC_MAX -> Prelim.zlength src <= ZHarnessC.ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
    0 <= level <= 9 -> ZHarnessC.c2_reach zinstC N src level x -> CI N x /\ CT x.
  Proof.
    intros level x HN Hs Hb Hl [k Hk].
    pz. exact (c2_iter_CT k _ x HN (proj1 (CI_init N src level HN Hs Hb Hl)) (CT_init level) Hk).
  Qed.
End C2.
