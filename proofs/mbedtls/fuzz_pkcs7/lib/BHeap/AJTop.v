(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ AVm AVst AVstT AHeapR.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AJTop () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.lkind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_kind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KNoacc"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
  Variable AL : asan_layout.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_nonlit_unit : forall h t, bwf h -> In t (tr_of h) -> t_lit t = false -> units_of_L (h_L h) (t_lo t) (t_len t).
  Proof.
    intros h t B Ht TL. pose proof (bwf_L h B) as WL. pose proof (bwf_breg h B) as BR. pose proof (bwf_pa h B) as [[P0 P1] PAL].
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c & j & Hc & Hj & ->)|[(c & j & Hc & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]];
      try discriminate TL.
    - (* [comment removed for export] *)
      dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
      unfold uunit_tr. cbn [t_lo t_len]. replace (region_beg (h_L h) c + j * kUserMapSize) with (region_beg (h_L h) c + (j * kUserMapSize)) by lia.
      apply (uunit_unit (h_L h) c (j * kUserMapSize) WL Hc); unfold kUserMapSize, kUserLimit, kRegionSize in *.
      + lia.
      + apply Z_mod_mult.
      + assert (j + 1 <= r_mapped_user (h_reg h c) / 2^18) by lia.
        pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)). rewrite MUAL in *. nia.
    - (* [comment removed for export] *)
      dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
      unfold funit_tr. cbn [t_lo t_len]. replace (fa_beg (h_L h) c + j * kUserMapSize) with (fa_beg (h_L h) c + (j * kUserMapSize)) by lia.
      apply (funit_unit (h_L h) c (j * kUserMapSize) WL Hc); unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize in *.
      + lia.
      + apply Z_mod_mult.
      + assert (j + 1 <= r_mapped_fa (h_reg h c) / 2^18) by lia.
        pose proof (Z.div_mod (r_mapped_fa (h_reg h c)) (2^18) ltac:(lia)). rewrite MFAL in *. nia.
    - (* [comment removed for export] *) unfold ri_tr. cbn [t_lo t_len]. apply ri_unit.
    - (* [comment removed for export] *)
      unfold pa_tr. cbn [t_lo t_len]. apply pa_unit. unfold kPaHullLen, kPaSlice in *. change (8388608 / 131072) with 64.
      split; [lia|]. assert (j + 1 <= h_pa_committed h / 131072) by lia.
      pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)). rewrite PAL in *. nia.
    - exfalso. rewrite (fixed_emb_lit h t HF) in TL. discriminate TL.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_of_knoacc : ltac2:(CDefT.buildp (gd_tbl_AJTop ()) "Ph,$0.Pt,$1.P,(2.$1.R1.(3.R2.))P,(4.$5.(6.R2.)$7.)(8.(9.(4.$:.(;.R3.)+8???7000.)(4.$:.(<.R3.)+20000000000.))(=.(<.R3.)(>.+2.+11.)))")
(* [comment removed for export] *).
  Proof.
    intros h t Ht TK.
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c & j & Hc & Hj & ->)|[(c & j & Hc & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]];
      try discriminate TK.
    apply in_app_iff in HF. destruct HF as [HF|HF].
    - unfold fixed_of in HF. rewrite !in_app_iff in HF. destruct HF as [HF|[HF|HF]].
      + destruct HF as [<-|[<-|[<-|[<-|[]]]]]; discriminate TK.
      + apply in_map_iff in HF. ddestruct HF as (r & <- & Hr). cbn [t_kind t_lo t_len] in *. right.
        unfold xkind in TK. destruct (Z.ltb_spec (snd r) (2^17)) as [LT|GE]; [exact LT| discriminate TK].
      + destruct HF as [<-|[<-|[<-|[]]]]; try discriminate TK. left. split; reflexivity.
    - unfold emb_tr in HF. destruct (a_emb (h_acct h) =? 0); [destruct HF| destruct HF as [<-|[]]; discriminate TK].
  Qed.

  #[using="Type"] Lemma ri_tr_in : forall h, In (ri_tr (h_L h)) (tr_of h).
  Proof. intros h. unfold tr_of. rewrite !in_app_iff. do 4 right. left. left. reflexivity. Qed.
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Top.
  Variable AL : asan_layout.   (* [comment removed for export] *)

  Ltac geo := unfold kPrimHullLen, kPaHullLen, kPaSlice, kUserMapSize, kHighMemBeg, lowhigh, ri_base, space_end, kSpaceSize in *.

  (* [comment removed for export] *)
  #[using="Type"] Theorem hm_J : forall h m mo, HK AL h mo -> bwf h -> hm_absent h m -> J m mo.
  Proof.
    intros h m mo [K VR] B HA. pose proof (bwf_L h B) as WL. dpose (wfL_geo (h_L h) WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & UC & (UNC & MPOS & LZK & MX & MH) & MND & MSEP & NZN & NZL & BANDM) & CE & RS & RC & VW & AT).
    dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
    dpose WF as (W1 & W2 & W3 & W4). aceilb.
    split; [exact W1|]. split; [exact W2|]. split; [exact MSEP|].
    split; [intros e He; split; [exact (NZN e He)| exact (TN e He)]|].
    (intros x JX NB dd_H; ddestruct dd_H as (a & e & He & E1 & E2 & XA & NC)).
    ddestruct (NC (bv_unsigned x) XA) as (en & Hen & Rn).
    (* [comment removed for export] *)
    assert (CLX : forall t, In t (tr_of h) -> t_kind t <> KNoacc -> ~ (t_lo t <= bv_unsigned x < t_hi t)).
    { intros t Ht TK Xt. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
      assert (CLN : clear (vm_noaccess (m_vmmaps mo)) (t_lo t) (t_hi t)) by (destruct (t_kind t); [exact (proj1 F3)| exact F3| exfalso; exact (TK eq_refl)]).
      specialize (CLN en Hen). lia. }
    destruct (MX e He (bv_unsigned x) ltac:(lia)) as [(t & Ht & TLt & Rt)|(U & n & HU & RU)].
    - (* [comment removed for export] *)
      pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3). pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _).
      specialize (F2 TLt). unfold haslit in F2. unfold t_hi in *.
      assert (UL : bv_unsigned (Z_to_bv 64 (t_lo t)) = t_lo t) by (apply u64_lit; lia).
      assert (UN' : bv_unsigned (Z_to_bv 64 (t_len t)) = t_len t) by (apply u64_lit; lia).
      destruct (MSEP e _ He F2) as [->|AP]; [| cbn [fst snd] in AP; rewrite UL, UN' in AP; exfalso; lia].
      cbn [fst snd] in E1, E2. rewrite UL in E1. rewrite UL, UN' in E2.
      destruct (t_kind t) eqn:TK.
      + exfalso. exact (CLX t Ht ltac:(rewrite TK; discriminate) Rt).
      + exfalso. exact (CLX t Ht ltac:(rewrite TK; discriminate) Rt).
      + destruct (tr_of_knoacc h t Ht TK) as [[L1 L2]|SM].
        * (* [comment removed for export] *) exfalso. apply NB. unfold jband. rewrite L1, L2 in Rt. lia.
        * (* [comment removed for export] *) exfalso. unfold JW in *. lia.
    - (* [comment removed for export] *)
      cbn [vst_of v_unit] in HU. pose proof (units_of_L_inside (h_L h) U n WL HU) as INS.
      assert (NT : forall t, In t (tr_of h) -> ~ (t_lo t <= bv_unsigned x < t_hi t)).
      { intros t Ht Xt.
        assert (HX : exists H, In H (hulls_of (h_L h)) /\ fst H <= bv_unsigned x < fst H + snd H).
        { destruct INS as [[I1 I2]|[I1 I2]]; [exists (l_b6 (h_L h), kPrimHullLen); split; [left; reflexivity| cbn; lia]| exists (l_pa (h_L h), kPaHullLen); split; [right; left; reflexivity| cbn; lia]]. }
        ddestruct HX as (H & HH & XH).
        destruct (THA t H Ht HH) as [(A1 & A2 & A3 & A4)|X]; [| unfold t_hi in *; lia].
        exact (CLX t Ht ltac:(rewrite A4; discriminate) Xt). }
      destruct HU as [(j & Hj & EU & En)|[(EU & En)|[(EU & En)|[(EU & En & N0)|(j & Hj & EU & En)]]]]; subst U n; geo.
      + (* [comment removed for export] *)
        apply HA. split; [| exact NT]. left. unfold kNumUnits, unit_lo, kSpaceSize, kUserMapSize in *. geo. change (2^37 / 2^18) with (2^19) in Hj.
        assert (j * 2^18 <= (2^19 - 1) * 2^18) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
      + (* [comment removed for export] *)
        exfalso. apply (NT (ri_tr (h_L h)) (ri_tr_in h)). unfold ri_tr, t_hi. cbn [t_lo t_len]. geo. lia.
      + (* [comment removed for export] *)
        apply HA. split; [| exact NT]. left. geo. lia.
      + (* [comment removed for export] *)
        exfalso. destruct (MH e (l_b6 (h_L h), kPrimHullLen) He ltac:(left; reflexivity) ltac:(cbn [fst snd]; geo; lia) ltac:(cbn [fst snd]; geo; lia)) as [M1 M2].
        cbn [fst snd] in M1, M2. unfold JW, kPrimHullLen in *.
        ddestruct (NC (l_sb (h_L h) + 2^37) ltac:(lia)) as (er & Her & Rr).
        pose proof (proj1 (Forall_forall _ _) TB (ri_tr (h_L h)) (ri_tr_in h)) as (_ & _ & [CLr _]).
        specialize (CLr er Her). unfold ri_tr, t_hi in CLr. cbn [t_lo t_len] in CLr. geo. lia.
      + (* [comment removed for export] *)
        apply HA. split; [| exact NT]. right. geo. change (8388608 / 131072) with 64 in Hj.
        assert (j * 131072 <= 63 * 131072) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem J_hm_absent : forall h m mo, HK AL h mo -> bwf h -> J m mo -> hm_absent h m.
  Proof.
    intros h m mo [K VR] B HJ x [HZ NT]. pose proof (bwf_L h B) as WL. dpose (wfL_geo (h_L h) WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & UC & (UNC & MPOS & LZK & MX & MH) & MND & MSEP & NZN & NZL & BANDM) & CE & RS & RC & VW & AT).
    dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
    ddestruct HJ as (_ & _ & _ & _ & J5). aceilb. geo.
    (* [comment removed for export] *)
    assert (UX : exists U n, units_of_L (h_L h) U n /\ U <= bv_unsigned x < U + n /\ JW <= n).
    { unfold JW. destruct HZ as [HZ|HZ].
      - destruct (Z.lt_ge_cases (bv_unsigned x) (l_sb (h_L h) + 2^18)) as [C|C].
        + dexists (l_b6 (h_L h)), (l_sb (h_L h) + 2^18 - l_b6 (h_L h)). split; [right; right; left; unfold kUserMapSize; split; reflexivity| lia].
        + set (j := (bv_unsigned x - l_sb (h_L h)) / 2^18).
          pose proof (Z.div_mod (bv_unsigned x - l_sb (h_L h)) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (bv_unsigned x - l_sb (h_L h)) (2^18) ltac:(lia)) as MB.
          dexists (l_sb (h_L h) + j * 2^18), (2^18). split; [left; exists j; unfold kNumUnits, kSpaceSize, unit_lo, kUserMapSize; split; [| split; reflexivity]| lia].
          change (2^37 / 2^18) with (2^19). split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
      - set (j := (bv_unsigned x - l_pa (h_L h)) / 131072).
        pose proof (Z.div_mod (bv_unsigned x - l_pa (h_L h)) 131072 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (bv_unsigned x - l_pa (h_L h)) 131072 ltac:(lia)) as MB.
        dexists (l_pa (h_L h) + j * 131072), 131072. split; [do 4 right; exists j; unfold kPaHullLen, kPaSlice; split; [| split; reflexivity]| lia].
        change (8388608 / 131072) with 64. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    ddestruct UX as (U & n & HU & XU & NW).
    pose proof (units_of_L_inside (h_L h) U n WL HU) as INS. dpose (units_of_L_wf (h_L h) U n WL HU) as (N0 & U0 & UCE & _).
    (* [comment removed for export] *)
    assert (APT : forall t, In t (tr_of h) -> U + n <= t_lo t \/ t_hi t <= U).
    { intros t Ht. destruct (t_lit t) eqn:TLt; [exact (UT t U n Ht TLt HU)|].
      pose proof (tr_nonlit_unit h t B Ht TLt) as TU.
      assert (HAPL : l_b6 (h_L h) + kPrimHullLen <= l_pa (h_L h) \/ l_pa (h_L h) + kPaHullLen <= l_b6 (h_L h)) by exact (hulls_apart AL h mo (conj K VR)).
      destruct (units_of_L_sep (h_L h) WL HAPL U n (t_lo t) (t_len t) HU TU) as [[E1 E2]|X]; [| unfold t_hi; lia].
      exfalso. apply (NT t Ht). unfold t_hi. lia. }
    apply (J5 x).
    - unfold JF. geo. destruct INS; lia.
    - unfold jband. geo. destruct INS; lia.
    - apply (jwin_of_unit _ _ U n); [exact NW| exact (UC U n HU)| | exact XU].
      intros y Hy. exact (UNC U n HU APT y Hy).
  Qed.
End Top.

End ARUN_1.
