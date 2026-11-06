(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA SymStepR PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap CutHeapA CutL5A CutBridgeA CutRtCpsA CutCertA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import IslInterpA IslSoundA IslResumeA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ISLC.
Import ISLA.
Definition mem := (word -> option byte).

Lemma zmemcmp_val : forall b1 b2, zmemcmp b1 b2 = memcmp_val b1 b2.
Proof. intros b1 b2. reflexivity. Qed.

Section Chain.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable FPI : FPState -> Prop.

Variable CF : cfg.
Variable E : nat -> word.
Hypothesis IO : ISLSA.init_ok CF E.
Variable fuel : nat.

Variable LB : list (Z * Z).
Variable FF : list fframe.
Variable LK0 : list fframe.
Variable cr : credit.
Variable A0 : list (Z * Z).
Variable M0 : mem.
Variable model0 : Model.
Variable sp0 : Z.
Variable SCR : Z.
Variable W : list L5.range.
Variable K : TSet.
Variable ra0 : Z.
Variable tpv : Z.
Variable scr_ms scr_mc : Z.

Hypothesis STK : CHA.astk ar M0 sp0 SCR.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis SCR8 : SCR mod 8 = 0.
Hypothesis FFRS0 : CHA.ffrs FF sp0.
Hypothesis KNIL : K [].
Hypothesis SPV : bv_unsigned (E (c_spk CF)) = sp0.
Hypothesis RAV : E 1%nat = Z_to_bv 64 ra0.
Hypothesis RAok : L5.ra_ok ra0.
Hypothesis TPV : tpv = hl_tp L.
Hypothesis SCRMS : 0 <= hl_scr_mem L <= scr_ms.
Hypothesis SCRMC : 0 <= scr_mc.

Definition WOK (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp0 SCR a /\ (exists w, In w W /\ L5.in_rng w a) /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Definition CLR (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp0 SCR a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WABS : forall a, in_ivs (c_wabs CF) a = true -> WOK a.
Hypothesis RTC : forall a, 0 < a < c_abs_hi CF -> rdb0 (hl_segs L) CF a <> None -> CLR a.
Hypothesis RGS : forall j rg, nth_error (c_rgs CF) j = Some rg ->
  (rg_k rg = c_spk CF /\ - SCR <= rg_lo rg /\ rg_hi rg <= 0) \/ (rg_k rg <> c_spk CF /\ forall off, rg_lo rg <= off < rg_hi rg -> WOK (ISLSA.rbase E rg + off)).
Hypothesis W_app : forall w a, In w W -> L5.in_rng w a -> a + 1 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a.
Hypothesis STKSH0 : shadow_zero M0 (sp0 - SCR) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp0 - SCR)) / 8).
Hypothesis MS_acc : forall LK A (M : mem) model lo hi, ri_inv HI LB FF LK cr A M (vml_of model) -> In (lo, hi) (c_msok CF) -> aacc M lo (hi - lo).
Hypothesis ABSHI : c_abs_hi CF <= hl_img_hi L.
Hypothesis RO_acc : forall LK A (M : mem) model lo hi, ri_inv HI LB FF LK cr A M (vml_of model) -> In (lo, hi) (c_rook CF) -> aacc M lo (hi - lo).
Hypothesis RO_rng : forall lo hi, In (lo, hi) (c_rook CF) -> hl_img_lo L <= lo /\ hi <= hl_img_hi L.
Hypothesis RO_clr : forall lo hi a, In (lo, hi) (c_rook CF) -> lo <= a < hi -> CLR a.
Hypothesis MEMSET : forall pc, In (pc, KMemset) (c_calls CF) -> CRC.amemset_spec_at L ar HI pc.
Hypothesis MEMCMP : forall pc, In (pc, KMemcmp) (c_calls CF) -> CRC.amemcmp_spec_at L ar HI pc scr_mc.

Definition ra_chk (ret : Z) : bool := ((0 <=? ret) && (ret <? 2 ^ 47) && (ret mod 2 =? 0))%bool.
Definition ev_chk (ev : event) : bool :=
  match ev with
  | EvMemset dst c n spoff ret tp => ((0 <? n) && (n <=? 2 ^ 27) && (spoff mod 16 =? 0) && (spoff <=? 0) && (- SCR <=? spoff - scr_ms) && ra_chk ret && (tp =? tpv))%bool
  | EvMemcmp poff q n zs1 zs2 spoff ret tp => ((0 <? n) && (n <=? 2 ^ 27) && (spoff mod 16 =? 0) && (spoff <=? 0) && (- SCR <=? spoff - scr_mc) && ra_chk ret && (tp =? tpv))%bool
  end.

Abbreviation segs := (hl_segs L).
Abbreviation vis := CCA.vis.

Definition KEPT (M : mem) : Prop := forall a, CHA.akept L ar LB FF sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Definition GROWS (M : mem) : Prop := forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None.
Definition CTX (fx : FPState) (M : mem) (model : Model) (A : list (Z * Z)) (LK : list fframe) : Prop :=
  CHA.amodel_ok A model /\ model_rt model0 model /\ incl A0 A /\ incl LK LK0 /\
  ri_inv HI LB FF LK cr A M (vml_of model) /\ CHA.ffroom FF LK 0 /\ FPI fx /\ KEPT M /\ GROWS M.
Definition INV (s : ast) (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (A : list (Z * Z)) (LK : list fframe) : Prop :=
  CTX fx M model A LK /\ ISLSA.sim segs CF E (vis A model M) s R (vis A model M) None.

Lemma ctx_rf : forall fx M model A LK, CTX fx M model A LK -> CHA.rng_facts L ar LB FF.
Proof. intros fx M model A LK (_ & _ & _ & _ & HH & _). exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)). Qed.

Lemma clr_vis : forall fx M model A LK a, CTX fx M model A LK -> CLR a -> ahid A model (Z_to_bv 64 a) = false.
Proof. intros fx M model A LK a (_ & _ & _ & _ & HH & _) (H1 & H2 & H3). exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp0 SCR a HH H1 H2 H3). Qed.
Lemma wok_clr : forall a, WOK a -> CLR a.
Proof. intros a (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ H2) | exact H4]. Qed.

Lemma stk_client0 : forall fx M model A LK a, CTX fx M model A LK -> sp0 - SCR <= a < sp0 -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp0 0 a /\
  (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros fx M model A LK a HC Ha. pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct STK as (S1 & S2 & S3 & S4 & _).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _).
  split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
Qed.
Lemma stk_vis : forall fx M model A LK a, CTX fx M model A LK -> sp0 - SCR <= a < sp0 -> ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros fx M model A LK a HC Ha. destruct (stk_client0 _ _ _ _ _ a HC Ha) as (H1 & H2 & H3). destruct HC as (_ & _ & _ & _ & HH & _).
  exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp0 0 a HH H1 H2 H3).
Qed.

Lemma rg_cases : forall j rg off, nth_error (c_rgs CF) j = Some rg -> rg_lo rg <= off < rg_hi rg ->
  (rg_k rg = c_spk CF /\ ISLSA.rbase E rg = sp0 /\ sp0 - SCR <= sp0 + off < sp0) \/ (rg_k rg <> c_spk CF /\ WOK (ISLSA.rbase E rg + off)).
Proof.
  intros j rg off Hj Ho. destruct (RGS j rg Hj) as [(Hk & Hlo & Hhi)|(Hk & HW)].
  - left. split; [exact Hk|]. split; [unfold ISLSA.rbase; rewrite Hk; exact SPV | lia].
  - right. split; [exact Hk | exact (HW off Ho)].
Qed.

Abbreviation rom := (seg_rom (hl_segs L)).

Lemma written_not_private : forall fx M model A LK (x : word), CTX fx M model A LK ->
  art_private L ar LB FF (bv_unsigned x) ->
  (forall lo hi, In (lo, hi) (c_wabs CF) -> ~ lo <= bv_unsigned x < hi) /\
  (forall j rg, nth_error (c_rgs CF) j = Some rg -> ~ ISLSA.rbase E rg + rg_lo rg <= bv_unsigned x < ISLSA.rbase E rg + rg_hi rg).
Proof.
  intros fx M model A LK x HC HP. pose proof HC as (_ & _ & _ & _ & HH & _). pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF.
  pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct STK as (S1 & S2 & S3 & S4 & _).
  assert (NW : forall a, aclientw L ar LB FF sp0 SCR a \/ (sp0 - SCR <= a < sp0) -> a = bv_unsigned x -> False).
  { intros a Ha ->. apply (CHA.aclientw_not_private L ar LY_img LY_ro LB FF LK cr A M 0 0 (bv_unsigned x) WF); [|exact HP].
    destruct Ha as [Ha|Ha]; [|right; left; split; lia]. eapply CHA.aclient_scr; [exact Ha | intros y Hy; lia]. }
  split.
  - intros lo hi Hin Hr. apply (NW (bv_unsigned x)); [|reflexivity]. left.
    assert (IV : in_ivs (c_wabs CF) (bv_unsigned x) = true).
    { clear - Hin Hr. induction (c_wabs CF) as [|[lo' hi'] t IH]; [destruct Hin|]. cbn [in_ivs]. apply orb_true_iff.
      destruct Hin as [Hin|Hin]; [injection Hin as -> ->; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia | right; exact (IH Hin)]. }
    exact (proj1 (proj2 (WABS _ IV))).
  - intros j rg Hj Hr. destruct (rg_cases j rg (bv_unsigned x - ISLSA.rbase E rg) Hj ltac:(lia)) as [(Hk & Hb & Hs)|(Hk & HW)].
    + apply (NW (bv_unsigned x)); [|reflexivity]. right. rewrite Hb in Hs. lia.
    + apply (NW (bv_unsigned x)); [|reflexivity]. left. replace (bv_unsigned x) with (ISLSA.rbase E rg + (bv_unsigned x - ISLSA.rbase E rg)) by lia. exact (proj1 (proj2 HW)).
Qed.

Lemma kept_not_written : forall fx M model A LK (x : word), CTX fx M model A LK ->
  CHA.akept L ar LB FF sp0 SCR W (bv_unsigned x) ->
  (forall lo hi, In (lo, hi) (c_wabs CF) -> ~ lo <= bv_unsigned x < hi) /\
  (forall j rg, nth_error (c_rgs CF) j = Some rg -> ~ ISLSA.rbase E rg + rg_lo rg <= bv_unsigned x < ISLSA.rbase E rg + rg_hi rg).
Proof.
  intros fx M model A LK x HC (Hx & HCl & HO). pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct STK as (S1 & S2 & S3 & S4 & _).
  assert (NW : forall a, WOK a -> a = bv_unsigned x -> False).
  { intros a (_ & _ & (w & Hw & Hin) & _) ->. exact (HO w Hw Hin). }
  split.
  - intros lo hi Hin Hr. apply (NW (bv_unsigned x)); [|reflexivity].
    assert (IV : in_ivs (c_wabs CF) (bv_unsigned x) = true).
    { clear - Hin Hr. induction (c_wabs CF) as [|[lo' hi'] t IH]; [destruct Hin|]. cbn [in_ivs]. apply orb_true_iff.
      destruct Hin as [Hin|Hin]; [injection Hin as -> ->; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia | right; exact (IH Hin)]. }
    exact (WABS _ IV).
  - intros j rg Hj Hr. destruct (rg_cases j rg (bv_unsigned x - ISLSA.rbase E rg) Hj ltac:(lia)) as [(Hk & Hb & Hs)|(Hk & HW)].
    + rewrite Hb in Hs. exact (CHA.client_high L ar LY_img 32%nat sp0 (CutHeap.CH.HD SCR 0 [] [] []) (conj S1 (conj S2 S3)) SCR_pos (le_n _) LB FF sp0 SCR _ RFx HCl ltac:(lia) ltac:(lia)).
    + apply (NW _ HW). lia.
Qed.

Lemma stretch_core : forall s fx R M model A LK R1 (MV1 : mem) s1 (pc1 : word),
  INV s fx R M model A LK ->
  msteps segs (@mkst fx R (pcw s) (vis A model M) rom) (@mkst fx R1 pc1 MV1 rom) ->
  ISLSA.sim segs CF E (vis A model M) s1 R1 MV1 None ->
  (forall M1 model1, CTX fx M1 model1 A LK -> vis A model1 M1 = MV1 -> srealizes segs SCFG (mkCfg (@mkst fx R1 pc1 M1 rom) model1) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (pcw s) M rom) model) K.
Proof.
  intros s fx R M model A LK R1 MV1 s1 pc1 [HC Hsim] MS Hsim1 CONT.
  pose proof HC as ((Hh & HMI) & Hrt & HA0 & HLK & HH & Hroom & HFP & HKP & HGR).
  pose proof (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ _ HH) as Hoff.
  destruct (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (HAwf & _).
  unfold CCA.vis in MS.
  eapply (L5LZ.cps_of_msteps_lazy segs (ahid A model) A fx fx R _ M R1 _ MV1 model K Hoff LY_nowrap (L5LZ.lazy_cover_ahid A model) HAwf HMI Hh MS).
  intros model1 HMI1 HS HCL.
  set (M1 := munrestrict (ahid A model) M MV1).
  assert (VML : vml_of model1 = vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  assert (HV1 : vis A model1 M1 = MV1) by (unfold CCA.vis; rewrite (L5LZ.sbm_ahid A model model1 HS); apply L5LZ.mrestrict_of_munrestrict; exact HCL).
  pose proof (ISLSA.sm_mem _ _ _ _ _ _ _ _ Hsim1) as Hm1.
  assert (FR : forall x : word, ahid A model x = false ->
            (forall lo hi, In (lo, hi) (c_wabs CF) -> ~ lo <= bv_unsigned x < hi) ->
            (forall j rg, nth_error (c_rgs CF) j = Some rg -> ~ ISLSA.rbase E rg + rg_lo rg <= bv_unsigned x < ISLSA.rbase E rg + rg_hi rg) ->
            M1 x = M x).
  { intros x Hx W1 W2. unfold M1. rewrite (L5LZ.munrestrict_visible _ _ _ _ Hx).
    rewrite (ISLSA.msim_frame segs CF E (vis A model M) s1 MV1 x Hm1 W1 W2). unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact Hx. }
  apply CONT; [|exact HV1].
  split; [split; [rewrite (L5LZ.sbm_halted _ _ HS); exact Hh | exact HMI1]|].
  split; [exact (L5LZ.model_rt_trans _ _ _ Hrt (L5LZ.sbm_model_rt _ _ HS))|].
  split; [exact HA0|]. split; [exact HLK|]. split; [|split; [exact Hroom | split; [exact HFP | split]]].
  - rewrite VML. apply (PmHeapIfaceA.aio_frame _ _ _ _ _ HIok _ _ _ _ _ M M1 _ HH).
    + intros a Ha HP. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hx; [unfold M1; apply L5LZ.munrestrict_hidden; exact Hx|].
      assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply ISLSA.wz_small; exact Ha).
      destruct (written_not_private fx M model A LK (Z_to_bv 64 a) HC ltac:(rewrite U; exact HP)) as [W1 W2]. exact (FR _ Hx W1 W2).
    + intros x Hx. destruct (ahid A model x) eqn:Hh'; [unfold M1; rewrite (L5LZ.munrestrict_hidden _ _ _ _ Hh'); exact Hx|].
      unfold M1. rewrite (L5LZ.munrestrict_visible _ _ _ _ Hh'). apply (ISLSA.msim_grows segs CF E (vis A model M) rom s1 MV1 Hm1).
      unfold CCA.vis. rewrite (L5LZ.mrestrict_visible' _ _ _ Hh'). exact Hx.
  - intros a HK. rewrite <- (HKP a HK). destruct (ahid A model (Z_to_bv 64 a)) eqn:Hx; [unfold M1; apply L5LZ.munrestrict_hidden; exact Hx|].
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply ISLSA.wz_small; exact (proj1 HK)).
    destruct (kept_not_written fx M model A LK (Z_to_bv 64 a) HC ltac:(rewrite U; exact HK)) as [W1 W2]. exact (FR _ Hx W1 W2).
  - intros a Ha Hc Hd. pose proof (HGR a Ha Hc Hd) as Hx0. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh'; [unfold M1; rewrite (L5LZ.munrestrict_hidden _ _ _ _ Hh'); exact Hx0|].
    unfold M1. rewrite (L5LZ.munrestrict_visible _ _ _ _ Hh'). apply (ISLSA.msim_grows segs CF E (vis A model M) rom s1 MV1 Hm1).
    unfold CCA.vis. rewrite (L5LZ.mrestrict_visible' _ _ _ Hh'). exact Hx0.
Qed.

Lemma stretch_out : forall s s1 fx R M model A LK,
  INV s fx R M model A LK -> arunS segs CF (call_pcs CF) fuel s = ROut s1 -> s_resv s1 = None ->
  (forall R1 M1 model1, CTX fx M1 model1 A LK -> ISLSA.sim segs CF E (vis A model M) s1 R1 (vis A model1 M1) None ->
      srealizes segs SCFG (mkCfg (@mkst fx R1 (Z_to_bv 64 (s_pc s1)) M1 rom) model1) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (s_pc s)) M rom) model) K.
Proof.
  intros s s1 fx R M model A LK HI0 Hrun Hrv CONT. pose proof HI0 as [HC Hsim].
  pose proof (@ISLSA.arunS_sound fx segs CF E (vis A model M) IO rom (call_pcs CF) fuel s R (vis A model M) None Hsim) as X. rewrite Hrun in X.
  destruct X as (R1 & MV1 & rv1 & MS & Hsim1).
  assert (Hrv1 : rv1 = None) by (rewrite (ISLSA.sm_resv _ _ _ _ _ _ _ _ Hsim1), Hrv; reflexivity). subst rv1.
  rewrite !mkstR_None in MS. change (Z_to_bv 64 (s_pc s)) with (pcw s).
  apply (stretch_core s fx R M model A LK R1 MV1 s1 (pcw s1) HI0 MS Hsim1). intros M1 model1 HC1 HV1. apply (CONT R1 M1 model1 HC1). rewrite HV1. exact Hsim1.
Qed.

Lemma stretch_fin : forall s s1 v imm fx R M model A LK,
  INV s fx R M model A LK -> arunS segs CF (call_pcs CF) fuel s = RFin s1 v imm -> s_resv s1 = None ->
  (forall R1 M1 model1, CTX fx M1 model1 A LK -> ISLSA.sim segs CF E (vis A model M) s1 R1 (vis A model1 M1) None ->
      srealizes segs SCFG (mkCfg (@mkst fx R1 (v_jalr (ISLSA.vden E v) imm) M1 rom) model1) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (s_pc s)) M rom) model) K.
Proof.
  intros s s1 v imm fx R M model A LK HI0 Hrun Hrv CONT. pose proof HI0 as [HC Hsim].
  pose proof (@ISLSA.arunS_sound fx segs CF E (vis A model M) IO rom (call_pcs CF) fuel s R (vis A model M) None Hsim) as X. rewrite Hrun in X.
  destruct X as (R1 & MV1 & rv1 & MS & Hsim1).
  assert (Hrv1 : rv1 = None) by (rewrite (ISLSA.sm_resv _ _ _ _ _ _ _ _ Hsim1), Hrv; reflexivity). subst rv1.
  rewrite !mkstR_None in MS. change (Z_to_bv 64 (s_pc s)) with (pcw s).
  apply (stretch_core s fx R M model A LK R1 MV1 s1 _ HI0 MS Hsim1). intros M1 model1 HC1 HV1. apply (CONT R1 M1 model1 HC1). rewrite HV1. exact Hsim1.
Qed.

Lemma span_in_sound : forall ivs n a i, span_in ivs a n = true -> 0 <= i < Z.of_nat n -> exists lo hi, In (lo, hi) ivs /\ lo <= a + i < hi.
Proof.
  induction n as [|n IH]; intros a i H Hi; [lia|]. cbn [span_in] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. exact (ISLSA.in_ivs_true _ _ H1).
  - destruct (IH (a + 1) (i - 1) H2 ltac:(lia)) as (lo & hi & Hin & Hr). exists lo, hi. split; [exact Hin | lia].
Qed.
Lemma in_ivs_of_In : forall ivs lo hi a, In (lo, hi) ivs -> lo <= a < hi -> in_ivs ivs a = true.
Proof.
  induction ivs as [|[lo' hi'] t IH]; intros lo hi a Hin Hr; [destruct Hin|]. cbn [in_ivs]. apply orb_true_iff.
  destruct Hin as [Hin|Hin]; [injection Hin as -> ->; left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia | right; exact (IH _ _ _ Hin Hr)].
Qed.
Lemma wr_chk_abs : forall a, wr_chk segs CF (AAbs a) = true -> 0 < a < c_abs_hi CF /\ in_ivs (c_wabs CF) a = true /\ abs_wr segs a = true.
Proof.
  intros a H. cbn [wr_chk] in H. apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H H2].
  apply andb_true_iff in H. destruct H as [H0 H1]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. repeat split; try lia; assumption.
Qed.
Lemma store_ok_abs : forall (M : mem) k a, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (forall i, 0 <= i < Z.of_nat k -> abs_wr segs (a + i) = true) ->
  store_ok segs M (Z_to_bv 64 a) k = true.
Proof.
  intros M k. induction k as [|k IH]; intros a Ha Hk H; [reflexivity|]. cbn [store_ok].
  pose proof (H 0 ltac:(lia)) as W0. rewrite Z.add_0_r in W0. unfold abs_wr in W0. unfold wview in W0 |- *.
  destruct (M (Z_to_bv 64 a)) as [b|].
  - rewrite ISLSA.wz_succ. apply IH; [lia | lia | intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia].
  - destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
    destruct (segment_byte_at _ _); [|discriminate].
    rewrite ISLSA.wz_succ. apply IH; [lia | lia | intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia].
Qed.

Lemma client_call : forall BS ST sp scr a, sp0 - SCR <= sp - scr -> sp <= sp0 ->
  aclient_g BS ST L ar LB FF sp0 SCR a -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros BS ST sp scr a H1 H2 Hc. eapply CHA.aclient_scr; [exact Hc | intros x Hx; lia]. Qed.

Lemma akept_call : forall sp scr dst n a, sp0 - SCR <= sp - scr -> sp <= sp0 ->
  (forall i, 0 <= i < n -> WOK (dst + i)) ->
  CHA.akept L ar LB FF sp0 SCR W a -> CHA.akept L ar LB FF sp scr [(dst, n)] a.
Proof.
  intros sp scr dst n a H1 H2 HW (Ha & Hc & Ho). split; [exact Ha|]. split; [exact (client_call _ _ sp scr a H1 H2 Hc)|].
  intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (HW (a - dst) ltac:(lia)) as (_ & _ & (w & Hw & Hr) & _).
  replace (dst + (a - dst)) with a in Hr by lia. exact (Ho w Hw Hr).
Qed.
Lemma clr_kept_call : forall sp scr (Wc : list L5.range) a, sp0 - SCR <= sp - scr -> sp <= sp0 -> CLR a -> L5.outside Wc a -> CHA.akept L ar LB FF sp scr Wc a.
Proof. intros sp scr Wc a H1 H2 (Ha & Hc & _) Ho. split; [exact Ha|]. split; [exact (client_call _ _ sp scr a H1 H2 Hc) | exact Ho]. Qed.

Lemma stk_kept_call : forall fx M model A LK sp scr dst n a, CTX fx M model A LK -> 0 <= scr -> sp0 - SCR <= sp - scr -> sp <= a < sp0 -> dst + n <= c_abs_hi CF -> c_abs_hi CF <= sp0 - SCR ->
  CHA.akept L ar LB FF sp scr [(dst, n)] a.
Proof.
  intros fx M model A LK sp scr dst n a HC H0 H1 Ha Hd Hh. destruct (stk_client0 fx M model A LK a HC ltac:(lia)) as (X1 & X2 & X3).
  split; [exact X1|]. split; [eapply CHA.aclient_scr_pt; [exact X2 | lia]|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
Qed.

Lemma vis_clr : forall fx M model A LK a, CTX fx M model A LK -> CLR a -> vis A model M (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof. intros fx M model A LK a HC Ha. unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact (clr_vis fx M model A LK a HC Ha). Qed.
Lemma vis_stk : forall fx M model A LK a, CTX fx M model A LK -> sp0 - SCR <= a < sp0 -> vis A model M (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof. intros fx M model A LK a HC Ha. unfold CCA.vis. apply L5LZ.mrestrict_visible'. exact (stk_vis fx M model A LK a HC Ha). Qed.
Lemma vis_rg : forall fx M model A LK j rg off, CTX fx M model A LK -> nth_error (c_rgs CF) j = Some rg -> rg_lo rg <= off < rg_hi rg ->
  vis A model M (Z_to_bv 64 (ISLSA.rbase E rg + off)) = M (Z_to_bv 64 (ISLSA.rbase E rg + off)).
Proof.
  intros fx M model A LK j rg off HC Hj Ho. destruct (rg_cases j rg off Hj Ho) as [(Hk & Hb & Hs)|(Hk & HW)].
  - rewrite Hb. apply (vis_stk fx M model A LK _ HC). lia.
  - apply (vis_clr fx M model A LK _ HC). exact (wok_clr _ HW).
Qed.

Lemma ctx_after_call : forall fx M model A LK sp scr (Wc : list L5.range) fx' (M' : mem) model' A' LK',
  CTX fx M model A LK -> sp0 - SCR <= sp - scr -> sp <= sp0 ->
  (forall a, CHA.akept L ar LB FF sp0 SCR W a -> CHA.akept L ar LB FF sp scr Wc a) ->
  FPI fx' -> CHA.ahpres L ar LB FF sp scr Wc M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
  ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
  CTX fx' M' model' A' LK'.
Proof.
  intros fx M model A LK sp scr Wc fx' M' model' A' LK' HC H1 H2 HAK HFP' (P1 & P2 & P3) Hrt HA Hmo' HLK' HH'.
  pose proof HC as (Hmo & Hrt0 & HA0 & HLK & HH & Hroom & HFP & HKP & HGR).
  split; [exact Hmo'|]. split; [exact (L5LZ.model_rt_trans _ _ _ Hrt0 Hrt)|]. split; [exact (incl_tran HA0 HA)|]. split; [exact (incl_tran HLK' HLK)|].
  split; [exact HH'|]. split.
  { pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH')) as [_ ND]. exact (CHA.ffroom_sub 32%nat 0 (le_n 32) _ _ _ _ Hroom HLK' ND). }
  split; [exact HFP'|]. split.
  - intros a HK. rewrite <- (HKP a HK). exact (P1 a (HAK a HK)).
  - intros a Ha Hc Hd. pose proof (HGR a Ha Hc Hd) as Hd1.
    destruct (Z_lt_dec a (sp - scr)) as [Hlt|Hge]; [|destruct (Z_lt_dec a sp) as [Hlt'|Hge']].
    + apply (P3 a Ha); [|exact Hd1]. eapply CHA.aclient_scr_pt; [exact Hc | lia].
    + replace a with (sp - scr + (a - (sp - scr))) by lia. apply P2. lia.
    + apply (P3 a Ha); [|exact Hd1]. eapply CHA.aclient_scr_pt; [exact Hc | lia].
Qed.

Lemma astk_call : forall fx M model A LK spoff scr, CTX fx M model A LK -> 0 <= scr -> spoff mod 16 = 0 -> spoff <= 0 -> - SCR <= spoff - scr ->
  CHA.astk ar M (sp0 + spoff) scr.
Proof.
  intros fx M model A LK spoff scr HC Hscr H16 Hle Hlo. pose proof HC as (_ & _ & _ & _ & HH & _ & _ & _ & HGR).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP.
  pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct STK as (S1 & S2 & S3 & S4 & S5 & S6).
  split; [rewrite Z.add_mod, S1, H16 by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact S4|]. split.
  - intros i Hi. replace (sp0 + spoff - scr + i) with (sp0 - SCR + (spoff - scr + i + SCR)) by lia.
    apply HGR; [lia | right; left; split; lia | apply S5; lia].
  - intros i Hi. destruct (Z_lt_dec (sp0 + spoff + i) sp0) as [Hlt|Hge].
    + replace (sp0 + spoff + i) with (sp0 - SCR + (spoff + i + SCR)) by lia. apply HGR; [lia | right; left; split; lia | apply S5; lia].
    + replace (sp0 + spoff + i) with (sp0 + (spoff + i)) by lia. apply HGR; [lia | right; left; split; lia | apply S6; lia].
Qed.

Lemma abs_hi_low : c_abs_hi CF <= sp0 - SCR - 4096.
Proof.
  destruct STK as (S1 & S2 & S3 & S4 & _). destruct LY_img as [I0 I1]. unfold BIGSHADOW_LO in I1. lia.
Qed.

Lemma call_memset : forall s1 s2 fx R1 M1 model1 A LK (MVb : mem) dst c n spoff ret tp,
  CTX fx M1 model1 A LK -> ISLSA.sim segs CF E MVb s1 R1 (vis A model1 M1) None ->
  In (s_pc s1, KMemset) (c_calls CF) ->
  sum_memset segs CF s1 = Some (EvMemset dst c n spoff ret tp, s2) -> ev_chk (EvMemset dst c n spoff ret tp) = true ->
  (forall fx' R' M' model' A' LK', INV s2 fx' R' M' model' A' LK' -> srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (s_pc s2)) M' rom) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R1 (Z_to_bv 64 (s_pc s1)) M1 rom) model1) K.
Proof.
  intros s1 s2 fx R1 M1 model1 A LK MVb dst c n spoff ret tp HC Hsim Hin Hsum Hchk CONT.
  pose proof HC as (Hmo & Hrt0 & HA0 & HLK & HH & Hroom & HFP & HKP & HGR).
  destruct (ISLRA.sum_memset_facts segs CF E MVb s1 R1 _ None dst c n spoff ret tp s2 Hsim Hsum) as (Ga0 & Ga1 & Ga2 & Gra & Gsp & Gtp & _ & Gn & Gspan & Gwr & Gpc2 & Grv2).
  unfold ev_chk, ra_chk in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Htp]. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hra].
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hlo]. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hle0].
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk H16]. apply andb_true_iff in Hchk. destruct Hchk as [Hn0 Hn27].
  apply andb_true_iff in Hra. destruct Hra as [Hra Hr2]. apply andb_true_iff in Hra. destruct Hra as [Hr0 Hr47].
  apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn27. apply Z.eqb_eq in H16. apply Z.leb_le in Hle0. apply Z.leb_le in Hlo.
  apply Z.leb_le in Hr0. apply Z.ltb_lt in Hr47. apply Z.eqb_eq in Hr2. apply Z.eqb_eq in Htp.
  rewrite SPV in Gsp. set (sp := sp0 + spoff) in *.
  pose proof abs_hi_low as AH. destruct STK as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (WD : forall i, 0 <= i < n -> WOK (dst + i) /\ 0 < dst + i < c_abs_hi CF /\ abs_wr segs (dst + i) = true).
  { intros i Hi. destruct (wr_chk_abs _ (Gwr (dst + i) ltac:(lia))) as (X1 & X2 & X3). split; [exact (WABS _ X2) | split; [exact X1 | exact X3]]. }
  assert (DLO : 0 < dst) by (destruct (WD 0 ltac:(lia)) as (_ & X & _); lia).
  assert (DHI : dst + n <= c_abs_hi CF) by (destruct (WD (n - 1) ltac:(lia)) as (_ & X & _); lia).
  assert (Hastk : CHA.astk ar M1 sp scr_ms) by (apply (astk_call fx M1 model1 A LK spoff scr_ms HC); lia).
  assert (Hraok : L5.ra_ok ret) by (split; lia).
  assert (Htp' : getr R1 (Z_to_bv 5 4) = Z_to_bv 64 (hl_tp L)) by (rewrite Gtp, Htp, TPV; reflexivity).
  assert (Hffrs : CHA.ffrs FF sp) by (eapply CHA.ffrs_le; [exact FFRS0 | lia]).
  assert (HPre : CRC.memset_pre L ar LB FF sp scr_ms dst c n R1 M1).
  { split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [lia|]. split; [|split; [|split]].
    + intros a Ha. destruct (span_in_sound _ _ _ (a - dst) Gspan ltac:(rewrite Z2Nat.id by lia; lia)) as (lo & hi & Hlh & Hr).
      replace (dst + (a - dst)) with a in Hr by lia. apply (MS_acc LK A M1 model1 lo hi HH Hlh a). lia.
    + intros i Hi. destruct (WD i Hi) as ((_ & X & _) & _). exact (client_call _ _ sp scr_ms _ ltac:(lia) ltac:(lia) X).
    + intros d k Hd Hk. apply store_ok_abs; [lia | lia |]. intros i Hi. replace (dst + d + i) with (dst + (d + i)) by lia. exact (proj2 (proj2 (WD (d + i) ltac:(lia)))).
    + destruct LY_img as [I0 I1]. split; [lia|]. split; [left; lia | left; lia]. }
  refine (CRC.memset_cps L ar HI FPI (s_pc s1) (MEMSET _ Hin) scr_ms LB FF LK cr A dst c n sp ret SCRMS fx R1 M1 model1 K HH Hmo KNIL HFP Gra Hraok Gsp Htp' Hastk Hroom Hffrs HPre _).
  intros fx' R' M' model' LB' cr' LBk Wc LK' A' HFP' (Pa0 & Pnew & -> & -> & -> & ->) HRP HP Hrt HA Hmo' HLK' HH'.
    rewrite <- Gpc2.
    assert (HC' : CTX fx' M' model' A' LK').
    { apply (ctx_after_call fx M1 model1 A LK sp scr_ms [(dst, n)] fx' M' model' A' LK' HC); try assumption; [lia|lia|].
      intros a HK. apply (akept_call sp scr_ms dst n a); [lia|lia| intros i Hi; exact (proj1 (WD i Hi)) | exact HK]. }
    apply (CONT fx' R' M' model' A' LK'). split; [exact HC'|].
    apply (ISLRA.resume_memset segs CF E IO MVb s1 R1 (vis A model1 M1) None dst c n spoff ret tp s2 R' (vis A' model' M') Hsim Hsum).
    + intros r Hr. exact (HRP r Hr).
    + exact Pa0.
    + intros i Hi. destruct (Pnew i Hi) as (v & -> & Hb). rewrite (vis_clr fx' M' model' A' LK' (dst + i) HC' (wok_clr _ (proj1 (WD i Hi)))). exact Hb.
    + intros a Ha Hnd Hw.
      assert (CL : CLR a) by (destruct Hw as [Hw|Hw]; [exact (wok_clr _ (WABS a Hw)) | exact (RTC a Ha Hw)]).
      rewrite (vis_clr fx' M' model' A' LK' a HC' CL), (vis_clr fx M1 model1 A LK a HC CL).
      apply (proj1 HP). apply (clr_kept_call sp scr_ms [(dst, n)] a); [lia|lia|exact CL|]. intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
    + intros j rg off Hj Ho Hsp. rewrite (vis_rg fx' M' model' A' LK' j rg off HC' Hj Ho), (vis_rg fx M1 model1 A LK j rg off HC Hj Ho).
      apply (proj1 HP). destruct (rg_cases j rg off Hj Ho) as [(Hk & Hb & Hs)|(Hk & HW)].
      * rewrite Hb. apply (stk_kept_call fx M1 model1 A LK sp scr_ms dst n _ HC); [lia|lia| specialize (Hsp Hk); lia | exact DHI | lia].
      * apply (clr_kept_call sp scr_ms [(dst, n)] _); [lia|lia|exact (wok_clr _ HW)|]. intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
        destruct (ISLSA.io_rg CF E IO j rg Hj) as (X & _). lia.
    + intros j rg off Hj Ho. rewrite (vis_rg fx' M' model' A' LK' j rg off HC' Hj Ho).
      pose proof (ISLSA.ms_def _ _ _ _ _ _ (ISLSA.sm_mem _ _ _ _ _ _ _ _ Hsim) j rg off Hj Ho) as D1. rewrite (vis_rg fx M1 model1 A LK j rg off HC Hj Ho) in D1.
      destruct HP as (P1 & P2 & P3). destruct (rg_cases j rg off Hj Ho) as [(Hk & Hb & Hs)|(Hk & HW)].
      * rewrite Hb in D1 |- *. destruct (Z_lt_dec (sp0 + off) (sp - scr_ms)) as [Hlt|Hge]; [|destruct (Z_lt_dec (sp0 + off) sp) as [Hlt'|Hge']].
        -- destruct (stk_client0 fx M1 model1 A LK (sp0 + off) HC ltac:(lia)) as (X1 & X2 & X3). apply (P3 _ X1); [|exact D1]. eapply CHA.aclient_scr_pt; [exact X2 | lia].
        -- replace (sp0 + off) with (sp - scr_ms + (sp0 + off - (sp - scr_ms))) by lia. apply P2. lia.
        -- destruct (stk_client0 fx M1 model1 A LK (sp0 + off) HC ltac:(lia)) as (X1 & X2 & X3). apply (P3 _ X1); [|exact D1]. eapply CHA.aclient_scr_pt; [exact X2 | lia].
      * destruct HW as (X1 & X2 & _). apply (P3 _ X1); [|exact D1]. exact (client_call _ _ sp scr_ms _ ltac:(lia) ltac:(lia) (aclientw_client _ _ _ _ _ _ _ X2)).
Qed.

Lemma stk_aacc : forall fx M model A LK p n, CTX fx M model A LK -> sp0 - SCR <= p -> p + n <= sp0 -> aacc M p n.
Proof.
  intros fx M model A LK p n HC Hp Hn a Ha. left.
  pose proof HC as (_ & _ & _ & _ & HH & _ & _ & HKP & _).
  pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct STK as (S1 & S2 & S3 & S4 & _).
  assert (B8 : (sp0 - SCR) mod 8 = 0) by (rewrite Zminus_mod, SCR8, (CHA.mod8_of_16 sp0 S1); reflexivity).
  set (base := sp0 - SCR) in *. set (j := (a - base) / 8).
  assert (HS : S a = S base + j).
  { unfold S, j. replace a with ((base / 8) * 8 + (a - base)) at 1 by (rewrite (Z.div_mod base 8) at 2 by lia; rewrite B8; lia).
    rewrite Z.div_add_l by lia. lia. }
  assert (J0 : 0 <= j) by (unfold j; apply Z.div_pos; lia).
  pose proof (Z.div_mod SCR 8 ltac:(lia)) as DM. rewrite SCR8 in DM.
  assert (J1 : j < SCR / 8) by (unfold j; apply Z.div_lt_upper_bound; lia).
  assert (J2 : SCR / 8 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - base) / 8) by (apply Z.div_le_mono; lia).
  assert (SLO : 0x7fff8000 <= S a) by (unfold S, SB; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia).
  assert (SHI : S a < 0x10007fff8000) by (unfold S, SB; assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia).
  unfold byte_at. rewrite HS. rewrite (HKP (S base + j)); [exact (STKSH0 j ltac:(lia))|].
  rewrite <- HS. split; [lia|]. split.
  - right; right; right; right; left. unfold in_shadow_of. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by lia.
    unfold S. split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia].
  - intros w Hw Hin. destruct (W_app w (S a) Hw Hin) as [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI in X; lia.
Qed.
Lemma call_memcmp : forall s1 s2 fx R1 M1 model1 A LK (MVb : mem) poff q n zs1 zs2 spoff ret tp,
  CTX fx M1 model1 A LK -> ISLSA.sim segs CF E MVb s1 R1 (vis A model1 M1) None ->
  In (s_pc s1, KMemcmp) (c_calls CF) ->
  sum_memcmp segs CF s1 = Some (EvMemcmp poff q n zs1 zs2 spoff ret tp, s2) -> ev_chk (EvMemcmp poff q n zs1 zs2 spoff ret tp) = true ->
  (forall fx' R' M' model' A' LK', INV s2 fx' R' M' model' A' LK' -> srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (s_pc s2)) M' rom) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R1 (Z_to_bv 64 (s_pc s1)) M1 rom) model1) K.
Proof.
  intros s1 s2 fx R1 M1 model1 A LK MVb poff q n zs1 zs2 spoff ret tp HC Hsim Hin Hsum Hchk CONT.
  pose proof HC as (Hmo & Hrt0 & HA0 & HLK & HH & Hroom & HFP & HKP & HGR).
  destruct (ISLRA.sum_memcmp_facts segs CF E MVb s1 R1 _ None poff q n zs1 zs2 spoff ret tp s2 Hsim Hsum)
    as (Ga0 & Ga1 & Ga2 & Gra & Gsp & Gtp & _ & Gn & Gspan & Gle & (j & rg & Hj & Hk & Hrg) & D1 & D2 & Gpc2 & Grv2 & Hs2).
  unfold ev_chk, ra_chk in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Htp]. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hra].
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hlo]. apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hle0].
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk H16]. apply andb_true_iff in Hchk. destruct Hchk as [Hn0 Hn27].
  apply andb_true_iff in Hra. destruct Hra as [Hra Hr2]. apply andb_true_iff in Hra. destruct Hra as [Hr0 Hr47].
  apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn27. apply Z.eqb_eq in H16. apply Z.leb_le in Hle0. apply Z.leb_le in Hlo.
  apply Z.leb_le in Hr0. apply Z.ltb_lt in Hr47. apply Z.eqb_eq in Hr2. apply Z.eqb_eq in Htp.
  rewrite SPV in Ga0, Gsp, D1. set (sp := sp0 + spoff) in *. set (p := sp0 + poff) in *.
  pose proof abs_hi_low as AH. destruct STK as (S1 & S2 & S3 & S4 & S5 & S6). destruct LY_img as [I0 I1].
  pose proof (ctx_rf _ _ _ _ _ HC) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _).
  destruct (RGS j rg Hj) as [(_ & Wlo & Whi)|(Hk' & _)]; [|exfalso; exact (Hk' Hk)].
  assert (PHI : p + n <= sp0) by (pose proof (Hrg (n - 1) ltac:(lia)); lia).
  assert (PLO : sp <= p) by lia.
  assert (QR : forall i, 0 <= i < n -> exists lo hi, In (lo, hi) (c_rook CF) /\ lo <= q + i < hi).
  { intros i Hi. exact (span_in_sound _ _ _ i Gspan ltac:(rewrite Z2Nat.id by lia; lia)). }
  assert (QLO : hl_img_lo L <= q) by (destruct (QR 0 ltac:(lia)) as (lo & hi & Hlh & Hr); destruct (RO_rng lo hi Hlh); lia).
  assert (QHI : q + n <= hl_img_hi L) by (destruct (QR (n - 1) ltac:(lia)) as (lo & hi & Hlh & Hr); destruct (RO_rng lo hi Hlh); lia).
  assert (Hastk : CHA.astk ar M1 sp scr_mc) by (apply (astk_call fx M1 model1 A LK spoff scr_mc HC); lia).
  assert (Hraok : L5.ra_ok ret) by (split; lia).
  assert (Htp' : getr R1 (Z_to_bv 5 4) = Z_to_bv 64 (hl_tp L)) by (rewrite Gtp, Htp, TPV; reflexivity).
  assert (Hffrs : CHA.ffrs FF sp) by (eapply CHA.ffrs_le; [exact FFRS0 | lia]).
  assert (D1' : rdn segs M1 (Z_to_bv 64 p) (Z.to_nat n) = Some (zbytes zs1)).
  { rewrite <- D1. symmetry. apply (L5C.rdn_agree segs M1 (vis A model1 M1)); [lia | rewrite Z2Nat.id by lia; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia. apply (vis_stk fx M1 model1 A LK i HC). lia. }
  assert (D2' : rdn segs M1 (Z_to_bv 64 q) (Z.to_nat n) = Some (zbytes zs2)).
  { rewrite <- D2. symmetry. apply (L5C.rdn_agree segs M1 (vis A model1 M1)); [lia | rewrite Z2Nat.id by lia; unfold BIGSHADOW_LO in I1; lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (QR (i - q) ltac:(lia)) as (lo & hi & Hlh & Hr). replace (q + (i - q)) with i in Hr by lia.
    apply (vis_clr fx M1 model1 A LK i HC). exact (RO_clr lo hi i Hlh Hr). }
  assert (HPre : CRC.memcmp_pre L ar LB FF sp scr_mc p q n (zbytes zs1) (zbytes zs2) R1 M1).
  { split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [lia|]. split.
    + split; [exact (stk_aacc fx M1 model1 A LK p n HC ltac:(lia) PHI)|]. split; [lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; lia|]. split; [|exact D1'].
      intros i Hi. right. right. left. split; lia.
    + split. { intros a Ha. destruct (QR (a - q) ltac:(lia)) as (lo & hi & Hlh & Hr). replace (q + (a - q)) with a in Hr by lia. exact (RO_acc LK A M1 model1 lo hi HH Hlh a ltac:(lia)). }
      split; [unfold BIGSHADOW_LO in I1; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI in *; lia|]. split; [|exact D2'].
      intros i Hi. left. lia. }
  refine (CRC.memcmp_cps L ar HI FPI (s_pc s1) scr_mc (MEMCMP _ Hin) scr_mc LB FF LK cr A p q n (zbytes zs1) (zbytes zs2) sp ret ltac:(lia)
            fx R1 M1 model1 K HH Hmo KNIL HFP Gra Hraok Gsp Htp' Hastk Hroom Hffrs HPre _).
  intros fx' R' M' model' LB' cr' LBk Wc LK' A' HFP' (Pa0 & -> & -> & -> & ->) HRP HP Hrt HA Hmo' HLK' HH'.
  rewrite <- Gpc2.
  assert (HC' : CTX fx' M' model' A' LK').
  { apply (ctx_after_call fx M1 model1 A LK sp scr_mc [] fx' M' model' A' LK' HC); try assumption; [lia|lia|].
    intros a (Ha & Hc & Ho). split; [exact Ha|]. split; [exact (client_call _ _ sp scr_mc a ltac:(lia) ltac:(lia) Hc) | intros w []]. }
  apply (CONT fx' R' M' model' A' LK'). split; [exact HC'|].
  apply (ISLRA.resume_memcmp segs CF E IO MVb s1 R1 (vis A model1 M1) None poff q n zs1 zs2 spoff ret tp s2 R' (vis A' model' M') Hsim Hsum).
  + intros r Hr. exact (HRP r Hr).
  + rewrite zmemcmp_val. exact Pa0.
  + intros a Ha Hw.
    assert (CL' : CLR a) by (destruct Hw as [Hw|Hw]; [exact (wok_clr _ (WABS a Hw)) | exact (RTC a Ha Hw)]).
    rewrite (vis_clr fx' M' model' A' LK' a HC' CL'), (vis_clr fx M1 model1 A LK a HC CL').
    apply (proj1 HP). apply (clr_kept_call sp scr_mc [] a); [lia|lia|exact CL'| intros w []].
  + intros j' rg' off Hj' Ho Hsp. rewrite (vis_rg fx' M' model' A' LK' j' rg' off HC' Hj' Ho), (vis_rg fx M1 model1 A LK j' rg' off HC Hj' Ho).
    apply (proj1 HP). destruct (rg_cases j' rg' off Hj' Ho) as [(Hk2 & Hb & Hs)|(Hk2 & HW)].
    * rewrite Hb. destruct (stk_client0 fx M1 model1 A LK (sp0 + off) HC ltac:(lia)) as (X1 & X2 & X3).
      split; [exact X1|]. split; [eapply CHA.aclient_scr_pt; [exact X2 | specialize (Hsp Hk2); lia] | intros w []].
    * apply (clr_kept_call sp scr_mc [] _); [lia|lia|exact (wok_clr _ HW)| intros w []].
  + intros j' rg' off Hj' Ho. rewrite (vis_rg fx' M' model' A' LK' j' rg' off HC' Hj' Ho).
    pose proof (ISLSA.ms_def _ _ _ _ _ _ (ISLSA.sm_mem _ _ _ _ _ _ _ _ Hsim) j' rg' off Hj' Ho) as DD. rewrite (vis_rg fx M1 model1 A LK j' rg' off HC Hj' Ho) in DD.
    destruct HP as (P1 & P2 & P3). destruct (rg_cases j' rg' off Hj' Ho) as [(Hk2 & Hb & Hs)|(Hk2 & HW)].
    * rewrite Hb in DD |- *. destruct (Z_lt_dec (sp0 + off) (sp - scr_mc)) as [Hlt|Hge]; [|destruct (Z_lt_dec (sp0 + off) sp) as [Hlt'|Hge']].
      -- destruct (stk_client0 fx M1 model1 A LK (sp0 + off) HC ltac:(lia)) as (X1 & X2 & X3). apply (P3 _ X1); [|exact DD]. eapply CHA.aclient_scr_pt; [exact X2 | lia].
      -- replace (sp0 + off) with (sp - scr_mc + (sp0 + off - (sp - scr_mc))) by lia. apply P2. lia.
      -- destruct (stk_client0 fx M1 model1 A LK (sp0 + off) HC ltac:(lia)) as (X1 & X2 & X3). apply (P3 _ X1); [|exact DD]. eapply CHA.aclient_scr_pt; [exact X2 | lia].
    * destruct HW as (X1 & X2 & _). apply (P3 _ X1); [|exact DD]. exact (client_call _ _ sp scr_mc _ ltac:(lia) ltac:(lia) (aclientw_client _ _ _ _ _ _ _ X2)).
Qed.

Lemma sim_rebase : forall (MVb : mem) s R (M : mem) rv, ISLSA.sim segs CF E MVb s R M rv -> ISLSA.sim segs CF E M s R M rv.
Proof.
  intros MVb s R M rv [A1 A2 A3 [B1 B2 B3 B4 B5] A5]. constructor; try assumption. constructor; try assumption. intros x. left. reflexivity.
Qed.
Lemma find_call_in : forall l pc k, find_call l pc = Some k -> In (pc, k) l.
Proof.
  induction l as [|[p' k'] t IH]; intros pc k H; [discriminate H|]. cbn [find_call] in H.
  destruct (Z.eqb_spec p' pc) as [->|Hne]; [injection H as ->; left; reflexivity | right; exact (IH _ _ H)].
Qed.
Lemma sum_memset_ev : forall s ev s2, sum_memset segs CF s = Some (ev, s2) -> s_resv s = None /\ exists dst c n spoff ret tp, ev = EvMemset dst c n spoff ret tp.
Proof.
  intros s ev s2 H. unfold sum_memset in H.
  destruct (gr s 10) as [dst| |]; try discriminate H. destruct (gr s 11) as [c| |]; try discriminate H. destruct (gr s 12) as [n| |]; try discriminate H.
  destruct (gr s 1) as [ret| |]; try discriminate H. destruct (gr s 2) as [|k2 spoff|]; try discriminate H. destruct (gr s 4) as [tp| |]; try discriminate H.
  destruct (s_resv s); [discriminate H|]. split; [reflexivity|].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  destruct (wrbs segs CF s (AAbs dst) (repeat (BL (c mod 256)) (Z.to_nat n))); [|discriminate H]. injection H as <- _. exists dst, c, n, spoff, ret, tp. reflexivity.
Qed.
Lemma sum_memcmp_ev : forall s ev s2, sum_memcmp segs CF s = Some (ev, s2) -> s_resv s = None /\ exists poff q n zs1 zs2 spoff ret tp, ev = EvMemcmp poff q n zs1 zs2 spoff ret tp.
Proof.
  intros s ev s2 H. unfold sum_memcmp in H.
  destruct (gr s 10) as [|kp poff|]; try discriminate H. destruct (gr s 11) as [q| |]; try discriminate H. destruct (gr s 12) as [n| |]; try discriminate H.
  destruct (gr s 1) as [ret| |]; try discriminate H. destruct (gr s 2) as [|k2 spoff|]; try discriminate H. destruct (gr s 4) as [tp| |]; try discriminate H.
  destruct (s_resv s); [discriminate H|]. split; [reflexivity|].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd; [|discriminate H] end.
  destruct (classify CF (AS kp poff)) as [adp|]; [|discriminate H].
  destruct (rdbs segs CF s adp (Z.to_nat n)) as [l1|]; [|discriminate H]. destruct (rdbs segs CF s (AAbs q) (Z.to_nat n)) as [l2|]; [|discriminate H].
  destruct (lits l1) as [zs1|]; [|discriminate H]. destruct (lits l2) as [zs2|]; [|discriminate H]. injection H as <- _.
  exists poff, q, n, zs1, zs2, spoff, ret, tp. reflexivity.
Qed.

Theorem chain_sound : forall n s fx R M model A LK s' log,
  INV s fx R M model A LK ->
  arunC segs CF n fuel s = CFin s' (AS 1%nat 0) 0 log -> s_resv s' = None -> forallb ev_chk log = true ->
  (forall fx' R' M' model' A' LK', INV s' fx' R' M' model' A' LK' -> srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0) M' rom) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (s_pc s)) M rom) model) K.
Proof.
  induction n as [|n IH]; intros s fx R M model A LK s' log HI0 Hrun Hrv Hchk CONT; [discriminate Hrun|].
  cbn [arunC] in Hrun.
  destruct (arunS segs CF (call_pcs CF) fuel s) as [s1 v imm|s1|c pc] eqn:HS; [| |discriminate Hrun].
  - injection Hrun as -> -> -> <-.
    apply (stretch_fin s s' (AS 1%nat 0) 0 fx R M model A LK HI0 HS Hrv). intros R1 M1 model1 HC1 Hsim1.
    assert (Hpc : v_jalr (ISLSA.vden E (AS 1%nat 0)) 0 = Z_to_bv 64 ra0).
    { rewrite ISLSA.vden_AS0, RAV. destruct RAok as [Hr1 Hr2]. unfold v_jalr, jalr_tgtZ. rewrite ISLSA.wz_small by lia. rewrite Z.add_0_r, land_m2_even by exact Hr2. reflexivity. }
    rewrite Hpc. apply (CONT fx R1 M1 model1 A LK). split; [exact HC1 | exact (sim_rebase _ _ _ _ _ Hsim1)].
  - destruct (existsb (Z.eqb (s_pc s1)) (call_pcs CF)); [|discriminate Hrun].
    destruct (summary segs CF s1) as [[ev s2]|] eqn:Hsum; [|discriminate Hrun].
    destruct (arunC segs CF n fuel s2) as [s3 v imm log'|s3 log'|c pc log'] eqn:Hrun2; try discriminate Hrun. injection Hrun as -> -> -> <-.
    cbn [forallb] in Hchk. apply andb_true_iff in Hchk. destruct Hchk as [Hchk1 Hchk2].
    unfold summary in Hsum. destruct (find_call (c_calls CF) (s_pc s1)) as [[|]|] eqn:Hfc; [| |discriminate Hsum]; apply find_call_in in Hfc.
    + destruct (sum_memset_ev _ _ _ Hsum) as (Hrv1 & dst & c & k & spoff & ret & tp & ->).
      apply (stretch_out s s1 fx R M model A LK HI0 HS Hrv1). intros R1 M1 model1 HC1 Hsim1.
      apply (call_memset s1 s2 fx R1 M1 model1 A LK (vis A model M) dst c k spoff ret tp HC1 Hsim1 Hfc Hsum Hchk1).
      intros fx' R' M' model' A' LK' HI2. exact (IH s2 fx' R' M' model' A' LK' s' log' HI2 Hrun2 Hrv Hchk2 CONT).
    + destruct (sum_memcmp_ev _ _ _ Hsum) as (Hrv1 & poff & q & k & zs1 & zs2 & spoff & ret & tp & ->).
      apply (stretch_out s s1 fx R M model A LK HI0 HS Hrv1). intros R1 M1 model1 HC1 Hsim1.
      apply (call_memcmp s1 s2 fx R1 M1 model1 A LK (vis A model M) poff q k zs1 zs2 spoff ret tp HC1 Hsim1 Hfc Hsum Hchk1).
      intros fx' R' M' model' A' LK' HI2. exact (IH s2 fx' R' M' model' A' LK' s' log' HI2 Hrun2 Hrv Hchk2 CONT).
Qed.
End Chain.
End ISLC.
