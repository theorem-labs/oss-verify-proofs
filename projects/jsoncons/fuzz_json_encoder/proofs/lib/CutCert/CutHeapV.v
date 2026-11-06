(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CHV.
Definition mem := (word -> option byte).

Section V.
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

Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.                     (* [comment removed for export] *)
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBo : list (Z * Z).            (* [comment removed for export] *)
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable D0 : Z.
(* [comment removed for export] *)
Variable G : Type.
Variable gB : G -> list (Z * Z).                                           (* [comment removed for export] *)
Variable CredV : G -> nat -> env -> credit -> Prop.                        (* [comment removed for export] *)
Variable XIv : G -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.    (* [comment removed for export] *)

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBo FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M00 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LBr (g : G) : list (Z * Z) := LBo ++ gB g.

(* [comment removed for export] *)
Definition okV (M0c : mem) : Prop :=
  (forall a, CHA.akept L ar LBo FFrest sp0 SCR W a -> M0c (Z_to_bv 64 a) = M00 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FFrest sp0 0 a -> M00 (Z_to_bv 64 a) <> None -> M0c (Z_to_bv 64 a) <> None) /\
  L5.defined M0c (sp0 - SCR) SCR /\ L5.defined M0c sp0 (ar_stack_top ar - sp0).

Definition aambV (g : G) (M0c : mem) : nat -> env -> list (Z * Z) -> mem -> Model -> Prop :=
  CHA.aamb L ar HI NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0.
Definition ambXV (g : G) (M0c : mem) : nat -> env -> list (Z * Z) -> mem -> Model -> Prop :=
  CHA.ambX L ar HI NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 (XIv g).
Definition ambV (i : nat) (E : env) (A : list (Z * Z)) (M : mem) (model : Model) : Prop :=
  exists (g : G) (M0c : mem), okV M0c /\ ambXV g M0c i E A M model.

Lemma ambV_intro : forall g M0c i E A M model, okV M0c -> ambXV g M0c i E A M model -> ambV i E A M model.
Proof. intros g M0c i E A M model H1 H2. exists g, M0c. split; assumption. Qed.

Lemma okV_refl : okV M00.
Proof. split; [intros; reflexivity|]. split; [intros a _ _ H; exact H|]. split; [exact DEF0 | exact DEFUP]. Qed.
Lemma okV_def0 : forall M0c, okV M0c -> L5.defined M0c (sp0 - SCR) SCR.
Proof. intros M0c (_ & _ & H & _). exact H. Qed.
Lemma okV_defup : forall M0c, okV M0c -> L5.defined M0c sp0 (ar_stack_top ar - sp0).
Proof. intros M0c (_ & _ & _ & H). exact H. Qed.

Lemma incl_LBo : forall g, incl LBo (LBr g).
Proof. intros g. unfold LBr. apply incl_appl, incl_refl. Qed.
Lemma akept_LBr : forall g sp scr Wx a, CHA.akept L ar LBo FFrest sp scr Wx a -> CHA.akept L ar (LBr g) FFrest sp scr Wx a.
Proof.
  intros g sp scr Wx a (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ (incl_LBo g) (incl_refl _) H2).
Qed.

(* [comment removed for export] *)
Lemma Wo_okV : forall g r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar (LBr g) FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros g r a Hr Hin. destruct (Wo_ok r a Hr Hin) as (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ (incl_LBo g) (incl_refl _) H2).
Qed.
Lemma CRS_okV : forall g r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar (LBr g) FFrest sp0 d a.
Proof.
  intros g r Hr. destruct (CRS_ok r Hr) as [H1 H2]. split; [exact H1|]. intros a Ha. destruct (H2 a Ha) as (X1 & X2 & X3).
  split; [exact X1|]. split; [|exact X3]. exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ (incl_LBo g) (incl_refl _) X2).
Qed.

Lemma ambV_model : forall i E A M model, ambV i E A M model -> m_halted model = None /\ MInv A model /\ A_wf A /\ H_off_segments (hl_segs L) (ahid A model).
Proof.
  intros i E A M model (g & M0c & _ & H).
  exact (CHA.ambX_model L ar C HI HIok LY_below NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 (XIv g) i E A M model H).
Qed.

(* [comment removed for export] *)
Lemma ih_of : forall g M0c mu, okV M0c -> CCA.IH (hl_segs L) CPS ambV K FPI mu -> CCA.IH (hl_segs L) CPS (ambXV g M0c) K FPI mu.
Proof.
  intros g M0c mu OKV H j cj fx2 E2 R2 A2 M2 model2 Hcj HAt HAmb HFP Hlt.
  exact (H j cj fx2 E2 R2 A2 M2 model2 Hcj HAt (ambV_intro g M0c j E2 A2 M2 model2 OKV HAmb) HFP Hlt).
Qed.

(* [comment removed for export] *)
Lemma frame00 : forall g M0c i E A M model, okV M0c -> aambV g M0c i E A M model ->
  (forall a, CHA.akept L ar LBo FFrest sp0 SCR W a -> M (Z_to_bv 64 a) = M00 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FFrest sp0 0 a -> M00 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None).
Proof.
  intros g M0c i E A M model (O1 & O2 & _ & _) (_ & _ & _ & _ & _ & Hfr & Hdf). split.
  - intros a Ha. rewrite (Hfr a (akept_LBr g _ _ _ a Ha)). exact (O1 a Ha).
  - intros a Ha Hc Hd. apply (Hdf a Ha); [|exact (O2 a Ha Hc Hd)].
    exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ (incl_LBo g) (incl_refl _) Hc).
Qed.

(* [comment removed for export] *)
Lemma ahpres_rebase : forall g M0c M1, okV M0c ->
  CHA.ahpres L ar (LBr g) FFrest sp0 SCR W M0c M1 -> CHA.ahpres L ar LBo FFrest sp0 SCR W M00 M1.
Proof.
  intros g M0c M1 (O1 & O2 & _ & _) (H1 & H2 & H3). split; [|split].
  - intros a Ha. rewrite (H1 a (akept_LBr g _ _ _ a Ha)). exact (O1 a Ha).
  - exact H2.
  - intros a Ha Hc Hd. apply (H3 a Ha).
    + exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ (incl_LBo g) (incl_refl _) Hc).
    + apply (O2 a Ha); [|exact Hd]. eapply CHA.aclient_scr; [exact Hc | intros x Hx; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amb_calleeV : forall g g' M0c i j E E2 A A2 M1 M2 model1 model2 c scr LBk FFk Wc cr2 LK2,
  okV M0c -> aambV g M0c i E A M1 model1 ->
  CHA.ahpres L ar LBk FFk (sp0 + c) scr Wc M1 M2 -> incl LBo LBk -> incl FFrest FFk -> c <= 0 -> 0 <= scr -> - SCR <= c - scr ->
  (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LBo FFrest sp0 SCR W a) ->
  model_rt model1 model2 -> CHA.amodel_ok A2 model2 -> incl A A2 ->
  ri_inv HI (CHA.curB (LBr g') BLS j E2) (CHA.curF FFrest sp0 FFS j E2) LK2 cr2 A2 M2 (vml_of model2) -> incl LK2 LK0 ->
  env_agree NF E E2 -> CredV g' j E2 cr2 -> CHA.ffroom (CHA.curF FFrest sp0 FFS j E2) LK2 (D0 - Z.of_nat (length (nth j FFS []))) ->
  okV M2 /\ aambV g' M2 j E2 A2 M2 model2.
Proof.
  intros g g' M0c i j E E2 A A2 M1 M2 model1 model2 c scr LBk FFk Wc cr2 LK2 OKV HA (HP1 & HP2 & HP3) HiB HiF Hc Hs0 Hc2 HWc Hrt2 Hmo2 HA2 HH2 HLK2 Hag2 HC2 HRoom.
  destruct (frame00 g M0c i E A M1 model1 OKV HA) as (F1 & F2).
  destruct HA as (Hmo & Hrt & HA0 & Hag & (cr & LK & HH & _) & _ & _).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP.
  destruct STK as (_ & S2 & S3).
  assert (DEF2 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FFrest sp0 0 a -> M00 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
  { intros a Ha HC0 Hd. pose proof (F2 a Ha HC0 Hd) as HdM.
    destruct (Z_le_dec (sp0 + c - scr) a) as [G1|G1]; [destruct (Z_lt_dec a (sp0 + c)) as [G2|G2]|].
    - pose proof (HP2 (a - (sp0 + c - scr)) ltac:(lia)) as Y. replace (sp0 + c - scr + (a - (sp0 + c - scr))) with a in Y by lia. exact Y.
    - apply (HP3 a Ha); [|exact HdM]. eapply CHA.aclient_scr_pt; [eapply CHA.aclient_incl; [exact HiB | exact HiF | exact HC0] | lia].
    - apply (HP3 a Ha); [|exact HdM]. eapply CHA.aclient_scr_pt; [eapply CHA.aclient_incl; [exact HiB | exact HiF | exact HC0] | lia]. }
  split.
  - split; [|split; [exact DEF2|split]].
    + intros a HK. rewrite <- (F1 a HK). apply HP1. destruct HK as (K1 & K2 & K3). split; [exact K1|]. split.
      * eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [exact HiB | exact HiF | exact K2] | intros x Hx; lia].
      * intros w Hw Hin. exact (HWc w a Hw Hin (conj K1 (conj K2 K3))).
    + intros k Hk. apply (DEF2 (sp0 - SCR + k)); [lia | right; left; split; lia | apply DEF0; exact Hk].
    + intros k Hk. apply (DEF2 (sp0 + k)); [lia | right; left; split; lia | apply DEFUP; exact Hk].
  - split; [exact Hmo2|]. split; [exact (L5LZ.model_rt_trans _ _ _ Hrt Hrt2)|]. split; [exact (incl_tran HA0 HA2)|].
    split; [eapply CC.env_agree_trans; eassumption|]. split; [exists cr2, LK2; repeat split; assumption|].
    split; [intros a _; reflexivity | intros a _ _ H; exact H].
Qed.

(* [comment removed for export] *)
Lemma custom_retV : forall g M0c scr ng BLk FLk wregs news a0x i c ps j cj ci,
  okV M0c ->
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng BLk FLk wregs news a0x c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  forall E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> aambV g M0c i E A M model -> env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    CCA.IH (hl_segs L) CPS ambV K FPI (CC.meas c E) ->
    CHA.common_facts L ar HI NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr ng c ps cj ci i E E' R' A M1 model1 /\
    forall (fx2 : FPState) R2 A2 M2 model2 ghosts LBk FFk Wc,
      length ghosts = ng -> FPI fx2 ->
      (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
      match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
      CHA.ahpres L ar LBk FFk (sp0 + CH2.ci_csp ci) scr Wc M1 M2 ->
      incl (CH2.den E' BLk ++ LBo) LBk -> incl (CHA.denF sp0 E' FLk ++ FFrest) FFk ->
      (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CHA.in_reg E' r a) ->
      ambV j (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) A2 M2 model2 ->
      (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) (CCA.vis A2 model2 M2) X) ->
      srealizes (hl_segs L) SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 (CC.cp_pc cj)) M2 (seg_rom (hl_segs L))) model2) K.
Proof.
  intros g M0c scr ng BLk FLk wregs news a0x i c ps j cj ci OKV Hcj Hchk E R A M model E' R' M1 model1 HAt HA Hag HLF HIH.
  unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d scr ng c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
  pose proof (CHA.common_sound L ar C HI HIok LY_img LY_ro NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W Wo BLS FFS (CredV g) D0 STK SCR_pos NF32 SP0 TP0 Wo_incl (Wo_okV g) FFRS0 WRS_ok
                (okV_def0 M0c OKV) (okV_defup M0c OKV) scr ng i c ps cj ci0 E R A M model E' R' M1 model1 Hc HAt HA Hag HLF) as CF.
  split; [exact CF|].
  destruct CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  apply andb_prop in Hb as [Hb Z8]. apply andb_prop in Hb as [Hb Z7]. apply andb_prop in Hb as [Hb Z6]. apply andb_prop in Hb as [Hb Z5].
  apply andb_prop in Hb as [Hb Z4]. apply andb_prop in Hb as [Hb Z3]. apply andb_prop in Hb as [Z1 Z2]. apply CH2.regs_eqb_eq in Z1.
  intros fx2 R2 A2 M2 model2 ghosts LBk FFk Wc Hlen HFP2 Hkeep Ha0 HP HiBk HiFk HWc HA2 Hnews.
  set (nx := CH2.ci_nx ci0) in *. set (E2 := CH2.retEx E' nx ghosts R2) in *.
  pose proof (CH2.retEx_agree E' nx ghosts R2 : env_agree nx E' E2) as Hag2.
  apply (HIH j cj fx2 E2 R2 A2 M2 model2 Hcj); [| exact HA2 | exact HFP2 | apply Hmeas; exact Hag2].
  split.
  - (* [comment removed for export] *)
    assert (HR1 : regs_ok E2 (APC.sr_fresh (CH2.ci_regs ci0) APC.caller_saved (nx + ng)) R2).
    { unfold E2, CH2.retEx. rewrite Hlen. apply (CH2.ret_regs (APS.ext_list E' nx ghosts) _ (nx + ng) R' R2).
      - intros r. rewrite (HR r). apply (SR.edenot_agree_AP nx); [apply APS.ext_list_agree|].
        unfold sr_get. destruct (bv_eqb r 0); [reflexivity | apply CH.nth_vars_lt; exact V1].
      - eapply APS.sr_vars_lt_mono; [exact V1 | lia].
      - exact Hkeep. }
    rewrite Z1. destruct a0x as [e|]; [apply CH2.regs_ok_upd_same; [exact HR1 | exact Ha0] | exact HR1].
  - (* [comment removed for export] *)
    pose proof HA' as (_ & _ & _ & _ & (cr1 & LK1 & HH1 & _) & _).
    pose proof HA2 as (g2 & M0c2 & _ & ((_ & _ & _ & _ & (cr2 & LK2 & HH2 & _) & _) & _)).
    assert (IB1 : incl (CH2.den E' BLk ++ LBo) (CHA.curB (LBr g) BLS i E)).
    { unfold CHA.curB, LBr. rewrite <- HdenB. intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; apply in_or_app;
        [left; exact (CH2.blk_in_den E' _ _ Z3 b Hb0) | right; apply in_or_app; left; exact Hb0]. }
    assert (IF1 : incl (CHA.denF sp0 E' FLk ++ FFrest) (CHA.curF FFrest sp0 FFS i E)).
    { unfold CHA.curF. rewrite <- HdenF. intros f Hf0. apply in_app_or in Hf0 as [Hf0|Hf0]; apply in_or_app; [left; exact (CHA.frm_in_den sp0 E' _ _ Z6 f Hf0) | right; exact Hf0]. }
    assert (IB2 : incl (CH2.den E' BLk ++ LBo) (CHA.curB (LBr g2) BLS j E2)).
    { unfold CHA.curB, LBr. rewrite <- (CH2.den_agree nx E' E2 BLk Hag2 Z2). intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; apply in_or_app;
        [left; exact (CH2.blk_in_den E2 _ _ Z4 b Hb0) | right; apply in_or_app; left; exact Hb0]. }
    assert (IF2 : incl (CHA.denF sp0 E' FLk ++ FFrest) (CHA.curF FFrest sp0 FFS j E2)).
    { unfold CHA.curF. rewrite <- (CHA.denF_agree sp0 nx E' E2 FLk Hag2 Z5). intros f Hf0. apply in_app_or in Hf0 as [Hf0|Hf0]; apply in_or_app; [left; exact (CHA.frm_in_den sp0 E2 _ _ Z7 f Hf0) | right; exact Hf0]. }
    unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in Z8. specialize (Z8 Y HY).
    destruct (CC.has_cell news Y) eqn:Hn; [apply CC.has_cell_In in Hn; exact (Hnews Y Hn HY)|]. rename Z8 into Hk.
    unfold CHA.kept_chk in Hk. apply andb_prop in Hk as [Hk K3]. apply andb_prop in Hk as [K1 K2]. apply CC.has_cell_In in K1.
    pose proof (proj1 (Forall_forall _ _) HK _ K1) as HY0.
    assert (GG : know_ok (hl_segs L) E' (CCA.vis A2 model2 M2) [Y]).
    { apply (CHA.ahpres_know L ar C HI HIok LY_img NF E0 LBo FFrest sp0 d Wo STK SCR_pos NF32 SP0 Wo_ok CRS_ok WRS_ok IMG_ok SCELLS GLO GHI SCELLS_ok GOT_ok
               E' A A2 M1 model1 M2 model2 BLk FLk LBk FFk _ _ _ _ _ _ _ _ (SR.ps_cells ps) scr (CH2.ci_csp ci0) Wc wregs [Y]
               HagE' HH1 HH2 IB1 IF1 IB2 IF2 HiBk HiFk Hc1 Hs0 Hc2 HWc HK);
        [constructor; [exact HY0 | constructor] | cbn [forallb]; rewrite K2; reflexivity | exact HP]. }
    assert (G2 : know_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) [Y]).
    { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 _ [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite K3; reflexivity | exact GG]. }
    inversion G2; assumption.
Qed.

(* [comment removed for export] *)
Hypothesis KNIL : K [].
Lemma callee_leafV : forall g M0c pc scr ng BLk wregs news a0x dc i c ps j cj ci,
  okV M0c ->
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = pc ->
  CHA.frames_eqb (nth j FFS []) (nth i FFS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> ambXV g M0c i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS ambV K FPI (CC.meas c E) ->
    (forall cr LK,
       CHA.common_facts L ar HI NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr ng c ps cj ci i E E' R' A M1 model1 ->
       ri_inv HI (CHA.curB (LBr g) BLS i E) (CHA.curF FFrest sp0 FFS i E) LK cr A M1 (vml_of model1) -> incl LK LK0 -> CredV g i E cr ->
       exists (Pre : bvmap 5 word -> mem -> Prop)
              (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       CBA.cps_asanG L ar HI FPI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr (CHA.curB (LBr g) BLS i E) (CHA.curF FFrest sp0 FFS i E) LK cr A dc Pre Post
       /\ Pre R' M1
       /\ forall R2 M2 model2 LB' cr' LBk Wc LK2 A2,
            Post R' M1 R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
            CHA.ahpres L ar LBk (CHA.curF FFrest sp0 FFS i E) (sp0 + CH2.ci_csp ci) scr Wc M1 M2 ->
            model_rt model1 model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
            ri_inv HI LB' (CHA.curF FFrest sp0 FFS i E) LK2 cr' A2 M2 (vml_of model2) ->
            exists (ghosts : list word) (g' : G), length ghosts = ng /\
              let E2 := CH2.retEx E' (CH2.ci_nx ci) ghosts R2 in
              match a0x with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
              incl (CH2.den E' BLk ++ LBo) LBk /\
              (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CHA.in_reg E' r a) /\
              (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LBo FFrest sp0 SCR W a) /\
              ri_inv HI (CHA.curB (LBr g') BLS j E2) (CHA.curF FFrest sp0 FFS i E) LK2 cr' A2 M2 (vml_of model2) /\ CredV g' j E2 cr' /\ XIv g' j E2 A2 M2 model2 /\
              (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros g M0c pc scr ng BLk wregs news a0x dc i c ps j cj ci OKV Hcj Hchk Hpc Hfeq Hdc fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH USER.
  destruct (custom_retV g M0c scr ng BLk (nth i FFS []) wregs news a0x i c ps j cj ci OKV Hcj Hchk E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  destruct (USER cr LK CF HH1 HLK1 HC1) as (Pre & Post & SPEC & HPre & HPost).
  apply CHA.frames_eqb_eq in Hfeq.
  assert (FV : CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d scr ng c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z5]. exact Z5. }
  rewrite Hpc.
  apply (SPEC fx' R' M1 model1 K HH1 Hmo1 KNIL HFP Hra Hraok Hsp Htp Hstk); [apply (CHA.ffroom_le _ _ _ _ HRoom1); exact Hdc | exact Hffrs | exact HPre |].
  intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (ghosts & g' & Hlen & Ha0 & HiB & HWr & HWk & HHj & HCj & HXj & Hnews).
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) ghosts R2) in *.
  pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) ghosts R2 : env_agree (CH2.ci_nx ci) E' E2) as Hag2.
  assert (HFj : CHA.curF FFrest sp0 FFS j E2 = CHA.curF FFrest sp0 FFS i E).
  { unfold CHA.curF. rewrite Hfeq. rewrite (CHA.denF_agree sp0 _ E' E2 _ Hag2 FV). rewrite HdenF. reflexivity. }
  assert (HagEE2 : env_agree NF E E2).
  { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
  assert (NEWA : okV M2 /\ aambV g' M2 j E2 A2 M2 model2).
  { apply (amb_calleeV g g' M0c i j E E2 A A2 M1 M2 model1 model2 (CH2.ci_csp ci) scr LBk (CHA.curF FFrest sp0 FFS i E) Wc cr' LK2 OKV HA' HP).
    - intros b Hb. apply HiB. apply in_or_app. right. exact Hb.
    - unfold CHA.curF. apply incl_appr, incl_refl.
    - exact Hc1.
    - exact Hs0.
    - exact Hc2.
    - exact HWk.
    - exact Hrt2.
    - exact Hmo2.
    - exact HA2.
    - rewrite HFj. exact HHj.
    - exact (incl_tran HLK2 HLK1).
    - exact HagEE2.
    - exact HCj.
    - rewrite HFj, Hfeq.
      pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHj)) as [_ ND].
      exact (CHA.ffroom_sub NF 0 NF32 _ _ _ _ HRoom1 HLK2 ND). }
  destruct NEWA as [OKV2 HAj].
  apply (CONT fx2 R2 A2 M2 model2 ghosts LBk (CHA.curF FFrest sp0 FFS i E) Wc Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HP HiB).
  - unfold CHA.curF. rewrite HdenF. apply incl_refl.
  - exact HWr.
  - exact (ambV_intro g' M2 j E2 A2 M2 model2 OKV2 (conj HAj HXj)).
  - exact Hnews.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ri_perm : forall LB LB' FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> Permutation LB LB' -> ri_inv HI LB' FF LK cr A M V.
Proof.
  intros LB LB' FF LK cr A M V HH HP. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [ND1 ND2].
  apply (PmHeapIfaceA.aio_perm _ _ _ _ _ HIok LB LB' FF FF LK cr A M V HH).
  - intros b. split; [apply (Permutation_in b HP) | apply (Permutation_in b (Permutation_sym HP))].
  - apply base.NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst HP)). apply base.NoDup_ListNoDup. exact ND1.
  - intros f. split; intros X; exact X.
  - exact (CBA.nodup_ff FF LK ND2).
Qed.
Lemma perm_ghost_out : forall (own lo g1 g2 : list (Z * Z)) b, Permutation (own ++ lo ++ g1 ++ b :: g2) (b :: own ++ lo ++ g1 ++ g2).
Proof. intros own lo g1 g2 b. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma perm_ghost_in : forall (own lo g1 g2 : list (Z * Z)) b, Permutation (b :: own ++ lo ++ g1 ++ g2) (own ++ lo ++ g1 ++ b :: g2).
Proof. intros own lo g1 g2 b. apply Permutation_sym. apply perm_ghost_out. Qed.
Lemma ri_ghost_out : forall own g1 g2 b FF LK cr A M V, ri_inv HI (own ++ LBo ++ g1 ++ b :: g2) FF LK cr A M V -> ri_inv HI (b :: own ++ LBo ++ g1 ++ g2) FF LK cr A M V.
Proof. intros own g1 g2 b FF LK cr A M V HH. exact (ri_perm _ _ FF LK cr A M V HH (perm_ghost_out own LBo g1 g2 b)). Qed.
Lemma ri_ghost_in : forall own g1 g2 b FF LK cr A M V, ri_inv HI (b :: own ++ LBo ++ g1 ++ g2) FF LK cr A M V -> ri_inv HI (own ++ LBo ++ g1 ++ b :: g2) FF LK cr A M V.
Proof. intros own g1 g2 b FF LK cr A M V HH. exact (ri_perm _ _ FF LK cr A M V HH (perm_ghost_in own LBo g1 g2 b)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable TAGS : list (list CC.tag).

(* [comment removed for export] *)
Definition leaf_okV (g : G) (M0c : mem) (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : Prop :=
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> ambXV g M0c i E A M model -> FPI fx' ->
    env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    CCA.IH (hl_segs L) CPS ambV K FPI (CC.meas c E) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.

(* [comment removed for export] *)
Lemma leaf_okV_of : forall g M0c i c ps, okV M0c ->
  CCA.leaf_ok (hl_segs L) CPS (ambXV g M0c) K FPI i c ps -> leaf_okV g M0c i c ps.
Proof.
  intros g M0c i c ps OKV H fx' E R A M model E' R' M1 model1 HAt HA HFP Hag HLF HIH.
  exact (H fx' E R A M model E' R' M1 model1 HAt HA HFP Hag HLF (ih_of g M0c _ OKV HIH)).
Qed.

Theorem cert_soundV :
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound (hl_segs L) c) ->
  CC.tags_chk CPS TAGS NF = true ->
  CHA.heap_chkA NF d BLS FFS CPS TAGS = true ->
  (* [comment removed for export] *)
  (forall g i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E E' R' M M' cr, env_agree NF E0 E ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> CredV g i E cr -> CredV g j (CC.env_over NF s E') cr) ->
  (forall g M0c, okV M0c -> forall i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E R E' R' A M model M1 model1,
       CCA.AtV (hl_segs L) c E R A M model -> aambV g M0c i E A M model ->
       env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> XIv g i E A M model -> XIv g j (CC.env_over NF s E') A M1 model1) ->
  (* [comment removed for export] *)
  (forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> forall g M0c, okV M0c -> leaf_okV g M0c i c ps) ->
  forall i c (fx : FPState) E R A M model,
    nth_error CPS i = Some c -> CCA.AtV (hl_segs L) c E R A M model -> ambV i E A M model -> FPI fx ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros FPM PLANS TCHK HCHK CG XG LEAVES.
  apply (CCA.cutcert_sound_tagged (hl_segs L) CPS TAGS NF ambV K FPI FPM PLANS TCHK ambV_model LY_nowrap).
  - intros i c tags k ps j s Hc Htg Hps Ht.
    assert (IL : CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s)) by (exists tags; repeat split; assumption).
    pose proof (CH2.leaves_all_sound CPS TAGS (CHA.leaf_chkA NF d BLS FFS) HCHK i c k ps _ IL) as X. cbn [CHA.leaf_chkA] in X.
    intros E R A M model E' R' M1 model1 HAt (g & M0c & OKV & HA & HXI) Hag HLF.
    exists g, M0c. split; [exact OKV|]. split.
    + exact (CHA.goto_amb L ar C HI HIok LY_img LY_ro NF E0 M0c model0 A0 (LBr g) FFrest LK0 sp0 d W Wo BLS FFS (CredV g) D0 STK SCR_pos NF32 SP0 Wo_incl (Wo_okV g) WRS_ok
               i c ps j s X (CG g i c k ps j s IL) E R A M model E' R' M1 model1 HAt HA Hag HLF).
    + exact (XG g M0c OKV i c k ps j s IL E R E' R' A M model M1 model1 HAt HA Hag HLF HXI).
  - intros i c tags k ps pc Hc Htg Hps Ht fx' E R A M model E' R' M1 model1 HAt (g & M0c & OKV & HAX) HFP Hag HLF HIH.
    assert (IL : CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc)) by (exists tags; repeat split; assumption).
    exact (LEAVES i c k ps pc IL g M0c OKV fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
Qed.

End V.
End CHV.
