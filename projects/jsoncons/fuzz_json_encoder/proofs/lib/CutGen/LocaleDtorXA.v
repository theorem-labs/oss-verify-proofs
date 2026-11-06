(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutPureA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_locale_dtor_xasan_T Cut_locale_dtor_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module G := Cut_locale_dtor_xasan.
Module GT := Cut_locale_dtor_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module LDA.
Definition IMP : Z := 6934032.     (* [comment removed for export] *)
Definition RETS : list Z := [1212668].      (* [comment removed for export] *)
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => Z.eqb pc 1212668
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk GT.NF G.HDECL RETS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : forall pc, In pc RETS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.
End LDA.

Section LocaleDtorOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_xasan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition E0of (R : bvmap 5 word) : env := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => []).

(* [comment removed for export] *)
Definition locale_dtor_specA' (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    PMSA.cps_asan L ar HI pc r sp 0 LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ 0 <= o < 2 ^ 62 /\ PMSA.u64 L M o (PMLA.CLASSIC_IMP IC) /\ PMSA.acobj ar FF sp o 8)
      (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

Theorem locale_dtor_ok : PMSA.locale_dtor_specA L ar HI IC 1212636.
Proof.
  intros LB FF LK cr A o sp r. unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & HO & LD & Hob) Hcont.
  unfold PMSA.a0, PMSA.u8, PMSA.u64, PMSA.acobj in *. change (PMLA.CLASSIC_IMP IC) with LDA.IMP in *.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  set (E0 := E0of R).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 0) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w (@nil L5.range) -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a [] _).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w (@nil L5.range) /\ L5.in_rng w a))
    by (intros rg []).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
  assert (VO : CL5A.visr (ahid A model) o 8).
  { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp 0 o 8 (o + k) RFx CSP Hob ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  set (Mv := CCA.vis A model M).
  rewrite <- LS in FPM. change 1212636 with (CC.cp_pc G.cp0).
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK cr sp G.HDECL [] [] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i _ _ _ _ => i = 0%nat) R r EV Hra Hraok LDA.RETS FPM) with (i := 0%nat).
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact LDA.heap_ok.
  - exact LDA.pure_ok.
  - rewrite LS. exact LDA.ret_at.
  - intros i c k ps j s IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ LDA.leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ LDA.leaf_ok _ _ _ _ _ IL) as X. unfold LDA.leaf_chk in X.
    apply Z.eqb_eq in X. subst pc. discriminate Hne.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB [] LK1 A1 HFP1); [repeat split; reflexivity | exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
  - reflexivity.
  - (* [comment removed for export] *)
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; lia | lia | lia].
    + eapply CL5.kword64_intro with (A := o) (z := LDA.IMP); [ev_start | lia | lia | reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [lia | lia | exact VO | exact LD].
  - reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End LocaleDtorOk.
Print Assumptions locale_dtor_ok.
