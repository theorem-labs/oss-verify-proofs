(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutPureA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_syscat_cboth_T Cut_syscat_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_syscat_cboth.
Module GT := Cut_syscat_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module SCA.
Definition GD : Z := 6882752.
Definition OBJ : Z := 1412240.
Definition RETS : list Z := [1007636].
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb pc 1007636 && CL.ps_reg_is ps 10 (ELit OBJ) && has (SR.ps_cells ps) (KWord (SA (ELit 0) GD) 1 (ELit 1)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vmc_refl. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk GT.NF G.HDECL RETS) = true. Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vmc_refl. Qed.
Lemma ret_at : forall pc, In pc RETS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.
Lemma guard_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GD) 2 = true. Proof. vmc_refl. Qed.

Lemma writable_static : forall (M : word -> option byte) A (N : nat), StreamSim.wseg_ok RSEGS (Z_to_bv 64 A) N = true -> 0 <= A < 2 ^ 64 -> A + Z.of_nat N <= 2 ^ 64 -> L5.writable RSEGS M A (Z.of_nat N).
Proof.
  intros M A N H HA HN d k Hd Hk. destruct k as [|k]; [reflexivity|].
  apply (store_ok_sub RSEGS M (Z_to_bv 64 A) (Z_to_bv 64 (A + d)) N (Datatypes.S k)); [rewrite u64_of_Z by lia; lia | apply store_ok_wseg; exact H | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia].
Qed.
End SCA.

Section SyscatOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition E0of (R : bvmap 5 word) : env := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => []).

Lemma syscat_run : forall (i0 : nat) (c0 : CC.cutpoint) LB FF LK cr A sp r dd (fx : FPState) R M model K,
  nth_error G.CPS i0 = Some c0 ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> PMSA.fp_ok fx ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
  CHA.astk ar M sp 128 -> CHA.ffroom FF LK dd -> CHA.ffrs FF sp ->
  PMSA.cstatic L SCA.GD 2 ->
  (bv_unsigned (ev (E0of R) 2) = sp -> 0x7fff7f800000 + 128 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
     CL5A.visr (ahid A model) SCA.GD 2 -> L5.defined (CCA.vis A model M) (sp - 128) 128 -> CCA.AtV (hl_segs L) c0 (E0of R) R A M model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
          (LK' : list fframe) (A' : list (Z * Z)),
      PMSA.fp_ok fx' -> (getr R' 10%bv = Z_to_bv 64 SCA.OBJ /\ L5.u8_at (hl_segs L) M' SCA.GD 1 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(SCA.GD, 2)]) -> regs_preserved R R' ->
      CHA.ahpres L ar LBk FF sp 128 W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom (hl_segs L))) model') K) ->
  srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c0)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros i0 c0 LB FF LK cr A sp r dd fx R M model K Hc0 HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hcs HAT Hcont.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  set (E0 := E0of R).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 128) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (GCL : forall a, SCA.GD <= a < SCA.GD + 2 -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. destruct (Hcs a Ha) as (I1 & I2 & I3). split; [unfold SCA.GD in Ha; lia|]. split.
    - right; right; left. split; [exact I1|]. intros [X|X]; [exact (I2 X) | exact (I3 X)].
    - apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). left. unfold BIGSHADOW_LO in *. lia. }
  assert (WOK : forall (w : L5.range) (a : Z), In w [(SCA.GD, 2)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (GCL a Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(SCA.GD, 2)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite !u64_of_Z in Ha by lia. exists (SCA.GD, 2). split; [left; reflexivity | unfold L5.in_rng, SCA.GD; cbn [fst snd]; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (VG : CL5A.visr (ahid A model) SCA.GD 2).
  { intros k Hk. destruct (GCL (SCA.GD + k) ltac:(lia)) as (G1 & G2 & G3). exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp _ _ HH G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VS : CL5A.visr (ahid A model) (sp - 128) 128).
  { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 _ HH); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
  rewrite <- LS in FPM.
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK cr sp G.HDECL [(SCA.GD, 2)] [(SCA.GD, 2)] dd STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i _ _ _ _ => i = i0) R r EV Hra Hraok SCA.RETS FPM) with (i := i0).
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SCA.heap_ok.
  - exact SCA.pure_ok.
  - rewrite LS. exact SCA.ret_at.
  - intros i c k ps j s IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ SCA.leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  -
    intros i c k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ SCA.leaf_ok _ _ _ _ _ IL) as X. unfold SCA.leaf_chk in X.
    apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply Z.eqb_eq in X. subst pc. discriminate Hne.
  -
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL [(SCA.GD, 2)] (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) dd i E A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB [(SCA.GD, 2)] LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    pose proof (CH2.leaves_all_sound _ _ _ SCA.leaf_ok _ _ _ _ _ IL) as X. unfold SCA.leaf_chk in X.
    apply andb_prop in X as [X Y2]. apply andb_prop in X as [_ Y1]. apply CC.has_cell_In in Y2.
    pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
    assert (CELLS : forall X0, In X0 (SR.ps_cells ps) -> kentry_ok (hl_segs L) E' (mrestrict (ahid A1 m') M') X0) by (intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0)).
    split; [|split; [|repeat split; reflexivity]].
    + replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ HLFv Y1). reflexivity.
    + pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ SCA.GD (CELLS _ Y2) ltac:(ev_start)) as G0. exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ G0).
  - exact Hc0.
  - apply (HAT U2 ltac:(clear - S2 S3 CL SP1; lia) S1 VG). apply (CL5A.defined_vis _ M _ _ VS). exact S5.
  - reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.

Theorem system_category_ok : PMSA.system_category_specA L ar HI PMLA.C_cboth 1007612.
Proof.
  intros LB FF LK cr A sp r. unfold PMSA.cps_asan. intros fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (RO & Hcs & CASE) Hcont.
  unfold PMSA.a0, PMSA.u8 in *. pose proof (L5A.aly_segs L C LAY) as LS.
  change (PMLA.SYSCAT_GUARD PMLA.C_cboth) with SCA.GD in *. change (PMLA.OBJ_SYSTEM_CATEGORY PMLA.C_cboth) with SCA.OBJ in *.
  destruct CASE as [[C0 C1] | C0].
  -
    change 1007612 with (CC.cp_pc G.cp1).
    apply (syscat_run 1%nat G.cp1 LB FF LK cr A sp r 0 fx R M model K eq_refl HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hcs); [|exact Hcont].
    intros U2 SR S1 VG DS. split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp1]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kunk_intro with (A := sp - 128) (N := 128); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 128) (N := 128); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia | exact S1].
    + eapply CL5A.kword8_intro with (A := SCA.GD) (z := 0); [ev_start | unfold SCA.GD; lia | unfold SCA.GD; lia | reflexivity | lia |].
      apply (CL5A.u8_vis (hl_segs L)); [unfold SCA.GD; lia | unfold SCA.GD; lia | exact (CL5A.visr_sub _ SCA.GD 2 SCA.GD 1 VG ltac:(lia) ltac:(lia)) | exact C0].
    + eapply CL5A.kword8_intro with (A := SCA.GD + 1) (z := 0); [ev_start | unfold SCA.GD; lia | unfold SCA.GD; lia | reflexivity | lia |].
      apply (CL5A.u8_vis (hl_segs L)); [unfold SCA.GD; lia | unfold SCA.GD; lia | exact (CL5A.visr_sub _ SCA.GD 2 (SCA.GD + 1) 1 VG ltac:(lia) ltac:(lia)) | exact C1].
    + eapply CPA.kwr_of_writable with (A := SCA.GD) (N := 2); [ev_start | reflexivity | unfold SCA.GD; lia | unfold SCA.GD; lia |].
      rewrite LS. exact (SCA.writable_static _ SCA.GD 2 SCA.guard_wr ltac:(unfold SCA.GD; lia) ltac:(unfold SCA.GD; lia)).
  -
    change 1007612 with (CC.cp_pc G.cp0).
    apply (syscat_run 0%nat G.cp0 LB FF LK cr A sp r 0 fx R M model K eq_refl HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hcs); [|exact Hcont].
    intros U2 SR S1 VG DS. split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kunk_intro with (A := sp - 128) (N := 128); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 128) (N := 128); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia | exact S1].
    + eapply CL5A.kword8_intro with (A := SCA.GD) (z := 1); [ev_start | unfold SCA.GD; lia | unfold SCA.GD; lia | reflexivity | lia |].
      apply (CL5A.u8_vis (hl_segs L)); [unfold SCA.GD; lia | unfold SCA.GD; lia | exact (CL5A.visr_sub _ SCA.GD 2 SCA.GD 1 VG ltac:(lia) ltac:(lia)) | exact C0].
Qed.
End SyscatOk.

