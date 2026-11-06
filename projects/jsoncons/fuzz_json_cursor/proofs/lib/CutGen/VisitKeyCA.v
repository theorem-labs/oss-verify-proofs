(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutPureA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_vis_key_casan_T Cut_vis_key_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_vis_key_casan.
Module GT := Cut_vis_key_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module VKeyA.
Definition PC : Z := 829724.
Definition RETPC : Z := 829928.
Definition RETS : list Z := [RETPC].
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb pc RETPC && Nat.eqb i 0 && CL.ps_reg_is ps 10 (ELit 1)
                     && has (SR.ps_cells ps) (KWord (SA (EVar 10) 8) 8 (ELit 4097)) && has (SR.ps_cells ps) (KWord (SA (EVar 10) 32) 8 (EVar 32)) && has (SR.ps_cells ps) (KWord (SA (EVar 10) 40) 8 (EVar 33)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vmc_refl. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk GT.NF G.HDECL RETS) = true. Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vmc_refl. Qed.
Lemma ret_at : forall pc, In pc RETS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.
End VKeyA.

Section VisitKeyOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Abbreviation IC := PMLA.C_casan.
Definition hid (P : Prop) : Prop := P.

Theorem visit_key_ok : PMSA.visit_key_specA L ar HI IC VKeyA.PC.
Proof.
  unfold PMSA.visit_key_specA, PMSA.visit_text_specA.
  intros LB FF LK cr A V sv p n sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & HVIS & HOV & HSTKSH & Hsv & Sv8 & Svsh & Hp & Hn & APV) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.VIS_SCR, PMSA.fobj, PMSA.vis_at, PMLA.fobj, PMLA.vis_at, PMSA.acobj, PMSA.u64, PMLA.apart in *.
  destruct HOV as (Vfr & V8 & Vsh). destruct HVIS as (_ & VDEF). change (48 / 8) with 6 in Vsh.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF V 48 RFx Vfr ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in Q5. change (hid (V + 48 <= hl_img_lo L \/ hl_img_hi L <= V)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  pose proof (CL5A.acobj_rng L ar LB FF sp sv 16 RFx ltac:(clear - S2; lia) Hsv ltac:(clear; lia)) as (T1 & T2 & T3 & T4 & T5). unfold BIGSHADOW_LO, BIGSHADOW_HI in T3.
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [p; n] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 CL SP1; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (V11 : ev E0 11 = Z_to_bv 64 sv) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U11 : bv_unsigned (ev E0 11) = sv) by (rewrite V11; apply u64_of_Z; clear - T1 T2; lia).
  assert (V32 : ev E0 32 = Z_to_bv 64 p) by reflexivity. assert (V33 : ev E0 33 = Z_to_bv 64 n) by reflexivity.
  assert (SCRV : CH.hd_scr G.HDECL = 2624) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (W := [(V + 8, 40)]).
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ V 48 a RFx Vfr ltac:(clear - Hin; lia)). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (V + 8, 40). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  rewrite <- LS in FPM.
  change VKeyA.PC with (CC.cp_pc G.cp0).
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i _ _ _ _ => i = 0%nat) R r EV Hra Hraok VKeyA.RETS FPM) with (i := 0%nat).
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact VKeyA.heap_ok.
  - exact VKeyA.pure_ok.
  - rewrite LS. exact VKeyA.ret_at.
  - intros i c k ps j s IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ VKeyA.leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  -
    intros i c k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ VKeyA.leaf_ok _ _ _ _ _ IL) as X. unfold VKeyA.leaf_chk in X.
    repeat (apply andb_prop in X as [X _]). apply Z.eqb_eq in X. subst pc. discriminate Hne.
  -
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof (CH2.leaves_all_sound _ _ _ VKeyA.leaf_ok _ _ _ _ _ IL) as X. unfold VKeyA.leaf_chk in X.
    apply andb_prop in X as [X Y40]. apply andb_prop in X as [X Y32]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [_ Yi]. apply Nat.eqb_eq in Yi. subst i.
    apply CC.has_cell_In in Y8, Y32, Y40.
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 0%nat E A1 M' m' HA') as Hoff.
    assert (CELLS : forall X0, In X0 (SR.ps_cells ps) -> kentry_ok (hl_segs L) E' (mrestrict (ahid A1 m') M') X0)
      by (intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)).
    assert (W10 : bv_unsigned (ev E' 10) = V) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
    assert (W32 : ev E' 32 = Z_to_bv 64 p) by (rewrite <- (proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); exact V32).
    assert (W33 : ev E' 33 = Z_to_bv 64 n) by (rewrite <- (proj1 HagE' 33%nat) by (apply Nat.ltb_lt; reflexivity); exact V33).
    pose proof HP as (_ & _ & HP3).
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB W LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split.
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10). reflexivity. }
    split; [|repeat split; reflexivity].
    assert (EDEF : L5.defined M' (V + 8) 40).
    { intros j Hj. apply (HP3 (V + 8 + j)); [clear - Hj Q3 Q6; lia | |].
      - exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp 2624 V 48 (V + 8 + j) Vfr ltac:(clear - Hj; lia))).
      - replace (V + 8 + j) with (V + (8 + j)) by (clear; lia). apply VDEF. clear - Hj; lia. }
    assert (EFL : L5.u64_at (hl_segs L) M' (V + 8) 4097).
    { pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (V + 8) (CELLS _ Y8) ltac:(ev_start)) as G0.
      apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite u64_of_Z in G0 by (clear; lia). exact G0. }
    unfold PMCUR.ev_at. split; [exact EDEF|]. split; [exact EFL|].
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (V + 32) (CELLS _ Y32) ltac:(ev_start)) as G0.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. unfold L5.u64_at in G0. rewrite Z_to_bv_bv_unsigned in G0.
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (V + 40) (CELLS _ Y40) ltac:(ev_start)) as G1.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G1. unfold CL5A.uv in G1. cbn [edenot] in G1. rewrite W33 in G1. unfold L5.u64_at in G1. rewrite Z_to_bv_bv_unsigned in G1.
    unfold PMSA.u64, L5.u64_at. split; [exact G0 | exact G1].
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VV : CL5A.visr (ahid A model) V 48).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 V 48 (V + k) RFx Vfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSV : forall a, in_shadow_of V 48 a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 V 48 a RFx Vfr ltac:(clear; lia) Ha) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 2624) 2624).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 2624) 2624) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DV : L5.defined Mv (V + 8) 40) by (apply (CL5A.defined_vis _ M _ _ (CL5A.visr_sub _ V 48 (V + 8) 40 VV ltac:(clear; lia) ltac:(clear; lia))); intros j Hj; replace (V + 8 + j) with (V + (8 + j)) by (clear; lia); apply VDEF; clear - Hj; lia).
    assert (UVV : CL5A.uv E0 (EVar 10) = V) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    assert (SVV : CL5A.visr (ahid A model) sv 16).
    { intros k Hk. destruct Hsv as [Hsv|(Hs1 & Hs2)].
      - destruct (CL5A.infr_wok L ar LB FF sp 0 sv 16 (sv + k) RFx Hsv ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3).
      - apply CLV; [clear - Hk T1 T2; lia | right; left; split; [clear - Hk Hs1 Hs2 S2 S3 CL SP1; lia | clear; lia] |].
        apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk T3. lia. }
    assert (SVSH : forall j, 0 <= j < 2 -> ahid A model (Z_to_bv 64 (S sv + j)) = false).
    { intros j Hj. destruct Hsv as [Hsv|(Hs1 & Hs2)].
      - destruct (CL5A.infr_sh_wok L ar LB FF sp 0 sv 16 (S sv + j) RFx Hsv ltac:(clear; lia) (CL5A.shreg_in_shadow sv 2 (S sv + j) Sv8 ltac:(clear; lia) ltac:(unfold S, SB; clear - Hj; lia))) as (G1 & G2 & G3).
        exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3).
      - pose proof (CHA.shadow_range sv 16 (S sv + j) T1 ltac:(clear; lia) T2 (CL5A.shreg_in_shadow sv 2 (S sv + j) Sv8 ltac:(clear; lia) ltac:(unfold S, SB; clear - Hj; lia))) as SRa.
        apply CLV; [clear - SRa; lia | do 4 right; left; apply (CL5A.in_shadow_mono sv 16 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar)); [clear - Hs1 S2 S3 CL SP1; lia | clear - T2; lia | clear; lia | exact (CL5A.shreg_in_shadow sv 2 (S sv + j) Sv8 ltac:(clear; lia) ltac:(unfold S, SB; clear - Hj; lia))] |].
        intros _. unfold S. clear - Hj Hs2 T2 SP1. lia. }
    assert (UVS : CL5A.uv E0 (EVar 11) = sv) by (unfold CL5A.uv; cbn [edenot]; exact U11).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kunk_intro with (A := V + 8) (N := 40); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DV].
    + eapply CL5.kwr_intro with (A := V + 8) (N := 40); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DV].
    + eapply CL5.krange_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact V8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 6 V UVV); [clear; lia | clear - Q3 Q6; lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VSV; apply (CL5A.shreg_in_shadow V 6); [exact V8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Vsh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := V) (N2 := 48); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in Q5; clear - Q5; lia].
    + eapply CL5.kunk_intro with (A := sp - 2624) (N := 2624); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 2624) (N := 2624); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 2624) (N1 := 2624) (A2 := V) (N2 := 48); [ev_start | reflexivity | ev_start | reflexivity | clear - Q4 S2; lia].
    + eapply CL5.kword64_intro with (A := sv) (z := p); [ev_start | clear - T1; lia | clear - T2; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - T1; lia | clear - T2; lia | exact (CL5A.visr_sub _ sv 16 sv 8 SVV ltac:(clear; lia) ltac:(clear; lia)) | exact Hp].
    + eapply CL5.kword64_intro with (A := sv + 8) (z := n); [ev_start | clear - T1; lia | clear - T2; lia | exact V33 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - T1; lia | clear - T2; lia | exact (CL5A.visr_sub _ sv 16 (sv + 8) 8 SVV ltac:(clear; lia) ltac:(clear; lia)) | exact Hn].
    + eapply CL5.krange_intro with (v := sv); [lin_eval; rw_atoms; clear; lia | clear - T1 T2; lia | clear - T1 T2 T4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sv); [lin_eval; rw_atoms; clear; lia | clear - T1 T2; lia | clear; lia | exact Sv8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 sv UVS); [clear; lia | clear - T1 T2; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (SVSH j Hj) | exact (Svsh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := sv) (N2 := 16); [reflexivity | reflexivity | ev_start | reflexivity | clear - T3; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 2624) (N1 := 2624) (A2 := sv) (N2 := 16); [ev_start | reflexivity | ev_start | reflexivity |].
      destruct Hsv as [Hsv|(Hs1 & Hs2)]; [destruct (CL5A.infr_rng L ar LB FF sv 16 RFx Hsv ltac:(clear; lia)) as (_ & _ & _ & Z4 & _); clear - Z4 S2; lia | clear - Hs1; lia].
    + eapply CL5.kdisj_intro with (A1 := sv) (N1 := 16) (A2 := V) (N2 := 48); [ev_start | reflexivity | ev_start | reflexivity | clear - APV; lia].
  - reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End VisitKeyOk.

