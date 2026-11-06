(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutPureA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_locale_xboth_T Cut_locale_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module G := Cut_locale_xboth.
Module GT := Cut_locale_xboth_T.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

Module LCA.
Definition GG : Z := 6947520.      (* [comment removed for export] *)
Definition GP : Z := 6947512.      (* [comment removed for export] *)
Definition IMP : Z := 6948560.     (* [comment removed for export] *)
Definition RETS : list Z := [1227224].      (* [comment removed for export] *)
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb pc 1227224 && has (SR.ps_cells ps) (KWord (SA (EVar 10) 0) 8 (ELit IMP)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk GT.NF G.HDECL RETS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : forall pc, In pc RETS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.
End LCA.

Section LocaleOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_xboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.              (* [comment removed for export] *)
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition E0of (R : bvmap 5 word) : env := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => []).

Theorem locale_ctor_later_ok : PMSA.locale_ctor_later_specA L ar HI IC 1227132.
Proof.
  intros LB FF LK cr A o sp r. unfold PMSA.cps_asan. intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & (LD1 & LD2) & RO & Hob & Ho8 & DO) Hcont.
  unfold PMSA.a0, PMSA.u8, PMSA.u64, PMSA.acobj in *.
  change (PMLA.GLOC_GUARD IC) with LCA.GG in *. change (PMLA.GLOC_PTR IC) with LCA.GP in *. change (PMLA.CLASSIC_IMP IC) with LCA.IMP in *.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.acobj_rng L ar LB FF sp o 8 RFx CSP Hob ltac:(lia)) as (O3 & O6 & O5 & O1 & O4).
  (* [comment removed for export] *)
  assert (FOOTCS : forall a, PMLA.in_foot IC a -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Hf. assert (RG : 65536 <= a < 7094272) by (destruct Hf as (iv & Hiv & Hr); cbn in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]); destruct Hiv).
    split; [clear - RG; lia|]. split; [right; right; left; rewrite ILO, IHI; split; [clear - RG; lia | exact (FOOTC a Hf)]|].
    apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). left. unfold BIGSHADOW_LO. clear - RG. lia. }
  assert (PTKF : forall a, LCA.GG <= a < LCA.GG + 1 \/ LCA.GP <= a < LCA.GP + 8 -> PMLA.in_foot IC a).
  { intros a Ha. pose proof PMTA.C_xboth_wf as [_ _ _ _ T5 T6 _ _ _ _]. unfold PMTA.cell_in_foot in *.
    destruct Ha as [Ha|Ha]; [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha]. }
  set (E0 := E0of R).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 64) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w [(o, 8)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.acobj_wok L ar LB FF sp _ o 8 a RFx CSP Hob Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(o, 8)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
  assert (VO : CL5A.visr (ahid A model) o 8).
  { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 8 (o + k) RFx CSP Hob ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VGG : CL5A.visr (ahid A model) LCA.GG 1).
  { intros k Hk. destruct (FOOTCS (LCA.GG + k) (PTKF (LCA.GG + k) ltac:(left; clear - Hk; lia))) as (G1 & G2 & G3). exact (CLV _ _ G1 G2 G3). }
  assert (VGP : CL5A.visr (ahid A model) LCA.GP 8).
  { intros k Hk. destruct (FOOTCS (LCA.GP + k) (PTKF (LCA.GP + k) ltac:(right; clear - Hk; lia))) as (G1 & G2 & G3). exact (CLV _ _ G1 G2 G3). }
  assert (VS : CL5A.visr (ahid A model) (sp - 64) 64).
  { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
  set (Mv := CCA.vis A model M).
  assert (DS : L5.defined Mv (sp - 64) 64) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
  assert (DOv : L5.defined Mv o 8) by (apply (CL5A.defined_vis _ M _ _ VO); exact DO).
  rewrite <- LS in FPM. change 1227132 with (CC.cp_pc G.cp0).
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK cr sp G.HDECL [(o, 8)] [(o, 8)] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i _ _ _ _ => i = 0%nat) R r EV Hra Hraok LCA.RETS FPM) with (i := 0%nat).
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact LCA.heap_ok.
  - exact LCA.pure_ok.
  - rewrite LS. exact LCA.ret_at.
  - intros i c k ps j s IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ LCA.leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ LCA.leaf_ok _ _ _ _ _ IL) as X. unfold LCA.leaf_chk in X.
    apply andb_prop in X as [X _]. apply Z.eqb_eq in X. subst pc. discriminate Hne.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL [(o, 8)] (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB [(o, 8)] LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    pose proof (CH2.leaves_all_sound _ _ _ LCA.leaf_ok _ _ _ _ _ IL) as X. unfold LCA.leaf_chk in X.
    apply andb_prop in X as [_ Y1]. apply CC.has_cell_In in Y1.
    pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
    assert (CELLS : forall X0, In X0 (SR.ps_cells ps) -> kentry_ok (hl_segs L) E' (mrestrict (ahid A1 m') M') X0) by (intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0)).
    assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
    split; [|repeat split; reflexivity].
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELLS _ Y1) ltac:(ev_start)) as G0. exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ G0).
  - reflexivity.
  - (* [comment removed for export] *)
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kunk_intro with (A := sp - 64) (N := 64); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 64) (N := 64); [ev_start | reflexivity | lia | lia | lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; lia | lia | lia | exact S1].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; lia | lia | lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; lia | lia | lia | exact Ho8].
    + eapply CL5A.kword8_intro with (A := LCA.GG) (z := 1); [ev_start | unfold LCA.GG; lia | unfold LCA.GG; lia | reflexivity | lia |].
      apply (CL5A.u8_vis (hl_segs L)); [unfold LCA.GG; lia | unfold LCA.GG; lia | exact VGG | exact LD1].
    + eapply CL5.kword64_intro with (A := LCA.GP) (z := LCA.IMP); [ev_start | unfold LCA.GP; lia | unfold LCA.GP; lia | reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [unfold LCA.GP; lia | unfold LCA.GP; lia | exact VGP | exact LD2].
    + eapply CL5.kunk_intro with (A := o) (N := 8); [ev_start | reflexivity | lia | lia | lia | exact DOv].
    + eapply CL5.kwr_intro with (A := o) (N := 8); [ev_start | reflexivity | lia | lia | lia | exact DOv].
    + eapply CL5.kdisj_intro with (A1 := sp - 64) (N1 := 64) (A2 := o) (N2 := 8); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
  - reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End LocaleOk.
Print Assumptions locale_ctor_later_ok.
