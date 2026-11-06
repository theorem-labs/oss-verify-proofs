(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutPureA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_errh_xasan_T Cut_errh_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module G := Cut_errh_xasan.
Module GT := Cut_errh_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module EHA.
Definition RETPC : Z := 836448.     (* [comment removed for export] *)
Definition RETS : list Z := [RETPC].
Definition A0E : expr := EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 32) (ELit (-24))) (ELit 1).
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb pc RETPC && Nat.eqb i 0 && CL.ps_reg_is ps 10 A0E)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk GT.NF G.HDECL RETS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : forall pc, In pc RETS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.
(* [comment removed for export] *)
Lemma kword32_intro : forall segs E (M : word -> option byte) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at segs M A z -> kentry_ok segs E M (KWord a 4 v).
Proof.
  intros segs E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.
(* [comment removed for export] *)
Lemma a0_val : forall E v, CL5A.uv E (EVar 32) = v -> 0 <= v < 2 ^ 31 -> CL5A.uv E A0E = (if Z.eqb v 24 then 1 else 0).
Proof.
  intros E v Hv Hr. unfold CL5A.uv, A0E in *. cbn [edenot] in *. rewrite u_sltu64, u_add64. cbn [edenot]. rewrite Hv. rewrite !u_lit64. unfold two64.
  destruct (Z.eqb_spec v 24) as [->|Hne].
  - reflexivity.
  - replace ((-24) mod 2 ^ 64) with (2 ^ 64 - 24) by reflexivity. rewrite (Z.mod_small 1) by lia.
    destruct (Z_lt_dec v 24) as [Hl|Hl].
    + rewrite Z.mod_small by lia. destruct (Z.ltb_spec (v + (2 ^ 64 - 24)) 1); [lia | reflexivity].
    + replace (v + (2 ^ 64 - 24)) with ((v - 24) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. destruct (Z.ltb_spec (v - 24) 1); [lia | reflexivity].
Qed.
End EHA.

Section ErrHandlerOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Definition hid (P : Prop) : Prop := P.

Theorem errh_ok : PMSA.errh_specA L ar HI 836392.
Proof.
  intros LB FF LK cr A t v sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha1 & Hfr & T8 & Hsh & Hv & Hvr) Hcont.
  unfold PMSA.a1, PMSA.a0, PMSA.u32, PMSA.ainfr in *.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF t 8 RFx Hfr ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (t + 8 <= 2147446784 \/ 17594333495296 <= t)) in Q5. change (hid (t + 8 <= hl_img_lo L \/ hl_img_hi L <= t)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  set (E0 := Env (reg_ev R (fun v0 => Z_to_bv 64 (nth (v0 - 32) [v] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 t) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 v) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = t) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = v) by (rewrite V32; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 16) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  rewrite <- LS in FPM.
  change 836392 with (CC.cp_pc G.cp0).
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK cr sp G.HDECL [] [] 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i _ _ _ _ => i = 0%nat) R r EV Hra Hraok EHA.RETS FPM) with (i := 0%nat).
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact EHA.heap_ok.
  - exact EHA.pure_ok.
  - rewrite LS. exact EHA.ret_at.
  - intros i c k ps j s IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EHA.leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EHA.leaf_ok _ _ _ _ _ IL) as X. unfold EHA.leaf_chk in X.
    apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply Z.eqb_eq in X. subst pc. discriminate Hne.
  - (* [comment removed for export] *)
    intros i c k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof (CH2.leaves_all_sound _ _ _ EHA.leaf_ok _ _ _ _ _ IL) as X. unfold EHA.leaf_chk in X.
    apply andb_prop in X as [X Y10]. apply andb_prop in X as [_ Yi]. apply Nat.eqb_eq in Yi. subst i.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB [] LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|repeat split; reflexivity].
    assert (W32 : CL5A.uv E' (EVar 32) = v) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); exact U32).
    replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10).
    rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' EHA.A0E)). f_equal. exact (EHA.a0_val E' v W32 Hvr).
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VT : CL5A.visr (ahid A model) t 8).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 t 8 (t + k) RFx Hfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VST : ahid A model (Z_to_bv 64 (S t)) = false).
    { destruct (CL5A.infr_sh_wok L ar LB FF sp 0 t 8 (S t) RFx Hfr ltac:(clear; lia) (CL5A.shreg_in_shadow t 1 (S t) T8 ltac:(clear; lia) ltac:(unfold S, SB; clear; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 16) 16).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 16) 16) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    pose proof (CHA.shadow_range t 8 (S t) Q3 ltac:(clear; lia) Q6 (CL5A.shreg_in_shadow t 1 (S t) T8 ltac:(clear; lia) ltac:(unfold S, SB; clear; lia))) as SRt.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply EHA.kword32_intro with (A := t) (z := v); [ev_start | clear - Q3; lia | clear - Q6; lia | exact V32 |].
      apply (CL5A.u32_vis (hl_segs L)); [clear - Q3; lia | clear - Q6; lia | exact (CL5A.visr_sub _ t 8 t 4 VT ltac:(clear; lia) ltac:(clear; lia)) | exact Hv].
    + eapply CL5.krange_intro with (v := v); [lin_eval; rw_atoms; clear; lia | clear - Hvr; lia | clear - Hvr; lia].
    + eapply CL5A.kword8_intro with (A := S t) (z := 4); [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U11; unfold S, SB; reflexivity | clear - SRt; lia | clear - SRt; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - SRt; lia | clear - SRt; lia | intros k Hk; replace (S t + k) with (S t) by (clear - Hk; lia); exact VST |].
      unfold L5.u8_at. unfold byte_at in Hsh. cbn [rdn]. rewrite Hsh. reflexivity.
    + eapply CL5.kalign_intro with (v := t); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact T8].
    + eapply CL5.krange_intro with (v := t); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1 S2 S3; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := t) (N2 := 8); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in Q5; clear - Q5; lia].
    + eapply CL5.kunk_intro with (A := sp - 16) (N := 16); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 16) (N := 16); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 16) (N1 := 16) (A2 := t) (N2 := 8); [ev_start | reflexivity | ev_start | reflexivity | clear - Q4 S2; lia].
  - reflexivity.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End ErrHandlerOk.
Print Assumptions errh_ok.
