(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceX L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_opnewx_xsrc_T_u5 Cut_opnewx_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5 MallocXSum_u5 MallocXCps_u5 MallocXLeaf_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import OpNewX_u5 MallocXCpsU MallocXLeafU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ONXU.
Import ONX.

Section OpNewXOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis MXU : malloc_u_spec L SCFG HI.
Let MXCPSU : MXCU.malloc_x_cpsU L HI := MXCU.malloc_x_cps_okU L HI MXU LAY.
Definition CredU (cr0 : credit) (n : Z) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else debit L cr0 n.
Theorem opnew_x_okU : PMES.opnew_x_specU L HI.
Proof.
  intros LB cr n sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Hn & Hcredit) Hcont.
  assert (HnB : 0 < n < 2 ^ 47) by (unfold NBU in Hn; lia).
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMES.OPNEWX_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 n) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = n) by (rewrite V10; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = n).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a -> CH2.wclient L sp a) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  unfold PML.cfg. change PML.PC_OPNEW with (CC.cp_pc G.cp0). rewrite <- LS.
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; exact S5).
  eapply (CH2.cert_sound3 L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LB sp G.HDECL [] G.BLS (CredU cr n) STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS XI) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|Hnm].
    { destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]). (* [comment removed for export] *)
      apply negb_true_iff in Y4. apply Z.eqb_eq in Y3. apply Nat.leb_le in Y2. apply expr_eqb_eq in Y1.
      destruct (MXL.mallocx_chk GT.NF G.HDECL c ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      apply (MXLU.mallocx_leaf_okU L HI HIok LAY GT.NF E0 M model LB sp G.HDECL [] G.BLS (CredU cr n) STKF SCRP NF32 U2 TP0 W_OK
               ltac:(intros rg []) WRS_OK ltac:(intros rg a []) G.CPS G.TAGS G.RETS K HKnil XI DEF0 MXCPSU i c kk ps j cj ci IL Hret Hcj Y3 Hchk); [|intros; exact I].
      intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold CredU in HC. rewrite X in HC. subst cr1.
      rewrite Y1. unfold MXL.uv, PB.uv, e_n. cbn [edenot]. destruct (FR E' HagE') as (F2 & F10). rewrite F10.
      split; [exact Hn|]. split; [exact Hcredit|]. intros E2 _. unfold CredU. rewrite Y4. reflexivity. }
    cbv iota in X.
    (* [comment removed for export] *)
    intros fx' E R1 M1 m1 E' R' M' HAt [HAmb _] HFP Hag HLF _. unfold exit_chk in X.
    pose proof (CH2.leaf_amb3 L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LB sp G.HDECL [] G.BLS (CredU cr n) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS G.TAGS heap_ok3 i c kk ps pc IL E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    (* [comment removed for export] *)
    apply Z.eqb_eq in X. apply Nat.leb_le in Y3. apply negb_true_iff in Y2. apply expr_eqb_eq in Y.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y3]]).
    destruct (FR E' HagE') as (F2 & F10).
    rewrite LS in HLF.
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y1. cbn [hd fst snd] in *. subst ce.
    set (pX := bv_unsigned (edenot E' pe)) in *.
    assert (HH2 : hi_heap HI ((pX, n) :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y4) in HH1. unfold CH2.den in HH1. cbn [map fst snd] in HH1. fold pX in HH1.
      unfold e_n in HH1. cbn [edenot] in HH1. rewrite F10 in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, n) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (HA0 : getr R' 10%bv = Z_to_bv 64 pX).
    { pose proof (CL.ps_reg_is_sound GK.RSEGS c ps E' R' M1 M' 10 pe HLF Y0) as G0. replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : reg) in G0 by (apply bv_eq; reflexivity). rewrite G0. unfold pX. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y5 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; exact S5).
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LB sp G.HDECL [] G.BLS (CredU cr n) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0. unfold SCRT in HP0.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    unfold CredU in HC1. rewrite Y2 in HC1. subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, n) :: LB) (debit L cr n) LB [] HFP); [| exact HRP | exact HP0 | exact Hbv1 | exact HH2].
    exists pX. split; [exact HA0|]. split; [|auto]. split; [repeat split; assumption|]. split; [exact Qap | exact Qdef].
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8240) 8240) by exact S5.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_unk. + e_wr. + e_range. + e_align S1.
  - (* [comment removed for export] *)
    split; [|exact I].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. exact HH.
  - exact Hfp.
Qed.
End OpNewXOk.
End ONXU.
