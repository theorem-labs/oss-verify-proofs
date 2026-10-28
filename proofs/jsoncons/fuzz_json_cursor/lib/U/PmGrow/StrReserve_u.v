(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_str_reserve_zero_csrc_T_u Cut_str_reserve_zero_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SRV.
Module G := Cut_str_reserve_zero_csrc_u.   Module GT := Cut_str_reserve_zero_csrc_T_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition RET : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr G.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition e_o := EVar 10.  Definition e_n := ELit 264.

Lemma heap_ok : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] = true.
Proof. vmc_refl. Qed.
Lemma no_goto : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.

Definition pre (i : nat) : bool := Nat.eqb i 0.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.leb GT.NF (CC.cp_nx c)
   && negb (pre i) && match nth i G.BLS [] with [_] => true | _ => false end
   && expr_eqb ce e_n && GK.has (SR.ps_cells ps) (KWord (SA e_o 0) 8 (ELit 265)) && GK.has (SR.ps_cells ps) (KWord (SA e_o 8) 8 (ELit 0))
   && GK.has (SR.ps_cells ps) (KWord (SA e_o 16) 8 pe)
   && (GK.has (SR.ps_cells ps) (KWord (SA pe 0) 1 (ELit 0))
       || (GK.has (SR.ps_cells ps) (KRange (EAlu ALU_SLTU (EAlu ALU_SUB pe (EAlu ALU_ADD e_o (ELit 1))) (ELit 1)) 1 1)
           && GK.has (SR.ps_cells ps) (KDisj (SA pe 0) (ELit 264) (SA e_o 0) (ELit 24)))))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [] pc then
        match CH2.ret_of G.RETS i k with
        | Some j => (Z.eqb pc MALLOC && pre i && negb (pre j) && expr_eqb (hd_size j) e_n && expr_eqb (CA.ps_reg ps 10) e_n && Nat.leb GT.NF (CC.cp_nx c))%bool
        | None => false
        end
      else exit_chk i c ps
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.
Lemma csaved_lt : forall y : reg, In (ridx y) CSAVED -> (ridx y < GT.NF)%nat.
Proof. intros y Hy. unfold CSAVED, CL5.CSAVED in Hy. cbn [In] in Hy. unfold GT.NF. intuition lia. Qed.

Section StrReserveOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else debit L cr0 264.

Theorem str_reserve_ok : PMS.str_reserve_spec L HI.
Proof.
  intros LB cr o sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Hw0 & Hw8 & Hw16 & Hobj & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. unfold PML.u64 in *. destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_RESERVE with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := G.HDECL)
    (W := [(o, 24)]) (BLS := G.BLS) (Cred := Cred cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - intros rg [].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbv beta iota in X. rewrite Hret in X.
    repeat (apply andb_prop in X as [X ?Y]). apply expr_eqb_eq in Y0. apply negb_true_iff in Y2.
    rewrite Y0. unfold e_n. cbn [edenot]. rewrite u64_of_Z by lia. unfold Cred in HC. rewrite Y3 in HC. subst cr'. split; [exact Hcredit|].
    intros E2 Hag2. unfold Cred. rewrite Y2. reflexivity.
  - intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hcall, Hret in X.
    repeat (apply andb_prop in X as [X ?Y]). apply Z.eqb_eq in X. contradiction.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hnc in X. unfold exit_chk in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] heap_ok i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    apply andb_prop in X as [X YN]. repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y5. apply negb_true_iff in Y4. apply expr_eqb_eq in Y2.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y5]]).
    destruct (FR E' HagE') as (F2 & F10).
    rewrite LS in HLF.
    assert (CELL : forall X0, GK.has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y3. cbn [hd fst snd] in *. subst ce.
    set (pX := bv_unsigned (edenot E' pe)) in *.
    assert (HH2 : hi_heap HI ((pX, 264) :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y6) in HH1. unfold CH2.den in HH1. cbn [map fst snd] in HH1. fold pX in HH1.
      unfold e_n in HH1. cbn [edenot] in HH1. rewrite u64_of_Z in HH1 by lia. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, 264) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (NUL : L5.u8_at GK.RSEGS M' pX 0).
    { apply orb_prop in YN as [YN|YN].
      - apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ YN)). unfold estart. cbn [a_base a_off]. fold pX. lia.
      - exfalso. apply andb_prop in YN as [YE YD]. pose proof (CELL _ YD) as GD. pose proof (CELL _ YE) as GE.
        cbn [kentry_ok] in GD, GE. unfold estart, elenZ, e_o in GD. cbn [a_base a_off edenot] in GD. fold pX in GD. rewrite F10 in GD. rewrite !u64_of_Z in GD by lia.
        change (edenot E' (EAlu ALU_SLTU (EAlu ALU_SUB pe (EAlu ALU_ADD e_o (ELit 1))) (ELit 1)))
          with (alu64 ALU_SLTU (alu64 ALU_SUB (edenot E' pe) (alu64 ALU_ADD (edenot E' e_o) (Z_to_bv 64 1))) (Z_to_bv 64 1)) in GE.
        rewrite u_sltu64, u_sub64, u_add64 in GE. unfold e_o in GE. cbn [edenot] in GE. fold pX in GE. rewrite F10 in GE. rewrite !u64_of_Z in GE by lia.
        rewrite (Z.mod_small (o + 1)) in GE by lia.
        destruct (Z.ltb_spec ((pX - (o + 1)) mod 2 ^ 64) 1) as [Hlt|]; [|lia].
        destruct GD as [GD|GD]; [rewrite <- (Z_mod_plus_full (pX - (o + 1)) 1 (2 ^ 64)) in Hlt; rewrite Z.mod_small in Hlt by lia; lia | rewrite Z.mod_small in Hlt by lia; lia]. }
    assert (W0 : L5.u64_at GK.RSEGS M' o 265).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) 0).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y0)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y7 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8320 + j) with (sp - (256 + (16 + 8224)) + (j + 176)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    unfold Cred in HC1. rewrite Y4 in HC1. subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, 264) :: LB) (debit L cr 264) LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    exists pX. split; [|split; [|auto]].
    + split; [|split; [reflexivity | cbn [length]; lia]]. unfold L5.lstr_long. cbn [length Z.of_nat]. split; [reflexivity|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|].
      split; [intros j Hj; cbn in Hj; lia | rewrite Z.add_0_r; exact NUL].
    + split; [repeat split; assumption|]. split; [exact Qap | exact Qdef].
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hds : L5.defined M (sp - 8320) 8320) by (intros i Hi; replace (sp - 8320 + i) with (sp - (256 + (16 + 8224)) + (i + 176)) by lia; apply S5; lia).
    assert (HZ : GK.zeros M o 24).
    { replace 24 with (8 + (8 + 8)) by lia. apply GK.zeros_app; [lia | apply GK.zeros_of_u64; [exact Hw0 | unfold GK.HULL_HI; lia | lia]|].
      apply GK.zeros_app; [lia | apply GK.zeros_of_u64; [exact Hw8 | unfold GK.HULL_HI; lia | lia]|].
      replace (o + 8 + 8) with (o + 16) by lia. apply GK.zeros_of_u64; [exact Hw16 | unfold GK.HULL_HI; lia | lia]. }
    split.
    { change (CC.cp_regs G.cp0) with (sr_upd sr_id 11 (ELit 256)). apply (regs_ok_pin E0 sr_id R 11%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha1. reflexivity. }
    unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply GK.kzero_intro with (A := o) (N := 24); [ev_start | reflexivity | lia | lia | lia | lia | exact HZ].
    + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. exact HH.
  - exact Hfp.
Qed.
End StrReserveOk.
End SRV.
