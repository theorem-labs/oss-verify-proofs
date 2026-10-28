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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_vec_push_fast_csrc_T_u Cut_vec_push_fast_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module VPF.
Module F := Cut_vec_push_fast_csrc_u.   Module FT := Cut_vec_push_fast_csrc_T_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition RET : Z := Eval vm_compute in hd 0 FT.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr F.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.

Lemma heap_ok_f : CH2.heap_chk FT.NF F.HDECL F.BLS F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] = true.
Proof. vmc_refl. Qed.
Lemma no_goto_f : CH2.leaves_all F.CPS F.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.

Definition e_o := EVar 10.  Definition e_b := EVar 32.  Definition e_len := EVar 33.  Definition e_cap := EVar 34.  Definition e_x := EVar 35.

Definition exit_f (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb FT.NF (CC.cp_nx c)
   && has cells (KWord (SA e_o 0) 8 e_b) && has cells (KWord (SA e_o 8) 8 (APC.eaddz (APC.eadd e_b e_len) 1)) && has cells (KWord (SA e_o 16) 8 (APC.eadd e_b e_cap))
   && has cells (KBlob (SA e_b 0) e_len 0) && has cells (KWord (SA (APC.eadd e_b e_len) 0) 1 e_x))%bool.
Definition leaf_f (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && Nat.eqb i 0 && exit_f c ps)%bool end.
Lemma leaf_f_ok : CH2.leaves_all F.CPS F.TAGS leaf_f = true.
Proof. vmc_refl. Qed.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Section VecPushFastOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma vec_push_fast : forall (LB : list (Z * Z)) (cr : credit) (o b cap xa x sp r : Z) (st : list Z),
  PML.cps_heap L HI PML.PC_VEC_PUSH r sp PMS.VEC_SCR LB cr
      (fun R M => Z.of_nat (length st) < cap /\ PML.entry L R M sp r PMS.VEC_SCR /\ PML.a0 R o /\ PML.a1 R xa /\ PML.u8 M xa x /\ sp <= xa < hl_sptop L /\
                  PML.u64 M o b /\ PML.u64 M (o + 8) (b + Z.of_nat (length st)) /\ PML.u64 M (o + 16) (b + cap) /\ L5.bytes_at GK.RSEGS M b st /\
                  In (b, cap) LB /\ (length st <= 1026)%nat /\ PML.obj_on_stack L sp o 24)
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\
          (Z.of_nat (length st) < cap /\ PML.u64 M' o b /\ PML.u64 M' (o + 8) (b + Z.of_nat (length st) + 1) /\ PML.u64 M' (o + 16) (b + cap) /\
            L5.bytes_at GK.RSEGS M' b (st ++ [x]) /\ LB' = LB /\ cr' = cr /\ LBk = lb_remove b LB)).
Proof.
  intros LB cr o b cap xa x sp r st. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hlt & Hentry & Ha0 & Ha1 & Hx & Hxa & Hw0 & Hw8 & Hw16 & Hbs & HinLB & Hlen & Hobj) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.VEC_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. unfold PML.u64, PML.u8 in *.
  destruct Hobj as (O1 & O2 & O3).
  set (len := Z.of_nat (length st)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ b cap HH HinLB) as HH'.
  set (xb := x mod 256). assert (Hxb : 0 <= xb < 256) by (unfold xb; apply Z.mod_pos_bound; lia).
  assert (Hx' : L5.u8_at GK.RSEGS M xa xb) by (apply (proj1 (GK.u8_at_mod M xa x)); exact Hx).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; len; cap; xb] 0))) (fun id => nth id [map (Z_to_bv 8) st] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 xa) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 len) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 xb) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = xa) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = len) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = cap) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = xb) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree FT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = xa /\
            bv_unsigned (ev E1 32) = b /\ bv_unsigned (ev E1 33) = len /\ bv_unsigned (ev E1 34) = cap /\ bv_unsigned (ev E1 35) = xb /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold FT.NF; lia). repeat split; try assumption. symmetry. exact B. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr F.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr F.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr F.HDECL) by (change (CH.hd_scr F.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= FT.NF)%nat) by (unfold FT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_VEC_PUSH with (CC.cp_pc F.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := FT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove b LB) (sp0 := sp) (d := F.HDECL)
    (W := [(o, 24)]) (BLS := F.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := F.CPS) (TAGS := F.TAGS) (RETS := F.RETS) (MALLOC := MALLOC) (FREE := FREE)
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
  -   intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia|]. left. lia.
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact F.plans.
  - exact F.tags_ok.
  - exact heap_ok_f.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_f _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. discriminate X.
  - intros i c kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X. rewrite Hcall in X. discriminate X.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X. rewrite Hnc in X.
    apply andb_prop in X as [Xi X]. apply andb_prop in Xi as [_ Xi]. apply Nat.eqb_eq in Xi. subst i. unfold exit_f in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) FT.NF E0 M model (lb_remove b LB) sp F.HDECL [(o, 24)] F.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] heap_ok_f _ c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X. apply Nat.leb_le in Y4.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree FT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y4]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F33 & F34 & F35 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (HH2 : hi_heap HI ((b, cap) :: lb_remove b LB) cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. change (nth 0 F.BLS []) with [(EVar 32, EVar 34)] in HH1. unfold CH2.den in HH1. cbn [map fst snd edenot] in HH1.
      destruct HagE1 as [AG1 _]. rewrite <- !AG1 in HH1 by (unfold FT.NF; lia). rewrite U32, U34 in HH1. exact HH1. }

    assert (UE : bv_unsigned (edenot E' (APC.eadd e_b e_len)) = b + len) by (apply CL5.u_lin; [unfold e_b, e_len; lin_eval; rw_atoms; lia | lia]).
    assert (UE1 : bv_unsigned (edenot E' (APC.eaddz (APC.eadd e_b e_len) 1)) = b + len + 1) by (apply CL5.u_lin; [unfold e_b, e_len; lin_eval; rw_atoms; lia | lia]).
    assert (UC : bv_unsigned (edenot E' (APC.eadd e_b e_cap)) = b + cap) by (apply CL5.u_lin; [unfold e_b, e_cap; lin_eval; rw_atoms; lia | lia]).
    assert (W0 : L5.u64_at GK.RSEGS M' o b).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y3)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact F32]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (b + len + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UE1]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) (b + cap)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UC]. }
    assert (BS : L5.bytes_at GK.RSEGS M' b st).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat b st (CELL _ Y0)); [unfold estart, e_b; cbn [a_base a_off edenot]; rewrite F32; lia | rewrite FB; reflexivity]. }
    assert (BX : L5.u8_at GK.RSEGS M' (b + len) x).
    { apply (proj2 (GK.u8_at_mod M' (b + len) x)). fold xb. apply (GK.kword8_elim E' M' _ _ (b + len) xb (CELL _ Y)); [unfold estart; cbn [a_base a_off]; rewrite UE; lia | exact F35]. }
    assert (BSX : L5.bytes_at GK.RSEGS M' b (st ++ [x])).
    { apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r. exact BX. }

    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < FT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold FT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED FT.NF y HLF Y5 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr F.HDECL) (CH.hd_scr F.HDECL)).
    { change (CH.hd_scr F.HDECL) with SCRT. eapply (L5.defined_sub _ _ _ _ _ S5); unfold SCRT; lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE FT.NF E0 M model (lb_remove b LB) sp F.HDECL [(o, 24)] F.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr F.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L (lb_remove b LB) sp (128 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr (lb_remove b LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact (CH2.heap_own_back L HI HIok LB cr M' _ b cap HH2 HinLB Hnd)].
    split; [reflexivity|]. repeat split; assumption.
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hdb : L5.defined M b cap) by exact Pdef.
    assert (WE : edenot E0 (EAlu Instr.ALU_ADD (EVar 32) (EVar 33)) = Z_to_bv 64 (b + len)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    assert (WC : edenot E0 (EAlu Instr.ALU_ADD (EVar 32) (EVar 34)) = Z_to_bv 64 (b + cap)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, F.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | lia | lia | exact V32 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + len); [ev_start | lia | lia | exact WE | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | lia | lia | exact WC | exact Hw16].
    + e_range. + e_range. + e_range.
    + eapply GK.kword8_intro with (A := xa) (z := xb); [ev_start | lia | lia | exact V35 | lia | exact Hx'].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := st) (A := b); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | lia | fold len; lia | lia | reflexivity | exact Hbs | fold len; ev_def].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 F.BLS [])) with [(b, cap)]; [exact HH'|].
    change (nth 0 F.BLS []) with [(EVar 32, EVar 34)]. unfold CH2.den. cbn [map fst snd edenot]. rewrite U32, U34. reflexivity.
  - exact Hfp.
Qed.

End VecPushFastOk.
End VPF.
