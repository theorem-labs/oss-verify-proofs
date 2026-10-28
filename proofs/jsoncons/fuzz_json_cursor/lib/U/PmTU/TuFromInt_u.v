(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_from_int_u64_csrc_T_u Cut_from_int_u64_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TFI.
Module U := Cut_from_int_u64_csrc_u.   Module UT := Cut_from_int_u64_csrc_T_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xb7c98.
Definition RET : Z := Eval vm_compute in hd 0 UT.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr U.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.

Lemma heap_ok_u : CH2.heap_chk UT.NF U.HDECL U.BLS U.CPS GK.HULL_LO GK.HULL_HI U.TAGS U.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vmc_refl. Qed.
Lemma no_goto_u : CH2.leaves_all U.CPS U.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.

Definition e_o := EVar 11.

Definition exit_u (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb UT.NF (CC.cp_nx c)
   && match CA.ps_reg ps 10 with
      | ELit k => Z.leb 1 k && Z.leb k 20 && CL.ps_reg_is ps 10 (ELit k) && has cells (KWord (SA e_o 0) 1 (ELit (2 * k))) && has cells (KWord (SA e_o (k + 1)) 1 (ELit 0))
      | _ => false
      end)%bool.
Definition leaf_u (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [MEMMOVE] pc) && Nat.eqb i 0 && exit_u c ps)%bool end.
Lemma leaf_u_ok : CH2.leaves_all U.CPS U.TAGS leaf_u = true.
Proof. vmc_refl. Qed.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Lemma bytes_of_defined : forall (M : PML.mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at GK.RSEGS M p s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|].
    intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
Qed.

Section TuFromIntOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem from_integer_u64_ok : PMFC.from_integer_u64_spec L HI.
Proof.
  intros LB cr o v sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Hv & Ha1 & Hstr & Hdo & Hobj & Himg) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMFC.FROMINT_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as (Hlen0 & Hb0 & _ & _). cbn [length Z.of_nat] in Hb0. rewrite Z.mul_0_r in Hb0.
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 v) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 o) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = v) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = o) by (rewrite V11; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree UT.NF E0 E1 -> bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 11) = o).
  { intros E1 [A B]. rewrite <- !A by (unfold UT.NF; lia). split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr U.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr U.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr U.HDECL) by (change (CH.hd_scr U.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= UT.NF)%nat) by (unfold UT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs U.HDECL) -> SGP.region_vars_lt UT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall rg a, In rg (CH.hd_img U.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [lia|]. split.
    - intros HS. pose proof (PmLayout.ly_static L LAY a HS). lia.
    - unfold in_errno. rewrite (PmLayout.ly_errno L LAY). lia. }
  unfold PML.cfg. change PMFC.PC_FROM_INT_U64 with (CC.cp_pc U.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := UT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := U.HDECL)
    (W := [(o, 24)]) (BLS := U.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := U.CPS) (TAGS := U.TAGS) (RETS := U.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
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
  - exact IMG_OK.
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact U.plans.
  - exact U.tags_ok.
  - exact heap_ok_u.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_u _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c0 kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_u_ok _ _ _ _ _ IL) as X. unfold leaf_u in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. discriminate X.
  - intros i c0 kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_u_ok _ _ _ _ _ IL) as X. unfold leaf_u in X. rewrite Hcall in X. discriminate X.
  -
    intros i c0 kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_u_ok _ _ _ _ _ IL) as X. unfold leaf_u in X. rewrite Hnc in X.
    apply andb_prop in X as [Xi X]. apply andb_prop in Xi as [_ Xi]. apply Nat.eqb_eq in Xi. subst i. unfold exit_u in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) UT.NF E0 M model LB sp U.HDECL [(o, 24)] U.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  U.CPS GK.HULL_LO GK.HULL_HI U.TAGS U.RETS MALLOC FREE [MEMMOVE] heap_ok_u _ c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    apply andb_prop in X as [X Xk]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y4]. apply CL.ps_at_sound in X. destruct X as [X|[]]. symmetry in X. apply Nat.leb_le in Y3.
    destruct (CA.ps_reg ps 10) as [kk0| | | | | | |] eqn:Ha0e; try discriminate Xk.
    apply andb_prop in Xk as [Xk YN]. apply andb_prop in Xk as [Xk YB]. apply andb_prop in Xk as [Xk YR]. apply andb_prop in Xk as [Y1 Y2]. apply Z.leb_le in Y1, Y2.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree UT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y3]]).
    destruct (FR E' HagE') as (F2 & F11).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (HH2 : hi_heap HI LB cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. change (nth 0 U.BLS []) with (@nil (expr * expr)) in HH1. exact HH1. }

    assert (DEF : L5.defined M' o 24).
    { intros j Hj. pose proof (Hdf1 (o + j) ltac:(lia)) as D. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 (o + j))). rewrite u64_of_Z by lia.
      apply D; [| exact (Hdo j Hj)]. split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia]. }
    assert (B0 : L5.u8_at GK.RSEGS M' o (2 * kk0)).
    { apply (GK.kword8_elim E' M' _ _ o _ (CELL _ YB)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F11; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (o + 1 + kk0) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ YN)). unfold estart, e_o. cbn [a_base a_off edenot]. rewrite F11. lia. }
    destruct (bytes_of_defined M' (Z.to_nat kk0) (o + 1) ltac:(lia) ltac:(lia)) as (d & Hdl & Hbs).
    { rewrite Z2Nat.id by lia. intros j Hj. replace (o + 1 + j) with (o + (1 + j)) by lia. apply DEF. lia. }
    assert (LEN : Z.of_nat (length d) = kk0) by (rewrite Hdl; apply Z2Nat.id; lia).
    assert (STR : PML.str_at M' o (PML.SShort d)).
    { unfold PML.str_at, L5.lstr_short. rewrite LEN. split; [lia|]. split; [exact B0|]. split; [exact Hbs | exact NUL]. }

    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < UT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold UT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED UT.NF y HLF Y4 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Ha0' : PML.a0 R' kk0).
    { unfold PML.a0. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound GK.RSEGS c0 ps E' R' M1 M' 10 (ELit kk0) HLF YR). reflexivity. }
    assert (Hds : L5.defined M (sp - CH.hd_scr U.HDECL) (CH.hd_scr U.HDECL)).
    { change (CH.hd_scr U.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8624 + j) with (sp - (320 + (256 + (16 + 8224))) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE UT.NF E0 M model LB sp U.HDECL [(o, 24)] U.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr U.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (320 + (256 + (16 + 8224))) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    exists d. split; [lia|]. split; [exact STR|]. split; [rewrite LEN; exact Ha0'|]. auto.
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8624) 8624) by (intros i Hi; replace (sp - 8624 + i) with (sp - (320 + (256 + (16 + 8224))) + (i + 192)) by lia; apply S5; lia).
    assert (B0 : edenot E0 (ELit 0) = Z_to_bv 64 0) by reflexivity.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, U.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range.
    + eapply GK.kword8_intro with (A := o) (z := 0); [ev_start | lia | lia | exact B0 | lia | exact Hb0].
    + apply AxSymRun3.kimg_intro; [lia | lia |]. intros j Hj. apply Himg. unfold PML.IMG_RO_HI. lia.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 U.BLS []) with (@nil (expr * expr)). exact HH.
  - exact Hfp.
Qed.
End TuFromIntOk.
End TFI.
