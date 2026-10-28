(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbh_obj_cseg_xsrc_T_u5 Cut_vbh_obj_cseg_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendK_u5 EncKit_u5 EncKit2_u5 EncKit3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbmKitX_u5 VbhKitX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBH_OC.
Import PML. Import PMES.
Module G := Cut_vbh_obj_cseg_xsrc_u5.   Module GT := Cut_vbh_obj_cseg_xsrc_T_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition ENDPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition KEPT : list nat := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition has := GK.has.
Ltac hcell a o := match goal with H : has _ (KWord (SA a o) _ _) = true |- _ => exact H end.
Ltac hblob := match goal with H : has _ (KBlob _ _ _) = true |- _ => exact H end.

Lemma heap_ok : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [ENDPC] && CL.ps_keeps ps KEPT && Nat.leb GT.NF (CC.cp_nx c) && Nat.eqb i 0
   
   && CH2.blocks_eqb (nth i G.BLS []) [])%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && exit_chk i c ps)%bool end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kept_lt48 : forall y : reg, In (ridx y) KEPT -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPT in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPT.
Proof. intros r H. unfold ridx, KEPT. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : PML.mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G0.
  replace x with (Z_to_bv 5 (Z.of_nat n)); [exact G0|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hx. pose proof (bv_unsigned_in_range 5 x) as RG.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. rewrite <- Hx. exact RG.
Qed.

Section Seg.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma seg_ok : forall (LB : list (Z * Z)) (cr : credit) (spf V b d : Z),
  PMES2.cps_seg L HI 247044 0x3c58c spf 0 LB cr
    (fun R M => getr R 2%bv = Z_to_bv 64 spf /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M spf 0 /\ spf mod 16 = 0 /\ getr R 8%bv = Z_to_bv 64 V /\
                u64 M (V + O_STACK) b /\ u64 M (V + O_STACK + 8) (b + 32 * d) /\ 0 <= b /\ 1 <= d <= 1023 /\ b + 32 * d <= hl_ceil L /\ obj_on_stack L (spf + 64) V ENC_SIZE)
    (fun R M R' M' LB' cr' LBk W =>
       (forall y : reg, In (bv_unsigned y) [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr R' y = getr R y) /\
       LB' = LB /\ LBk = LB /\ W = [] /\ cr' = cr /\ (forall a, spf <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))).
Proof.
  intros LB cr spf V b d. unfold PMES2.cps_seg.
  intros fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hsp & Htp & Hstk & Hsp16 & Hs0 & T1 & T2 & HB0 & HD & HBC & HOV).
  destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5). destruct HOV as (OV1 & OV2 & OV3). unfold ENC_SIZE, MAX_DEPTH, O_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia. unfold PML.a0 in *.
  assert (Hd1 : 1 <= d) by lia. assert (HdNN : 0 <= d) by lia. replace (V + 264 + 8) with (V + 272) in T2 by lia.
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [0; d; b] 0))) (fun id => nth id (@nil (list byte)) [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 spf) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- Hs0; exact (EV 8%bv)).
  assert (V33 : ev E0 33 = Z_to_bv 64 d) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = spf) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = d) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; lia).

  assert (FR : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (ev E1 2) = spf /\ bv_unsigned (ev E1 8) = V /\ bv_unsigned (ev E1 33) = d /\ bv_unsigned (ev E1 34) = b).
  { intros E1 [AG _]. rewrite <- !AG by (unfold GT.NF; lia). repeat split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 0) by reflexivity.
  assert (STKF : spf mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= spf /\ spf <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (rewrite SCRV; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (HSTKE : hl_stack L = CH.hd_hstk G.HDECL) by (rewrite LSTK; reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (Wm := (@nil L5.range)).
  set (LBR := LB).

  assert (W_OK : forall (w : L5.range) (a : Z), In w Wm -> L5.in_rng w a -> CH2.wclient L spf a).
  { intros w a Hw Hin. destruct Hw. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBR spf a)).
  { intros rg Hrg. unfold G.HDECL, GT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
    rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w Wm /\ L5.in_rng w a)).
  { intros rg Hrg. destruct Hrg. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (Hds : L5.defined M (spf - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros j Hj; lia).
  unfold PML.cfg. change 247044 with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBR) (sp0 := spf) (d := G.HDECL)
    (W := Wm) (BLS := G.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - exact LSTK0.
  - exact STKF.
  - exact SCRP.
  - exact HSTKE.
  - exact NF32.
  - exact U2.
  - exact TP0.
  - exact W_OK.
  - exact CRS_OK.
  - exact WRS_OK.
  - exact IMG_OK.
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - exact FPM0.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbn [negb andb] in X. discriminate X.
  - intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hcall in X. cbn [negb andb] in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c0' kk0 ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hnc in X. cbn [negb andb] in X. unfold exit_chk in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LBR spf G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] heap_ok i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    match goal with H : Nat.leb GT.NF (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
    match goal with H : Nat.eqb i 0 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
    match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
    destruct (FR E' HagE') as (F2 & F8 & F33 & F34).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
    { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
    assert (KEEP : forall y : reg, In (ridx y) KEPT -> getr R' y = getr R y).
    { intros y Hy. match goal with H : CL.ps_keeps ps KEPT = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPT GT.NF y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LBR spf G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP. rewrite SCRV in HP.
    assert (KST : forall a, spf <= a < 2 ^ 64 ->  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_stack_stk L LBR M spf 0 Wm a); [repeat split; try lia; intros j Hj; lia | lia | lia | rewrite LER; lia |].
      unfold Wm. apply L5C.outside_nil. }
    apply Z.eqb_eq in X. unfold ENDPC in X. rewrite X, LS.
    assert (HH2 : hi_heap HI LB cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app] in HH1. exact HH1. }
    apply (Hcont fx' R' M' m1 LB cr LBR Wm HFP); [| exact HP | exact Hbv1 | exact HH2].
    split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact KST.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS. split; [exact (regs_ok_id R _ _)|].
    unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil]; first
      [ eapply CL5.kword64_intro; [ev_start | lia | lia | | eassumption]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])

      | e_range
      | e_align OV3 | e_align SK1
      | e_unk | e_wr | e_disj
      | idtac ].
    all: fail "entry knowledge left".
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    change (CH2.den E0 (nth 0 G.BLS [])) with (@nil (Z * Z)). exact HH.
  - exact Hfp.
Qed.
End Seg.
End VBH_OC.
