(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbh_obj_root_xsrc_T_u5 Cut_vbh_obj_root_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendK_u5 EncKit_u5 EncKit2_u5 EncKit3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbhKitX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBH_OR.
Import PML. Import PMES.
Module G := Cut_vbh_obj_root_xsrc_u5.   Module GT := Cut_vbh_obj_root_xsrc_T_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition MIDPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition KEPT : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition has := GK.has.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr G.HDECL.

Lemma heap_ok : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [MIDPC] && CL.ps_keeps ps KEPT && Nat.leb GT.NF (CC.cp_nx c) && Nat.eqb i 0 && CH2.blocks_eqb (nth i G.BLS []) []
   && CL.ps_reg_is ps 2 (EAlu ALU_ADD (EVar 2) (ELit (-64))) && CL.ps_reg_is ps 8 (EVar 10) && CL.ps_reg_is ps 9 (EAlu ALU_ADD (EVar 10) (ELit 264))
   && has cells (KWord (SA (EVar 2) (-8)) 8 (EVar 1)) && has cells (KWord (SA (EVar 2) (-16)) 8 (EVar 8)) && has cells (KWord (SA (EVar 2) (-24)) 8 (EVar 9))
   && has cells (KWord (SA (EVar 2) (-32)) 8 (EVar 18))
   && has cells (KWord (SA (EVar 10) 400) 4 (ELit 1))
   && CL.ps_reg_is ps 18 (EVar 34))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && exit_chk i c ps)%bool end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kept_lt48 : forall y : reg, In (ridx y) KEPT -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPT in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [3; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPT.
Proof. intros r H. unfold ridx, KEPT. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : PML.mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G0.
  replace x with (Z_to_bv 5 (Z.of_nat n)); [exact G0|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hx. pose proof (bv_unsigned_in_range 5 x) as RG.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. rewrite <- Hx. exact RG.
Qed.

Section Head.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem head_ok : PMES2.head_obj_root_spec L HI.
Proof.
  unfold PMES2.head_obj_root_spec, PMES2.head_spec, PMES2.cps_seg.
  intros LBo cr sp r V S2 kx bx g fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hentry & Ha0 & HGX & Hinv & Hdep & Himg & Hlits & Hroom & Hcred & Hobjs).
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5).
  unfold VIS_SCR, WD_SCR_X, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK, PMES2.HEAD_SCR, NEWLINE_SCR in *.
  change (1024 + Z.max (256 + (16 + 8224)) 9600) with 10624 in *. change (96 + (80 + (256 + (16 + 8224)))) with 8672 in *.
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PML.apart in OV2, OAP.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_kpm L LAY) as KPM.
  destruct g as [es len0 rep b capb]. cbn [g_es g_len g_rep g_sb g_scap g_lbv] in *.
  unfold PMES2.par_root, PMES2.RX_OBJ_ROOT, PML.a0, PML.a1, PML.a2 in *.
  subst es.
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5). cbn [g_es g_len g_rep g_sb g_scap] in I1, I2, I3, I4, I5. unfold MAX_DEPTH in *.
  set (d := depth []) in *.
  assert (HdZ : d = 0) by reflexivity.
  assert (HdNN : 0 <= d) by (unfold d, depth; lia).
  pose proof I2 as TT. destruct TT as (T1 & T2 & T3 & T4 & T5 & T6). fold d in T2, T4, T6.
  replace (V + O_STACK + 8) with (V + 272) in T2 by (unfold O_STACK; lia). unfold O_STACK in T1, T3.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  set (LB := LBo ++ srep_blocks rep ++ stack_blocks b capb) in *.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & _).

  assert (HBC : 0 <= b /\ b + capb <= hl_ceil L /\ 0 <= capb <= 32768).
  { destruct T5 as [[Hc0 Hb0]|(kk & Hkk & Hck)]; [lia|]. assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk.
    assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
    assert (HinLB : In (b, capb) LB) by (unfold LB, stack_blocks; destruct (Z.eqb_spec capb 0); [nia|]; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    destruct (Hwf _ HinLB) as ((P0 & _ & _ & _ & P4) & _). cbn [fst snd] in P0, P4. nia. }
  (* [comment removed for export] *)
  pose proof I1 as HOBJ0.
  destruct I1 as (_ & _ & E16 & _ & _ & _ & E29 & _ & E31 & E32 & _ & _ & _ & _ & _ & _ & _ & _ & E240 & _ & _ & _ & _ & _ & Ecol & E400 & _).
  unfold O_OPT_VPTR, VT_ENC_OPTIONS, O_SPLITS, O_MAX_DEPTH, O_COLUMN, O_DEPTH in E16, E29, E31, E32, E240, Ecol, E400.
  replace (V + 28 + 1) with (V + 29) in E29 by lia. replace (V + 28 + 3) with (V + 31) in E31 by lia. replace (V + 28 + 4) with (V + 32) in E32 by lia. fold d in E400.
  assert (D400 : L5.defined M (V + 400) 4) by (intros j Hj; exact (EK3.defined_of_u32 M (V + 400) _ E400 ltac:(lia) ltac:(lia) j Hj)).
  assert (RA64 : 0 <= r < 2 ^ 64) by (destruct Hraok as [R1' R2']; unfold L5.ra_ok in *; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; d; b; capb] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V1 : ev E0 1 = Z_to_bv 64 r) by (rewrite <- Hra; exact (EV 1%bv)).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 d) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 capb) by reflexivity.
  assert (U1 : bv_unsigned (ev E0 1) = r) by (rewrite V1; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = d) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = capb) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 1) = r /\ bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = V /\ bv_unsigned (ev E1 33) = d /\ bv_unsigned (ev E1 34) = b /\
            ev E1 8 = getr R 8%bv /\ ev E1 9 = getr R 9%bv /\ ev E1 18 = getr R 18%bv /\ ev E1 19 = getr R 19%bv /\ ev E1 20 = getr R 20%bv /\ ev E1 4 = getr R 4%bv).
  { intros E1 [AG _]. rewrite <- !AG by (unfold GT.NF; lia). repeat split; first [assumption | exact (EV 8%bv) | exact (EV 9%bv) | exact (EV 18%bv) | exact (EV 19%bv) | exact (EV 20%bv) | exact (EV 4%bv)]. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (HSTKE : hl_stack L = CH.hd_hstk G.HDECL) by (rewrite LSTK; reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (Wm := [(V + 400, 4)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w Wm -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LB sp a)).
  { intros rg Hrg. unfold G.HDECL, GT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    all: rewrite U10 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]).  }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w Wm /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + 400, 4). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (Hds2 : L5.defined M (sp - 8672) 8672) by (intros j Hj; replace (sp - 8672 + j) with (sp - 10624 + (j + 1952)) by lia; apply SK5; lia).
  assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; exact Hds2).
  assert (IMGL : forall z, 65536 <= z < 827984 -> M (Z_to_bv 64 z) = None) by (intros z Hz; apply Himg; exact Hz).
  unfold PML.cfg. change PC_VISIT_BEGIN_OBJECT with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := G.HDECL)
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
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LB sp G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] heap_ok i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    (* [comment removed for export] *)
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    match goal with H : Nat.leb GT.NF (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
    match goal with H : Nat.eqb i 0 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
    match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
    destruct (FR E' HagE') as (F1 & F2 & F10 & F33 & F34 & G8 & G9 & G18 & G19 & G20 & G4).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
    { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
    assert (KEEP : forall y : reg, In (ridx y) KEPT -> getr R' y = getr R y).
    { intros y Hy. match goal with H : CL.ps_keeps ps KEPT = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPT GT.NF y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
    (* [comment removed for export] *)
    assert (HH2 : hi_heap HI LB cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app] in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _).
    (* [comment removed for export] *)
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LB sp G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP.
    change (CH.hd_scr G.HDECL) with SCRT in HP. unfold SCRT in HP.
    assert (KST : forall a, sp <= a < 2 ^ 64 -> ~ (V + 400 <= a < V + 404) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_stack_stk L LB M sp 8672 Wm a); [repeat split; try lia; exact Hds2 | lia | lia | rewrite LER; lia |].
      unfold Wm. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
    assert (KBL : forall A n a, In (A, n) LB -> A <= a < A + n -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros A n a Hin Ha. destruct (Hwf _ Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _ & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_block L LB sp 8672 Wm A n a Hin Ha); [lia | lia | rewrite LER, ILO, IHI in *; lia |].
      unfold Wm. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
    assert (AGV : forall a n, V <= a -> a + n <= V + 400 -> L5C.agree_on M M' a n) by (intros a n Ha Hn i1 Hi1; apply KST; lia).
    assert (AGS2 : L5C.agree_on M M' S2 24) by (intros i1 Hi1; apply KST; lia).
    assert (D400' : u32 M' (V + 400) (d + 1)).
    { pose proof (PB2.kword32_elim E' M' _ _ (V + 400) (CELL _ ltac:(eassumption)) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite F10; lia)) as T.
      unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 1) in T by lia. rewrite HdZ. exact T. }
    assert (HOBJ' : PMES2.enc_objx M' V S2 d (d + 1)).
    { apply (VBHK.enc_objx_agree_d M M' V S2 d d (d + 1) ltac:(lia) ltac:(unfold ENC_SIZE; lia)); unfold O_STACK, O_INDENT, O_COLON, O_DEPTH, O_COLUMN.
      - apply AGV; lia. - apply AGV; lia. - apply AGV; lia.
      - intros i1 Hi1. apply (Hdf1 (V + 296 + i1) ltac:(lia)); [|exact (Ecol i1 Hi1)]. split; [right; left; lia | unfold in_errno; rewrite LER; lia].
      - exact D400'. - rewrite (PMES2.enc_objx_eq M V S2 d) in HOBJ0. exact HOBJ0. }
    assert (HSTK' : stack_at M' V [] b capb).
    { apply (EK.stack_at_agree M M' V _ b capb ltac:(lia) ltac:(unfold ENC_SIZE; lia)); [unfold O_STACK; apply AGV; lia | | exact I2].
      intros Hne. assert (HinLB' : In (b, capb) LB) by (unfold LB, stack_blocks; destruct (Z.eqb_spec capb 0); [lia|]; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
      destruct (Hwf _ HinLB') as ((Q0 & Q1 & Q2 & Q3 & Q4) & _ & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4.
      split; [lia|]. split; [lia|]. intros i1 Hi1. apply (KBL b capb); [exact HinLB' | lia]. }
    assert (HSINK' : sink_at M' S2 rep).
    { apply (EK.sink_at_agree M M' S2 rep ltac:(lia) ltac:(lia) AGS2); [|exact I3].
      destruct rep as [s0|cap0 p0 s0]; [exact I|]. cbn [srep_blocks] in LB.
      assert (HinP : In (p0, cap0) LB) by (unfold LB; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (Hwf _ HinP) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _ & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4.
      split; [lia|]. split; [lia|]. intros i1 Hi1. apply (KBL p0 cap0); [exact HinP | lia]. }
    assert (HLITS' : lits_ok M').
    { apply (PML.lits_ok_agree M M'); [|exact Hlits]. intros a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
      apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X0; pose proof (PmLayout.ly_static L LAY a X0); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
      unfold Wm. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
    assert (HIMG' : img_ro M').
    { apply (EK.img_ro_hpres L LB sp 8672 Wm M M' LAY HP); [|exact Himg]. intros w a [<-|[]] Hw. unfold L5.in_rng, IMG_RO_HI in *. cbn [fst snd] in Hw. lia. }
    assert (HP2 : L5C.hpres L LBo sp 8672 (PMES2.W_head V S2) M M').
    { apply (VBHK.hpres_mono L LB LBo sp 8672 Wm _ M M'); [intros b0 Hb0; unfold LB; apply in_or_app; left; exact Hb0 | | exact HP].
      intros a Ho. unfold Wm. apply L5C.outside_cons; [|apply L5C.outside_nil]. intros Hin. apply (Ho (V + O_DEPTH, 4)); [right; left; reflexivity | unfold O_DEPTH; exact Hin]. }
    apply Z.eqb_eq in X. unfold MIDPC in X. rewrite X, LS.
    apply (Hcont fx' R' M' m1 LB cr LBo (PMES2.W_head V S2) HFP); [| exact HP2 | exact Hbv1 | exact HH2].
    exists rep. unfold PMES2.FRAME.
    split. { rewrite (REG 2%bv 2%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
    split; [rewrite (REG 8%bv 8%nat (EVar 10) ltac:(eassumption) eq_refl); cbn [edenot]; rewrite <- (Z_to_bv_bv_unsigned _ (ev E' 10)), F10; reflexivity|].
    split. { unfold O_STACK. rewrite (REG 9%bv 9%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split.
    { (* [comment removed for export] *) rewrite HdZ. repeat split.
      - rewrite (REG 18%bv 18%nat (EVar 34) ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
 }
    split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
    split.
    { (* [comment removed for export] *) unfold PMES2.frame_at.
      assert (FRM : forall off k (x : bv 5), has (SR.ps_cells ps) (KWord (SA (EVar 2) off) 8 (EVar k)) = true -> ev E' k = getr R x -> u64 M' (sp - 64 + (64 + off)) (bv_unsigned (getr R x))).
      { intros off k x Hh Hk. apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (sp - 64 + (64 + off)) _ (CELL _ Hh)); [unfold estart; cbn [a_base a_off edenot]; rewrite F2; lia|].
        cbn [edenot]. rewrite Hk. reflexivity. }
      split; [replace r with (bv_unsigned (getr R 1%bv)) by (rewrite Hra; apply u64_of_Z; lia); apply (FRM (-8) 1%nat 1%bv ltac:(eassumption)); rewrite <- (EV 1%bv); destruct HagE' as [AG _]; symmetry; apply AG; unfold GT.NF; lia|].
      split; [apply (FRM (-16) 8%nat 8%bv ltac:(eassumption) G8)|]. split; [apply (FRM (-24) 9%nat 9%bv ltac:(eassumption) G9)|].
      split; [apply (FRM (-32) 18%nat 18%bv ltac:(eassumption) G18)|]. intros Hf; discriminate Hf. }
    split; [intros j Hj; replace (sp - 64 + j) with (sp - 8672 + (j + 8608)) by lia; apply (L5C.hpres_defined _ _ _ _ _ _ _ HP); lia|].
    split.
    { (* [comment removed for export] *) unfold PMES2.head_post. cbn [depth length Z.of_nat Z.mul Z.add]. 
      split; [rewrite HdZ in HOBJ'; exact HOBJ'|]. split; [exact HSTK'|]. split; [exact HSINK'|]. rewrite I4. lia. }
    split; [exact HLITS'|]. split; [exact HIMG'|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    assert (BP : 0 <= PMES.bpot_st L capb) by (unfold PMES.bpot_st; pose proof (VBHK.kv_st_nonneg capb); pose proof (PmLayout.ly_bov L LAY); nia).
    unfold PMES.ecreditU, PMES.screditU, PMES.kenc, PMES.benc in *. cbn [g_rep g_scap] in Hcred. pose proof (VBHK.kv_st_nonneg capb). nia.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS. split; [exact (regs_ok_id R _ _)|].
    unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil]; first
      [ eapply CL5.kword64_intro; [ev_start | lia | lia | | eassumption]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
      | eapply PB.kword32_intro; [ev_start | lia | lia | | first [exact E240 | exact E400 | exact C1]]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
      | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E29 | exact E31 | exact E32 | exact C2]]
      | e_range
      | e_align OV3 | e_align SK1 | e_align P2
      | e_unk | e_wr | e_disj
      | (cbn [kentry_ok]; split; [lia | split; [lia | exact IMGL]])
      | idtac ].
    all: fail "entry knowledge left".
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (CH2.den E0 (nth 0 G.BLS [])) with (@nil (Z * Z)). exact HH.
  - exact Hfp.
Qed.
End Head.
End VBH_OR.
