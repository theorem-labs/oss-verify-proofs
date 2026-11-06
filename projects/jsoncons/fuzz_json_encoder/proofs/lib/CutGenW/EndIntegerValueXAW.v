(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SmallPtXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_eiv_xasan_T Cut_eiv_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_eiv_xasan.
Module GT := Cut_eiv_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module EIV.
Definition NEG : Z := 900560. Definition POS : Z := 902024.
Definition FFS : list (list (expr * Z * Z)) := [[]].
Definition CPF0 : list SGP.region := [(EVar 2, -16544, ELit 16544)].
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      ((Z.eqb pc NEG || Z.eqb pc POS) && CRB.tail_base_chk GT.NF pc c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && Nat.eqb i 0
       && CBA.regions_eqb (CC.cp_F c) CPF0 && CL.ps_reg_is ps 10 (EVar 10) && CL.ps_reg_is ps 11 (EVar 11) && CL.ps_reg_is ps 12 (EVar 12))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros [|[|i]]; reflexivity. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros [|[|i]]; reflexivity. Qed.
(* [comment removed for export] *)
Lemma num_final_len : forall s, PML.num_final s -> (1 <= length s)%nat.
Proof. intros [|c s] (k & Hk & Hin); [cbn in Hk; injection Hk as <-; cbn in Hin; exfalso; lia | cbn; lia]. Qed.
End EIV.

Section EndIntegerValueOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_xasan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FOOTXC : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a.            (* [comment removed for export] *)
(* [comment removed for export] *)
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variable benc : PMES.eghost -> Z.
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.
Hypothesis ENC_AGREE : PMXA.enc_agreeP enc_invA.                                  (* [comment removed for export] *)
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable CLA : Z.                                                                    (* [comment removed for export] *)
Hypothesis NEG_OK : PMXAW.end_number_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PMW.FEndInt EIV.NEG.      (* [comment removed for export] *)     (* [comment removed for export] *)
Hypothesis POS_OK : PMXAW.end_number_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PMW.FEndInt EIV.POS.      (* [comment removed for export] *)     (* [comment removed for export] *)
Lemma FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Proof. intros a (iv & Hiv & Hr). apply FOOTXC. exists iv. split; [unfold PMLA.FOOTX; apply in_or_app; left; exact Hiv | exact Hr]. Qed.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem end_integer_value_okw : PMXAW.end_integer_value_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA 876732.
Proof.
  unfold PMXAW.end_integer_value_specXAW, PMXAW.end_number_specXAW, PMXAW.ptrans_stalexAW, PMXAW.ptrans_gbxAW.
  intros mw LBo0 FF LK cr A sp r P V E SQ B kx bx g ps eg ww xw cw. unfold PMSA.cps_asan.
  (* [comment removed for export] *)
  change (PML.ps_blocks ps ++ LBo0 ++ PMES.g_lbv eg) with (PML.ps_blocks ps ++ (LBo0 ++ PMES.g_lbv eg)). set (LBo := LBo0 ++ PMES.g_lbv eg).
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (((Ha0 & Ha1 & Ha2) & HMORE & HST & HNUM) & Hsp32 & Hstksh & HPA & HPSH & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HINV & HLIT & HSYNC & Hkx & Hbx & HPC & OP & OV & OE & OS2 & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & HWB & HRM & HW4) Hcont.
  specialize (Hsp32 eq_refl). set (LB := PML.ps_blocks ps ++ LBo) in *. set (ps1 := PML.ps_set_win ps mw) in *.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.fobj in *. change (PMXA.ENDNUMXA_SCR XKA.VIS) with 16544 in *. change (PMXA.DVXA4 XKA.VISD) with 9 in Hroom.
  pose proof OP as (Pfr & P8 & Psh). pose proof OE as (Efr & E8 & Esh). pose proof OV as (Vfr & V8 & Vsh). pose proof OS2 as (S2fr & S28 & S2sh). unfold PMES.ENC_SIZE in Vfr, Vsh.
  pose proof HPA as HPA0. unfold PMSA.parser_at, PMLA.parser_at in HPA0.
  destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A16 & _ & _ & _ & _ & _ & _ & A23 & A24 & _ & _ & _ & _ & A29 & PDEF).
  cbn [PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_st PML.ps_set_win ps1] in A16, A23, A24.
  set (bptr := PML.ps_bptr ps) in *. set (bcap := PML.ps_bcap ps) in *. set (buf := PML.ps_buf ps) in *.
  destruct A23 as ((_ & W224 & W232 & W240 & BBS & BNUL) & BC8 & BLT).
  pose proof (EIV.num_final_len buf HNUM) as BL1.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct (CL5A.infr_rng L ar LB FF V 408 RFx Vfr ltac:(clear; lia)) as (VR1 & VR2 & VR3 & VR4 & VR5 & VR6 & VR7).
  destruct (CL5A.infr_rng L ar LB FF SQ 24 RFx S2fr ltac:(clear; lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5. change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7.
  change (hid (V + 408 <= 2147446784 \/ 17594333495296 <= V)) in VR5. change (hid (V + 408 <= hl_img_lo L \/ hl_img_hi L <= V)) in VR7.
  change (hid (SQ + 24 <= 2147446784 \/ 17594333495296 <= SQ)) in SR5. change (hid (SQ + 24 <= hl_img_lo L \/ hl_img_hi L <= SQ)) in SR7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  (* [comment removed for export] *)
  assert (INB : In (bptr, bcap) LB) by (unfold LB, PML.ps_blocks; left; reflexivity).
  assert (INS : In (PML.ps_sb ps, PML.ps_scap ps) LB) by (unfold LB, PML.ps_blocks; right; left; reflexivity).
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (bptr, bcap) INB) as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & _). cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT _ INS) as ((KS0 & _ & KS16 & KS3 & KS4 & (_ & _ & KS7)) & _). cbn [fst snd] in KS0, KS16, KS3, KS4, KS7.
  pose proof (CHA.mod8_of_16 _ KB16) as KB8. pose proof (CHA.mod8_of_16 _ KS16) as KS8.
  change (hid (bptr + bcap <= 2147446784 \/ 17594333495296 <= bptr)) in KB6.
  assert (G33 : 33 <= bcap / 8) by (apply Z.div_le_lower_bound; clear - A24; lia).
  assert (N8' : bcap = 8 * (bcap / 8)) by (pose proof (Z_div_mod_eq_full bcap 8) as D; rewrite BC8 in D; clear - D; lia).
  pose proof (proj1 HPSH) as BSH. cbn [PML.ps_bptr PML.ps_bcap] in BSH. fold bptr bcap in BSH.
  assert (BZ : shadow_zero M bptr (bcap / 8)).
  { intros j Hj. destruct BSH as [BZ0 _]. apply BZ0. clear - Hj N8'. lia. }
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [bptr; bcap; bcap / 8] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 P) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 V) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 E) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 bptr) by reflexivity. assert (V33 : ev E0 33 = Z_to_bv 64 bcap) by reflexivity. assert (V34 : ev E0 34 = Z_to_bv 64 (bcap / 8)) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = V) by (rewrite V11; apply u64_of_Z; clear - VR3 VR6; lia).
  assert (U12 : bv_unsigned (ev E0 12) = E) by (rewrite V12; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = bptr) by (rewrite V32; apply u64_of_Z; clear - KB0 KB7 KB3; lia).
  assert (U33 : bv_unsigned (ev E0 33) = bcap) by (rewrite V33; apply u64_of_Z; clear - KB0 KB7 KB3; lia).
  assert (U34 : bv_unsigned (ev E0 34) = bcap / 8) by (rewrite V34; apply u64_of_Z; clear - G33 N8' KB7 KB0; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 16544) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := PMLA.W_parA IC P E ++ PMXA.W_encA IC V SQ). set (Wo := ([] : list L5.range)).      (* [comment removed for export] *)
  assert (WINC : incl Wo WW) by (intros w []).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a [] _).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a))
    by (intros rg []).
  assert (SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (Mx : word -> option byte) (_ : Model) => Mx = M).
  (* [comment removed for export] *)
  assert (FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7077888).
  { intros a Hf. destruct Hf as (iv & Hiv & Hr); cbn in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]); destruct Hiv. }
  assert (PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                   \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                   \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> PMLA.in_foot IC a).
  { intros a Ha. pose proof PMTA.C_xasan_wf as [T1 T2 T3 _ T5 T6 T7 T8 _ _]. unfold PMTA.cell_in_foot, PmIcptIfaceA.ATEXIT_TAB_BYTES in *.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]];
      [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha | apply (proj2 (proj2 T7)); exact Ha | apply (proj2 (proj2 T8)); exact Ha
      | apply (proj2 (proj2 T1)); exact Ha | subst a; apply (proj2 (proj2 T2)); clear; lia | apply (proj2 (proj2 T3)); exact Ha]. }
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok) as AIOWF.
  rewrite <- LS in FPM.
  change 876732 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS EIV.FFS Cred 9 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact EIV.heap_ok.
  - (* [comment removed for export] *) intros i c kk ps0 j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EIV.leaf_ok _ _ _ _ _ IL) as X. exact (Bool.diff_false_true X).
  - intros i c kk ps0 j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EIV.leaf_ok _ _ _ _ _ IL) as X. exact (Bool.diff_false_true X).
  - (* [comment removed for export] *)
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ EIV.leaf_ok _ _ _ _ _ IL) as X. unfold EIV.leaf_chk in X. cbn beta iota in X.
    apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yi].
    apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Ypc Xbase].
    apply Nat.eqb_eq in Yi. subst i. apply CBA.regions_eqb_eq in YF.
    assert (OKpc : PMXAW.end_number_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PMW.FEndInt pc) by (apply orb_prop in Ypc; destruct Ypc as [Hp|Hp]; apply Z.eqb_eq in Hp; rewrite Hp; [exact NEG_OK | exact POS_OK]).
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXI].
    refine (CRB.tail_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS EIV.FFS Cred 9 STKF SCRP NF32 U2 V4 WINC WOK Hffrs WRS_OK
              K PMSA.fp_ok DEF0 S6 HKnil R r EV Hra Hraok pc 16544 9 0%nat c ps0 Xbase _ (EIV.ffs_i 0) _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA HFP Hag HLF _);
      [exact Xfoot | rewrite SCRV; clear; lia | clear; lia |].
    intros cr1 LK1 HRP HP HH1 HLK1 HC1 HagE' HA'. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS 0 E1 = LB) by (unfold CHA.curB; rewrite EIV.bls_i; reflexivity). rewrite HB in *.
    (* [comment removed for export] *)
    assert (HXM : M1 = M) by exact HXI.
    pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
    assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat ltac:(unfold GT.NF; clear; lia)); exact U2).
    set (Sg := fun a => 0 <= a < 2 ^ 64 /\ (a < sp - 16544 \/ sp <= a)).
    assert (AG : forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a (Ha & Ho). rewrite <- HXM. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside, EIV.CPF0.
      apply Forall_cons; [|apply Forall_nil]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W2, !L5.unsigned_lit by (clear - Ha; lia) || (rewrite W2; rewrite L5.unsigned_lit by exact Ha; cbn [edenot]; rewrite L5.unsigned_lit by (clear; lia)).
      clear - Ho. lia. }
    assert (OUTW : forall a n, 0 <= a -> a + n <= sp - 16544 -> PTA.out Sg a n).
    { intros a n Ha Hn. split; [exact Ha|]. split; [clear - Hn S3 SP1; lia|]. intros i Hi. split; [clear - Ha Hi Hn S3 SP1; lia | left; clear - Hi Hn; lia]. }
    assert (OBLK : forall u n, In (u, n) LB -> PTA.out Sg u n /\ (forall a, in_shadow_of u n a -> Sg a)).
    { intros u n Hin. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) Hin) as ((D0 & _ & _ & D3 & D4 & (_ & _ & D7)) & _). cbn [fst snd] in D0, D3, D4, D7.
      split; [apply OUTW; [clear - D0; lia | clear - D4 S2; lia]|]. intros a Ha. pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha) as RG. split; [clear - RG; lia | left; clear - RG CL S2; lia]. }
    assert (OSH : forall o n, 0 <= o -> 0 < n -> o + n <= 2 ^ 47 -> forall a, in_shadow_of o n a -> Sg a).
    { intros o n Ho Hn Hhi a Ha. pose proof (SHR o n a Ho Hn Hhi Ha) as RG. split; [clear - RG; lia | left; clear - RG CL S2; lia]. }
    (* [comment removed for export] *)
    assert (XSG : forall a, XKA.xfoot IC V SQ eg a -> Sg a).
    { intros a Ha. unfold hid in VR5, SR5.
      destruct (XKA.xfoot_cases IC V SQ eg a Ha) as [Hv|[Hs|[(b & Hb & Hr)|[Hsh|Hl]]]].
      - unfold PMES.ENC_SIZE in Hv. split; [clear - Hv VR3 VR6; lia | left; clear - Hv VR4 S2; lia].
      - split; [clear - Hs SR3 SR6; lia | left; clear - Hs SR4 S2; lia].
      - assert (HbL : In b LB) by (unfold LB, LBo; apply in_or_app; right; apply in_or_app; right; exact Hb). destruct b as [u n]. cbn [fst snd] in Hr.
        destruct (OBLK u n HbL) as ((X0 & X1 & X2) & XS). destruct Hr as [Hr|Hr]; [exact (X2 a Hr) | exact (XS a Hr)].
      - unfold PMES.ENC_SIZE in Hsh. destruct Hsh as [Hsh|Hsh]; [exact (OSH V 408 VR3 ltac:(clear; lia) VR6 a Hsh) | exact (OSH SQ 24 SR3 ltac:(clear; lia) SR6 a Hsh)].
      - unfold PMLA.LIT_LO, PMLA.LIT_HI in Hl. cbn in Hl. split; [clear - Hl; lia | left; clear - Hl CL S2; lia]. }
    destruct (XKA.xinv_keep L IC enc_invA ENC_AGREE XKA.lits_inside_xasan V SQ M M' eg (fun a Ha => AG a (XSG a Ha)) (conj HINV HLIT)) as [HINV' HLIT'].
    eexists _, _. split; [exact (OKpc mw LBo0 FF LK1 cr A1 sp r P V E SQ B kx bx g ps eg ww xw cw)|].
    split.
    { (* [comment removed for export] *)
      unfold PMSA.std_args, PMSA.a0, PMSA.a1, PMSA.a2, PMSA.stksh, PMSA.parser_at, PMSA.parser_sh, PMSA.win_okA, PMSA.vis_at, PMSA.ec_at, PMSA.ls_ok, PMSA.fobj. fold LB ps1.
      assert (RG : forall q v, CL.ps_reg_is ps0 q (EVar q) = true -> (q < GT.NF)%nat -> ev E0 q = Z_to_bv 64 v -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 v).
      { intros q v Hq Hlt Hv. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). cbn [edenot]. rewrite <- (proj1 HagE' q Hlt). exact Hv. }
      split; [split; [split; [exact (RG 10%nat P Y10 ltac:(unfold GT.NF; clear; lia) V10) | split; [exact (RG 11%nat V Y11 ltac:(unfold GT.NF; clear; lia) V11) | exact (RG 12%nat E Y12 ltac:(unfold GT.NF; clear; lia) V12)]] | split; [exact HMORE | split; [exact HST | exact HNUM]]]|].
      split; [intros _; exact Hsp32|].
      split.
      { apply (PTA.stksh_ag ar M M' sp 16544); [|exact Hstksh]. intros a Ha.
        assert (AL : (sp - 16544) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 16544) with ((2 * (sp / 16) - 2068) * 8) by lia; apply Z_mod_mult).
        destruct (PTA.stksh_rng ar sp 16544 a ltac:(clear - S2; lia) AL C8 (proj2 SP1) STOP ltac:(clear - CL; lia) Ha) as (G1 & G2). apply AG. split; [exact G1|]. left.
        unfold in_shadow_of, S, SB in G2. clear - G2 CL S2. lia. }
      split.
      { (* [comment removed for export] *)
        assert (PA' : PMLA.parser_at (hl_segs L) IC M' P (PML.PS (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) (PML.ps_level ps1) (PML.ps_stack ps1)
                                                          (PML.ps_sb ps1) (PML.ps_scap ps1) (PML.ps_bcap ps1) (PML.ps_bptr ps1) (PML.ps_buf ps1) (PML.ps_win ps1))).
        { apply (PTA.parser_at_st (hl_segs L) IC M M' Sg AG P ps1 (PML.ps_st ps1)).
          - intros k n Hk Hn _. apply OUTW; [clear - O3 Hk; lia | clear - O4 Hk Hn S2; lia].
          - exact (proj1 (OBLK _ _ INB)).
          - exact (proj1 (OBLK _ _ INS)).
          - exact HPA.
          - apply (PTA.u8_ag (hl_segs L) M M' Sg AG); [apply OUTW; [clear - O3; lia | clear - O4 S2; lia] | exact A16].
          - rewrite (AG (P + 208) ltac:(split; [clear - O3 O6; lia | left; clear - O4 S2; lia])). apply PDEF. clear; lia. }
        unfold ps1 in PA' |- *. destruct ps; exact PA'. }
      split.
      { apply (PTA.parser_sh_ag M M' Sg AG ps); [clear - KB3; cbn; fold bcap; lia | split; [clear; lia | unfold ps1 in A29; cbn [PML.ps_stack PML.ps_scap PML.ps_set_win] in A29; exact A29] | exact KB8 | exact KS8 | exact (proj2 (OBLK _ _ INB)) | exact (proj2 (OBLK _ _ INS)) | exact HPSH]. }
      split; [exact HWF|].
      split.
      { apply (PTA.win_okA_ag M M' Sg AG LBo0 ps); [| | exact HWIN].
        - intros ch a Hch Ha. assert (HinC : In (ch, 16384) LB) by (unfold LB, LBo; apply in_or_app; right; apply in_or_app; left; exact Hch).
          destruct (OBLK _ _ HinC) as ((_ & _ & OB) & OS). destruct Ha as [Ha|Ha]; [exact (OB a Ha) | exact (OS a Ha)].
        - intros ch Hch. assert (HinC : In (ch, 16384) LB) by (unfold LB, LBo; apply in_or_app; right; apply in_or_app; left; exact Hch).
          destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) HinC) as ((D0 & _ & D16 & _ & _ & (_ & _ & D7)) & _). cbn [fst snd] in D0, D16, D7.
          split; [clear - D0; lia|]. split; [clear - D7; lia | exact (CHA.mod8_of_16 _ D16)]. }
      split; [exact HBB|].
      split; [apply (PTA.vis_at_ag (hl_segs L) IC M M' Sg AG); [apply OUTW; [clear - VR3; lia | clear - VR4 S2; lia] | exact HVIS]|].
      split; [apply (PTA.ec_at_ag (hl_segs L) IC M M' Sg AG); [apply OUTW; [clear - Q3; lia | clear - Q4 S2; lia] | exact HEC]|].
      split.
      { apply (PTA.ls_ok_ag (hl_segs L) IC M M' Sg AG g HG); [|intros a Ha; exact (PTKF a Ha) | exact HLS].
        intros a Ha. assert (RG' : 65536 <= a < 7077888) by (destruct Ha as [Ha|Ha]; [cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan] in Ha; clear - Ha; lia | exact (FOOTCL a Ha)]).
        split; [clear - RG'; lia|]. split; [clear - RG'; lia | left; clear - RG' CL S2; lia]. }
      split; [exact HG|].
      split; [exact HINV'|]. split; [exact HLIT'|]. split; [exact HSYNC|]. split; [exact Hkx|]. split; [exact Hbx|]. split; [exact HPC|].
      assert (FOBJ : forall o n g, CL5A.ainfr FF o n -> o mod 8 = 0 -> 0 < g -> n = 8 * g -> 0 <= o -> o + n <= 2 ^ 47 -> shadow_zero M o g -> CL5A.ainfr FF o n /\ o mod 8 = 0 /\ shadow_zero M' o g).
      { intros o n g' Hfr Ho8 Hg Hn Ho0 Ohi Hz. split; [exact Hfr|]. split; [exact Ho8|]. apply (PTA.shadow_zero_ag M M' Sg AG); [|exact Hz].
        intros j Hj. apply (OSH o n Ho0 ltac:(clear - Hg Hn; lia) Ohi). rewrite Hn. apply (CL5A.shreg_in_shadow o g'); [exact Ho8 | exact Hg | unfold S, SB; clear - Hj; lia]. }
      split; [exact (FOBJ P 272 34 Pfr P8 ltac:(clear; lia) eq_refl ltac:(clear - O3; lia) O6 Psh)|].
      split; [change (408 / 8) with 51 in Vsh; exact (FOBJ V 408 51 Vfr V8 ltac:(clear; lia) eq_refl ltac:(clear - VR3; lia) VR6 Vsh)|].
      split; [exact (FOBJ E 16 2 Efr E8 ltac:(clear; lia) eq_refl ltac:(clear - Q3; lia) Q6 Esh)|].
      split; [change (24 / 8) with 3 in S2sh; exact (FOBJ SQ 24 3 S2fr S28 ltac:(clear; lia) eq_refl ltac:(clear - SR3; lia) SR6 S2sh)|].
      split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|]. split; [exact AP4|]. split; [exact AP5|]. split; [exact AP6|].
      (* [comment removed for export] *)
      split; [| split; [exact HRM | exact HW4]].
      apply (SPTAW.win_bytesA_ag L M M' Sg AG LBo0 ps ps ww); [| exact HWIN | exact HWB | reflexivity].
      intros ch a Hch Ha. assert (HinC : In (ch, 16384) LB) by (unfold LB, LBo; apply in_or_app; right; apply in_or_app; left; exact Hch).
      destruct (OBLK _ _ HinC) as ((_ & _ & OB) & _). exact (OB a Ha). }
    (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPOST HRP2 HP2 Hrt2 HA2 Hmo2 HLK2 HH2.
    pose proof HPOST as (ps' & code & g' & eg' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB' & HLBk & HWc & _).
    apply (Hcont fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPOST HRP2); [| exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
    rewrite SCRV in HP. rewrite HWc. rewrite HWc in HP2. rewrite HLBk in HP2 |- *.
    apply (CRB.ahpres_trans L ar LBo0 LB LBo0 FF sp 16544 16544 WW WW WW M M' M2 HP HP2);
      [unfold LB, LBo; intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx | apply incl_refl | clear; lia | clear - S3 SP1; lia | clear - CL; lia | clear - S2; lia
      | intros w a Hw Hin; exists w; split; assumption | intros w a Hw Hin; exists w; split; assumption].
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VOB : forall o n, CL5A.ainfr FF o n -> 0 < n -> CL5A.visr (ahid A model) o n /\ (forall a, in_shadow_of o n a -> ahid A model (Z_to_bv 64 a) = false)).
    { intros o n Hfr Hn. split.
      - intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o n (o + q) RFx Hfr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3).
      - intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o n a RFx Hfr Hn Ha) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    destruct (VOB P 272 Pfr ltac:(clear; lia)) as (VP & VSP).
    assert (VS : CL5A.visr (ahid A model) (sp - 16544) 16544).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VB : CL5A.visr (ahid A model) bptr bcap).
    { intros q Hq. apply CLV; [clear - Hq KB0 KB7; lia | left; exists (bptr, bcap); split; [exact INB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq KB6. lia. }
    assert (VBS : forall a, in_shadow_of bptr bcap a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. pose proof (SHR bptr bcap a ltac:(clear - KB0; lia) KB3 KB7 Ha) as RG. apply CLV; [clear - RG; lia | do 6 right; exists (bptr, bcap); split; [exact INB | exact Ha] |].
      exact (CL5A.not_stk_shadow_sh L ar LB FF bptr bcap a RFx ltac:(clear - KB0; lia) KB3 KB4 Ha). }
    set (Mv := CCA.vis A model M).
    assert (DP : L5.defined Mv P 272).
    { apply (CL5A.defined_vis _ M P 272 VP). destruct Pfr as (f & Hf & G1 & G2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFT f Hf) as (_ & _ & _ & _ & Fdef & _).
      intros q Hq. replace (P + q) with (ff_addr f + (P - ff_addr f + q)) by (clear; lia). apply Fdef. clear - Hq G1 G2. lia. }
    assert (DS : L5.defined Mv (sp - 16544) 16544) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DB : L5.defined Mv bptr bcap) by (apply (CL5A.defined_vis _ M _ _ VB); exact KBdef).
    assert (PD : 0 <= P / 8 <= 2 ^ 44 - 34) by (split; [apply Z.div_pos; clear - O3; lia | apply Z.div_le_upper_bound; clear - O6; lia]).
    assert (UVP : CL5A.uv E0 (EVar 10) = P) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    assert (UVB : CL5A.uv E0 (EVar 32) = bptr) by (unfold CL5A.uv; cbn [edenot]; exact U32).
    change (272 / 8) with 34 in Psh.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kwr_intro with (A := P) (N := 272); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DP].
    + eapply CL5.kword64_intro with (A := P + 224) (z := bcap + 1); [ev0 | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - KB0 KB7 KB3; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ P 272 (P + 224) 8 VP ltac:(clear; lia) ltac:(clear; lia)) | exact W224].
    + eapply CL5.kword64_intro with (A := P + 240) (z := bptr); [ev0 | clear - O3; lia | clear - O6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ P 272 (P + 240) 8 VP ltac:(clear; lia) ltac:(clear; lia)) |].
      replace (P + 240) with (P + 224 + 16) by (clear; lia). exact W240.
    + eapply CL5.krange_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact P8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 34 P UVP); [clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VSP; apply (CL5A.shreg_in_shadow P 34); [exact P8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Psh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := P) (N2 := 272); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := bcap); [lin_eval; rw_atoms; clear; lia | clear - A24 KB0 KB7; lia | clear - A24 KB0 KB7; lia].
    + eapply CL5.kalign_intro with (v := bcap); [lin_eval; rw_atoms; clear; lia | clear - A24 KB0 KB7; lia | clear; lia | exact BC8].
    + eapply CL5.krange_intro with (v := bptr); [lin_eval; rw_atoms; clear; lia | clear - KB0 KB7 KB3; lia | clear - KB0 KB3 KB4 SP1 CL; lia].
    + eapply CL5.kalign_intro with (v := bptr); [lin_eval; rw_atoms; clear; lia | clear - KB0 KB7 KB3; lia | clear; lia | exact KB16].
    + eapply CL5.kunk_intro with (A := bptr) (N := bcap); [ev0 | unfold elenZ; cbn [edenot]; exact U33 | clear - KB0; lia | clear - KB7; lia | clear - KB7 KB3; lia | exact DB].
    + eapply CL5A.kzero_intro with (A := bptr / 8 + SB) (N := bcap / 8); [rewrite CL5A.estart_srl3', UVB; reflexivity | unfold elenZ; cbn [edenot]; exact U34 | unfold SB; clear - KB0; lia | unfold SB; clear - KB0 KB7 KB3; pose proof (Z.div_le_upper_bound bptr 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia | unfold SB; clear - KB0 KB7 KB3; pose proof (Z.div_le_upper_bound bptr 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VBS; rewrite N8'; apply (CL5A.shreg_in_shadow bptr (bcap / 8)); [exact KB8 | clear - G33; lia | unfold S, SB; clear - Hj; lia] | exact (BZ j Hj)].
    + eapply CL5.krange_intro with (v := bcap / 8); [lin_eval; rw_atoms; clear; lia | clear - G33 KB7 KB0 N8'; lia | clear - G33 KB7 KB0 N8'; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := bptr) (N2 := bcap); [reflexivity | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U33 | unfold hid in KB6; clear - KB6; lia].
    + eapply CL5.kwr_intro with (A := sp - 16544) (N := 16544); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp32].
    + eapply CL5.kdisj_intro with (A1 := sp - 16544) (N1 := 16544) (A2 := P) (N2 := 272); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 16544) (N1 := 16544) (A2 := bptr) (N2 := bcap); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U33 | clear - KB4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := P) (N1 := 272) (A2 := bptr) (N2 := bcap); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U33 |].
      destruct Pfr as (f & Hf & F1 & F2). destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (bptr, bcap) INB) as (_ & _ & _ & _ & QF0). pose proof (QF0 f (in_or_app _ _ _ (or_introl Hf))) as QF. cbn [fst snd] in QF. clear - QF F1 F2. lia.
    + eapply CL5.kunk_intro with (A := sp - 16544) (N := 16544); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
  - (* [comment removed for export] *)
    split; [|reflexivity].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite EIV.bls_i, EIV.ffs_i. cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.
Print Assumptions end_integer_value_okw.
End EndIntegerValueOk.
