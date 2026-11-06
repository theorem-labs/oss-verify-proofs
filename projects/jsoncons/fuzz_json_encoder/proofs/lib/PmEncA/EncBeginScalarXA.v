(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA EncKitA EncBridgesA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_begin_scalar_root_xasan_T Cut_begin_scalar_root_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Ltac lia ::= L5FastLia.plia.

Module G := Cut_begin_scalar_root_xasan.
Module GT := Cut_begin_scalar_root_xasan_T.

Module EBSA.
Import PMES.
Definition RETPC : Z := 766060.      (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition VE := EVar 10. Definition S2E := EVar 32. Definition BE := EVar 34.
Definition FFS : list (list (expr * Z * Z)) := [[]].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition CPF0 : list SGP.region := [(EVar 2, -4624, ELit 4624); (VE, 296, ELit 8)].
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      (Nat.eqb i 0 && CBA.regions_eqb (CC.cp_F c) CPF0 && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && CBA.exit_base_chk GT.NF RETPC c ps)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
End EBSA.
Import PMES.

Section BeginScalarOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable CL : Z.                        (* [comment removed for export] *)
Abbreviation IC := PMLA.C_xasan.
Abbreviation EC := PMESA.EC_xasan.
Abbreviation RSEGS := (hl_segs L).

Definition hid (P : Prop) : Prop := P.

(* [comment removed for export] *)
Theorem begin_scalar_root_ok : forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : eghost),
  PMSA.cps_asan L ar HI PMESA.PC_BEGIN_SCALAR_xasan r sp PMESA.BSCALAR_SCRA (LBo ++ g_lbv g) FF LK cr A PMESA.NEWLINE_DA
    (fun R M => PMSA.a0 R V /\ PMSA.stksh ar M sp PMESA.BSCALAR_SCRA /\ PMESA.enc_invA L IC EC M V S2 g /\ g_es g = [] /\ PMLA.img_ro IC M /\
                PMESA.ecreditA L CL cr g kx bx /\ PMESA.objs_encA M FF V S2)
    (fun R M R' M' LB' cr' LBk W => PMESA.enc_invA L IC EC M' V S2 g /\ LB' = LBo ++ g_lbv g /\ LBk = LBo /\ W = PMESA.W_h V S2 /\ cr' = cr).
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hstksh & Hinv & Hes & Himg & Hcred & Hobjs) Hcont.
  unfold PMSA.a0, PMESA.BSCALAR_SCRA, PMESA.NEWLINE_SCRA, PMESA.STRX_SCRA, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMESA.NEWLINE_DA in *.
  change (64 + (192 + (256 + (16 + 4096)))) with 4624 in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  destruct (L5A.aly_cost L C LAY) as (KPM & BLIN & BOV).
  (* [comment removed for export] *)
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL0 & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2' & S3 & S4 & S5 & S6).
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PMLA.apart in OV1, OV2, OV3, OAP. change (408 / 8) with 51 in OV3. change (24 / 8) with 3 in OS3.
  destruct (CL5A.infr_rng L ar _ _ V 408 RFx OV1 ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar _ _ S2 24 RFx OS1 ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. exfalso. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  set (b := g_sb g).
  assert (B47 : 0 <= b /\ b <= 2 ^ 47).
  { destruct I2 as (_ & _ & _ & _ & [(_ & E)|(k0 & Hk0 & Hc)] & _); [unfold b; rewrite E; clear; lia|].
    destruct I7 as (_ & _ & _ & _ & RB). assert (Hin : In (g_sb g, g_scap g) (g_lbv g)).
    { unfold g_lbv, stack_blocks. apply in_or_app. right. assert (0 < 2 ^ k0) by (apply Z.pow_pos_nonneg; clear - Hk0; lia).
      destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [clear - E H Hc; lia | left; reflexivity]. }
    destruct (RB _ Hin) as (R0 & _ & R2 & R3). cbn [fst snd] in *. unfold b. clear - R0 R2 R3. lia. }
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; 0; b] 0))) (fun _ => @nil (bv 8))).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity. assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2' S3 SP1 CL0; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; clear - B47; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 4624) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2' S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (SCR8 : CH.hd_scr G.HDECL mod 8 = 0) by (rewrite SCRV; reflexivity).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := PMESA.W_h V S2). set (Wo := WW).
  assert (WINC : incl Wo WW) by (apply incl_refl).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin.
    - exact (CL5A.infr_wok L ar LBo FF sp _ V 408 a (CHA.rng_incl L ar _ _ LBo FF RFx ltac:(intros y Hy; apply in_or_app; left; exact Hy) ltac:(apply incl_refl)) OV1 ltac:(clear - Hin; lia)).
    - exact (CL5A.infr_wok L ar LBo FF sp _ S2 24 a (CHA.rng_incl L ar _ _ LBo FF RFx ltac:(intros y Hy; apply in_or_app; left; exact Hy) ltac:(apply incl_refl)) OS1 Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (V + O_COLUMN, 8). split; [left; reflexivity | unfold L5.in_rng, O_COLUMN; cbn [fst snd]; clear - Ha; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (S2, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBo FF sp G.HDECL a)).
  { pose proof (CHA.rng_incl L ar _ _ LBo FF RFx ltac:(intros y Hy; apply in_or_app; left; exact Hy) ltac:(apply incl_refl)) as RFo.
    intros rg Hrg. unfold G.HDECL, GT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, elenZ in Ha.
    - unfold estart in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (CL5A.infr_wok L ar LBo FF sp (CH.hd_scr G.HDECL) V 408 a RFo OV1 ltac:(clear - Ha; lia)) as (G1 & G2 & G3). exact (conj G1 (conj (aclientw_client _ _ _ _ _ _ _ G2) G3)).
    - unfold estart in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (CL5A.infr_wok L ar LBo FF sp (CH.hd_scr G.HDECL) V 408 a RFo OV1 ltac:(clear - Ha; lia)) as (G1 & G2 & G3). exact (conj G1 (conj (aclientw_client _ _ _ _ _ _ _ G2) G3)).
    - rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow V 51 a OV2 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 51) with 408 in SH.
      destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr G.HDECL) V 408 a RFo OV1 ltac:(clear; lia) SH) as (G1 & G2 & G3). exact (conj G1 (conj (aclientw_client _ _ _ _ _ _ _ G2) G3)).
    - rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv in Ha. cbn [edenot] in Ha. rewrite U32 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow S2 3 a OS2 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr G.HDECL) S2 24 a RFo OS1 ltac:(clear; lia) SH) as (G1 & G2 & G3). exact (conj G1 (conj (aclientw_client _ _ _ _ _ _ _ G2) G3)). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  assert (IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (W_app : forall w a, In w WW -> L5.in_rng w a -> ~ (2147446784 <= a < 17594333495296) /\ ~ (PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC)).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin; cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan]; unfold hid in O5, Q5; clear - Hin O5 Q5 O1 Q1 FSLO; split; lia. }
  assert (W_S2 : In (S2, 24) WW) by (right; left; reflexivity).
  assert (W_COL : forall a, V + O_COLUMN <= a < V + O_COLUMN + 8 -> exists w, In w WW /\ L5.in_rng w a).
  { intros a Ha. exists (V + O_COLUMN, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  (* [comment removed for export] *)
  set (GR := stack_blocks (g_sb g) (g_scap g)).
  set (XIv := fun (g1 : eghost) (i : nat) (E : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) => PMESA.enc_invA L IC EC M1 V S2 g1 /\ g1 = g).
  set (CredV := fun (g1 : eghost) (i : nat) (E : env) (cr1 : credit) => cr1 = cr).
  set (gB := EBA.gB GR).
  assert (GBL : gB g = g_lbv g) by reflexivity.
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (Hffrs0 : CHA.ffrs FF sp) by exact Hffrs.
  unfold PMSA.cfg. change PMESA.PC_BEGIN_SCALAR_xasan with (CC.cp_pc G.cp0).
  eapply (CHV.cert_soundV L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS EBSA.FFS 2 eghost gB CredV XIv STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact EBSA.heap_ok.
  - intros g1 i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EBSA.leaf_ok _ _ _ _ _ IL) as X. exact (Bool.diff_false_true X).
  - intros g1 M0c OKV i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ EBSA.leaf_ok _ _ _ _ _ IL) as X. exact (Bool.diff_false_true X).
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ EBSA.leaf_ok _ _ _ _ _ IL) as X. unfold EBSA.leaf_chk in X.
    apply andb_prop in X as [X Xbase]. apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [X0 YF]. apply Nat.eqb_eq in X0. subst i. apply CBA.regions_eqb_eq in YF.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXI]. destruct HXI as [HX1 ->].
    assert (DEFC : L5.defined M0c (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by exact (CHV.okV_def0 L ar M LBo FF sp G.HDECL WW M0c OKV).
    pose proof (CHV.Wo_okV L ar LBo FF sp G.HDECL Wo eghost gB WOK g) as WOKg.
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M0c model A (CHV.LBr LBo eghost gB g) FF LK sp G.HDECL WW Wo G.BLS EBSA.FFS (CredV g) 2 STKF SCRP NF32 U2 WINC WOKg WRS_OK
              K DEFC R r EV Hra Hraok EBSA.RETPC 0%nat c ps _ Xbase Yfoot eq_refl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact EBSA.ret_at|].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    unfold CredV in HC1. subst cr1.
    apply (CHV.ahpres_rebase L ar GT.NF M LBo FF sp G.HDECL WW eghost gB NF32 g M0c M' OKV) in HP.
    rewrite SCRV in HP.
    (* [comment removed for export] *)
    assert (W2 : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; clear; lia); exact U2).
    assert (W10 : bv_unsigned (ev E' 10) = V) by (destruct HagE' as [AG _]; rewrite <- (AG 10%nat) by (unfold GT.NF; clear; lia); exact U10).
    assert (AGR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 4624 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1 N2. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside, EBSA.CPF0, EBSA.VE. rewrite L5.unsigned_lit by exact Ha.
      repeat (apply Forall_cons); try (apply Forall_nil); cbn [fst snd]; unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite ?W2, ?W10; rewrite u64_of_Z by (clear; lia); clear - N1 N2; lia. }
    (* [comment removed for export] *)
    assert (SHB : forall p n j, 0 <= p -> p mod 8 = 0 -> 0 < n -> p + n <= 2 ^ 47 -> 0 <= j < n / 8 -> M' (Z_to_bv 64 (S p + j)) = M1 (Z_to_bv 64 (S p + j))).
    { intros p n j P0 P8 N0 PN Hj.
      pose proof (Z.mul_div_le n 8 ltac:(clear; lia)) as ML.
      pose proof (CL5A.shreg_in_shadow p (n / 8) (S p + j) P8 ltac:(clear - Hj; lia) ltac:(unfold S; clear - Hj; lia)) as SH.
      pose proof (CHA.shadow_range p (8 * (n / 8)) (S p + j) P0 ltac:(clear - Hj; lia) ltac:(clear - PN ML; lia) SH) as SR.
      apply AGR; [clear - SR; lia | clear - SR S2' CL0; lia | unfold hid in O5; clear - SR O5; lia]. }
    assert (HINV : PMESA.enc_invA L IC EC M' V S2 g).
    { pose proof HX1 as (_ & _ & _ & _ & _ & _ & (Z1 & Z2 & Z3 & Z4 & RB)). unfold ENC_SIZE in Z2.
      assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> (a + n <= sp - 4624 \/ sp <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M1 M' a n).
      { intros a n H0 H1 H2 H3 i Hi. apply AGR; clear - H0 H1 H2 H3 Hi; lia. }
      apply (EKA.enc_invA_agree L IC EC M1 M' V S2 g); [| | | | | exact HX1].
      - apply AG; unfold O_COLUMN; clear - Z1 Z2 O4 S2'; lia.
      - apply AG; unfold O_COLON, ENC_SIZE; clear - Z1 Z2 O4 S2'; lia.
      - pose proof HX1 as (I1' & _). destruct I1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
        intros i Hi. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). apply X. exact Hi.
      - apply AG; clear - Q3 Q4 Q6 S2' OAP; lia.
      - intros bb Hbb. destruct (RB bb Hbb) as (Rb0 & Rb1 & Rb2 & Rb3).
        assert (HinL : In bb (CHA.curB (CHV.LBr LBo eghost gB g) G.BLS 0 E1)) by (unfold CHA.curB, CHV.LBr; cbn [nth G.BLS GT.BL0 CH2.den map app]; rewrite GBL; apply in_or_app; right; exact Hbb).
        destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) bb HinL) as ((K0 & K1 & K16 & K3 & K4 & K5) & _ & _ & _ & FA).
        assert (APV : fst bb + snd bb <= V \/ V + 408 <= fst bb).
        { destruct OV1 as (f & Hf & F1 & F2). specialize (FA f ltac:(apply in_or_app; left; exact Hf)). clear - FA F1 F2. lia. }
        split; [apply AG; clear - Rb0 Rb3 K4 S2' APV; lia|].
        intros j Hj. apply (SHB (fst bb) (snd bb) j Rb0 (CHA.mod8_of_16 _ Rb1) Rb2 Rb3 Hj). }
    apply (Hcont fx' R' M' model2 (LBo ++ g_lbv g) cr LBo WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 |].
    + split; [exact HINV|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    + unfold CHA.curB, CHV.LBr in HH1. cbn [nth G.BLS GT.BL0 CH2.den map app] in HH1. rewrite GBL in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (LBo ++ g_lbv g) FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VV : CL5A.visr (ahid A model) V 408).
    { intros k Hk. destruct (CL5A.infr_wok L ar _ FF sp 0 V 408 (V + k) RFx OV1 ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSV : forall j, 0 <= j < 51 -> ahid A model (Z_to_bv 64 (S V + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar _ FF sp 0 V 408 (S V + j) RFx OV1 ltac:(clear; lia) (CL5A.shreg_in_shadow V 51 (S V + j) OV2 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS2 : CL5A.visr (ahid A model) S2 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar _ FF sp 0 S2 24 (S2 + k) RFx OS1 ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSS : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S S2 + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar _ FF sp 0 S2 24 (S S2 + j) RFx OS1 ltac:(clear; lia) (CL5A.shreg_in_shadow S2 3 (S S2 + j) OS2 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4624) 4624).
    { intros k Hk. apply CLV; [clear - Hk S2' S3 CL0 SP1; lia | right; left; split; [clear - Hk S2' S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar _ FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2' CL0. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 4624) 4624) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    destruct I1 as (E1' & E2' & Erest). pose proof Erest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ECOL & _).
    destruct I2 as (T1 & T2 & _). rewrite Hes in T2. unfold depth in T2. cbn [length] in T2. rewrite Z.mul_0_r, Z.add_0_r in T2. fold b in T1, T2.
    unfold O_SINK, O_STACK, O_COLUMN in *.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | clear - O3; lia | clear - O6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ V 408 (V + 8) 8 VV ltac:(clear; lia) ltac:(clear; lia)) | exact E2'].
    + eapply CL5.kword64_intro with (A := V + 264) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V34 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ V 408 (V + 264) 8 VV ltac:(clear; lia) ltac:(clear; lia)) | exact T1].
    + eapply CL5.kwr_intro with (A := V + 296) (N := 8); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia |].
      apply (CL5A.defined_vis _ M _ _ (CL5A.visr_sub _ V 408 (V + 296) 8 VV ltac:(clear; lia) ltac:(clear; lia))). exact ECOL.
    + eapply CL5.krange_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL0 SP1 S2' S3; lia].
    + eapply CL5.kalign_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact OV2].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 51 V); [unfold CL5A.uv; cbn [edenot]; exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSV j Hj) | exact (OV3 j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := V) (N2 := 408); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := S2); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL0 SP1 S2' S3; lia].
    + eapply CL5.kalign_intro with (v := S2); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact OS2].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 S2); [unfold CL5A.uv; cbn [edenot]; exact U32 | clear; lia | clear - Q3 Q6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSS j Hj) | exact (OS3 j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := S2) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in Q5; clear - Q5; lia].
    + eapply CL5.kunk_intro with (A := sp - 4624) (N := 4560); [ev_start | reflexivity | clear - S2' CL0; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros k Hk; apply DS; clear - Hk; lia].
    + eapply CL5.kunk_intro with (A := sp - 64) (N := 64); [ev_start | reflexivity | clear - S2' CL0; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros k Hk; replace (sp - 64 + k) with (sp - 4624 + (4560 + k)) by (clear; lia); apply DS; clear - Hk; lia].
    + eapply CL5.kwr_intro with (A := sp - 4624) (N := 4624); [ev_start | reflexivity | clear - S2' CL0; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2' S3 CL0 SP1; lia | clear - S2' S3 CL0 SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2' S3 CL0 SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := sp - 4624) (N2 := 4624); [reflexivity | reflexivity | ev_start | reflexivity | clear - S2' CL0; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4624) (N1 := 4624) (A2 := V) (N2 := 408); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2'; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4624) (N1 := 4624) (A2 := S2) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - Q4 S2'; lia].
    + eapply CL5.kdisj_intro with (A1 := V) (N1 := 408) (A2 := S2) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - OAP; lia].
    + eapply CL5.kword64_intro with (A := V + 272) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V34 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ V 408 (V + 272) 8 VV ltac:(clear; lia) ltac:(clear; lia)) | replace (V + 272) with (V + 264 + 8) by (clear; lia); exact T2].
  - (* [comment removed for export] *)
    apply (CHV.ambV_intro L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS EBSA.FFS 2 eghost gB CredV XIv g M 0%nat E0 A M model
             (CHV.okV_refl L ar M LBo FF sp G.HDECL WW DEF0 S6)).
    split; [|split; [exact Hinv | reflexivity]].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF, CHV.LBr. cbn [nth G.BLS GT.BL0 EBSA.FFS CH2.den CHA.denF map app length Z.of_nat Z.sub]. rewrite GBL.
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | replace (2 - 0) with 2 by (clear; lia); exact Hroom].
  - exact Hfp.
Qed.
End BeginScalarOk.
Print Assumptions begin_scalar_root_ok.
