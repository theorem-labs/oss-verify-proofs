(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncPure_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import FxKitX_u5 DumpBufX_u5 FxKitXU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_wd_xsrc_T_u5 Cut_wd_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module WDXU.
Import PMES.
Module G := Cut_wd_xsrc_u5.
Module GT := Cut_wd_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := 0x3f450.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -9600, ELit 9600)].
Definition SPE : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)).       (* [comment removed for export] *)
Definition DT_SCR : Z := 9344.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition ret_cut (i k : nat) : nat := match CH2.ret_of G.RETS i k with Some j => j | None => 0%nat end.
(* [comment removed for export] *)
Definition dt_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) (EVar 33) && expr_eqb (nth 11 regs (ELit 0)) (EVar 11) && expr_eqb (nth 12 regs (ELit 0)) (ELit 0) && expr_eqb (nth 2 regs (ELit 0)) SPE)%bool
  then FXKU.strans_chkN GT.NF G.HDECL S2E 0 DT_SCR (Some 1) c ps cj BLi BLj else None.
Definition sinkj (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let j := ret_cut i k in
  (negb (Nat.eqb j 0) && match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition kind (i k : nat) : nat := (match i, k with 0, 0 => 4 | 1, 0 => 6 | _, _ => 0 end)%nat.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb 48 (CC.cp_nx c)) &&
  match t with
  | CC.TGoto j s => false
  | CC.TOther pc =>
      if Z.eqb pc PMFX.PC_DTOA_TRUE then (Z.eqb (SR.ps_pc ps) pc && sinkj dt_chk i k c ps && Nat.eqb (kind i k) 4)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 0) && Nat.eqb (kind i k) 6)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Definition phase (i : nat) (p : Z) : Prop := match i with 1%nat => 1 <= p <= 28 | _ => p = 0 end.

Lemma kword32_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  PML.u32 M A z -> kentry_ok RSEGS E M (KWord a 4 v).
Proof.
  intros E M a v A z Ha H0 H1 Hv Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.

Section WriteDoubleOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis DTOK : PMFXT.dtoa_true_x_specU L HI PML.STRTOD_SCR_V.

Theorem write_double_x_ok : write_double_x_specU L HI WD_SCR_X.
Proof.
  intros wd LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & (Hfmt & Hprec & (dp & Hdpc)) & Hwd1 & Hwd2) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2'' & S3 & S4 & S5).
  unfold WD_SCR_X, PML.HEAP_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hobj as (OS1 & OS2 & OS3). unfold PML.apart in Hapsk.
  pose proof (proj1 (GK.u8_at_mod M (wd + 8) dp) Hdpc) as Hdp. set (dpm := dp mod 256) in Hdp. assert (Hdpm : 0 <= dpm < 256) by (unfold dpm; apply Z.mod_pos_bound; lia).
  clearbody dpm. clear Hdpc dp. rename dpm into dp.
  set (len0 := len (PML.srep_chars rep)).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; dp] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 wd) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 SK) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 dp) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = wd) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = SK) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = dp) by (rewrite V33; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 9600) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 9600 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a []. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. apply S5. lia. }
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) => ESBU.sink_inv M1 S2 g1 /\ phase i (ESBU.s_len g1 - len0)).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; apply app_nil_r).
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E0 E /\
                  exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb. }
  assert (KIMG : forall LBx a, 0x10000 <= a < PML.IMG_RO_HI -> L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
  { intros LBx a Ha. unfold PML.IMG_RO_HI in Ha. apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (IMGC : forall g1 M0c i E (M1 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
                  CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> PML.img_ro M1).
  { intros g1 M0c i E M1 m1 (O1 & _) (_ & _ & _ & _ & Hfr & _) a Ha. rewrite (Hfr a (KIMG _ a Ha)). rewrite (O1 a (KIMG _ a Ha)). exact (Himg a Ha). }
  assert (OUTF : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 -> ~ (sp - 9600 <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a)).
  { intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
    pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
    unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
    rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-9600) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 9600) by lia. lia. }
  assert (SINKAG : forall g1 (M1 M' : mem), (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) ->
                   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 9600 <= a < sp) -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
                   ESBU.sink_inv M1 S2 g1 -> ESBU.sink_inv M' S2 g1).
  { intros g1 M1 M' HB HFR (HS & HL). split; [|exact HL].
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 9600 \/ sp <= a) -> (a + n <= hl_errno L \/ hl_errno L + 4 <= a) -> L5C.agree_on M1 M' a n).
    { intros a n H0 H1 H2 H3 q Hq. apply HFR; [lia | lia | unfold in_errno; lia]. }
    destruct SPR as (P1 & P2 & P3).
    apply (EK.sink_at_agree M1 M' S2 (ESBU.s_rep g1)); [lia | lia | apply AG; rewrite ?LER; unfold hl_ceil in *; lia | | exact HS].
    destruct (ESBU.s_rep g1) as [s|cap p s] eqn:Hrep; [exact I|].
    destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *. rewrite ILO, IHI in R1.
    split; [lia|]. split; [unfold hl_ceil in *; lia|]. apply AG; rewrite ?LER; unfold hl_ceil in *; lia. }
  assert (STRETCH : forall g1 M0c i c kk ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c kk ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.okV L M LBo sp G.HDECL W M0c ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E0 E' /\ PML.img_ro M').
  { intros g1 M0c i c kk ps t E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _].
    destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    destruct HX as (HX1 & HX2). pose proof (CC.lf_frame _ _ _ _ _ _ _ HLF) as FR.
    split; [|split; [exact HagE' |]].
    - apply (SINKAG g1 M1 M' HB); [|exact HX1]. intros a Ha N1 N2. apply FR. exact (OUTF (CC.cp_F c) E' a XF HagE' Ha N1).
    - apply (EK.img_ro_agree M1 M'); [|exact (IMGC g1 M0c i E M1 m1 OKV HA)]. intros a Ha. unfold PML.IMG_RO_HI in Ha.
      apply FR. apply (OUTF (CC.cp_F c) E' a XF HagE'); unfold hl_ceil in *; lia. }
  assert (HK' : forall c ps E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps)).
  { intros c ps E' R' M1 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
  unfold PML.cfg. change PC_WRITE_DOUBLE with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - intros g1 M0c OKV i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [_ X]. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
    apply Nat.leb_le in XN.
    assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
               CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
               CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> ESBU.sink_inv M' S2 g1).
    { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF)). }
    set (j := ret_cut i kk) in *.
    assert (HRET : forall f, sinkj f i kk c ps = true -> CH2.ret_of G.RETS i kk = Some j /\ exists cj, nth_error G.CPS j = Some cj /\ isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) = true).
    { intros f Hs. unfold sinkj in Hs. apply andb_prop in Hs as [Hs1 Hs2]. fold j in Hs1, Hs2.
      split; [unfold j, ret_cut in *; destruct (CH2.ret_of G.RETS i kk) as [j0|]; [reflexivity | discriminate Hs1]|].
      destruct (nth_error G.CPS j) as [cj|]; [|discriminate]. exists cj. split; [reflexivity | exact Hs2]. }
    destruct (Z.eqb_spec pc PMFX.PC_DTOA_TRUE) as [->|Hne1].
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 X3]. apply Z.eqb_eq in X1.
      destruct (HRET _ X3) as (Hret & cj & Hcj & X3b). clear X3.
      destruct (dt_chk c ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. clear X3b.
      unfold dt_chk in Hchk.
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
      apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R12]. apply andb_prop in Hb as [R10 R11].
      apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R12. apply expr_eqb_eq in R2X.
      apply (FXKU.strans_leaf_okN L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               S2 Hobj W_S2 S2E 0 eq_refl OADDR PMFX.PC_DTOA_TRUE DT_SCR (fun pay => 1 <= pay <= 28) (fun R' _ => PML.a0 R' 1) (Some 1) i c kk ps j cj ci g1 M0c OKV IL Hret Hcj X1 Hchk).
      * intros R2 pay HR2. split; [exact HR2 | lia].
      * exact XILEAF.
      * intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP CONT.
        assert (HP0 : ESBU.s_len g1 - len0 = 0).
        { destruct HX as (_ & HP). clear - HP Xk. destruct i as [|[|i]]; destruct kk as [|kk]; cbn [kind Nat.eqb] in Xk; first [discriminate Xk | exact HP]. }
        assert (HRM : len (PML.srep_chars (ESBU.s_rep g1)) + 28 <= CLU) by (destruct HINV as [_ HL]; rewrite HL; unfold len0 in *; lia).
        pose proof CF as [HA' HR Hreq (Q1 & Q2 & Q3 & Q4 & Q5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct HA' as (Hmo1 & Hbv1 & HagE1 & _ & Hfr1 & Hdf1).
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & HIMG).
        assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
        assert (U11' : bv_unsigned (ev E' 11) = SK) by (destruct HagE' as [AG _]; rewrite <- (AG 11%nat) by (unfold GT.NF; lia); exact U11).
        assert (U33' : bv_unsigned (ev E' 33) = dp) by (destruct HagE' as [AG _]; rewrite <- (AG 33%nat) by (unfold GT.NF; lia); exact U33).
        rewrite Hreq in HR.
        assert (Ga0 : getr R' 10%bv = Z_to_bv 64 dp).
        { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10. cbn [edenot]. rewrite <- U33'. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 SK).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11. cbn [edenot]. rewrite <- U11'. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (Ga2 : getr R' 12%bv = Z_to_bv 64 0).
        { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite R12. reflexivity. }
        assert (CSP : CH2.ci_csp ci = -256).
        { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
          apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 256)) in G2; [| unfold SPE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
        assert (HU : PML.u64 M' SK S2).
        { apply (EK.u64_agree M M' SK S2); [| lia | lia | exact HskS2].
          intros q Hq. rewrite (Hfr1 q); [apply (proj1 OKV q) |]; (split; [lia | split; [right; left; split; [unfold hl_ceil in *; lia | lia] | split; [unfold in_errno; rewrite LER; unfold hl_ceil in *; lia | ]]]);
            (intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia). }
        destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *.
        apply (DTOK dp (CH2.den E' (nth i G.BLS []) ++ LBo ++ []) cr1 (sp + -256) (CC.cp_pc cj) SK S2 kx bx (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        { unfold PMFXT.DT_SCR, PMFXT.DF_SCR, PMFXT.PR_SCR, PMFXT.DB_SCR, PMFXT.STRX_SCR, STRX_SCR, PMFX.SNPRINTF_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK, PML.STRTOD_SCR_V.
          change (144 + Z.max (160 + Z.max 6144 (Z.max (96 + 8944) (96 + (256 + (16 + 8224))))) (Z.max (80 + 80) (64 + 32 + (256 + (16 + 8224))))) with 9344.
          split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                   split; [exact T1 | split; [unfold DT_SCR in *; lia | split; [lia | split; [exact T4 | unfold DT_SCR in *; exact T5]]]]]]]]|].
          split; [| split; [exact HU | split; [lia | split; [lia | split; [unfold PML.apart; lia | split; [exact (proj1 HINV) | split; [unfold PML.obj_on_stack; lia | split; [exact HIMG | split; [exact HSC | exact HRM]]]]]]]]].
          split; [exact Ga0|]. split; [lia|]. split; [exact Ga1 | exact Ga2]. }
        intros fx2 R3 M3 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRa0 & Hs2 & Hlen2 & HLB' & HLBk & HWc & HSC') HRP2 HPRES Hbv2 HH2.
        apply (CONT fx2 R3 M3 model2 LB' cr' LBk Wc HFP2); [| exact HRP2 | exact HPRES | exact Hbv2 | exact HH2].
        exists rep', pay. split; [lia|]. split; [exact HRa0|]. split; [exact Hs2|]. split; [exact Hlen2|]. split; [exact HLB'|]. split; [exact HLBk|]. split; [exact HWc|].
        exact HSC'.
      * intros E R1 M1 m1 E' R' M' E2 M3 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HPRES HINV2 Hslen HPay.
        split; [exact HINV2|]. destruct HX as (_ & HP).
        rewrite Hslen. subst j. unfold ret_cut, phase in HP |- *. clear - HP Xk HPay.
        do 2 (destruct i as [|i]; [destruct kk as [|kk]; cbn [kind CH2.ret_of G.RETS find Nat.eqb andb] in *; first [discriminate Xk | lia] |]). discriminate Xk.
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Xi]. apply andb_prop in X as [X1 XA0].
      intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
      destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HAmb HX Hag HLF) as (HINV & HagE'0 & _).
      assert (DEFC : L5.defined M0c (sp - 9600) 9600) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
      apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
               (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
               9600 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3 RETPC i c kk ps pc ret_at IL X1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
      intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
      destruct HX as (_ & HPH).
      assert (HP2 : L5C.hpres L LBo sp 9600 W M M').
      { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
      assert (Ga0 : PML.a0 R' 0).
      { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (ELit 0) HLF XA0) as G10.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). unfold PML.a0. rewrite G10. reflexivity. }
      assert (HPAY : 1 <= ESBU.s_len g1 - len0 <= 28).
      { unfold phase in HPH. clear - HPH Xi. do 2 (destruct i as [|i]; [destruct kk as [|kk]; cbn [kind] in Xi; first [discriminate Xi | exact HPH | lia] |]). discriminate Xi. }
      apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
      -- exists (ESBU.s_rep g1), (ESBU.s_len g1 - len0). destruct HINV as [Hs Hl].
         split; [lia|]. split; [exact Ga0|]. split; [exact Hs|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
      -- unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL in HH1.
         assert (Hnil : CH2.den E (nth i G.BLS []) = []) by (clear - Xi; do 2 (destruct i as [|i]; [reflexivity|]); discriminate Xi).
         rewrite Hnil in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 9600) 9600) by (intros j Hj; apply S5; lia).
    split.
    + intros x. unfold sr_get. destruct (bv_eqb x 0) eqn:Hx0.
      * assert (x = 0%bv) by (apply bv_eq; unfold bv_eqb in Hx0; lia). subst x. unfold getr. rewrite Hx0. reflexivity.
      * rewrite <- (ridx_roundtrip x) at 1. pose proof (ridx_range x) as Hlt. set (nn := ridx x) in *. clearbody nn.
        do 32 (destruct nn as [|nn]; [cbn [nth G.cp0 CC.cp_regs]; first [ reflexivity | (cbn [edenot ev reg_ev Nat.ltb Nat.leb]; reflexivity) ] |]). exfalso. lia.
    + unfold know_ok, G.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2].
      * eapply GK.kword8_intro with (A := wd) (z := 0); [ev_start | lia | lia | reflexivity | lia | exact Hfmt].
      * eapply kword32_intro with (A := wd + 4) (z := 0); [ev_start | lia | lia | reflexivity | exact Hprec].
      * eapply GK.kword8_intro with (A := wd + 8) (z := dp); [ev_start | lia | lia | exact V33 | lia | exact Hdp].
      * e_range. * e_range. * e_range. * e_range.
      * e_align OS3.
      * e_wr. * e_range. * e_align S1.
      * e_disj. * e_disj. * e_disj. * e_disj.
      * e_unk.
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [split; [exact Hsink | reflexivity] | cbn [phase ESBU.s_len]; lia]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; cbn [nth G.BLS GT.BL0 CH2.den map app]; rewrite (GBL (ESBU.SG rep len0)); cbn [ESBU.s_rep]; exact HH|].
    exact Hcred.
  - exact Hfp.
Qed.
End WriteDoubleOk.
End WDXU.
Print Assumptions WDXU.write_double_x_ok.
