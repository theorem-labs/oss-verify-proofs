(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncBridges_u5 EncAppendK_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit2_u5 EncTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_begin_scalar_root_xsrc_T_u5 Cut_begin_scalar_root_xsrc_u5 Cut_begin_scalar_xsrc_T_u5 Cut_begin_scalar_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EBSU.
Import PMES.
Module G := Cut_begin_scalar_root_xsrc_u5.
Module GT := Cut_begin_scalar_root_xsrc_T_u5.
Module N := Cut_begin_scalar_xsrc_u5.
Module NT := Cut_begin_scalar_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -8592, ELit 8592); (EVar 10, 296, ELit 8)].

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c)) &&
  match t with
  | CC.TGoto j s => false
  | CC.TOther pc => (Nat.eqb i 0 && PB.exit_base_chk GT.NF RETPC c ps)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section BeginScalarOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp V S2 : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis U10 : bv_unsigned (ev E0 10) = V.
Hypothesis SPR : hl_ceil L + 8592 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OBJS : objs_enc L sp V S2.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 8592 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1 N2. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-8592) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 8592) by lia. lia.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 296 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U10. rewrite (u64_of_Z 8) by lia. lia.
Qed.

Lemma inv_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' ->
  (forall b, In b (g_lbv g) -> block_range L (fst b) (snd b)) ->
  enc_inv M V S2 g -> enc_inv M' V S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HG HB HI0.
  destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE, PML.apart in *. destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 8592 \/ sp <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 H3 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  apply (EK.enc_inv_agree M M' V S2 g); try (unfold ENC_SIZE; lia).
  - apply AG; unfold O_COLUMN; lia.
  - apply AG; unfold O_COLON, ENC_SIZE; lia.
  - destruct HI0 as (I1 & _). destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
    intros i Hi. apply HG. apply X. exact Hi.
  - apply AG; lia.
  - intros b Hb. destruct (HB b Hb) as (R0 & R1 & R2 & R3 & R4). split; [lia|]. split; [lia|]. apply AG; lia.
  - exact HI0.
Qed.

(* [comment removed for export] *)
Lemma blk_stretch : forall (F : list SGP.region) E' (M M' : mem) bb bm a n, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> block_range L bb bm -> bb <= a -> a + n <= bb + bm -> L5C.agree_on M M' a n.
Proof.
  intros F E' M M' bb bm a n HF Hag HFR (R0 & R1 & R2 & R3 & R4) Ha Hn i Hi.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  apply HFR. apply (out_F0 F E' i HF Hag); lia.
Qed.
End Stretch.

(* [comment removed for export] *)
Theorem begin_scalar_root_ok : forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost),
  PML.cps_heap L HI PC_BEGIN_SCALAR r sp (16 + NEWLINE_SCR) (LBo ++ g_lbv g) cr
    (fun R M => PML.entry L R M sp r (16 + NEWLINE_SCR) /\ PML.a0 R V /\ enc_inv M V S2 g /\ g_es g = [] /\ ecreditU L cr g kx bx /\ objs_enc L sp V S2)
    (fun R M R' M' LB' cr' LBk W => enc_inv M' V S2 g /\ LB' = LBo ++ g_lbv g /\ LBk = LBo /\ W = W_h V S2 /\ cr' = cr).
Proof.
  intros LBo cr sp r V S2 kx bx g. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Hinv & Hes & Hcred & Hobjs) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  unfold NEWLINE_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PML.apart in OV2, OAP.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  set (b := g_sb g).
  assert (B64 : 0 <= b < 2 ^ 64).
  { destruct I2 as (_ & _ & _ & _ & [(_ & E)|(k0 & Hk0 & Hc)] & _); [unfold b; rewrite E; lia|].
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
    assert (Hin : In (g_sb g, g_scap g) (LBo ++ g_lbv g)).
    { apply in_or_app. right. unfold g_lbv, stack_blocks. apply in_or_app. right. assert (0 < 2 ^ k0) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [lia | left; reflexivity]. }
    destruct (Hwf _ Hin) as ((R0 & R1 & R2 & R3 & R4) & _). cbn [fst snd] in *. unfold b, hl_ceil in *. lia. }
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; 0; b] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 8592) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 8592 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := W_h V S2).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_COLUMN, 8). split; [left; reflexivity | unfold L5.in_rng, O_COLUMN; cbn [fst snd]; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. replace (sp - 8592 + j) with (sp - (16 + (80 + (256 + (16 + 8224)))) + j) by lia. apply S5. lia. }
  set (GR := stack_blocks (g_sb g) (g_scap g)).
  set (XIv := fun (g1 : eghost) (i : nat) (E : env) (M1 : mem) => enc_inv M1 V S2 g1 /\ g1 = g).
  set (CredV := fun (g1 : eghost) (i : nat) (E : env) (cr1 : credit) => cr1 = cr).
  set (gB := EB.gB GR).
  assert (GBL : gB g = g_lbv g) by reflexivity.
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  unfold PML.cfg. change PC_BEGIN_SCALAR with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - intros g1 M0c OKV i c kk ps j sg IL. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [_ X]. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
    apply andb_prop in X as [X0 X1]. apply Nat.eqb_eq in X0. subst i.
    intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _. destruct HX as [HX1 ->].
    assert (DEFC : L5.defined M0c (sp - 8592) 8592) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
    apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo eghost gB g) sp G.HDECL W G.BLS (CredV g) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g)
             (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
             8592 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3 RETPC 0%nat c kk ps pc ret_at IL X1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
    intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _). unfold CredV in HC1. subst cr1.
    assert (HP2 : L5C.hpres L LBo sp 8592 W M M').
    { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W eghost gB NF32 g M0c M' OKV). rewrite SCRV. exact HP. }
    assert (HINV : enc_inv M' V S2 g).
    { destruct IL as (tags & Hc & _). pose proof (AGE 0%nat c E E' Hc HagE1 Hag) as HagE2.
      apply (inv_stretch E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' M1 M' g XF HagE2 (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF)); [|exact HX1].
      intros b0 Hb0. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b0). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb0. }
    apply (Hcont fx' R' M' m1 (LBo ++ g_lbv g) cr LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
    + split; [exact HINV|]. repeat split.
    + unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    destruct I1 as (H1 & H2 & _). destruct I2 as (T1 & T2 & _). rewrite Hes in T2. unfold depth in T2. cbn [length] in T2. rewrite Z.mul_0_r, Z.add_0_r in T2. fold b in T1, T2.
    unfold O_SINK, O_STACK in *.
    assert (Hds : L5.defined M (sp - 8592) 8592) by (intros j Hj; replace (sp - 8592 + j) with (sp - (16 + (80 + (256 + (16 + 8224)))) + j) by lia; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | lia | lia | exact V32 | exact H2].
    + eapply CL5.kword64_intro with (A := V + 264) (z := b); [ev_start | lia | lia | exact V34 | exact T1].
    + eapply CL5.kword64_intro with (A := V + 272) (z := b); [ev_start | lia | lia | exact V34 | replace (V + 272) with (V + 264 + 8) by lia; exact T2].
    + e_range. + e_align OV3.
    + e_range. + e_align OS3.
    + e_unk. + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv g M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [exact Hinv | reflexivity]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; cbn [nth G.BLS GT.BL0 CH2.den map app]; rewrite GBL; exact HH | reflexivity].
  - exact Hfp.
Qed.
End BeginScalarOk.
End EBSU.
Print Assumptions EBSU.begin_scalar_root_ok.
