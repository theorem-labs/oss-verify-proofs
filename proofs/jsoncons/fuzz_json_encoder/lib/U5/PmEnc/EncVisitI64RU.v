(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncBridges2_u5 EncHtrans_u5 EncStrans_u5 EncPure_u5 EncAppendK_u5 EncKit2_u5 EncTail_u5 EncVisitNullB_u5 EncVisitNullHU EncVisitI64B_u5 EncBridgesU EncStransU EncBridges2U EncHtransU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_int64_root_xsrc_T_u5 Cut_visit_int64_root_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require L5FastLia.
#[local] Ltac lia ::= L5FastLia.plia.   (* [comment removed for export] *)
Open Scope Z_scope.

Module EVI64RU.
Import PMES.
Import EVNB.
Import EVI64B.
Module G := GR.
Module GT := GRT.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

Section Root.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis FROM_OK : from_integer_i64_x_specU L HI.

Section Stretch.
Variables (E0 : env) (sp V S2 : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis U10 : bv_unsigned (ev E0 10) = V.
Hypothesis SPR : hl_ceil L + 10624 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OBJS : objs_enc L sp V S2.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F F0R = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 10624 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> SGP.outside E' F (Z_to_bv 64 a).
Proof using OBJS SPR U10 U2.
  intros F E' a HF Hag Ha N1 N2. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3). unfold hl_ceil in *.
  unfold F0R in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-10624) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 10624) by lia. lia.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 296 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U10. rewrite (u64_of_Z 8) by lia. lia.
Qed.
Lemma inv_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F F0R = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' ->
  (forall b0, In b0 (g_lbv g) -> block_range L (fst b0) (snd b0)) ->
  enc_inv M V S2 g -> enc_inv M' V S2 g.
Proof using OBJS SPR U10 U2.
  intros F E' M M' g HF Hag HFR HG HB HI0.
  destruct OBJS as ((A1 & A2 & A3) & (B1' & B2' & B3') & C). unfold ENC_SIZE, PML.apart in *. destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 10624 \/ sp <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 H3 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  apply (EK.enc_inv_agree M M' V S2 g); try (unfold ENC_SIZE; lia).
  - apply AG; unfold O_COLUMN; lia.
  - apply AG; unfold O_COLON, ENC_SIZE; lia.
  - destruct HI0 as (I1 & _). destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
    intros i Hi. apply HG. apply X. exact Hi.
  - apply AG; lia.
  - intros b0 Hb0. destruct (HB b0 Hb0) as (Q0 & Q1 & Q2 & Q3 & Q4). unfold hl_ceil in *. split; [lia|]. split; [lia|]. apply AG; lia.
  - exact HI0.
Qed.
Lemma lits_stretch : forall (F : list SGP.region) E' (M M' : mem), SP.F_sub F F0R = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> forall a, PML.LIT_LO <= a < PML.LIT_HI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof using OBJS SPR U10 U2.
  intros F E' M M' HF Hag HFR a Ha. destruct OBJS as ((A1 & A2 & A3) & _). unfold ENC_SIZE in *. destruct SPR as (P1 & P2 & P3).
  unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *. apply HFR. apply (out_F0 F E' a HF Hag); lia.
Qed.
End Stretch.

Theorem visit_int64_root_okU : forall (v : Z) (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost),
  g_es g = [] ->
  PML.cps_heap L HI PC_VISIT_INT64 r sp EVNHU.VSCR (LBo ++ g_lbv g) cr
    (fun R M => PML.entry L R M sp r EVNHU.VSCR /\ PML.a0 R V /\ (PML.a1 R v /\ 0 <= v < 2 ^ 64) /\ enc_inv M V S2 g /\ ev_guard (g_es g) EvI64 /\ eroomU g EvI64 /\ PML.img_ro M /\ PML.lits_ok M /\
                ecreditU L cr g kx bx /\ objs_enc L sp V S2)
    (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (pay : Z),
        PML.a0 R' 1 /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) EvI64 /\ pay_ok EvI64 pay /\ g_len g' = g_len g + ev_ind (g_es g) EvI64 + pay /\
        PML.lits_ok M' /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_enc V S2 /\ ecreditU L cr' g' kx bx).
Proof using FPM FROM_OK HIok LAY.
  intros v LBo cr sp r V S2 kx bx g Hes. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & [Ha1 VR] & Hinv & _ & Hroom & Himg & Hlits & Hcred & Hobjs) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  unfold EVNHU.VSCR, WD_SCR_X, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. change (1024 + Z.max (256 + (16 + 8224)) 9600) with 10624 in *.
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PML.apart in OV2, OAP.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_kpm L LAY) as KPM.
  destruct g as [es len0 rep b cb]. cbn [g_es g_len g_rep g_sb g_scap] in *. subst es.
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5). cbn [g_es g_len g_rep g_sb g_scap] in I1, I2, I3, I4, I5.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  pose proof I2 as TT. unfold stack_at in TT. destruct TT as (T1 & T2 & T3 & T4 & T5 & T6). change (depth []) with 0 in T2, T4. rewrite Z.mul_0_r, Z.add_0_r in T2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (DCOL : L5.defined M (V + 296) 8).
  { destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  destruct (EAK.u64_of_defined M (V + 296) DCOL) as (col & Hcol0 & Hcol).
  assert (B64 : 0 <= b < 2 ^ 64).
  { destruct T5 as [(E1 & E2)|(k0 & Hk0 & Ecb)]; [lia|].
    assert (INB : In (b, cb) (LBo ++ g_lbv (EG [] len0 rep b cb))).
    { apply in_or_app. right. unfold g_lbv, stack_blocks. cbn [g_rep g_sb g_scap]. pose proof (EVNHU.pow2_10 k0 Hk0). destruct (Z.eqb_spec cb 0); [lia|]. apply in_or_app. right. left. reflexivity. }
    destruct (Hwf _ INB) as ((B0 & _ & _ & _ & B4) & _). cbn [fst snd] in *. unfold hl_ceil in B4. lia. }
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; 0; b; cb; 0; col] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 v) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (V37 : ev E0 37 = Z_to_bv 64 col) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = v) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; lia).
  assert (U37 : bv_unsigned (ev E0 37) = col) by (rewrite V37; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 10624) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 10624 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := W_enc V S2).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[<-|[<-|[<-|[]]]]] Hin; unfold L5.in_rng, O_STACK, O_DEPTH, PML.LIT_LO, PML.LIT_HI in Hin; cbn [fst snd] in Hin; (split; [lia|]); [left; lia | left; lia | left; lia | right].
    unfold in_errno. rewrite ILO, IHI, LER. split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
    split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite ILO, IHI; lia)) as [Y|[Y|Y]]; lia | lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
      rewrite U10 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 40). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [right; right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros j Hj; apply S5; lia).
  assert (W_S2 : In (S2, 24) W) by (right; right; left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  assert (S2ADDR : PB.uv E0 S2E = S2) by (unfold PB.uv, S2E; cbn [edenot]; exact U32).
  set (GR := stack_blocks b cb).
  set (PAYOK := fun (i : nat) (pay : Z) => if FIr i then 1 <= pay <= 20 else pay = 0).
  set (XIv := fun (g1 : eghost) (i : nat) (E : env) (M1 : mem) =>
                enc_inv M1 V S2 g1 /\ g_es g1 = [] /\ g_sb g1 = b /\ g_scap g1 = cb /\ (exists pay, PAYOK i pay /\ g_len g1 = len0 + pay) /\
                PML.lits_ok M1 /\ True).
  set (CredV := EBU.CredV L kx bx).
  set (gB := EBU.gB GR).
  assert (GBL : forall g1, g_sb g1 = b -> g_scap g1 = cb -> gB g1 = g_lbv g1).
  { intros g1 E1 E2. unfold gB, EBU.gB, g_lbv, GR. rewrite E1, E2. reflexivity. }
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (NILB : forall i E, CH2.den E (nth i G.BLS []) = []).
  { intros i E. unfold G.BLS, GR.BLS. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. }
  assert (HEAP : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 ->
                  env_agree GT.NF E0 E /\ exists cr1, hi_heap HI (LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [exact HagE|]. exists cr1. split; [|exact HC1].
    unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. exact HH1. }
  assert (BLKS : forall g1 cr1 (M1 : mem) VM, hi_heap HI (LBo ++ gB g1) cr1 M1 VM -> forall b0, In b0 (gB g1) -> block_range L (fst b0) (snd b0)).
  { intros g1 cr1 M1 VM HH1 b0 Hb0. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf1 & _). apply Hwf1. apply in_or_app. right. exact Hb0. }
  assert (KIMG : forall LBx a, 0x10000 <= a < PML.IMG_RO_HI -> L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
  { intros LBx a Ha. unfold PML.IMG_RO_HI in Ha. apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng, O_STACK, O_DEPTH, PML.LIT_LO, PML.LIT_HI; cbn [fst snd]; lia. }
  assert (IMGC : forall g1 M0c i E (M1 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
                  CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> PML.img_ro M1).
  { intros g1 M0c i E M1 m1 (O1 & _) (_ & _ & _ & _ & Hfr & _) a Ha. rewrite (Hfr a (KIMG _ a Ha)). rewrite (O1 a (KIMG _ a Ha)). exact (Himg a Ha). }
  assert (HK' : forall c ps E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps)).
  { intros c ps E' R' M1 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.okV L M LBo sp G.HDECL W M0c ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      enc_inv M' V S2 g1 /\ env_agree GT.NF E0 E' /\ PML.img_ro M' /\ PML.lits_ok M' /\ True).
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okr _ _ _ _ _ IL) as X. unfold leaf_chkr in X. apply andb_prop in X as [XF _].
    apply andb_prop in XF as [XF XB]. apply andb_prop in XF as [XF _].
    destruct (HEAP g1 M0c i E M1 m1 HA) as (HagE & cr1 & HH1 & _).
    destruct IL as (tags & Hc & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    destruct HX as (HX1 & X2 & X3 & X4 & X5 & X7 & X8).
    assert (LAG : forall a, PML.LIT_LO <= a < PML.LIT_HI -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { exact (lits_stretch E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' M1 M' XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF)). }
    split; [|split; [exact HagE'| split; [| split; [exact (PML.lits_ok_agree M1 M' LAG X7) | exact I]]]].
    - apply (inv_stretch E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF)); [|exact HX1].
      rewrite <- (GBL g1 X3 X4). exact (BLKS g1 cr1 M1 _ HH1).
    - apply (EK.img_ro_agree M1 M'); [|exact (IMGC g1 M0c i E M1 m1 OKV HA)]. intros a Ha. unfold PML.IMG_RO_HI in Ha.
      apply (CC.lf_frame _ _ _ _ _ _ _ HLF). apply (out_F0 E0 sp V S2 U2 U10 SPR Hobjs (CC.cp_F c) E' a XF HagE'); unfold hl_ceil in *; lia. }
  assert (HPLITh : forall LBk spc scr (M1 M2 : mem), L5C.hpres L LBk spc scr [(S2, 24)] M1 M2 -> forall a, PML.LIT_LO <= a < PML.LIT_HI -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros LBk spc scr M1 M2 HP a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). unfold PML.LIT_LO, PML.LIT_HI in Ha.
    apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X0; pose proof (PmLayout.ly_static L LAY a X0); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (INVFR : forall (M1 M2 : mem) g1', (forall b0, In b0 (g_lbv g1') -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 64 /\ L5C.agree_on M1 M2 (fst b0) (snd b0)) ->
             L5C.agree_on M1 M2 V ENC_SIZE -> L5C.agree_on M1 M2 S2 24 -> enc_inv M1 V S2 g1' -> enc_inv M2 V S2 g1').
  { intros M1 M2 g1' HB AV AS HI1. pose proof HI1 as (J1 & _).
    assert (DC : L5.defined M2 (V + O_COLUMN) 8).
    { destruct J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X9 & _).
      apply (L5C.defined_agree M1 M2); [intros z Hz; apply AV; unfold O_COLUMN, ENC_SIZE in *; lia | exact X9]. }
    apply (EK.enc_inv_agree M1 M2 V S2 g1'); try (unfold ENC_SIZE; lia).
    - intros z Hz. apply AV. unfold O_COLUMN, ENC_SIZE in *. lia.
    - intros z Hz. apply AV. unfold O_COLON, ENC_SIZE in *. lia.
    - exact DC.
    - exact AS.
    - exact HB.
    - exact HI1. }
  unfold PML.cfg. change PC_VISIT_INT64 with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3r.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - intros g1 M0c OKV i c kk ps j sg IL. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okr _ _ _ _ _ IL) as X. unfold leaf_chkr in X. apply andb_prop in X as [_ X]. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okr _ _ _ _ _ IL) as X. unfold leaf_chkr in X. apply andb_prop in X as [XF X].
    apply andb_prop in XF as [XF XB]. apply andb_prop in XF as [XF XN]. apply Nat.leb_le in XN. pose proof XB as XB'. apply CH2.blocks_eqb_eq in XB'.
    assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
               CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
               CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
               enc_inv M' V S2 g1 /\ incl (stack_blocks (g_sb g1) (g_scap g1)) (CH2.den E' (nth i G.BLS []) ++ LBo ++ GR)).
    { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & _).
      split; [exact HINV|]. destruct HX as (_ & _ & X3 & X4 & _). rewrite X3, X4. fold GR. intros b0 Hb0. apply in_or_app; right; apply in_or_app; right; exact Hb0. }
    destruct (Z.eqb_spec pc PCF) as [->|Hne1].
    { (* [comment removed for export] *)
      apply andb_prop in X as [X Xa1]. apply andb_prop in X as [X Xa0]. apply andb_prop in X as [X XCJ]. apply andb_prop in X as [Xpc Xi]. apply Nat.eqb_eq in Xi. subst i.
      apply Z.eqb_eq in Xpc. apply expr_eqb_eq in Xa0, Xa1.
      unfold call_j in XCJ. destruct (CH2.ret_of GR.RETS 0 kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error GR.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in XCJ as [XCJ Xcond]. apply andb_prop in Xcond as [Xj Xnx]. apply Nat.eqb_eq in Xj. subst j. apply Nat.leb_le in Xnx.
      destruct (EST.strans_chk GRT.NF GR.HDECL S2E 0 FISCR c ps cj (nth 0 GR.BLS []) (nth 1 GR.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      apply (ESTU.strans_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS GR kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               V S2 Hobjs W_S2 S2E 0 eq_refl OADDR PCF FISCR (fun pay => 1 <= pay <= 20) 0%nat c kk ps 1%nat cj ci g1 M0c OKV IL Hret Hcj Xpc Hchk).
      * intros pay Hp. unfold ESTU.PAYMAX. lia.
      * exact XILEAF.
      * intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP Hk.
        pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct HA' as (Hmo1 & _).
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & HIMG & _).
        destruct HagE' as [AG _].
        assert (Ga0 : getr R' 10%bv = Z_to_bv 64 v).
        { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq, Xa0. cbn [edenot].
          rewrite <- AG by (unfold GT.NF; lia). rewrite <- Ha1. exact (EV 11%bv). }
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 (V + 8)).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq, Xa1.
          assert (UU : bv_unsigned (edenot E' SKE) = V + 8).
          { apply CL5.u_lin; [|lia]. unfold SKE. lin_eval. rewrite <- AG by (unfold GT.NF; lia). rewrite U10. lia. }
          rewrite <- UU. symmetry. apply Z_to_bv_bv_unsigned. }
        rewrite NILB in HH1. cbn [app] in HH1.
        pose proof HINV as (J1 & _ & Hsink & Hln & _). pose proof J1 as (_ & HSK & _).
        apply (FROM_OK v (LBo ++ GR) cr1 (sp + CH2.ci_csp ci) (CC.cp_pc cj) (V + 8) S2 (ESTU.kxs L kx g1) (ESTU.bxs L bx g1) (g_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        { split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity | unfold FROMINT_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; exact Hstk']]]]|].
          split; [split; [exact Ga0 | split; [exact VR | exact Ga1]]|].
          split; [unfold O_SINK in HSK; exact HSK|]. split; [lia|]. split; [lia|]. split; [unfold PML.apart; lia|].
          split; [exact Hsink|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HIMG|]. split; [exact HSC|].
          pose proof HX as (_ & _ & _ & _ & (p0 & P0 & X5) & _). unfold PAYOK in P0. cbn in P0. rewrite Hln, X5, P0.
          unfold eroomU, kmax in Hroom. cbn [g_len g_es ev_ind pre_scalar fst quotes pay_hi] in Hroom. lia. }
        intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 POST HRP HPRES Hbv2 HH2.
        apply (Hk fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 POST HRP HPRES Hbv2 HH2).
      * intros E R1 M1 m1 E' R' M' E2 M2 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HP HINV2 G1 G2 G3 G4 HPay _.
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & _ & HLITS & _).
        pose proof HX as (_ & X2 & X3 & X4 & (p0 & P0 & X5) & X7 & _). unfold PAYOK in P0. cbn in P0.
        split; [exact HINV2|]. split; [rewrite G1; exact X2|]. split; [rewrite G2; exact X3|]. split; [rewrite G3; exact X4|].
        split; [exists pay; split; [unfold PAYOK; cbn; exact HPay | rewrite G4, X5, P0; lia]|].
        split; [exact (PML.lits_ok_agree M' M2 (HPLITh _ _ _ M' M2 HP) HLITS) | exact I]. }
    (* [comment removed for export] *)
    apply andb_prop in X as [X XA0]. apply andb_prop in X as [X X2]. apply andb_prop in X as [Xpc Xi]. apply Nat.eqb_eq in Xi. subst i. apply Z.eqb_eq in Xpc. subst pc.
    intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
    destruct (STRETCH g1 M0c 1%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HAmb HX Hag HLF) as (HINV & HagE'0 & HIMG & HLITS & _).
    pose proof HX as (_ & X2' & X3 & X4 & (p1 & P1 & X5) & X7 & _). unfold PAYOK in P1. cbn in P1.
    assert (DEFC : L5.defined M0c (sp - 10624) 10624) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
    apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo eghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
             (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
             10624 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3r RETPC 1%nat c kk ps RETPC ret_at IL X2 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
    intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
    assert (HP2 : L5C.hpres L LBo sp 10624 W M M').
    { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W eghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
    assert (Ga0 : PML.a0 R' 1).
    { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (ELit 1) HLF XA0) as G10.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). exact G10. }
    apply (Hcont fx' R' M' m1 (LBo ++ g_lbv g1) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
    * exists g1, p1. split; [exact Ga0|]. split; [exact HINV|]. split; [rewrite X2'; reflexivity|]. split; [exact P1|].
      split; [rewrite X5; cbn; lia|].
      split; [exact HLITS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
    * unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. rewrite <- (GBL g1 X3 X4). exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    destruct I1 as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                    H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & _).
    unfold O_SINK, O_STACK in *.
    assert (Hds : L5.defined M (sp - 10624) 10624) by (intros j Hj; apply S5; lia).
    assert (IMGL : forall z, 65536 <= z < 827984 -> M (Z_to_bv 64 z) = None) by (intros z Hz; apply Himg; exact Hz).
    clear HEAP BLKS STRETCH IMGC KIMG HPLITh AGE HK' Hcont HH Hwf Hnd T5 T6 Hinv I2 I3 Himg Hlits Hcred.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0, GR.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | lia | lia | exact V32 | exact H2].
    + eapply CL5.kword64_intro with (A := V + 296) (z := col); [ev_start | lia | lia | exact V37 | exact Hcol].
    + e_range.
    + e_wr.
    + e_range. + e_align OV3.
    + e_range. + e_align OS3.
    + e_unk. + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
    + cbn [kentry_ok]. split; [lia | split; [lia | exact IMGL]].
    + eapply CL5.kword64_intro with (A := V + 264) (z := b); [ev_start | lia | lia | exact V34 | exact T1].
    + eapply CL5.kword64_intro with (A := V + 272) (z := b); [ev_start | lia | lia | exact V34 | replace (V + 272) with (V + 264 + 8) by lia; exact T2].
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv (EG [] len0 rep b cb) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [|exact Hcred].
      unfold CH2.cur, CH2V.LBr. rewrite NILB, (GBL (EG [] len0 rep b cb) eq_refl eq_refl). exact HH.
    + split; [exact Hinv|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; split; [reflexivity | cbn; lia]|].
      split; [exact Hlits | exact I].
  - exact Hfp.
Qed.
End Root.
End EVI64RU.
