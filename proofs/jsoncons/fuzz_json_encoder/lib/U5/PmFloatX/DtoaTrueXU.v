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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Arr FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import G3PureX_u5 G3WalkX_u5 WdHeadX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncPure_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import FxKitX_u5 DumpBufX_u5 WdBrX_u5 FxKitXU DtoaTrueXHU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_dt_xsrc_T_u5 Cut_dt_xsrc_u5.

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DTXU.
Import PMES.
Import DTXHU.

Section DtoaTrueOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.
Hypothesis PROK : PMFXT.prettify_x_specU L HI.
Hypothesis DFOK : PMFXT.dtoa_false_x_specU L HI PML.STRTOD_SCR_V.

Ltac rcut := repeat match goal with |- context [ret_cut ?a ?b] => let v := eval vm_compute in (ret_cut a b) in change (ret_cut a b) with v end.
Ltac dik i kk Xk := destruct i as [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]; destruct kk as [|[|kk]]; cbn [kind] in Xk; try discriminate Xk.
Ltac reg_case RG Ha0 Ha1 :=
  first [ reflexivity
        | (rewrite <- RG; reflexivity)
        | (rewrite <- RG; etransitivity; [|symmetry; first [exact Ha1 | exact Ha0]]; reflexivity) ].

Theorem dtoa_true_x_ok : PMFXT.dtoa_true_x_specU L HI PML.STRTOD_SCR_V.
Proof.
  intros dp LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Hdp & Ha1 & Ha2) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2'' & S3 & S4 & S5).
  unfold PML.a0, PML.a1, PML.a2 in Ha0, Ha1, Ha2.
  assert (DTV : PMFXT.DT_SCR PML.STRTOD_SCR_V = 9344) by (vm_compute; reflexivity).
  rewrite DTV in S2'', S5, Hcont.
  assert (BLS0 : forall i, nth i G.BLS [] = []) by (intros i; do 12 (destruct i as [|i]; [reflexivity|]); destruct i; reflexivity).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hobj as (OS1 & OS2 & OS3). unfold PML.apart in Hapsk.
  set (len0 := len (PML.srep_chars rep)).
  assert (ROOM : len0 + 28 <= CLU) by exact Hroom.
  assert (CLO : 2 ^ 47 - 2 ^ 31 - 2 ^ 23 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 9344) by reflexivity.
  assert (SPRc : hl_ceil L + CH.hd_scr G.HDECL <= sp) by (rewrite SCRV; unfold hl_ceil; lia).
  assert (SPR0 : hl_ceil L + 9344 <= sp) by (unfold hl_ceil; lia).
  pose proof (conj S1 (conj SPRc (conj S3 S4))) as STKF.
  pose proof (conj SPR0 (conj S3 S4)) as SPR.
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a []. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; apply app_nil_r).
  assert (KIMG : forall LBx a, 2 ^ 16 <= a < PML.IMG_RO_HI -> L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
  { intros LBx a Ha. unfold PML.IMG_RO_HI in Ha. apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (HBLK : forall b, In b (LBo ++ PML.srep_blocks rep) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). apply (Hwf b Hb). }
  assert (UG : forall (ln kv : Z) (R' : bvmap 5 word), 0 <= ln < 2 ^ 64 ->
            let E1 := EX (Env (reg_ev R (fun v0 => Z_to_bv 64 (nth (v0 - 32) [S2; ln; kv] 0))) (fun _ => [])) R' in
            (forall x : reg, ev E1 (ridx x) = getr R x) /\
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = dp /\ bv_unsigned (ev E1 11) = SK /\ bv_unsigned (ev E1 32) = S2 /\ bv_unsigned (ev E1 33) = ln /\
            ev E1 32 = Z_to_bv 64 S2 /\ ev E1 33 = Z_to_bv 64 ln /\ ev E1 34 = Z_to_bv 64 kv).
  { intros ln kv R' Hln E1.
    assert (EV1 : forall x : reg, ev E1 (ridx x) = getr R x) by (intros x; unfold E1; rewrite DTXHU.EX_lo by (pose proof (ridx_range x); lia); apply CL5.ev_reg).
    split; [exact EV1|].
    split; [rewrite (EV1 2%bv : ev E1 2 = _), Hsp; apply u64_of_Z; lia|].
    split; [rewrite (EV1 10%bv : ev E1 10 = _), Ha0; apply u64_of_Z; lia|].
    split; [rewrite (EV1 11%bv : ev E1 11 = _), Ha1; apply u64_of_Z; lia|].
    split; [cbn [ev DTXHU.EX nth Nat.ltb Nat.leb Nat.sub reg_ev]; apply u64_of_Z; lia|].
    split; [cbn [ev DTXHU.EX nth Nat.ltb Nat.leb Nat.sub reg_ev]; apply u64_of_Z; lia|].
    split; [reflexivity|]. split; reflexivity. }
  assert (MAIN : forall (i0 : nat) (c0 : CC.cutpoint) (ln kv : Z) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : mem),
     nth_error G.CPS i0 = Some c0 -> phase i0 0 -> 1 <= ln <= 21 -> -343 <= kv <= 309 ->
     CC.At RSEGS c0 (EX (Env (reg_ev R (fun v0 => Z_to_bv 64 (nth (v0 - 32) [S2; ln; kv] 0))) (fun _ => [])) R1) R1 M1 -> PML.fp_ok fx1 ->
     (forall x : word, ~ (sp - 9344 <= bv_unsigned x < sp) -> M1 x = M x) -> L5.defined M1 (sp - 9344) 9344 ->
     srealizes RSEGS SCFG (@PML.cfg fx1 R1 (CC.cp_pc c0) M1 model) K).
  { intros i0 c0 ln kv fx1 R1 M1 Hc0 HPH0 Hln Hkv HAt1 Hfp1 FR1 DALL1.
    destruct (UG ln kv R1 ltac:(lia)) as (EV1 & U2 & U10 & U11 & U32 & U33 & V32 & V33 & V34).
    set (E1 := EX _ R1) in *.
    assert (V2 : ev E1 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV1 2%bv)).
    assert (V4 : ev E1 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV1 4%bv)).
    assert (TP0 : ev E1 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
    assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E1 rg a -> CH2.sclient L LBo sp a)).
    { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
    assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E1 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
    { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (OADDR : estart E1 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
    assert (FRZ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 9344 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn'. apply FR1. rewrite u64_of_Z by lia. exact Hn'. }
    assert (GR1 : mem_grows M M1).
    { intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 9344)) as [Hlo|Hlo]; [rewrite (FR1 x) by lia; exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hhi|Hhi]; [|rewrite (FR1 x) by lia; exact Hx].
      pose proof (DALL1 (bv_unsigned x - (sp - 9344)) ltac:(lia)) as D. replace (sp - 9344 + (bv_unsigned x - (sp - 9344))) with (bv_unsigned x) in D by lia.
      rewrite Z_to_bv_bv_unsigned in D. exact D. }
    set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M2 : mem) => ESBU.sink_inv M2 S2 g1 /\ phase i (ESBU.s_len g1 - len0)).
    assert (AGE : forall i cp E E', nth_error G.CPS i = Some cp -> env_agree GT.NF E1 E -> env_agree (CC.cp_nx cp) E E' -> env_agree GT.NF E1 E').
    { intros i cp E E' Hcp H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i cp Hcp)]]. }
    assert (BRG : forall g1 M0c i E (M2 : mem) m1, CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 ->
                    (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E1 E /\
                    exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M2 (m_vmmaps m1) /\ CredV g1 i E cr1).
    { intros g1 M0c i E M2 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
      destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb. }
    assert (IMGC : forall g1 M0c i E (M2 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
                    CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> PML.img_ro M2).
    { intros g1 M0c i E M2 m1 (O1 & _) (_ & _ & _ & _ & Hfr & _) a Ha. rewrite (Hfr a (KIMG _ a Ha)). rewrite (O1 a (KIMG _ a Ha)). exact (Himg a Ha). }
    assert (OUTF : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E1 E' -> 0 <= a < 2 ^ 64 -> ~ (sp - 9344 <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a)).
    { intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
      pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
      unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
      rewrite (PB.estart_agree GT.NF E1 E' (EVar 2) (-9344) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 9344) by lia. lia. }
    assert (SINKAG : forall g1 (M2 M' : mem), (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) ->
                     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 9344 <= a < sp) -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
                     ESBU.sink_inv M2 S2 g1 -> ESBU.sink_inv M' S2 g1).
    { intros g1 M2 M' HB HFR (HS & HL). split; [|exact HL].
      assert (AG : forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= sp - 9344 \/ sp <= a) -> (a + k <= hl_errno L \/ hl_errno L + 4 <= a) -> L5C.agree_on M2 M' a k).
      { intros a k H0 H1 H2 H3 q Hq. apply HFR; [lia | lia | unfold in_errno; lia]. }
      destruct SPR as (P1 & P2 & P3).
      apply (EK.sink_at_agree M2 M' S2 (ESBU.s_rep g1)); [lia | lia | apply AG; rewrite ?LER; unfold hl_ceil in *; lia | | exact HS].
      destruct (ESBU.s_rep g1) as [s|cap p s] eqn:Hrep; [exact I|].
      destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1' & R2 & R3 & R4). cbn [fst snd] in *. rewrite ILO, IHI in R1'.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. apply AG; rewrite ?LER; unfold hl_ceil in *; lia. }
    assert (STRETCH : forall g1 M0c i cp kk ps t E R2 (M2 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i cp kk ps t -> CC.At (hl_segs L) cp E R2 M2 ->
                        CH2V.okV L M LBo sp G.HDECL W M0c ->
                        CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> XIv g1 i E M2 ->
                        env_agree (CC.cp_nx cp) E E' -> CC.leaf_facts (hl_segs L) cp ps E' R' M2 M' ->
                        ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E1 E' /\ PML.img_ro M').
    { intros g1 M0c i cp kk ps t E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _].
      destruct IL as (tags & Hcp & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i cp E E' Hcp HagE Hag) as HagE'.
      destruct HX as (HX1 & HX2). pose proof (CC.lf_frame _ _ _ _ _ _ _ HLF) as FR.
      split; [|split; [exact HagE' |]].
      - apply (SINKAG g1 M2 M' HB); [|exact HX1]. intros a Ha N1 N2. apply FR. exact (OUTF (CC.cp_F cp) E' a XF HagE' Ha N1).
      - apply (EK.img_ro_agree M2 M'); [|exact (IMGC g1 M0c i E M2 m1 OKV HA)]. intros a Ha. unfold PML.IMG_RO_HI in Ha.
        apply FR. apply (OUTF (CC.cp_F cp) E' a XF HagE'); unfold hl_ceil in *; lia. }
    unfold PML.cfg. rewrite <- LS. rewrite <- LS in HAt1.
    eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E1 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
              G.CPS K PML.fp_ok G.TAGS) with (i := i0) (E := E1).
    - rewrite LS. exact FPM.
    - rewrite LS. exact G.plans.
    - exact G.tags_ok.
    - exact heap_ok3.
    - intros g1 i c kk ps j sg IL E E' R' M2 M' cr1 _ _ _ HC. exact HC.
    - intros g1 M0c OKV i c kk ps j sg IL. exfalso.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. cbv beta iota in X. rewrite andb_false_r in X. discriminate X.
    - intros i c kk ps pc IL g1 M0c OKV.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. cbv beta iota zeta in X.
      apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
      destruct (Z.eqb_spec pc PML.PC_STR_PUSH_BACK) as [->|Hne1].
      { cbv iota in X.
        apply andb_prop in X as [X Xk]. apply andb_prop in X as [Xpc Xs]. apply Z.eqb_eq in Xpc. apply Nat.eqb_eq in Xk.
        unfold sinkj, ret_cut in Xs. destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate Xs].
        apply andb_prop in Xs as [_ Xs].
        destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate Xs].
        destruct (ESB.pushb_chk GT.NF G.HDECL S2E 0 c ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
        apply (ESBU.pushb_leaf_ok L HI HIok LAY GT.NF E1 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
                 S2 Hobj W_S2 S2E 0 eq_refl OADDR PUSHB_OK i c kk ps j cj ci g1 M0c OKV IL Hret Hcj Xpc Hchk).
        - intros E R2 M2 m1 E' R' M' HAt HA HX Hag HLF.
          destruct (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & _).
          split; [exact HINV|]. destruct HX as (_ & HP).
          clear - HP Xk ROOM. dik i kk Xk; cbn [phase] in HP; lia.
        - intros E E' R' M2 M' E2 M3 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1.
          destruct HX as (_ & HP). clear - HP Xk Hret HINV2 G1.
          dik i kk Xk; vm_compute in Hret; injection Hret as <-; (split; [exact HINV2|]); cbn [phase] in HP |- *; rewrite G1; lia. }
      destruct (Z.eqb_spec pc PMFX.PC_PRETTIFY) as [->|Hne2].
      { cbv iota in X.
        apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 Xs]. apply Z.eqb_eq in X1. apply Nat.eqb_eq in Xk.
        unfold sinkj in Xs. apply andb_prop in Xs as [Xj0 Xs].
        assert (Hret : CH2.ret_of G.RETS i kk = Some (ret_cut i kk)) by (unfold ret_cut in *; destruct (CH2.ret_of G.RETS i kk); [reflexivity | discriminate Xj0]).
        destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xs].
        destruct (pr_chk c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
        unfold pr_chk in Hchk.
        lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
        apply andb_prop in Hb as [Hb C2]. apply andb_prop in Hb as [Hb C1]. apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R15].
        apply andb_prop in Hb as [Hb R14]. apply andb_prop in Hb as [Hb R13]. apply andb_prop in Hb as [Hb R12]. apply andb_prop in Hb as [R10 R11].
        apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R12. apply expr_eqb_eq in R13. apply expr_eqb_eq in R14. apply expr_eqb_eq in R15.
        apply expr_eqb_eq in R2X.
        apply (FXKU.strans_leaf_okN L HI HIok LAY GT.NF E1 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
                 S2 Hobj W_S2 S2E 0 eq_refl OADDR PMFX.PC_PRETTIFY PR_SCR (fun pay => 2 <= pay <= 27) (fun _ _ => True) None i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj X1 Hchk).
        - intros; exact I.
        - intros E R2 M2 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF)).
        - intros E R2 M2 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP CONT.
          destruct (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & HIMG).
          destruct HX as (_ & HP).
          assert (HP1 : 0 <= ESBU.s_len g1 - len0 <= 1) by (clear - HP Xk; dik i kk Xk; cbn [phase] in HP; lia).
          pose proof CF as [HA' HR Hreq (Q1 & Q2 & Q3 & Q4 & Q5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
          destruct HA' as (Hmo1 & _).
          assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
          assert (U11' : bv_unsigned (ev E' 11) = SK) by (destruct HagE' as [AG _]; rewrite <- (AG 11%nat) by (unfold GT.NF; lia); exact U11).
          assert (V33' : ev E' 33 = Z_to_bv 64 ln) by (destruct HagE' as [AG _]; rewrite <- (AG 33%nat) by (unfold GT.NF; lia); exact V33).
          assert (V34' : ev E' 34 = Z_to_bv 64 kv) by (destruct HagE' as [AG _]; rewrite <- (AG 34%nat) by (unfold GT.NF; lia); exact V34).
          rewrite Hreq in HR.
          assert (CSP : CH2.ci_csp ci = -144).
          { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
            apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 144)) in G2; [| unfold SPE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
          assert (Ga0 : getr R' 10%bv = Z_to_bv 64 (sp - 140)).
          { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10.
            apply PB.edenot_of_uv. unfold PB.uv. apply CL5.u_lin; [unfold BUFE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. }
          assert (Ga1 : getr R' 11%bv = Z_to_bv 64 ln).
          { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11. cbn [edenot]. exact V33'. }
          assert (Ga2 : getr R' 12%bv = Z_to_bv 64 kv).
          { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite R12.
            unfold KE. cbn [edenot]. rewrite V34'. unfold ext_val. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64).
            rewrite sext32_of_mod64 by lia. reflexivity. }
          assert (Ga3 : getr R' 13%bv = Z_to_bv 64 (2 ^ 64 - 4)).
          { rewrite (HR 13%bv). unfold sr_get. change (bv_eqb (13%bv : bv 5) 0) with false. cbv iota. change (ridx 13%bv) with 13%nat. rewrite R13. reflexivity. }
          assert (Ga4 : getr R' 14%bv = Z_to_bv 64 17).
          { rewrite (HR 14%bv). unfold sr_get. change (bv_eqb (14%bv : bv 5) 0) with false. cbv iota. change (ridx 14%bv) with 14%nat. rewrite R14. reflexivity. }
          assert (Ga5 : getr R' 15%bv = Z_to_bv 64 SK).
          { rewrite (HR 15%bv). unfold sr_get. change (bv_eqb (15%bv : bv 5) 0) with false. cbv iota. change (ridx 15%bv) with 15%nat. rewrite R15. cbn [edenot]. rewrite <- U11'. symmetry. apply Z_to_bv_bv_unsigned. }
          rewrite LS in HK.
          assert (HU : PML.u64 M' SK S2).
          { pose proof (PB.has_ok E' M' _ _ HK C1) as HC0.
            apply (CL5.kword64_elim RSEGS E' M' _ _ SK S2 HC0); [unfold estart; cbn [a_base a_off edenot]; rewrite U11'; lia |].
            destruct HagE' as [AG _]. cbn [edenot]. rewrite <- (AG 32%nat) by (unfold GT.NF; lia). exact U32. }
          assert (HDEF : L5.defined M' (sp - 144) 104).
          { pose proof (PB.has_ok E' M' _ _ HK C2) as HKU.
            apply (CL5.kunk_elim RSEGS E' M' _ _ (sp - 144) 104 HKU); [unfold estart; cbn [a_base a_off edenot]; rewrite U2'; lia | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity]. }
          assert (HDB : L5.defined M' (sp - 140) ln) by (apply (L5.defined_sub M' (sp - 144) 104); [exact HDEF | lia | lia]).
          destruct (defined_bytes M' (sp - 140) (Z.to_nat ln)) as (bs & Hbs & Hbl).
          { rewrite Z2Nat.id by lia. exact HDB. }
          { unfold hl_ceil in *; lia. }
          { rewrite Z2Nat.id by lia. unfold hl_ceil in *; lia. }
          assert (HRM : len (PML.srep_chars (ESBU.s_rep g1)) + 27 <= CLU) by (destruct HINV as [_ HL]; rewrite HL; unfold len0 in *; lia).
          destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *.
          assert (PRV : PR_SCR = 8592) by reflexivity.
          assert (PRV' : PMFXT.PR_SCR = 8592) by (vm_compute; reflexivity).
          rewrite PRV in T2, T5.
          apply (PROK (sp - 140) ln kv bs (CH2.den E' (nth i G.BLS []) ++ LBo ++ []) cr1 (sp + -144) (CC.cp_pc cj) SK S2 kx bx (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
          { rewrite PRV'.
            split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                     split; [exact T1 | split; [lia | split; [lia | split; [exact T4 | exact T5]]]]]]]]|].
            split.
            { split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [exact Ga3|]. split; [exact Ga4|]. split; [exact Ga5|].
              split; [lia|]. split; [lia|].
              exists S2. split; [exact HU|]. split; [lia|].
              split; [exact Hbs|]. split; [exact HDB|]. split; [unfold PMFXT.len; rewrite Hbl; apply Z2Nat.id; lia|].
              split; [lia|]. split; [unfold hl_ceil in *; lia|]. split; [unfold PML.apart; lia | unfold PML.apart; lia]. }
            split; [exact HU|]. split; [lia|]. split; [lia|]. split; [unfold PML.apart; lia|]. split; [exact (proj1 HINV)|].
            split; [unfold PML.obj_on_stack; lia|]. split; [exact HIMG|]. split; [exact HSC | exact HRM]. }
          intros fx2 R3 M3 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRa0 & Hs2 & Hlen2 & HLB' & HLBk & HWc & HSC') HRP2 HPRES Hbv2 HH2.
          apply (CONT fx2 R3 M3 model2 LB' cr' LBk Wc HFP2); [| exact HRP2 | exact HPRES | exact Hbv2 | exact HH2].
          exists rep', pay. split; [exact HPay|]. split; [exact I|]. split; [exact Hs2|]. split; [exact Hlen2|]. split; [exact HLB'|]. split; [exact HLBk|]. split; [exact HWc|].
          exact HSC'.
        - intros E R2 M2 m1 E' R' M' E2 M3 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HPRES HINV2 Hslen HPay.
          destruct HX as (_ & HP). split; [exact HINV2|]. cbv beta in HPay. clear - HP Xk Hslen HPay.
          dik i kk Xk; rcut; cbn [phase] in HP |- *; rewrite Hslen; lia. }
      destruct (Z.eqb_spec pc PMFX.PC_DTOA_FALSE) as [->|Hne3].
      { cbv iota in X.
        apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 Xs]. apply Z.eqb_eq in X1. apply Nat.eqb_eq in Xk.
        unfold sinkj in Xs. apply andb_prop in Xs as [Xj0 Xs].
        assert (Hret : CH2.ret_of G.RETS i kk = Some (ret_cut i kk)) by (unfold ret_cut in *; destruct (CH2.ret_of G.RETS i kk); [reflexivity | discriminate Xj0]).
        destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xs].
        destruct (df_chk c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
        unfold df_chk in Hchk.
        lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
        apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R12]. apply andb_prop in Hb as [R10 R11].
        apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R2X.
        apply (FXKU.strans_leaf_okN L HI HIok LAY GT.NF E1 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
                 S2 Hobj W_S2 S2E 0 eq_refl OADDR PMFX.PC_DTOA_FALSE DF_SCR (fun pay => 1 <= pay <= 27) (fun R' _ => PML.a0 R' 1) (Some 1) i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj X1 Hchk).
        - intros R2 pay HR2. split; [exact HR2 | lia].
        - intros E R2 M2 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF)).
        - intros E R2 M2 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP CONT.
          destruct (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & HIMG).
          destruct HX as (_ & HP).
          assert (HP0 : ESBU.s_len g1 - len0 = 0) by (clear - HP Xk; dik i kk Xk; cbn [phase] in HP; exact HP).
          pose proof CF as [HA' HR Hreq (Q1 & Q2 & Q3 & Q4 & Q5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
          destruct HA' as (Hmo1 & _).
          assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
          assert (U10' : bv_unsigned (ev E' 10) = dp) by (destruct HagE' as [AG _]; rewrite <- (AG 10%nat) by (unfold GT.NF; lia); exact U10).
          assert (U11' : bv_unsigned (ev E' 11) = SK) by (destruct HagE' as [AG _]; rewrite <- (AG 11%nat) by (unfold GT.NF; lia); exact U11).
          rewrite Hreq in HR.
          assert (CSP : CH2.ci_csp ci = -144).
          { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
            apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 144)) in G2; [| unfold SPE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
          assert (Ga0 : getr R' 10%bv = Z_to_bv 64 dp).
          { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10. cbn [edenot]. rewrite <- U10'. symmetry. apply Z_to_bv_bv_unsigned. }
          assert (Ga1 : getr R' 11%bv = Z_to_bv 64 SK).
          { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11. cbn [edenot]. rewrite <- U11'. symmetry. apply Z_to_bv_bv_unsigned. }
          rewrite LS in HK.
          assert (CS1 : CH2.leaves_all G.CPS G.TAGS (fun i c k ps t => negb (Nat.eqb (kind i k) 4) || CC.has_cell (SR.ps_cells ps) (KWord (SA (EVar 11) 0) 8 (EVar 32))) = true)
            by (vm_compute; reflexivity).
          pose proof (CH2.leaves_all_sound _ _ _ CS1 _ _ _ _ _ IL) as XC. cbv beta in XC. rewrite Xk in XC. cbn [Nat.eqb negb orb] in XC.
          assert (HU : PML.u64 M' SK S2).
          { pose proof (PB.has_ok E' M' _ _ HK XC) as HC0.
            apply (CL5.kword64_elim RSEGS E' M' _ _ SK S2 HC0); [unfold estart; cbn [a_base a_off edenot]; rewrite U11'; lia |].
            destruct HagE' as [AG _]. cbn [edenot]. rewrite <- (AG 32%nat) by (unfold GT.NF; lia). exact U32. }
          assert (HRM : len (PML.srep_chars (ESBU.s_rep g1)) + 27 <= CLU) by (destruct HINV as [_ HL]; rewrite HL; unfold len0 in *; lia).
          destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *.
          assert (DFV : DF_SCR = 9200) by reflexivity.
          assert (DFV' : PMFXT.DF_SCR PML.STRTOD_SCR_V = 9200) by (vm_compute; reflexivity).
          rewrite DFV in T2, T5.
          apply (DFOK dp (CH2.den E' (nth i G.BLS []) ++ LBo ++ []) cr1 (sp + -144) (CC.cp_pc cj) SK S2 kx bx (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
          { rewrite DFV'.
            split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                     split; [exact T1 | split; [lia | split; [lia | split; [exact T4 | exact T5]]]]]]]]|].
            split; [split; [exact Ga0|]; split; [lia | exact Ga1]|].
            split; [exact HU|]. split; [lia|]. split; [lia|]. split; [unfold PML.apart; lia|]. split; [exact (proj1 HINV)|].
            split; [unfold PML.obj_on_stack; lia|]. split; [exact HIMG|]. split; [exact HSC | exact HRM]. }
          intros fx2 R3 M3 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRa0 & Hs2 & Hlen2 & HLB' & HLBk & HWc & HSC') HRP2 HPRES Hbv2 HH2.
          apply (CONT fx2 R3 M3 model2 LB' cr' LBk Wc HFP2); [| exact HRP2 | exact HPRES | exact Hbv2 | exact HH2].
          exists rep', pay. split; [exact HPay|]. split; [exact HRa0|]. split; [exact Hs2|]. split; [exact Hlen2|]. split; [exact HLB'|]. split; [exact HLBk|]. split; [exact HWc|].
          exact HSC'.
        - intros E R2 M2 m1 E' R' M' E2 M3 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HPRES HINV2 Hslen HPay.
          destruct HX as (_ & HP). split; [exact HINV2|]. cbv beta in HPay. clear - HP Xk Hslen HPay.
          dik i kk Xk; rcut; cbn [phase] in HP |- *; rewrite Hslen; lia. }
      cbv iota in X.
      match type of X with context [FXK.fp_site ?sg pc] => destruct (FXK.fp_site sg pc) as [hv|] eqn:Hfs end.
      + apply andb_prop in X as [X Xp4]. apply andb_prop in X as [X Xp0]. apply andb_prop in X as [X Xk].
        apply andb_prop in X as [Xpc Xinl]. apply Z.eqb_eq in Xpc. apply Z.leb_le in Xp0. apply Z.ltb_lt in Xp4. apply Nat.eqb_eq in Xk.
        unfold inlj in Xinl. apply andb_prop in Xinl as [_ Xinl].
        destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xinl].
        apply andb_prop in Xinl as [Xinl Xbv]. apply andb_prop in Xinl as [Xchk Xbe].
        apply (FXKU.inl_leaf_okV L HI HIok LAY GT.NF E1 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
                 G.CPS G.TAGS K heap_ok3 (fun _ _ _ _ _ _ H => H) i c kk ps pc (ret_cut i kk) cj 4 hv g1 M0c OKV IL Hcj Xchk Xbe Xbv).
        * rewrite LS, Xpc. exact (FXKU.fp_site_step RSEGS pc hv Xp0 Xp4 Hfs).
        * intros E E' R2 R' M2 M' m1 E2 HAt HA HX Hag HLF Hag2.
          destruct (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & _).
          destruct HX as (_ & HP). split; [exact HINV|]. clear - HP Xk.
          dik i kk Xk; rcut; cbn [phase] in HP |- *; lia.
      + apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 X10]. apply Nat.eqb_eq in Xk.
        intros fx' E R2 M2 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
        destruct (STRETCH g1 M0c i c kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HAmb HX Hag HLF) as (HINV & HagE'0 & _).
        assert (DEFC : L5.defined M0c (sp - 9344) 9344) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
        apply (PB.exit_ret L HI HIok LAY GT.NF E1 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
                 (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
                 9344 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV1 r Hra Hraok heap_ok3 RETPC i c kk ps pc ret_at IL X1 fx' E R2 M2 m1 E' R' M' HAt HAmb Hag HLF).
        intros HRP HPR HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
        destruct HX as (_ & HPH).
        assert (HP2 : L5C.hpres L LBo sp 9344 W M M').
        { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HPR. }
        assert (HPAY : 1 <= ESBU.s_len g1 - len0 <= 28) by (clear - HPH Xk; dik i kk Xk; cbn [phase] in HPH; lia).
        assert (Ga0 : PML.a0 R' 1).
        { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M2 M' 10 (ELit 1) HLF X10) as G10.
          replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). unfold PML.a0. rewrite G10. reflexivity. }
        apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
        * exists (ESBU.s_rep g1), (ESBU.s_len g1 - len0). destruct HINV as [Hs Hl].
          split; [lia|]. split; [exact Ga0|]. split; [exact Hs|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
        * unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL, BLS0 in HH1. cbn [CH2.den map app] in HH1. exact HH1.
    - exact Hc0.
    - exact HAt1.
    - apply (CH2V.amb3V_intro L HI GT.NF E1 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M i0 E1 M1 model
               (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
      split.
      + apply (CH2.amb_pure_step L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E1 M model (CH2V.LBr LBo ESBU.sghost gB (ESBU.SG rep len0)) sp G.HDECL W G.BLS
                 (CredV (ESBU.SG rep len0)) STKF SCRP NF32 W_OK i0 i0 E1 E1 M M1 model).
        * split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
          split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
          exists cr. split; [|exact Hcred].
          unfold CH2.cur, CH2V.LBr. rewrite (GBL (ESBU.SG rep len0)), BLS0. cbn [ESBU.s_rep CH2.den map app]. exact HH.
        * intros a Hfs. apply FR1. intros Hin. apply Hfs. left. rewrite SCRV. exact Hin.
        * exact GR1.
        * apply CC.env_agree_refl.
        * reflexivity.
        * intros cr1 HC. exact HC.
      + split; [|cbn [ESBU.s_len]; rewrite Z.sub_diag; exact HPH0].
        split; [|reflexivity]. cbn [ESBU.s_rep].
        apply (EK.sink_at_agree M M1 S2 rep); [lia | lia | intros q Hq; apply FRZ1; unfold hl_ceil in *; lia | | exact Hsink].
        destruct rep as [s|cap p s] eqn:Hrep; [exact I|].
        destruct (HBLK (p, cap) ltac:(apply in_or_app; right; left; reflexivity)) as (R0 & R1' & R2 & R3 & R4). cbn [fst snd] in R0, R1', R2, R3, R4. rewrite ILO, IHI in R1'.
        split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros q Hq. apply FRZ1; unfold hl_ceil in *; lia.
    - exact Hfp1. }
  destruct Hmo as (Hh & Hl & Hmat).
  unfold PML.cfg. eapply TWBX.cj_evt_srz; [exact Hh | exact Hl | |].
  { unfold canon_regs. rewrite Hsp. rewrite Ha0, Ha1.
    eapply (wh_true (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                    (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp dp SK M).
    - lia.
    - lia.
    - lia.
    - exact S1.
    - exact Hfp.
    - apply TWBX.stk_of_defined; [replace (sp - (sp - 9344)) with 9344 by lia; exact S5 | unfold hl_ceil in *; lia | lia].
    - apply TWBX.mem_inv_of_clear. intros a Ha. apply Himg. unfold PML.IMG_RO_HI. lia.
    - reflexivity. }
  intros ms1 ms1' HP EQV.
  destruct HP as [HP|HP].
  - destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & fs0w & ja & -> & FC & FR0 & ST & MU & WM & MI).
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
    pose proof (fun x => getr_eqv _ _ x REQ) as RG. cbv beta in RG.
    lazymatch goal with |- srealizes _ _ (mkCfg (MS _ ?F2 (Z_to_bv 64 ?pcv) ?fc2 None _ _) _) _ =>
      change (mkCfg (MS R' F2 (Z_to_bv 64 pcv) fc2 None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F2 fc2) R' (CC.cp_pc G.cp0) m' model) end.
    assert (DALL : L5.defined m' (sp - 9344) 9344).
    { pose proof (TWBX.stk_defined _ _ _ ST ltac:(unfold hl_ceil in *; lia) ltac:(unfold SPB; lia)) as DST. unfold SPB in DST.
      pose proof (TWBX.rw_defined _ _ _ FR0 ltac:(unfold SPB; unfold hl_ceil in *; lia)) as D0. unfold SPB, FRZ in D0. cbn [cells_size csize Nat.add] in D0.
      change (Z.of_nat 144) with 144 in D0.
      intros q Hq.
      destruct (Z_lt_le_dec q 9200); [apply DST; lia|].
      replace (sp - 9344 + q) with (sp - 144 + (q - 9200)) by lia. apply D0. lia. }
    assert (FRw : forall x : word, ~ (sp - 9344 <= bv_unsigned x < sp) -> m' x = M x) by (intros x Hx; apply MU; apply DTXHU.outside1; exact Hx).
    destruct (UG 1 0 R' ltac:(lia)) as (EV1 & U2 & U10 & U11 & U32 & U33 & V32 & V33 & V34).
    set (E1 := EX _ R') in *.
    assert (HskS2' : PML.u64 m' SK S2).
    { apply (EK.u64_agree M m' SK S2); [| lia | lia | exact HskS2]. intros q Hq. apply FRw. rewrite u64_of_Z by lia. lia. }
    assert (GSP : getr R' (Z_to_bv 5 (Z.of_nat 2)) = edenot E1 SPE).
    { rewrite (PB.edenot_of_uv E1 _ (sp - 144)).
      - rewrite <- (RG (Z_to_bv 5 (Z.of_nat 2))). reflexivity.
      - unfold PB.uv. apply CL5.u_lin; [unfold SPE; lin_eval; rewrite U2; lia | unfold hl_ceil in *; lia]. }
    apply (MAIN 0%nat G.cp0 1 0 (mkFP F' fc') R' m' ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(lia)); [| exact FC | exact FRw | exact DALL].
    fold E1. unfold CC.At. rewrite regs0, know0. split.
    + apply DTXHU.regs_ok_of. intros nn Hn.
      assert (Hn' : (nn = 1 \/ nn = 2 \/ nn = 3 \/ nn = 4 \/ nn = 5 \/ nn = 6 \/ nn = 7 \/ nn = 8 \/ nn = 9 \/ nn = 10 \/ nn = 11 \/ nn = 12 \/ nn = 13 \/ nn = 14 \/ nn = 15 \/ nn = 16
               \/ nn = 17 \/ nn = 18 \/ nn = 19 \/ nn = 20 \/ nn = 21 \/ nn = 22 \/ nn = 23 \/ nn = 24 \/ nn = 25 \/ nn = 26 \/ nn = 27 \/ nn = 28 \/ nn = 29 \/ nn = 30 \/ nn = 31)%nat) by lia.
      repeat destruct Hn' as [->|Hn']; try subst nn; cbn [nth REGS0];
        first [ exact GSP | reg_case RG Ha0 Ha1 | (cbn [edenot]; unfold E1; cbn [ev DTXHU.EX Nat.ltb Nat.leb nth DTXHU.CSV Nat.sub]; reflexivity) ].
    + unfold know_ok, KNOW0.
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2'].
      * e_range. * e_range. * e_range. * e_align OS3.
      * e_wr. * e_range. * e_align S1.
      * e_disj. * e_disj. * e_disj.
      * e_unk. * e_unk.
      * eapply (TWBX.kw8_of_cell E1 m' _ _ 136%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 1%bv)].
      * eapply (TWBX.kw8_of_cell E1 m' _ _ 128%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 8%bv)].
      * eapply (TWBX.kw8_of_cell E1 m' _ _ 120%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 9%bv)].
      * e_unk.
  - destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & res & ln & kv & fs0w & j0 & dig & j1 & -> &
                    Hres & Hln & Hkv & FC & FR0 & ST & MU & WM & MI).
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
    pose proof (fun x => getr_eqv _ _ x REQ) as RG. cbv beta in RG.
    assert (DALL : L5.defined m' (sp - 9344) 9344).
    { pose proof (TWBX.stk_defined _ _ _ ST ltac:(unfold hl_ceil in *; lia) ltac:(unfold SPB; lia)) as DST. unfold SPB in DST.
      pose proof (TWBX.rw_defined _ _ _ FR0 ltac:(unfold SPB; unfold hl_ceil in *; lia)) as D0. unfold SPB, FRG in D0. cbn [cells_size csize Nat.add] in D0.
      change (Z.of_nat 144) with 144 in D0.
      intros q Hq.
      destruct (Z_lt_le_dec q 9200); [apply DST; lia|].
      replace (sp - 9344 + q) with (sp - 144 + (q - 9200)) by lia. apply D0. lia. }
    assert (FRw : forall x : word, ~ (sp - 9344 <= bv_unsigned x < sp) -> m' x = M x) by (intros x Hx; apply MU; apply DTXHU.outside1; exact Hx).
    destruct (UG ln kv R' ltac:(lia)) as (EV1 & U2 & U10 & U11 & U32 & U33 & V32 & V33 & V34).
    set (E1 := EX _ R') in *.
    assert (HskS2' : PML.u64 m' SK S2).
    { apply (EK.u64_agree M m' SK S2); [| lia | lia | exact HskS2]. intros q Hq. apply FRw. rewrite u64_of_Z by lia. lia. }
    assert (GSP : getr R' (Z_to_bv 5 (Z.of_nat 2)) = edenot E1 SPE).
    { rewrite (PB.edenot_of_uv E1 _ (sp - 144)).
      - rewrite <- (RG (Z_to_bv 5 (Z.of_nat 2))). reflexivity.
      - unfold PB.uv. apply CL5.u_lin; [unfold SPE; lin_eval; rewrite U2; lia | unfold hl_ceil in *; lia]. }
    assert (KN1 : know_ok RSEGS E1 m' KNOW1).
    { unfold know_ok, KNOW1.
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      - eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2'].
      - e_range. - e_range. - e_range. - e_align OS3.
      - e_wr. - e_range. - e_align S1.
      - e_disj. - e_disj. - e_disj.
      - e_unk. - e_unk.
      - eapply (TWBX.kw4_of_cell E1 m' _ _ 104%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact V34].
      - eapply (TWBX.kw4_of_cell E1 m' _ _ 108%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact V33].
      - eapply (TWBX.kw8_of_cell E1 m' _ _ 136%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 1%bv)].
      - eapply (TWBX.kw8_of_cell E1 m' _ _ 128%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 8%bv)].
      - eapply (TWBX.kw8_of_cell E1 m' _ _ 120%nat); [exact FR0 | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2; unfold SPB; lia | unfold SPB; unfold hl_ceil in *; lia | unfold SPB; lia | exact (EV1 9%bv)].
      - e_unk.
      - e_range. }
    assert (Hn' : forall nn, (0 < nn < 32)%nat -> (nn = 1 \/ nn = 2 \/ nn = 3 \/ nn = 4 \/ nn = 5 \/ nn = 6 \/ nn = 7 \/ nn = 8 \/ nn = 9 \/ nn = 10 \/ nn = 11 \/ nn = 12 \/ nn = 13 \/ nn = 14 \/ nn = 15 \/ nn = 16
             \/ nn = 17 \/ nn = 18 \/ nn = 19 \/ nn = 20 \/ nn = 21 \/ nn = 22 \/ nn = 23 \/ nn = 24 \/ nn = 25 \/ nn = 26 \/ nn = 27 \/ nn = 28 \/ nn = 29 \/ nn = 30 \/ nn = 31)%nat) by lia.
    destruct Hres as [->| ->].
    + lazymatch goal with |- srealizes _ _ (mkCfg (MS _ ?F2 (Z_to_bv 64 ?pcv) ?fc2 None _ _) _) _ =>
        change (mkCfg (MS R' F2 (Z_to_bv 64 pcv) fc2 None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F2 fc2) R' (CC.cp_pc G.cp2) m' model) end.
      apply (MAIN 2%nat G.cp2 ln kv (mkFP F' fc') R' m' ltac:(reflexivity) ltac:(reflexivity) Hln Hkv); [| exact FC | exact FRw | exact DALL].
      fold E1. unfold CC.At. rewrite regs2, know2, know21. split; [|exact KN1].
      apply DTXHU.regs_ok_of. intros nn Hn.
      destruct (Hn' nn Hn) as [->|Hn2]; repeat destruct Hn2 as [->|Hn2]; try subst nn; cbn [nth REGS2];
        first [ exact GSP | reg_case RG Ha0 Ha1 | (cbn [edenot]; unfold E1; cbn [ev DTXHU.EX Nat.ltb Nat.leb nth DTXHU.CSV Nat.sub]; reflexivity) ].
    + lazymatch goal with |- srealizes _ _ (mkCfg (MS _ ?F2 (Z_to_bv 64 ?pcv) ?fc2 None _ _) _) _ =>
        change (mkCfg (MS R' F2 (Z_to_bv 64 pcv) fc2 None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F2 fc2) R' (CC.cp_pc G.cp1) m' model) end.
      apply (MAIN 1%nat G.cp1 ln kv (mkFP F' fc') R' m' ltac:(reflexivity) ltac:(reflexivity) Hln Hkv); [| exact FC | exact FRw | exact DALL].
      fold E1. unfold CC.At. rewrite regs1, know1. split; [|exact KN1].
      apply DTXHU.regs_ok_of. intros nn Hn.
      destruct (Hn' nn Hn) as [->|Hn2]; repeat destruct Hn2 as [->|Hn2]; try subst nn; cbn [nth REGS1];
        first [ exact GSP | reg_case RG Ha0 Ha1 | (cbn [edenot]; unfold E1; cbn [ev DTXHU.EX Nat.ltb Nat.leb nth DTXHU.CSV Nat.sub]; reflexivity) ].
Qed.
End DtoaTrueOk.
End DTXU.
