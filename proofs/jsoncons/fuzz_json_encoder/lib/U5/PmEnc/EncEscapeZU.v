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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncPure_u5 EncEscK_u5 EncEscapeB_u5 EncSinkBridgesU EncEscapeU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_escape_string_xsrc_T_u5 Cut_escape_string_xsrc_u5 Cut_escape_string_zero_xsrc_T_u5 Cut_escape_string_zero_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EEZU.
Import PMES.
Import EESB.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

Section EscapeOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.
Hypothesis TOCP_OK : to_codepoint_spec L.

(* [comment removed for export] *)
Theorem escape_zero_okU : forall (q : Z),
  stransU L HI PC_ESCAPE_STRING ESC_SCR
      (fun LBo _ R M SK => PML.a0 R q /\ PML.a1 R (len (@nil Z)) /\ PML.a2 R 0 /\ PML.a3 R 0 /\ getr R 14%bv = Z_to_bv 64 SK /\
                         L5.bytes_at RSEGS M q [] /\ L5.defined M q (len (@nil Z)) /\ in_blocks LBo q (len (@nil Z)) /\ 4096 <= q < 2 ^ 47)
      (fun R' pay => PML.a0 R' pay) (fun pay => pay = esc_len []) (esc_len []).
Proof.
  intros q LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & Ha2 & Ha3 & H14 & Hbq & Hdq & Hinb & Hq) & HSK & SK1 & SK2 & SKap & Hsink & HS2 & Himg & HSC & HROOM) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  unfold ESC_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. change (144 + (256 + (16 + 8224))) with 8640 in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof HS2 as (OS1 & OS2 & OS3). unfold PML.apart in SKap. change (len (@nil Z)) with 0 in *.
  set (len0 := len (PML.srep_chars rep)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2] 0))) (fun _ => @nil byte)).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 0) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 0) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V13 : ev E0 13 = Z_to_bv 64 0) by (rewrite <- Ha3; exact (EV 13%bv)).
  assert (V14 : ev E0 14 = Z_to_bv 64 SK) by (rewrite <- H14; exact (EV 14%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = 0) by (rewrite V11; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = 0) by (rewrite V12; apply u64_of_Z; lia).
  assert (U13 : bv_unsigned (ev E0 13) = 0) by (rewrite V13; apply u64_of_Z; lia).
  assert (U14 : bv_unsigned (ev E0 14) = SK) by (rewrite V14; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (V10 : ev E0 10 = Z_to_bv 64 q) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U10 : bv_unsigned (ev E0 10) = q) by (rewrite V10; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr GZ.HDECL = 8640) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr GZ.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 8640 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (S2R : sp <= S2 /\ S2 + 24 <= hl_sptop L) by (split; lia).
  assert (SCRP : 0 <= CH.hd_scr GZ.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GZT.NF)%nat) by (unfold GZT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs GZ.HDECL) -> SGP.region_vars_lt GZT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U14 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs GZ.HDECL) -> SGP.region_vars_lt GZT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img GZ.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr GZ.HDECL) (CH.hd_scr GZ.HDECL)) by (rewrite SCRV; intros j Hj; apply S5; lia).
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  change (esc_len []) with 0 in HROOM.
  set (g := ESBU.SG rep len0).
  set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) => ESBU.sink_inv M1 S2 g1 /\ ESBU.s_len g1 = len0 /\ ESBU.s_len g1 <= CLU).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; rewrite app_nil_r; reflexivity).
  assert (NILB : forall i E, CH2.den E (nth i GZ.BLS []) = []) by (intros i E; unfold GZ.BLS; destruct i as [|[|i]]; reflexivity).
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GZT.NF E0 model LBo sp GZ.HDECL W GZ.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b, In b (gB g1) -> block_range L (fst b) (snd b)) /\ env_agree GZT.NF E0 E /\ exists cr1, hi_heap HI (LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. cbn [app] in HH1.
    split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). apply in_or_app. right. exact Hb. }
  unfold PML.cfg. change PC_ESCAPE_STRING with (CC.cp_pc GZ.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GZT.NF E0 M model LBo sp GZ.HDECL W GZ.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            GZ.CPS K PML.fp_ok GZ.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact GZ.plans.
  - exact GZ.tags_ok.
  - exact heap_ok3z.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - (* [comment removed for export] *)
    intros g1 M0c OKV i c kk ps j sg IL. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okz _ _ _ _ _ IL) as X. unfold leaf_chkz in X. apply andb_prop in X as [_ X]. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okz _ _ _ _ _ IL) as X. unfold leaf_chkz in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XNF]. apply Nat.leb_le in XNF.
    apply andb_prop in X as [X XA0]. apply andb_prop in X as [X X2]. apply andb_prop in X as [Xi X1]. apply Nat.eqb_eq in Xi. apply Z.eqb_eq in X1. subst i pc.
    intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
    pose proof IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HAmb) as (HB & HagE & _). destruct HX as (HX1 & HX2 & _).
    assert (HagE' : env_agree GZT.NF E0 E').
    { eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact XNF]]. }
    assert (HINV : ESBU.sink_inv M' S2 g1).
    { change GZT.NF with EESB.GT.NF in HagE'. change (ESB.sink_inv M' S2 (ESB.SG (ESBU.s_rep g1) (ESBU.s_len g1))).
      apply (EESU.sink_stretch L E0 sp S2 U2 SPR S2R (CC.cp_F c) E' M1 M' _ XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF)); [|exact HX1].
      cbn [ESB.s_rep]. rewrite <- (GBL g1). exact HB. }
    assert (DEFC : L5.defined M0c (sp - 8640) 8640) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp GZ.HDECL W M0c OKV)).
    apply (PB.exit_ret L HI HIok LAY GZT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp GZ.HDECL W GZ.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK GZ.CPS GZ.TAGS K (XIv g1)
             (CH2V.okV_def0 L M LBo sp GZ.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
             8640 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3z RETPC 0%nat c kk ps RETPC ret_at
             IL X2 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
    intros HRP HP HA' _. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
    assert (HP2 : L5C.hpres L LBo sp 8640 W M M').
    { rewrite <- SCRV. apply (CH2V.hpres_rebase L GZT.NF M LBo sp GZ.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
    assert (Ga0 : PML.a0 R' 0).
    { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (ELit 0) HLF XA0) as G10.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). exact G10. }
    apply (Hcont fx' R' M' m1 (LBo ++ gB g1) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
    * exists (ESBU.s_rep g1), 0. destruct HINV as [HS HL].
      split; [reflexivity|]. split; [exact Ga0|]. split; [exact HS|]. split; [rewrite HL, HX2; unfold len0; lia|].
      split; [rewrite (GBL g1); reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
    * unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8640) 8640) by (intros z Hz; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, GZ.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HSK].
    + e_range. + e_range.
    + cbn [kentry_ok]. split; [lia | split; [lia | intros z Hz; apply Himg; unfold PML.IMG_RO_HI; lia]].
    + e_range.
    + e_range. + e_align OS3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
    + e_range.
    + e_unk.
    + e_range.
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GZT.NF E0 M model LBo sp GZ.HDECL W GZ.BLS ESBU.sghost gB CredV XIv g M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp GZ.HDECL W DEF0)).
    split; [|split; [split; [exact Hsink | reflexivity] | split; [reflexivity | cbn [g ESBU.s_len]; unfold len0; lia]]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; rewrite NILB, (GBL g); cbn [app g ESBU.s_rep]; exact HH|].
    exact HSC.
  - exact Hfp.
Qed.

Lemma stransU_pre_weaken : forall pc scr (A A' : list (Z * Z) -> Z -> bvmap 5 word -> mem -> Z -> Prop) Ret PayP paymax,
  (forall LBo x R M SK, A' LBo x R M SK -> A LBo x R M SK) -> stransU L HI pc scr A Ret PayP paymax -> stransU L HI pc scr A' Ret PayP paymax.
Proof.
  intros pc scr A A' Ret PayP paymax HW HS LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HK Hfp (Hentry & HA & Hrest) Hcont.
  exact (HS LBo cr sp r SK S2 kx bx rep fx R M model K HH Hmo HK Hfp (conj Hentry (conj (HW _ _ _ _ _ HA) Hrest)) Hcont).
Qed.

Theorem escape_string_ok : escape_string_specU L HI.
Proof.
  intros q bs. destruct bs as [|b0 bs'].
  - exact (escape_zero_okU q).
  - eapply stransU_pre_weaken; [|eapply (EESU.escape_main_okU L HI); try eassumption; unfold len; cbn [length]; lia].
    intros LBo x R M SK (A0 & A1 & A2 & A3 & A14 & AB & AD & AI & _). exact (conj A0 (conj A1 (conj A2 (conj A3 (conj A14 (conj AB (conj AD AI))))))).
Qed.
End EscapeOk.
End EEZU.
