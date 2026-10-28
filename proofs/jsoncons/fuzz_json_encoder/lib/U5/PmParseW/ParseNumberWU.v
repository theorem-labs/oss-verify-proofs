(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5 ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseBridgesX_u5 ParseBridges6_u5 ParseBridges6X_u5 ParseBridgesPX3_u5 XInvKit_u5 ParseNumberChk_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallWin_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import SmallPtW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseBridges6W_u5 ParseNumberKW_u5 ParseNumberChkW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallPtX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require ParseNumberW_u5 ParseBridges6WU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PNWU.
Import PNC.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section MainU.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPR_OK : PMS.str_append_range_spec L HI.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis ENDI_OK : PMW.end_integer_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDF_OK : PMW.end_fraction_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Abbreviation SSCR := PML.STRTOD_SCR_V.
Abbreviation WDX := PMES.WD_SCR_X.
Abbreviation SCRC := (PMX.PFX_SCR SSCR WDX).
Variables (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate) (eg : eghost).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Variables (p e : Z).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo ++ g_lbv eg) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r SCRC.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R p.
Hypothesis Ha2 : PML.a2 R V.
Hypothesis Ha3 : PML.a3 R E.
Hypothesis Hwin : PML.ps_win ps = Some (p, e).
Hypothesis Hmore : PML.ps_more ps = true.
Hypothesis Hst : PML.ps_st ps = PML.ST_NUMBER.
Hypothesis HPA : PML.parser_at M P ps.
Hypothesis HWF : PML.wf_ps ps.
Hypothesis HWIN : PML.win_ok M LBo ps.
Hypothesis HBB : PML.buf_bound ps B.
Hypothesis HVIS : PML.vis_at M V.
Hypothesis HEC : PML.ec_at M E 0.
Hypothesis HLS : PML.ls_ok g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis HINV : enc_inv M V S2 eg.
Hypothesis HLIT : PML.lits_ok M.
Hypothesis HSYNC : PMX.enc_sync ps eg.
Hypothesis Hkx : 0 <= kx.
Hypothesis Hbx : 0 <= bx.
Hypothesis HPC : PML.pcredit_x L cr ps (kx + PMX.kenc L eg) (bx + PMES.benc L eg).
Hypothesis OBJS : PMX.objs_x L sp P V E S2.
Variables (pos0 : Z) (winb : list Z).
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Hcpr : 0 <= pos0 < 2 ^ 64.
Hypothesis Hwinb : L5.bytes_at RSEGS M p winb /\ Z.of_nat (length winb) = e - p.
Hypothesis Hwinr : Forall (fun c => 0 <= c < 256) winb.

Variable cw : PMR.ctrl.
Hypothesis HRM : PMR.rm_match cw M P ps.
Hypothesis HROOM : PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm PMW.FParseNumber cw winb).
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state) (eg' : eghost),
      PML.parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps)) /\ PML.wf_ps ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.LS2 /\ code <> 0) /\
      enc_inv M' V S2 eg' /\ PML.lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
      LB' = PML.ps_blocks ps' ++ LBo ++ g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\ PML.pcredit_x L cr' ps' (kx + PMX.kenc L eg') (bx + PMES.benc L eg') /\
      (PMS.not_retreated ps ps' /\ (exists p e : Z, PML.ps_win ps' = Some (p, e) /\ PML.a0 R' p) /\
       (code = 0 -> PML.ps_level ps' = PML.ps_level ps /\ PML.ps_more ps' = true /\ (PML.ps_st ps' = PML.ST_NUMBER -> PMS.win_exhausted ps') /\
                   In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])) /\
      PNKW.w3n cw winb M' P ps ps' eg eg' code) ->
   regs_preserved R R' -> L5C.hpres L LBk sp SCRC W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Local Abbreviation wlen := (e - p) (only parsing).
Local Abbreviation bcap := (PML.ps_bcap ps) (only parsing).
Local Abbreviation k0 := ((PML.ps_bcap ps) / 2) (only parsing).
Local Abbreviation bptr := (PML.ps_bptr ps) (only parsing).
Local Abbreviation size0 := (Z.of_nat (length (PML.ps_buf ps))) (only parsing).
Local Abbreviation sb := (PML.ps_sb ps) (only parsing).
Local Abbreviation scap := (PML.ps_scap ps) (only parsing).
Local Abbreviation slen := (Z.of_nat (length (PML.ps_stack ps))) (only parsing).
Local Abbreviation level := (PML.ps_level ps) (only parsing).
Local Abbreviation sst0 := (PML.ps_sst ps) (only parsing).
Local Abbreviation nst0 := (PML.ps_nst ps) (only parsing).
Local Abbreviation done := (PML.b2z (PML.ps_done ps)) (only parsing).

Local Abbreviation T_OBJJ := (@ParseNumberW_u5.OBJJ L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_OP := (@ParseNumberW_u5.OP L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_OV := (@ParseNumberW_u5.OV L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_OE := (@ParseNumberW_u5.OE L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_AP1 := (@ParseNumberW_u5.AP1 L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_AP2 := (@ParseNumberW_u5.AP2 L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_AP3 := (@ParseNumberW_u5.AP3 L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_KENC0 := (@ParseNumberW_u5.KENC0 L LAY) (only parsing).
Local Abbreviation E0 := (@ParseNumberW_u5.E0 S2 B ps R p e pos0 winb) (only parsing).
Local Abbreviation T_PAR := (@ParseNumberW_u5.PAR P ps M p e Hwin Hmore Hst HPA) (only parsing).
Local Abbreviation T_SPF := (@ParseNumberW_u5.SPF L sp r ps R M p e Hentry winb) (only parsing).
Local Abbreviation T_STKX := (@ParseNumberW_u5.STKX L sp r ps R M p e Hentry winb) (only parsing).
Local Abbreviation T_U52 := (@ParseNumberW_u5.U52 L sp r P V E S2 B ps R M p e Hentry OBJS pos0 winb) (only parsing).
Local Abbreviation T_NUM := (@ParseNumberW_u5.NUM SCFG_P L HI HIok LBo cr P B kx (bx + PMES.benc L eg) ps eg M model p e HH Hwin Hmore Hst HPA HWF HWIN HBB HPC winb Hwinb) (only parsing).
Local Abbreviation T_EV0 := (@ParseNumberW_u5.EV0 S2 B ps R p e pos0 winb) (only parsing).
Local Abbreviation T_VV := (@ParseNumberW_u5.VV L sp r P V E S2 B ps R M p e Hentry Ha0 Ha1 Ha2 Ha3 pos0 winb) (only parsing).
Local Abbreviation T_UU := (@ParseNumberW_u5.UU SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_At0 := (@ParseNumberW_u5.At0 SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HVIS HEC HLS HPC OBJS pos0 winb Hpos0 Hcpr Hwinb) (only parsing).
Local Abbreviation W := (@ParseNumberW_u5.W P V E S2) (only parsing).
Local Abbreviation T_STKF := (@ParseNumberW_u5.STKF L sp r ps R M p e Hentry winb) (only parsing).
Local Abbreviation T_SCRP := (@ParseNumberW_u5.SCRP ps p e winb) (only parsing).
Local Abbreviation T_NF32 := (@ParseNumberW_u5.NF32 ps p e winb) (only parsing).
Local Abbreviation T_U2 := (@ParseNumberW_u5.U2 SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_TP0 := (@ParseNumberW_u5.TP0 L LAY sp r P V E S2 B ps R M p e Hentry Ha0 Ha1 Ha2 Ha3 pos0 winb) (only parsing).
Local Abbreviation T_STATW := (@ParseNumberW_u5.STATW L LAY sp ps p e winb) (only parsing).
Local Abbreviation T_W_OK := (@ParseNumberW_u5.W_OK L LAY sp r P V E S2 ps R M p e Hentry OBJS winb) (only parsing).
Local Abbreviation T_CRS_OK := (@ParseNumberW_u5.CRS_OK SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_WRS_OK := (@ParseNumberW_u5.WRS_OK SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_IMG_OK := (@ParseNumberW_u5.IMG_OK L LAY ps p e winb) (only parsing).
Local Abbreviation T_DEF0 := (@ParseNumberW_u5.DEF0 L sp r ps R M p e Hentry winb) (only parsing).
Local Abbreviation KXf := (@ParseNumberW_u5.KXf L kx) (only parsing).
Local Abbreviation KXg := (@ParseNumberW_u5.KXg L kx) (only parsing).
Local Abbreviation statw := (ParseNumberW_u5.statw) (only parsing).
Local Abbreviation cutn := (ParseNumberW_u5.cutn) (only parsing).
Local Abbreviation text := (@ParseNumberW_u5.text ps winb) (only parsing).
Local Abbreviation auto_ok := (@ParseNumberW_u5.auto_ok ps p e winb) (only parsing).
Local Abbreviation appk := (ParseNumberW_u5.appk) (only parsing).
Local Abbreviation XI := (@ParseNumberW_u5.XI LBo P E B g ps M p e winb) (only parsing).
Local Abbreviation GX := (@ParseNumberW_u5.GX E ps eg) (only parsing).
Local Abbreviation CI := (@ParseNumberW_u5.CI winb cw) (only parsing).
Local Abbreviation NOFJ := (@ParseNumberW_u5.NOFJ p e) (only parsing).
Local Abbreviation SGO := (@ParseNumberW_u5.SGO p e winb cw) (only parsing).
Local Abbreviation SFIN := (@ParseNumberW_u5.SFIN p e winb cw) (only parsing).
Local Abbreviation SERR := (@ParseNumberW_u5.SERR winb cw) (only parsing).
Local Abbreviation SAPPX := (@ParseNumberW_u5.SAPPX p e winb cw) (only parsing).
Local Abbreviation SEND := (@ParseNumberW_u5.SEND LBo P E B g ps eg p e winb cw) (only parsing).
Local Abbreviation SIM := (@ParseNumberW_u5.SIM LBo P E B g ps eg p e winb cw) (only parsing).
Local Abbreviation XIv := (@ParseNumberW_u5.XIv LBo P V E S2 B g ps eg M p e winb cw) (only parsing).
Local Abbreviation T_ec_at_fun := (@ParseNumberW_u5.ec_at_fun E ps p e winb) (only parsing).
Local Abbreviation T_below_frame := (@ParseNumberW_u5.below_frame SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_u8_frame := (ParseNumberW_u5.u8_frame) (only parsing).
Local Abbreviation T_CRS_OKV := (@ParseNumberW_u5.CRS_OKV SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_okV_defc := (@ParseNumberW_u5.okV_defc L LAY LBo sp r P V E S2 ps R M p e Hentry winb) (only parsing).
Local Abbreviation T_okV_hpres := (@ParseNumberW_u5.okV_hpres L LBo sp r P V E S2 ps R M p e Hentry winb) (only parsing).
Local Abbreviation T_FRZ := (@ParseNumberW_u5.FRZ SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_W_low := (@ParseNumberW_u5.W_low L sp r P V E S2 ps R M p e Hentry OBJS winb) (only parsing).
Local Abbreviation T_ls_pre := (@ParseNumberW_u5.ls_pre L HI LAY LBo sp r P V E S2 B kx _ g ps R M model p e Hentry HLS HG OBJS pos0 winb) (only parsing).
Local Abbreviation T_stat_step := (@ParseNumberW_u5.stat_step SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_buf_step := (@ParseNumberW_u5.buf_step SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_goto_facts := (ParseNumberW_u5.goto_facts) (only parsing).
Local Abbreviation T_goto_cred := (@ParseNumberW_u5.goto_cred L S2 B kx _ ps R p e pos0 winb) (only parsing).
Local Abbreviation T_mod64_sub := (@ParseNumberW_u5.mod64_sub ps p e winb) (only parsing).
Local Abbreviation T_content_sound := (@ParseNumberW_u5.content_sound SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr) (only parsing).
Local Abbreviation T_uv_over := (ParseNumberW_u5.uv_over) (only parsing).
Local Abbreviation T_leaf_know := (@ParseNumberW_u5.leaf_know L LAY) (only parsing).
Local Abbreviation T_jv_agree := (ParseNumberW_u5.jv_agree) (only parsing).
Local Abbreviation T_gblocks_amb := (@ParseNumberW_u5.gblocks_amb SCFG_P L HI HIok LAY LBo sp r P V E S2 B kx _ ps R M model p e Hentry OBJS pos0 winb) (only parsing).
Local Abbreviation T_xinv_stretch := (@ParseNumberW_u5.xinv_stretch SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_goto_xi0 := (@ParseNumberW_u5.goto_xi0 SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr) (only parsing).
Local Abbreviation T_HCU := (@ParseNumberW_u5.HCU SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_jj_of_d := (@ParseNumberW_u5.jj_of_d SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_jpos_sound := (@ParseNumberW_u5.jpos_sound SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_jzero_sound := (ParseNumberW_u5.jzero_sound) (only parsing).
Local Abbreviation T_wbyte := (@ParseNumberW_u5.wbyte SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr) (only parsing).
Local Abbreviation T_goto_sim := (@ParseNumberW_u5.goto_sim SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr cw HRM) (only parsing).
Local Abbreviation T_goto_xi := (@ParseNumberW_u5.goto_xi SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr cw HRM) (only parsing).
Local Abbreviation T_statw_kept := (@ParseNumberW_u5.statw_kept L LAY ps p e winb) (only parsing).
Local Abbreviation T_OADDR := (@ParseNumberW_u5.OADDR SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_OBJ := (@ParseNumberW_u5.OBJ L sp P V E S2 ps p e OBJS winb) (only parsing).
Local Abbreviation T_other_facts := (ParseNumberW_u5.other_facts) (only parsing).
Local Abbreviation T_mod_pos := (@ParseNumberW_u5.mod_pos ps p e winb) (only parsing).
Local Abbreviation T_amb_def := (@ParseNumberW_u5.amb_def SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Hwin Hmore Hst HPA HWF HWIN HBB HPC pos0 winb Hwinb) (only parsing).
Local Abbreviation T_nth_cut := (ParseNumberW_u5.nth_cut) (only parsing).
Local Abbreviation T_EADDR := (@ParseNumberW_u5.EADDR SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_PADDR := (@ParseNumberW_u5.PADDR SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_EOBJ := (@ParseNumberW_u5.EOBJ L sp P V E S2 OBJS) (only parsing).
Local Abbreviation T_SETEC_W_in := (@ParseNumberW_u5.SETEC_W_in P V E S2 M p e pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_reg_at := (ParseNumberW_u5.reg_at) (only parsing).
Local Abbreviation T_pa_cap := (@ParseNumberW_u5.pa_cap ps p e winb) (only parsing).
Local Abbreviation T_pa_len := (ParseNumberW_u5.pa_len) (only parsing).
Local Abbreviation T_WPAR_in := (@ParseNumberW_u5.WPAR_in P V E S2) (only parsing).
Local Abbreviation T_W_ENC := (@ParseNumberW_u5.W_ENC P V E S2) (only parsing).
Local Abbreviation T_S2LT := (@ParseNumberW_u5.S2LT ps p e winb) (only parsing).
Local Abbreviation T_VADDR := (@ParseNumberW_u5.VADDR SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_S2ADDR := (@ParseNumberW_u5.S2ADDR L sp r P V E S2 B ps R M p e Hentry OBJS pos0 winb) (only parsing).
Local Abbreviation T_xi_stat := (@ParseNumberW_u5.xi_stat LBo P E B g ps M p e winb) (only parsing).
Local Abbreviation T_ls_at_leaf := (@ParseNumberW_u5.ls_at_leaf SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HLS HG HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_leaf_setec := (@ParseNumberW_u5.leaf_setec SCFG_P L HI HIok LAY SETEC_OK LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model K p e HH HKnil Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HEC HLS HG HPC OBJS pos0 winb Hcpr Hwinb Hwinr cw) (only parsing).
Local Abbreviation T_wf_upd := (@ParseNumberW_u5.wf_upd ps Hmore Hst HWF) (only parsing).
Local Abbreviation T_pa_retext := (@ParseNumberW_u5.pa_retext P) (only parsing).
Local Abbreviation T_view_sound := (@ParseNumberW_u5.view_sound SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_leaf_append := (@ParseNumberW_u5.leaf_append SCFG_P L HI HIok LAY APPR_OK LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) g ps eg R M model K p e HH HKnil Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb Hwinr cw) (only parsing).
Local Abbreviation T_text_len := (@ParseNumberW_u5.text_len ps M p e winb Hwinb) (only parsing).
Local Abbreviation T_blk_frame := (@ParseNumberW_u5.blk_frame SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_cur_range := (@ParseNumberW_u5.cur_range SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).
Local Abbreviation T_ecell0 := (@ParseNumberW_u5.ecell0 SCFG_P L HI HIok LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb) (only parsing).

Definition BXg (g1 : eghost) (tlb : list (Z * Z)) : Z := ParseNumberW_u5.BXf L (bx + PMES.benc L g1) tlb.
Definition CredV (g1 : eghost) (i : nat) (E1 : env) (cr1 : credit) : Prop := ParseNumberW_u5.CredV L kx (bx + PMES.benc L g1) g1 i E1 cr1.
Lemma CRED_EQ : forall g1 i E1 cr1, CredV g1 i E1 cr1 <-> PPS.bufcred L cr1 (PB.cap_of G.BLS i E1) (KXg g1 (PB.tl_of G.BLS i E1)) (BXg g1 (PB.tl_of G.BLS i E1)).
Proof. intros g1 i E1 cr1. split; intros H; exact H. Qed.
Lemma cred_of_blocks : forall g1 i E1 cr1 ps1, CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps1 -> In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  (CredV g1 i E1 cr1 <-> PML.pcredit_x L cr1 ps1 (kx + PMX.kenc L g1) (bx + PMES.benc L g1)).
Proof.
  intros g1 i E1 cr1 ps1 Hden Hsc.
  pose proof (PmLayout.ly_kpm L LAY) as KPM. pose proof (PmLayout.ly_bov L LAY) as BOV.
  pose proof (T_KENC0 g1) as K0. pose proof (EK.benc_nonneg L KPM BOV g1) as B0.
  rewrite (PPS.pcredit_x_bufcred L cr1 ps1 (kx + PMX.kenc L g1) (bx + PMES.benc L g1) KPM BOV Hsc ltac:(lia) ltac:(lia)).
  unfold CredV, ParseNumberW_u5.CredV, ParseNumberW_u5.KXg, ParseNumberW_u5.KXf, ParseNumberW_u5.BXf, PB.cap_of, PB.tl_of. rewrite Hden.
  unfold PML.ps_blocks. cbn [hd tl snd fst].
  rewrite (Z.add_assoc (PPS.stk_kx L (PML.ps_scap ps1)) kx (PMX.kenc L g1)). reflexivity.
Qed.
Abbreviation gB := PMES.g_lbv.
Abbreviation LBr := (CH2V.LBr LBo eghost gB).
Abbreviation HAMBV := (CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV).
Abbreviation AMB3XV := (CH2V.amb3XV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV XIv).
Abbreviation OKV := (CH2V.okV L M LBo sp G.HDECL W).
Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Lemma leaf_setec : forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther PML.PC_SET_EC) -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = PML.PC_SET_EC -> PNC.kind_of i = PNC.KPre -> PNC.kind_of j = PNC.KSetEc -> PNC.foot_pre_chk c = true ->
  PB2.setec_chk GT.NF G.HDECL PNC.Eb 0 c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> (GT.NF <= CH2.ci_nx ci)%nat ->
  forall g1 M0c, OKV M0c -> CC.leaf_ok (hl_segs L) G.CPS (AMB3XV g1 M0c) K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j cj ci IL Hret Hcj Hpc Hki Hkj Hfoot Hchk Hnx g1 M0c HOK.
  intros fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH.
  assert (Hg : g1 = eg) by (destruct HA as (_ & (_ & HGX & _)); unfold ParseNumberW_u5.GX in HGX; rewrite Hki in HGX; exact HGX).
  subst g1.
  exact (T_leaf_setec i c k ps1 j cj ci IL Hret Hcj Hpc Hki Hkj Hfoot Hchk Hnx eg M0c HOK fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH).
Qed.
Lemma leaf_append : forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther PML.PC_APPEND_RANGE) -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = PML.PC_APPEND_RANGE -> PNC.kind_of i = PNC.KPre -> PNC.kind_of j = PNC.KApp -> PNC.foot_pre_chk c = true -> (0 < i)%nat ->
  PB3.appendr_chk GT.NF G.HDECL PNC.Pb 224 PNC.SEG PNC.WLEN 132 c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> PNC.app_leaf_chk i c ps1 cj = true ->
  forall g1 M0c, OKV M0c -> CC.leaf_ok (hl_segs L) G.CPS (AMB3XV g1 M0c) K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j cj ci IL Hret Hcj Hpc Hki Hkj Hfoot Hi0 Hchk Happ g1 M0c HOK.
  intros fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH.
  assert (Hg : g1 = eg) by (destruct HA as (_ & (_ & HGX & _)); unfold ParseNumberW_u5.GX in HGX; rewrite Hki in HGX; exact HGX).
  subst g1.
  exact (T_leaf_append i c k ps1 j cj ci IL Hret Hcj Hpc Hki Hkj Hfoot Hi0 Hchk Happ eg M0c HOK fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH).
Qed.
Lemma en_stack : forall c w, PMR.c_stack (PMR.q_c (PMR.end_number c w)) = PMR.c_stack c.
Proof.
  intros c w. unfold PMR.end_number, PMR.bind. cbn [PMR.q_code PMR.q_c PMR.q_w negb Z.eqb].
  unfold PMR.after_value. repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Lemma frm_end : forall c E' (M1 M' : mem), PNC.foot_end_chk c = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M1 a) -> L5.frame_but [(sp - PNC.SCR, PNC.SCR)] M1 M'.
Proof.
  intros c E' M1 M' Hf Hag HF x Hx. apply HF.
  pose proof (T_FRZ E' Hag) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
  unfold PNC.foot_end_chk in Hf. rewrite forallb_forall in Hf.
  unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  specialize (Hf _ Hin). unfold PNC.stack_reg_eqb in Hf.
  apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2].
  apply expr_eqb_eq in H1, H3. apply Z.eqb_eq in H2. subst rb rlo rlen.
  unfold estart, elenZ. cbn [a_base a_off].
  unfold PB.uv in Hsp. rewrite Hsp.
  change (bv_unsigned (edenot E' (ELit PNC.SCR))) with PNC.SCR.
  specialize (Hx (sp - PNC.SCR, PNC.SCR) (or_introl eq_refl)). unfold L5.in_rng in Hx. cbn [fst snd] in Hx. lia.
Qed.
Lemma out_hi : forall a n, sp <= a -> a + n <= 2 ^ 64 -> PB2.out [(sp - PNC.SCR, PNC.SCR)] a n.
Proof.
  intros a n H1 H2. pose proof T_STKX as (X1 & X2 & X3 & X4). unfold PB2.out.
  split; [lia|]. split; [lia|]. intros j Hj r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
Qed.
Lemma out_lo : forall a n, 0 <= a -> 0 <= n -> a + n <= hl_ceil L -> PB2.out [(sp - PNC.SCR, PNC.SCR)] a n.
Proof.
  intros a n H0 Hn H1. pose proof T_STKX as (X1 & X2 & X3 & X4). unfold PB2.out.
  split; [lia|]. split; [lia|]. intros j Hj r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
Qed.
Lemma win_bytes_M' : forall M' : mem, (forall a, L5C.kept L LBo sp SCRC W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5.bytes_at RSEGS M' p winb.
Proof.
  intros M' Hk.
  pose proof T_SPF as (_ & _ & _ & _ & _ & HS6 & HS7). pose proof T_STKX as (X1 & X2 & X3 & X4).
  assert (HB0 : PMW.win_bytes M ps winb).
  { unfold PMW.win_bytes. rewrite Hwin. split; [exact (proj1 Hwinb)|]. split; [exact (proj2 Hwinb)|].
    eapply Forall_impl; [|exact Hwinr]. intros a Ha. cbn beta in *. lia. }
  assert (HW0 : forall (r0 : L5.range) (a : Z), In r0 W -> L5.in_rng r0 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L).
  { intros r0 a Hr Ha. destruct (T_W_OK r0 a Hr Ha) as (_ & [Y|Y]); [left; lia | right; tauto]. }
  assert (HSC : hl_ceil L + SCRC <= sp) by (replace (2 ^ 23) with 8388608 in HS7 by reflexivity; lia).
  pose proof (SPTW.win_bytes_kept L HI HIok LAY (PML.ps_blocks ps ++ LBo ++ g_lbv eg) cr M M' (m_vmmaps model) LBo sp SCRC W ps ps winb HH
                (fun b Hb => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))) Hk HSC ltac:(rewrite HS6; lia) ltac:(lia) HW0 HWIN HB0 eq_refl) as X.
  unfold PMW.win_bytes in X. rewrite Hwin in X. exact (proj1 X).
Qed.
Definition endreg_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc PNC.ENDI || Z.eqb pc PNC.ENDF)%bool
      then (expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) PNC.Pb && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) PNC.Vb
            && expr_eqb (nth 12 (CA.ps_reglist ps) (ELit 0)) PNC.Eb)%bool
      else true
  | _ => true
  end.
Lemma endreg_ok : CH2.leaves_all G.CPS G.TAGS endreg_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma end_args : forall i c k ps1 pc E' R', is_leaf i c k ps1 (CC.TOther pc) -> (pc = PNC.ENDI \/ pc = PNC.ENDF) ->
  regs_ok E' (CA.ps_reglist ps1) R' -> env_agree GT.NF E0 E' -> forall (Mx : mem) psx, PMS.std_args R' Mx P V E psx.
Proof.
  intros i c k ps1 pc E' R' IL Hpc HR Hag Mx psx.
  assert (Hpcb : (Z.eqb pc PNC.ENDI || Z.eqb pc PNC.ENDF)%bool = true) by (destruct Hpc as [-> | ->]; vm_compute; reflexivity).
  pose proof (CH2.leaves_all_sound G.CPS G.TAGS endreg_chk endreg_ok i c k ps1 (CC.TOther pc) IL) as HER.
  unfold endreg_chk in HER. rewrite Hpcb in HER.
  apply andb_prop in HER as [HER N12]. apply andb_prop in HER as [N10 N11].
  apply expr_eqb_eq in N10, N11, N12.
  pose proof T_PADDR as XP. pose proof T_EADDR as XE. pose proof T_VADDR as XV.
  unfold estart in XP, XE. cbn [a_base a_off] in XP, XE.
  unfold PMS.std_args, PML.a0, PML.a1, PML.a2.
  erewrite (T_reg_at E' (CA.ps_reglist ps1) R' 10); [|exact HR|reflexivity|reflexivity].
  erewrite (T_reg_at E' (CA.ps_reglist ps1) R' 11); [|exact HR|reflexivity|reflexivity].
  erewrite (T_reg_at E' (CA.ps_reglist ps1) R' 12); [|exact HR|reflexivity|reflexivity].
  rewrite N10, N11, N12.
  rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' PNC.Pb)), <- (Z_to_bv_bv_unsigned _ (edenot E' PNC.Vb)), <- (Z_to_bv_bv_unsigned _ (edenot E' PNC.Eb)).
  change (bv_unsigned (edenot E' PNC.Pb)) with (PB.uv E' PNC.Pb).
  change (bv_unsigned (edenot E' PNC.Vb)) with (PB.uv E' PNC.Vb).
  change (bv_unsigned (edenot E' PNC.Eb)) with (PB.uv E' PNC.Eb).
  rewrite (PB.uv_agree GT.NF E0 E' PNC.Pb Hag ltac:(vm_compute; reflexivity)), (PB.uv_agree GT.NF E0 E' PNC.Vb Hag ltac:(vm_compute; reflexivity)), (PB.uv_agree GT.NF E0 E' PNC.Eb Hag ltac:(vm_compute; reflexivity)).
  change (bv_unsigned (edenot E0 PNC.Pb)) with (PB.uv E0 PNC.Pb) in XP.
  change (bv_unsigned (edenot E0 PNC.Eb)) with (PB.uv E0 PNC.Eb) in XE.
  split; [f_equal; lia|]. split; [f_equal; exact XV|]. f_equal; lia.
Qed.
Lemma kept_scr : forall LB a, L5C.kept L LB sp SCRC W a -> L5C.kept L LB sp (CH.hd_scr G.HDECL) W a.
Proof.
  intros LB a (H1 & H2 & H3 & H4).
  assert (SCGE : CH.hd_scr G.HDECL <= SCRC) by (rewrite ParseNumberW_u5.SCRV; vm_compute; discriminate).
  assert (SCG0 : 0 <= CH.hd_scr G.HDECL) by (rewrite ParseNumberW_u5.SCRV; lia).
  split; [exact H1|]. split; [|split; [exact H3|exact H4]].
  destruct H2 as [H2|[H2|H2]]; [left; exact H2 | right; left; lia | right; right; exact H2].
Qed.
Lemma kept_M' : forall M0c (M' : mem) g1, OKV M0c ->
  (forall a, L5C.kept L (CH2V.LBr LBo eghost PB6W.gB g1) sp (CH.hd_scr G.HDECL) W a -> M' (Z_to_bv 64 a) = M0c (Z_to_bv 64 a)) ->
  forall a, L5C.kept L LBo sp SCRC W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros M0c M' g1 HOK HK a Ha. pose proof (kept_scr LBo a Ha) as Ha'.
  rewrite (HK a (CH2V.kept_LBr L LBo eghost PB6W.gB g1 sp _ W a Ha')). exact (proj1 HOK a Ha').
Qed.
Lemma mod_eq0 : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> 0 <= (a mod 2 ^ 64 - b mod 2 ^ 64) mod 2 ^ 64 <= 0 -> a = b.
Proof.
  intros a b Ha Hb H. rewrite (Z.mod_small a), (Z.mod_small b) in H by lia.
  assert (H0 : (a - b) mod 2 ^ 64 = 0) by lia.
  apply Z.mod_divide in H0; [|lia]. destruct H0 as (q & Hq). lia.
Qed.
Lemma mod_le_nonneg : forall a hi, - 2 ^ 62 <= a < 2 ^ 62 -> hi < 2 ^ 63 -> 0 <= a mod 2 ^ 64 <= hi -> 0 <= a.
Proof.
  intros a hi Ha Hh H. destruct (Z_lt_le_dec a 0) as [Hn|Hp]; [|exact Hp]. exfalso.
  assert (Hm : a mod 2 ^ 64 = a + 2 ^ 64) by (rewrite <- (Z.mod_add a 1 (2 ^ 64)) by lia; apply Z.mod_small; lia).
  lia.
Qed.
Lemma ls_ok_below : forall c E' (M1 M' : mem) g1, (PNC.foot_pre_chk c || PNC.foot_end_chk c)%bool = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M1 a) -> g1 <> PML.LS0 -> PML.ls_ok g1 M1 -> PML.ls_ok g1 M'.
Proof.
  intros c E' M1 M' g1 Hf Hag HF Hg HL.
  pose proof (T_below_frame c E' M1 M' Hf Hag HF) as HB.
  pose proof T_SPF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7). pose proof T_STKX as (X1 & X2 & X3 & X4).
  apply (PB2.ls_ok_fr [(sp - 11248, 2 ^ 64 - (sp - 11248))] M1 M'); [| exact Hg | | exact HL].
  - intros x Hx. specialize (Hx _ (or_introl eq_refl)). unfold L5.in_rng in Hx. cbn [fst snd] in Hx.
    pose proof (bv_unsigned_in_range _ x) as Hxr.
    rewrite <- (Z_to_bv_bv_unsigned _ x). apply HB. unfold bv_modulus in Hxr. lia.
  - unfold PB2.out. split; [lia|]. split; [lia|]. intros j Hj r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
Qed.
Definition XPREM (i : nat) (c : CC.cutpoint) (ps1 : SR.post_spec) (cells' : list kentry) (ml code : Z) (g' : PML.ls_state) (pe ce : expr) (pv : PB2.pvals) (g1 : eghost) (M0c : mem) : Prop :=
  forall E1 E' R' (M1 M' : mem) model1 buf, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> SIM g1 i E1 M1 -> g1 = eg -> HAMBV g1 M0c i E1 M' model1 -> env_agree GT.NF E0 E' ->
      know_ok RSEGS E' M' cells' -> L5.defined M' E 16 ->
      PML.parser_at M' P (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) buf (Some (p, e))) ->
      Z.of_nat (length buf) = uv E' (PB2.pv_size pv) ->
      PML.ec_at M' E code /\ PML.ls_ok g' M' /\ p <= uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) <= e /\
      exists txt, PML.parser_at M' P (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) txt (Some (p, e))) /\
                  Z.of_nat (length txt) + (e - uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) <= B /\
                  (ml = 1 -> PML.num_prefix (uv E' (PB2.pv_nst pv)) txt /\ uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) = e) /\
                  PNKW.w3n cw winb M' P ps (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) txt (Some (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)), e))) eg g1 code.
Lemma prem_setec : forall i c k ps1 pe ce pv code g1 M0c, is_leaf i c k ps1 (CC.TOther PNC.RETPC) -> PNC.kind_of i = PNC.KSetEc ->
  PNC.exit_setec_chk i c ps1 = true -> PNCW.wl_chk i c k ps1 (CC.TOther PNC.RETPC) = true ->
  PNC.view_chk 0 (PNC.cells16 (SR.ps_cells ps1)) (nth i G.BLS []) = Some (pe, ce, pv) ->
  CAX.cell_at (PNC.cells16 (SR.ps_cells ps1)) PNC.Eb 0 4 = Some (ELit code) -> OKV M0c ->
  XPREM i c ps1 (PNC.cells16 (SR.ps_cells ps1)) 0 code PML.LS2 pe ce pv g1 M0c.
Proof.
  intros i c k ps1 pe ce pv code g1 M0c IL Hk Hchk Hwl HV Hcell HOK.
  unfold XPREM.
  intros E1 E' R' M1 M' model1 buf Hag HLF HXI HSIM Hg1 HAMB Hag0 HKC HdE HPAb Hlenb.
  subst g1.
  unfold PNC.exit_setec_chk in Hchk. cbv zeta in Hchk. rewrite HV, Hcell in Hchk. cbv beta iota in Hchk.
  apply andb_prop in Hchk as [Hchk CX]. apply andb_prop in Hchk as [Hchk CB]. apply andb_prop in Hchk as [Hchk CF]. apply andb_prop in Hchk as [CB0 CRG].
  apply andb_prop in CX as [CX P3]. apply andb_prop in CX as [CX P2]. apply andb_prop in CX as [CX P1]. apply andb_prop in CX as [CX SZ].
  apply andb_prop in CX as [CX H8]. apply andb_prop in CX as [L1 L31]. apply Z.leb_le in L1, L31.
  assert (HWK : PNCW.WK i = PNCW.WSetEc) by (rewrite (PNCW.WK_ret i ltac:(rewrite Hk; discriminate)), Hk; reflexivity).
  destruct (PNCW.wl_exit_setec i _ _ _ (PNCW.wl_exit i c k ps1 Hwl) HWK) as (HEC0 & z & Hz & HzE).
  rewrite Hcell in Hz. injection Hz as Hz. subst z.
  unfold ParseNumberW_u5.SIM in HSIM. rewrite HWK in HSIM. destruct HSIM as (c1 & w1 & HERR). rewrite <- HzE in HERR.
  pose proof (T_FRZ E' Hag0) as (FPb & FSEG & FWEND & FBX & _ & _ & _ & _ & _ & _ & FEb & FVb & _ & _ & _ & FSZ0 & _).
  set (a0e := nth 10 (CA.ps_reglist ps1) (ELit 0)) in *.
  pose proof (fun H => T_cur_range E' M' _ a0e _ HKC Hag0 H P1 P2) as CR. specialize (CR ltac:(lia)). destruct CR as (CR1 & CR2).
  pose proof HBB as HB0. unfold PML.buf_bound, PML.winlen, PML.buf_need in HB0. rewrite Hwin in HB0.
  assert (Hif : (PML.ST_NUMBER =? PML.ST_STRING) = false) by (vm_compute; reflexivity).
  rewrite Hmore, Hst, Hif in HB0. cbn [andb] in HB0.
  split.
  { unfold PML.ec_at.
    pose proof (PB2.cell_at_ok E' M' _ PNC.Eb 0 4 (ELit code) HKC Hcell) as K32.
    assert (HEs : estart E' (SA PNC.Eb 0) = E) by (unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' PNC.Eb)) with (PB.uv E' PNC.Eb); lia).
    pose proof (PB2.kword32_elim E' M' _ _ E K32 HEs) as U32.
    assert (UC : PB.uv E' (ELit code) = code) by (unfold PB.uv; cbn [edenot]; apply u64_of_Z; lia).
    rewrite UC in U32.
    split; [exact U32|]. split; [exact HdE|]. right. split; [lia|].
    pose proof (PB.has_ok E' M' _ _ HKC H8) as K64.
    assert (HE8 : estart E' (SA PNC.Eb 8) = E + 8) by (unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' PNC.Eb)) with (PB.uv E' PNC.Eb); lia).
    exact (PB2.kword64_elim E' M' _ _ (E + 8) K64 HE8). }
  split.
  { unfold ParseNumberW_u5.XI in HXI. rewrite Hk in HXI.
    apply (ls_ok_below c E' M1 M' PML.LS2 ltac:(rewrite CF; reflexivity) Hag0 (CC.lf_frame _ _ _ _ _ _ _ HLF)); [discriminate | exact HXI]. }
  split; [exact CR1|].
  exists buf. split; [exact HPAb|].
  split.
  { rewrite Hlenb, (expr_eqb_eq _ _ SZ), FSZ0.
    pose proof (PB.prove_ok E' M' _ _ HKC P3) as K3. cbn [kentry_ok] in K3.
    change (bv_unsigned (edenot E' (APC.esub PNC.BX (APC.eadd PNC.SIZE0 (APC.esub PNC.WEND a0e)))))
      with (PB.uv E' (APC.esub PNC.BX (APC.eadd PNC.SIZE0 (APC.esub PNC.WEND a0e)))) in K3.
    rewrite PB.uv_esub, PB.uv_eadd, PB.uv_esub, FBX, FSZ0, FWEND in K3.
    rewrite (Z.mod_small (e - uv E' a0e)) in K3 by lia.
    rewrite (Z.mod_small (_ + (e - uv E' a0e))) in K3 by lia.
    assert (K4 : 0 <= B - (Z.of_nat (length (PML.ps_buf ps)) + (e - uv E' a0e))).
    { eapply mod_le_nonneg; cycle 2; [exact K3 | lia | lia]. }
    lia. }
  split; [intros H01; discriminate H01|].
  exact (PNKW.w3_err cw c1 w1 winb M' P ps _ eg code HERR ltac:(lia)).
Qed.
Lemma prem_pre : forall i c k ps1 pe ce pv g1 M0c, is_leaf i c k ps1 (CC.TOther PNC.RETPC) -> PNC.kind_of i = PNC.KPre ->
  PNC.exit_pre_chk i c ps1 = true -> PNCW.wl_chk i c k ps1 (CC.TOther PNC.RETPC) = true ->
  PNC.view_chk 1 (SR.ps_cells ps1) (nth i G.BLS []) = Some (pe, ce, pv) -> OKV M0c ->
  XPREM i c ps1 (SR.ps_cells ps1) 1 0 g pe ce pv g1 M0c.
Proof.
  intros i c k ps1 pe ce pv g1 M0c IL Hki Hchk HW HV HOK.
  unfold XPREM.
  intros E1 E' R' M1 M' model1 buf Hag HLF HXI HSIM Hg1 HAMB HAG HKC HdE HPAb Hlenb.
  subst g1.
  pose proof HXI as HXI0.
  pose proof (PNCW.wl_exit _ _ _ _ HW) as HX.
  assert (HWK : PNCW.WK i = PNCW.WGo).
  { destruct (PNCW.wl_exit_other _ _ _ _ HX) as (W1 & W2 & W3 & W4).
    destruct (PNCW.WK_pre i Hki) as [Q|[Q|[Q|[Q|Q]]]]; [exfalso; exact (W1 Q) | exact Q | exfalso; exact (W2 Q) | exfalso; exact (W3 Q) | exfalso; exact (W4 Q)]. }
  destruct (PNCW.wl_exit_go _ _ _ _ HX HWK) as (Hnx & HJ0 & HA0 & pe2 & ce2 & pv2 & cn2 & HV2 & Hn2 & Hcn2).
  rewrite HV in HV2. injection HV2 as Q1 Q2 Q3. subst pe2 ce2 pv2.
  unfold PNC.exit_pre_chk in Hchk. cbv zeta in Hchk. rewrite HV in Hchk.
  destruct (PNC.cut_states i) as [Si|] eqn:HSi; cbv beta iota in Hchk; [|rewrite andb_false_r in Hchk; discriminate Hchk].
  rewrite Hn2 in Hchk. cbv beta iota in Hchk.
  apply andb_prop in Hchk as [Hchk A]. apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk _].
  apply andb_prop in Hchk as [Hchk Hfoot]. apply andb_prop in Hchk as [_ _].
  apply andb_prop in A as [A A10]. apply andb_prop in A as [A A9]. apply andb_prop in A as [A A8]. apply andb_prop in A as [A A7].
  apply andb_prop in A as [A A6]. apply andb_prop in A as [A A5]. apply andb_prop in A as [A A4]. apply andb_prop in A as [A A3].
  apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1, A2. apply expr_eqb_eq in A4, A5.
  pose proof (T_FRZ E' HAG) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20).
  pose proof T_NUM as (ch & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 & N26 & N27 & N28).
  assert (Hpe : 0 <= p /\ e < 2 ^ 64).
  { destruct N6 as (B1 & _ & _ & _ & B5). pose proof T_STKX as (X1 & X2 & X3 & X4). lia. }
  destruct (T_cur_range E' M' (SR.ps_cells ps1) (nth 10 (CA.ps_reglist ps1) (ELit 0)) 0 HKC HAG ltac:(lia) A8 A9) as (Hc0 & Hc1).
  pose proof (ParseNumberW_u5.rng_is_sound E' M' _ _ _ HKC HA0) as HA0'. rewrite PB.uv_esub, F2 in HA0'.
  assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
  pose proof (ParseNumberW_u5.mod64_zero _ _ (PB.uv_range E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) Hp64 HA0') as Ha0p.
  pose proof (ParseNumberW_u5.rng_is_sound E' M' _ _ _ HKC HJ0) as HJ0'. rewrite PB.uv_esub, F15 in HJ0'.
  assert (Hw64 : 0 <= e - p < 2 ^ 64) by lia.
  pose proof (ParseNumberW_u5.mod64_zero _ _ Hw64 (PB.uv_range E' PNC.JV) HJ0') as HJV.
  pose proof (T_jv_agree _ E1 E' Hag Hnx) as HJV1.
  unfold ParseNumberW_u5.XI in HXI. rewrite Hki in HXI. cbv beta iota zeta in HXI. destruct HXI as (_ & HBY & HAU).
  unfold ParseNumberW_u5.auto_ok in HAU. cbv beta zeta in HAU.
  destruct (Nat.eqb_spec i 0) as [Hi0|Hi0]; [rewrite Hi0 in HWK; vm_compute in HWK; discriminate HWK|].
  rewrite ?(proj2 (Nat.eqb_neq i 0) Hi0) in HAU. cbv iota in HAU. rewrite HSi in HAU. cbv beta iota zeta in HAU.
  destruct HAU as (_ & kq & Hk & HkS).
  replace (e - p - uv E1 PNC.JV) with 0 in Hk by lia.
  unfold ParseNumberW_u5.text in Hk. cbn [Z.to_nat firstn] in Hk. rewrite app_nil_r in Hk.
  unfold ParseNumberW_u5.SIM in HSIM. rewrite HWK in HSIM. cbv beta iota zeta in HSIM. unfold ParseNumberW_u5.SGO in HSIM.
  destruct HSIM as (n & HNOF & Hnle & HPN). unfold ParseNumberW_u5.NOFJ in HNOF.
  assert (Hnl : n = length winb) by (pose proof (proj2 Hwinb); lia).
  subst n. unfold ParseNumberW_u5.CI in HPN. rewrite PNKW.pn_all in HPN.
  destruct (PNKW.fixz_fields (PNKW.CI cw winb (PNCW.NST i))) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  destruct (PNKW.CI_fields cw winb (PNCW.NST i)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & _).
  pose proof HRM as (HRC & _ & HRN). destruct (HRN Hst) as (_ & Hdl).
  rewrite Hn2, (PB2.uv_lit E' cn2 ltac:(lia)) in HPAb |- *.
  split; [exact (T_ecell0 E' M' (SR.ps_cells ps1) HKC HAG A3 HdE)|].
  split; [exact (T_ls_at_leaf i c k ps1 PNC.RETPC IL (or_introl Hki) Hfoot eg M0c HOK E1 E' R' M1 M' model1 Hag HLF HAMB HXI0)|].
  split; [lia|].
  exists (PML.ps_buf ps).
  split.
  { eapply T_pa_retext; [exact HPAb| |].
    - rewrite A4, F17. exact (T_buf_step c E' M1 M' ltac:(apply orb_true_intro; left; exact Hfoot) HAG (CC.lf_frame _ _ _ _ _ _ _ HLF) HBY).
    - apply Nat2Z.inj. rewrite Hlenb, A5, F16. reflexivity. }
  split; [lia|].
  split.
  { intros _. split; [|lia]. unfold PML.num_prefix. exists kq. split; [exact Hk|].
    rewrite forallb_forall in A6. specialize (A6 _ HkS). unfold PNC.nst_ok in A6.
    apply orb_prop in A6 as [Q|Q]; [apply Z.eqb_eq in Q; left; lia | apply andb_prop in Q as [Q4 Q5]; apply Z.eqb_eq in Q4; apply Z.eqb_eq in Q5; right; split; lia]. }
  replace (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) with e by lia.
  apply (PNKW.w3_ret cw _ winb M M' P ps _ eg e HRM HPN).
  - exact (eq_trans Z1 Y1).
  - exact (eq_trans Z2 Y2).
  - exact (eq_trans Z3 Y3).
  - exact (eq_trans Z4 Y4).
  - exact (eq_trans Z5 Y5).
  - exact (eq_sym Hst).
  - exact (eq_sym Hmore).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hst.
  - rewrite Z6, Y6. cbn [PML.ps_nst]. exact (eq_sym Hcn2).
  - rewrite Z7, Y7. cbn [PML.ps_buf]. rewrite Hdl. pose proof (proj2 Hwinb). lia.
  - unfold PML.winlen. rewrite Hwin. pose proof (proj2 Hwinb). lia.
  - reflexivity.
Qed.
Lemma prem_app : forall i c k ps1 pe ce pv g1 M0c, is_leaf i c k ps1 (CC.TOther PNC.RETPC) -> PNC.kind_of i = PNC.KApp ->
  PNC.exit_app_chk i c ps1 = true -> PNCW.wl_chk i c k ps1 (CC.TOther PNC.RETPC) = true ->
  PNC.view_chk 1 (SR.ps_cells ps1) (nth i G.BLS []) = Some (pe, ce, pv) -> OKV M0c ->
  XPREM i c ps1 (SR.ps_cells ps1) 1 0 g pe ce pv g1 M0c.
Proof.
  intros i c k ps1 pe ce pv g1 M0c IL Hki Hchk HW HV HOK.
  unfold XPREM.
  intros E1 E' R' M1 M' model1 buf Hag HLF HXI HSIM Hg1 HAMB HAG HKC HdE HPAb Hlenb.
  subst g1.
  pose proof HXI as HXI0.
  pose proof IL as (tags & Hc & _).
  pose proof (T_nth_cut i c Hc) as Hcut.
  unfold PNC.exit_app_chk in Hchk. cbv zeta in Hchk. rewrite HV in Hchk.
  destruct (PNC.nstc_of c) as [e0|] eqn:Hnst; [destruct e0 as [cn| | | | | | |]|]; cbv beta iota in Hchk;
    try (rewrite andb_false_r in Hchk; discriminate Hchk).
  apply andb_prop in Hchk as [Hchk A]. apply andb_prop in Hchk as [Hchk Hbvl].
  apply andb_prop in Hchk as [Hchk Hfoot]. apply andb_prop in Hchk as [_ _].
  apply andb_prop in A as [A A10]. apply andb_prop in A as [A A9]. apply andb_prop in A as [A A8]. apply andb_prop in A as [A A7].
  apply andb_prop in A as [A A6]. apply andb_prop in A as [A A5]. apply andb_prop in A as [A A4]. apply andb_prop in A as [A A3].
  apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1, A2. apply expr_eqb_eq in A4, A5.
  pose proof (T_FRZ E' HAG) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20).
  pose proof T_NUM as (ch & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 & N26 & N27 & N28).
  assert (Hpe : 0 <= p /\ e < 2 ^ 64).
  { destruct N6 as (B1 & _ & _ & _ & B5). pose proof T_STKX as (X1 & X2 & X3 & X4). lia. }
  destruct (T_cur_range E' M' (SR.ps_cells ps1) (nth 10 (CA.ps_reglist ps1) (ELit 0)) 0 HKC HAG ltac:(lia) A7 A8) as (Hc0 & Hc1).
  unfold ParseNumberW_u5.XI in HXI. rewrite Hki in HXI. cbv beta iota zeta in HXI.
  destruct HXI as (_ & n & kq & cap' & p' & Hn & Hsz & Hden & Hstr & Hnl & Happ).
  rewrite Hcut in Hsz.
  unfold ParseNumberW_u5.appk in Happ. rewrite Hcut, Hnst in Happ. cbv beta iota in Happ.
  unfold ParseNumberW_u5.SIM in HSIM. rewrite (PNCW.WK_ret i ltac:(rewrite Hki; discriminate)), Hki in HSIM. cbv beta iota zeta in HSIM.
  unfold PNCW.NLIT in HSIM. change (PNCW.cutn i) with (ParseNumberW_u5.cutn i) in HSIM. rewrite Hcut, Hnst in HSIM. cbv beta iota in HSIM.
  unfold ParseNumberW_u5.SAPPX in HSIM.
  destruct HSIM as (c1 & HPN & Hc1n & Hc1d & Hc1st & Hc1m & Hc1dn & Hc1l & Hc1s).
  pose proof (PB.uv_agree _ E1 E' _ Hag A6) as Hsz'.
  pose proof (PB.prove_ok _ _ _ _ HKC A9) as HR9. cbn [kentry_ok] in HR9.
  fold (uv E' (APC.esub (APC.esub (nth 10 (CA.ps_reglist ps1) (ELit 0)) PNC.SEG) (APC.esub (PNC.sz_of c) PNC.SIZE0))) in HR9.
  rewrite !PB.uv_esub, F2, F16, Hsz', Hsz in HR9.
  rewrite (Z.mod_small (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) - p)) in HR9 by lia.
  replace (size0 + n - size0) with n in HR9 by lia. rewrite (Z.mod_small n) in HR9 by lia.
  assert (HR : (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) - p - n) mod 2 ^ 64 = 0) by lia.
  pose proof (ParseNumberW_u5.mod64_zero (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) - p) n ltac:(lia) ltac:(lia) HR) as Hn'.
  assert (Hnwl : n = e - p) by lia.
  pose proof (T_text_len n Hn) as Htl.
  pose proof (ParseNumberW_u5.pa_def _ _ _ HPAb) as HdP.
  destruct (T_view_sound 1 (SR.ps_cells ps1) (nth i G.BLS []) pe ce pv E' M' HV (or_intror eq_refl) HKC HAG HdP) as (HBLi & _).
  pose proof Hbvl as Hbv. rewrite HBLi in Hbv. cbn [CH2.blocks_vars_lt forallb fst snd] in Hbv.
  apply andb_prop in Hbv as [B1 _]. apply andb_prop in B1 as [B1 B2].
  rewrite HBLi, !PB.den_cons in Hden. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden.
  injection Hden as Hp1 Hcap1 _ _.
  pose proof HAMB as (_ & _ & _ & (cr1 & HH1 & _) & _).
  destruct (hio_wf _ _ _ HIok _ _ _ _ HH1) as (HB & _).
  assert (Hin : In (p', cap') (CH2.cur (LBr eg) G.BLS i E1)).
  { unfold CH2.cur. apply in_or_app. left. rewrite HBLi, !PB.den_cons. left. rewrite Hp1, Hcap1. reflexivity. }
  destruct (proj1 (HB _ Hin)) as (Z1 & _ & _ & Z4 & Z5). cbn [fst snd] in Z1, Z4, Z5.
  destruct Hstr as ((_ & _ & _ & _ & HBY & _) & _ & Hlt).
  pose proof (T_blk_frame c E' M1 M' p' cap' (text n) ltac:(apply orb_true_intro; left; exact Hfoot) HAG (CC.lf_frame _ _ _ _ _ _ _ HLF)
                ltac:(lia) Z5 ltac:(lia) HBY) as HBY'.
  pose proof HRM as (HRC & _ & HRN). destruct (HRN Hst) as (_ & Hdl).
  rewrite A4, (PB2.uv_lit E' cn ltac:(lia)) in HPAb |- *.
  split; [exact (T_ecell0 E' M' (SR.ps_cells ps1) HKC HAG A3 HdE)|].
  split; [exact (T_ls_at_leaf i c k ps1 PNC.RETPC IL (or_intror Hki) Hfoot eg M0c HOK E1 E' R' M1 M' model1 Hag HLF HAMB HXI0)|].
  split; [lia|].
  exists (text n).
  split.
  { eapply T_pa_retext; [exact HPAb| |].
    - rewrite (PB.uv_agree _ E1 E' pe Hag B1), Hp1. exact HBY'.
    - apply Nat2Z.inj. rewrite Hlenb, A5, Hsz', Hsz. exact Htl. }
  split; [lia|].
  split.
  { intros _. split; [|lia]. unfold PML.num_prefix. exists kq. split; [exact Hnl|].
    unfold PNC.nst_ok in Happ.
    apply orb_prop in Happ as [Q|Q]; [apply Z.eqb_eq in Q; left; lia | apply andb_prop in Q as [Q4 Q5]; apply Z.eqb_eq in Q4; apply Z.eqb_eq in Q5; right; split; lia]. }
  replace (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) with e by lia.
  apply (PNKW.w3_ret cw c1 winb M M' P ps _ eg e HRM HPN).
  - exact Hc1st.
  - exact Hc1m.
  - exact Hc1dn.
  - exact Hc1l.
  - exact Hc1s.
  - exact (eq_sym Hst).
  - exact (eq_sym Hmore).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hst.
  - cbn [PML.ps_nst]. exact Hc1n.
  - cbn [PML.ps_buf]. rewrite Hc1d, Hdl. lia.
  - unfold PML.winlen. rewrite Hwin. pose proof (proj2 Hwinb). lia.
  - reflexivity.
Qed.
Lemma leaf_end : forall pc f, pc = PNC.ENDI \/ pc = PNC.ENDF -> f = PMW.FEndInt \/ f = PMW.FEndFrac -> PMW.end_number_specwU L HI SSCR WDX PMR.the_rm f pc ->
  forall i c k ps1 j cj ci, is_leaf i c k ps1 (CC.TOther pc) -> CH2.ret_of G.RETS i k = Some j -> nth_error G.CPS j = Some cj ->
  SR.ps_pc ps1 = pc -> PNC.kind_of i = PNC.KApp -> PNC.kind_of j = PNC.KEnd -> PNC.foot_pre_chk c = true ->
  PBX.ptrans_chkx GT.NF G.HDECL PNC.Eb 0 PNC.Pb 0 PNC.ENDNUM_SCR PNC.Vb PML.LIT_LO 12 c ps1 cj (nth i G.BLS []) (nth j G.BLS []) = Some ci -> PNC.end_leaf_chk i c ps1 cj = true ->
  forall g1 M0c, OKV M0c -> CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv G.CPS K PML.fp_ok g1 M0c i c ps1.
Proof.
  intros pc f Hpc Hf SPEC i c k ps1 j cj ci IL Hret Hcj Hpcl Hki Hkj Hfoot Hchk Hend g1 M0c HOK.
  unfold PMW.end_number_specwU, PMW.ptrans_stalexwU in SPEC.
  pose proof (ParseBridges6WU.PB6WU.gbxw_EU L HI PMR.the_rm f _ _ _ _ _ _ pc _ _ _ (SPEC (PML.ps_win ps))) as CE.
  assert (PAOUT_CAP : forall (th : ParseBridges6W_u5.PB6W.THW PMR.the_rm) pst (M2 : mem) P2 ps2,
            (fun ps0 M' P' ps' => PML.parser_at M' P' (PML.ps_set_win ps' (PML.ps_win ps)) /\ PML.ps_win ps' = PML.ps_win ps0) pst M2 P2 ps2 ->
            PML.ps_bcap ps2 mod 2 = 0).
  { intros th pst M2 P2 ps2 [HPA2 _]. exact (T_pa_cap M2 P2 ps2 _ HPA2). }
  refine (ParseBridges6WU.PB6WU.ptrans_leaf_okxwU L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS CredV XIv
    T_STKF T_SCRP T_NF32 T_U2 T_TP0 T_W_OK T_CRS_OK T_WRS_OK T_IMG_OK
    G.CPS G.TAGS G.RETS K HKnil T_DEF0 PNC.Eb 0 ltac:(vm_compute; reflexivity) E T_EADDR g HG
    PNC.Pb 0 ltac:(vm_compute; reflexivity) P T_PADDR V S2 OBJS T_WPAR_in T_W_ENC PNC.Vb ltac:(vm_compute; reflexivity) T_VADDR T_S2LT T_S2ADDR
    ltac:(vm_compute; reflexivity) pc _ _ _ _ _ _ _ _ _ _ CE (fun th => PAOUT_CAP th) B kx bx Hkx Hbx
    PML.LIT_LO 12%nat i c k ps1 j cj ci g1 M0c eq_refl HOK IL Hret Hcj Hpcl Hchk _).
  intros E1 E' R' M1 M' model1 cr1 Hag0 Hsr Hnx Hag HLF HR HAV HXV HH1 HC.
  pose proof HXV as (HXI & HGX & HXK & HSIM).
  assert (Hg : g1 = eg) by (unfold ParseNumberW_u5.GX in HGX; rewrite Hki in HGX; exact HGX).
  subst g1.
  unfold PNC.end_leaf_chk in Hend. cbv zeta in Hend.
  apply andb_prop in Hend as [Hend EV]. apply andb_prop in Hend as [Hend NXJ]. apply andb_prop in Hend as [Hend NXC].
  apply andb_prop in Hend as [Hend RE]. apply andb_prop in Hend as [Hend RV]. apply andb_prop in Hend as [BV RP].
  destruct (PNC.view_chk 1 (SR.ps_cells ps1) (nth i G.BLS [])) as [[[pe ce] pv]|] eqn:HV; [|discriminate EV].
  destruct (PNC.nstc_of c) as [ns|] eqn:Hns; [|discriminate EV]. destruct ns; try discriminate EV.
  pose proof HXI as HXI0.
  unfold ParseNumberW_u5.XI in HXI. rewrite Hki in HXI.
  destruct HXI as (HSTAT & nx & kx0 & capx & px & (Hn0 & Hnw) & Hsz & Hden1 & Hstr & Hnl & Happ).
  unfold ParseNumberW_u5.SIM in HSIM.
  pose proof T_leaf_know c ps1 E' R' M1 M' HLF as HKC.
  pose proof (CH2.leaves_all_sound G.CPS G.TAGS PNCW.wl_chk PNCW.wl_ok i c k ps1 (CC.TOther pc) IL) as HWL.
  destruct (PNCW.wl_end i c k ps1 pc j Hpc HWL Hret) as (HWKi & HWKj & HNLi & _).
  rewrite HWKi, HNLi in HSIM. destruct HSIM as (kq & nq & HNOFJ & Hnlt & HPN).
  pose proof T_STKX as (X1 & X2 & X3 & X4).
  pose proof (@ParseNumberW_u5.amb_def SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Hwin Hmore Hst HPA HWF HWIN HBB HPC pos0 winb Hwinb
                eg M0c HOK i E1 M' model1) as HAD.
  assert (HdP : L5.defined M' P 272).
  { pose proof T_OP as (Y1 & Y2 & _). apply (HAD P 272 HAV (ParseNumberW_u5.pa_def _ _ _ HPA)). left. lia. }
  assert (HdE : L5.defined M' E 16).
  { pose proof T_OE as (Y1 & Y2 & _). apply (HAD E 16 HAV (proj1 (proj2 HEC))). left. lia. }
  destruct (T_view_sound 1 (SR.ps_cells ps1) (nth i G.BLS []) pe ce pv E' M' HV (or_intror eq_refl) HKC Hag0 HdP)
    as (HBLi & Hnst & buf & HPAb & Hlenb & Hce & Hpe & Hdpe).
  pose proof HAV as (A1 & A2 & A3 & A4 & A5 & A6).
  assert (Hci : ParseNumberW_u5.cutn i = c) by (apply T_nth_cut; destruct IL as (tgs & IL1 & _); exact IL1).
  assert (HFIN : PML.num_final (ParseNumberW_u5.text ps winb nx)).
  { unfold ParseNumberW_u5.appk in Happ. rewrite Hci, Hns in Happ.
    exists kx0. split; [exact Hnl|]. unfold PNC.final_ok in Happ.
    apply existsb_exists in Happ as (y & Hy & Hz). apply Zeq_bool_eq in Hz. subst y. exact Hy. }
  apply andb_prop in EV as [EV EVi]. apply andb_prop in EV as [EV EVh]. apply andb_prop in EV as [EV EVg]. apply andb_prop in EV as [EV EVf].
  apply andb_prop in EV as [EV EVe]. apply andb_prop in EV as [EV EVd]. apply andb_prop in EV as [EV EVc]. apply andb_prop in EV as [EVa EVb].
  pose proof Hden1 as Hden2. rewrite HBLi, !PB.den_cons in Hden2. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden2.
  injection Hden2 as Hpx Hcapx _ _.
  pose proof BV as Hbv0. rewrite HBLi in Hbv0. cbn [CH2.blocks_vars_lt forallb fst snd] in Hbv0.
  apply andb_prop in Hbv0 as [Bpc _]. apply andb_prop in Bpc as [B1 B2].
  rewrite <- (PB.uv_agree _ E1 E' pe Hag B1) in Hpx. rewrite <- (PB.uv_agree _ E1 E' ce Hag B2) in Hcapx.
  assert (HBR : block_range L px capx).
  { destruct (hio_wf _ _ _ HIok _ _ _ _ HH1) as (HB & _). apply (HB (px, capx)).
    unfold CH2.cur. rewrite Hden1. apply in_or_app. left. left. reflexivity. }
  pose proof Hstr as (HLS1 & Hc8 & Hclt). destruct HLS1 as (_ & _ & _ & _ & HBM1 & _).
  pose proof (T_text_len nx ltac:(lia)) as HTL.
  assert (HBT : L5.bytes_at RSEGS M' (uv E' pe) (ParseNumberW_u5.text ps winb nx)).
  { rewrite Hpx. destruct HBR as (R1 & _ & _ & R4 & R5).
    apply (T_blk_frame c E' M1 M' px capx _ ltac:(rewrite Hfoot; reflexivity) Hag0 (CC.lf_frame _ _ _ _ _ _ _ HLF)); [lia|exact R5|lia|exact HBM1]. }
  assert (HLT : length (ParseNumberW_u5.text ps winb nx) = length buf).
  { apply Nat2Z.inj. rewrite Hlenb, (expr_eqb_eq _ _ EVd), (PB.uv_agree _ E1 E' (sz_of c) Hag EVe), <- Hci, Hsz. lia. }
  assert (HK07 : 0 <= kx0 <= 7).
  { destruct HFIN as (k' & Hk' & Hin). rewrite Hnl in Hk'. injection Hk' as <-. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; lia. }
  assert (HSTAT' : forall a, ParseNumberW_u5.statw a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { apply (T_stat_step c E' M1 M' ltac:(rewrite Hfoot; reflexivity) Hag0 (CC.lf_frame _ _ _ _ _ _ _ HLF)).
    exact (T_xi_stat i E1 M1 (or_intror Hki) HXI0). }
  set (JVv := uv E' PNC.JV).
  assert (HJV : JVv = uv E1 PNC.JV) by (apply (T_jv_agree _ E1 E' Hag); apply Nat.ltb_lt; exact NXC).
  pose proof HJV as HJV'. unfold JVv in HJV'.
  assert (J0 : 0 <= uv E' PNC.JV <= wlen) by (unfold ParseNumberW_u5.NOFJ in HNOFJ; pose proof (proj2 Hwinb); lia).
  assert (HNXQ : nx = Z.of_nat nq).
  { pose proof (T_FRZ E' Hag0) as (_ & FSEG & FWEND & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FSZ0 & _).
    pose proof (T_HCU E' Hag0 J0) as HCU'.
    pose proof (PB.prove_ok E' M' (SR.ps_cells ps1) _ HKC EVh) as KH. cbn [kentry_ok] in KH.
    change (bv_unsigned (edenot E' (APC.esub (APC.esub PNC.CURJ PNC.SEG) (APC.esub (sz_of c) PNC.SIZE0))))
      with (PB.uv E' (APC.esub (APC.esub PNC.CURJ PNC.SEG) (APC.esub (sz_of c) PNC.SIZE0))) in KH.
    rewrite !PB.uv_esub in KH.
    unfold ParseNumberW_u5.NOFJ in HNOFJ. pose proof (proj2 Hwinb) as HL.
    rewrite HCU', FSEG, FSZ0, (PB.uv_agree _ E1 E' (sz_of c) Hag EVe), <- Hci, Hsz in KH.
    assert (HWS : e - p <= 16384).
    { pose proof HWIN as HW. unfold PML.win_ok in HW. rewrite Hwin in HW. destruct HW as (ch & _ & Hc1 & Hc2 & _). lia. }
    apply mod_eq0 in KH; [lia | lia | lia]. }
  assert (HPQ : e - JVv = p + Z.of_nat nq) by (unfold ParseNumberW_u5.NOFJ in HNOFJ; pose proof (proj2 Hwinb); lia).
  set (pst := PML.PS 17 (PML.ps_sst ps) (uv E' (PB2.pv_nst pv)) true (PML.ps_done ps) (PML.ps_level ps) (PML.ps_stack ps)
                (PML.ps_sb ps) (PML.ps_scap ps) (uv E' ce) (uv E' pe) (ParseNumberW_u5.text ps winb nx) (Some (e - JVv, e))).
  exists (skipn nq winb, [], ParseNumberW_u5.CI winb cw nq kq), pst.
  split.
  { pose proof (T_FRZ E' Hag0) as (_ & _ & _ & _ & F5 & _ & F7 & _).
    rewrite HBLi, !PB.den_cons. change (CH2.den E' []) with (@nil (Z * Z)).
    unfold PML.ps_blocks, pst. cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap].
    rewrite F5, F7. reflexivity. }
  split.
  { unfold ParseBridges6WU.PB6WU.ptrans_prexU.
    split.
    { unfold PB6W.argsXW, PMW.ax. cbv beta.
      split; [split; [exact (end_args i c k ps1 pc E' R' IL Hpc HR Hag0 M' pst)|split; [reflexivity|split; [reflexivity|exact HFIN]]]|].
      split.
      { unfold PMW.win_bytes, pst. cbn [PML.ps_win].
        pose proof (win_bytes_M' M' (kept_M' M0c M' eg HOK A5)) as HWB.
        unfold ParseNumberW_u5.NOFJ in HNOFJ. pose proof (proj2 Hwinb) as HL.
        replace (e - JVv) with (p + Z.of_nat nq) by lia.
        split; [exact (PB3.bytes_at_skipn M' p winb nq ltac:(lia) HWB)|].
        split; [rewrite length_skipn; lia|].
        apply Forall_forall. intros x Hx. assert (Hx' : In x winb) by (rewrite <- (firstn_skipn nq winb); apply in_or_app; right; exact Hx).
        pose proof (proj1 (Forall_forall _ _) Hwinr x Hx') as Hx2. cbn beta in Hx2. lia. }
      unfold ParseNumberW_u5.CI. cbn [PMW.rm_stale PMR.the_rm]. unfold PMR.rm_stale.
      destruct (PNKW.CI_fields cw (firstn nq winb) kq) as (C1 & C2 & C3 & C4 & C5 & _).
      destruct HRM as ((R1 & R2 & R3 & R4 & R5) & _ & _).
      unfold PMR.rm_core, pst. cbn [PML.ps_st PML.ps_more PML.ps_done PML.ps_level PML.ps_stack].
      rewrite C1, C2, C3, C4, C5, R1, R2, R3, R4, R5, Hst, Hmore. repeat split; reflexivity. }
    split.
    { rewrite Hwin. unfold PML.ps_set_win, pst. eapply T_pa_retext; [exact HPAb | exact HBT | exact HLT]. }
    split.
    { unfold PML.wf_ps_stale, pst. cbn [PML.ps_nst]. split; [exact Hnst|].
      exists kx0. unfold PML.ps_set_nst. apply T_wf_upd; [exact HK07|].
      intros _. exists kx0. split; [exact Hnl | left; reflexivity]. }
    split.
    { unfold PML.win_ok, pst. cbn [PML.ps_win]. rewrite HPQ.
      pose proof T_NUM as (ch & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 & N26 & N27 & N28).
      pose proof (proj2 Hwinb) as HL.
      exists ch. split; [exact N1|]. split; [lia|]. split; [lia|].
      pose proof HH1 as HH2. unfold CH2.cur, CH2V.LBr in HH2.
      destruct (hio_wf _ _ _ HIok _ _ _ _ HH2) as (HB & _).
      destruct (HB _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl N1))))) as (_ & Hdch & _). cbn [fst snd] in Hdch.
      eapply (L5.defined_sub _ _ _ _ _ Hdch); lia. }
    split.
    { pose proof HBB as HB. unfold PML.buf_bound, PML.winlen, PML.buf_need in HB. rewrite Hwin in HB.
      assert (Hif : (PML.ST_NUMBER =? PML.ST_STRING) = false) by (vm_compute; reflexivity).
      rewrite Hmore, Hst, Hif in HB. cbn [andb] in HB.
      unfold PMS.buf_bound_stale, PML.winlen, pst. cbn [PML.ps_win PML.ps_buf].
      unfold ParseNumberW_u5.NOFJ in HNOFJ. pose proof (proj2 Hwinb) as HL.
      split; [|split]; lia. }
    split.
    { unfold PML.vis_at.
      pose proof (PB.has_ok E' M' (SR.ps_cells ps1) _ HKC EVb) as KV.
      assert (HVs : estart E' (SA PNC.Vb 0) = V).
      { unfold estart. cbn [a_base a_off]. change (bv_unsigned (edenot E' PNC.Vb)) with (PB.uv E' PNC.Vb).
        rewrite (PB.uv_agree GT.NF E0 E' PNC.Vb Hag0 ltac:(vm_compute; reflexivity)). pose proof T_VADDR as XV. lia. }
      exact (PB2.kword64_elim E' M' _ _ V KV HVs). }
    split; [exact (T_ecell0 E' M' (SR.ps_cells ps1) HKC Hag0 EVa HdE)|].
    split; [exact (T_ls_pre eg M0c HOK i E1 M' model1 HAV HSTAT')|].
    assert (HXK' : XIK.xinv V S2 M' eg).
    { exact (@ParseNumberW_u5.xinv_stretch SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb
               eg c E' M1 M' ltac:(apply orb_true_intro; left; exact Hfoot) Hag0 (CC.lf_frame _ _ _ _ _ _ _ HLF)
               (@ParseNumberW_u5.gblocks_amb SCFG_P L HI HIok LAY LBo sp r P V E S2 B kx (bx + PMES.benc L eg) ps R M model p e Hentry OBJS pos0 winb eg M0c i E1 M' model1 HAV)
               HXK). }
    split; [exact (proj1 HXK')|].
    split; [exact (proj2 HXK')|].
    split.
    { destruct HSYNC as (HD & HKI). split; [exact HD|].
      unfold PMX.key_inv, pst. cbn [PML.ps_st PML.ps_stack PML.ps_level PML.ps_more]. intros _ [Hks | (x & Hx1 & Hx2)].
      - exfalso. vm_compute in Hks. lia.
      - apply HKI; [exact Hmore|]. right. exists x. exact (conj Hx1 Hx2). }
    split.
    { assert (HdenP : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks pst).
      { rewrite Hden1. unfold PML.ps_blocks, pst. cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]. rewrite Hpx, Hcapx. reflexivity. }
      assert (Hscap : In (PML.ps_scap pst) [66; 132; 264; 528; 1056]) by exact (proj1 (proj2 (proj2 (proj2 HWF)))).
      exact (proj1 (cred_of_blocks eg i E1 cr1 pst HdenP Hscap) HC). }
    unfold ParseBridges6WU.PB6WU.roomW. cbv beta iota.
    unfold PMW.wroomrU in HROOM |- *. cbn [PMW.rm_step PMR.the_rm] in HROOM |- *.
    unfold PMW.inp_buf, pst. cbn [PML.ps_buf].
    assert (HDL : PMR.c_dlen (ParseNumberW_u5.CI winb cw nq kq) = Z.of_nat (length (ParseNumberW_u5.text ps winb nx))).
    { unfold ParseNumberW_u5.CI. destruct (PNKW.CI_fields cw (firstn nq winb) kq) as (_ & _ & _ & _ & _ & _ & D7 & _).
      rewrite D7. pose proof HRM as (_ & _ & HRN). destruct (HRN Hst) as (_ & HD). rewrite HD, HTL, HNXQ, length_firstn. lia. }
    destruct (PNKW.end_number_textw _ (ParseNumberW_u5.text ps winb nx) (skipn nq winb) HDL) as (_ & QE & QA & _).
    destruct Hf as [-> | ->]; cbn [PMR.rstep PMR.r_of0 PMR.r_of PMW.r_evs PMW.r_allow] in HROOM |- *;
      rewrite HPN in HROOM; cbn [PMR.r_of PMW.r_evs PMW.r_allow] in HROOM; rewrite <- QE, <- QA; exact HROOM. }
  intros R2 M2 cr2 ps2 code g' eg' E2 HPOST Hag2 Hcode Hx10 Hden2 HHP2.
  destruct HPOST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
  cbv beta in Q1, Q13, Q14.
  destruct Q1 as (Q1a & Q1b).
  assert (HJ2 : uv E2 PNC.JV = uv E' PNC.JV) by (apply (T_jv_agree _ E' E2 Hag2); rewrite Hnx; apply Nat.ltb_lt; exact NXJ).
  assert (Hscap2 : In (PML.ps_scap ps2) [66; 132; 264; 528; 1056]) by exact (proj1 (proj2 (proj2 (proj2 Q2)))).
  assert (HS11 : code = 0 -> PML.ps_level ps2 = PML.ps_level ps /\ PML.ps_more ps2 = true /\ In (PML.ps_st ps2) [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END]).
  { intros Hc0. destruct Q13 as [(_ & R2m & R2s & _ & R2l & _) | Hc19]; [|lia].
    unfold pst in R2s, R2l. cbn [PML.ps_level] in R2s, R2l. split; [exact R2l|]. split; [exact R2m|].
    rewrite R2s. destruct (PML.ps_level ps =? 0); [left; reflexivity | right; left; reflexivity]. }
  assert (HDL2 : PMR.c_dlen (ParseNumberW_u5.CI winb cw nq kq) = Z.of_nat (length (ParseNumberW_u5.text ps winb nx))).
  { unfold ParseNumberW_u5.CI. destruct (PNKW.CI_fields cw (firstn nq winb) kq) as (_ & _ & _ & _ & _ & _ & D7 & _).
    rewrite D7. pose proof HRM as (_ & _ & HRN). destruct (HRN Hst) as (_ & HD). rewrite HD, HTL, HNXQ, length_firstn. lia. }
  split.
  2: { exact (proj2 (cred_of_blocks eg' j E2 cr2 ps2 Hden2 Hscap2) Q12). }
  unfold ParseNumberW_u5.XIv.
  split.
  { unfold ParseNumberW_u5.XI. rewrite Hkj. exists ps2, code, g'.
      split; [exact Q1a|].
      split; [rewrite Q1b; unfold pst; cbn [PML.ps_win]; rewrite HJ2; reflexivity|].
      split; [unfold ParseNumberW_u5.NOFJ in HNOFJ; pose proof (proj2 Hwinb); rewrite HJ2; lia|].
      split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
      split; [exact Q7|]. split; [exact Q8|]. split; [exact HS11|]. exact Hden2. }
  split.
  { unfold ParseNumberW_u5.GX. rewrite Hkj. intros c0 Hc0 Hz.
    pose proof (T_ec_at_fun M2 _ _ Hc0 Q5) as Hcc. rewrite Hcc in Hz.
    destruct (Q11 Hz) as (HD & _). destruct (HS11 Hz) as (HL2 & _). rewrite HD, HL2. reflexivity. }
  split; [exact (conj Q9 Q10)|].
  unfold ParseNumberW_u5.SIM. rewrite HWKj. unfold ParseNumberW_u5.SEND.
  exists ps2, code, g', nq, kq.
  split.
  { split; [exact Q1a|].
      split; [rewrite Q1b; unfold pst; cbn [PML.ps_win]; rewrite HJ2; reflexivity|].
      split; [unfold ParseNumberW_u5.NOFJ in HNOFJ; pose proof (proj2 Hwinb); rewrite HJ2; lia|].
      split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
      split; [exact Q7|]. split; [exact Q8|]. split; [exact HS11|]. exact Hden2. }
  split; [unfold ParseNumberW_u5.NOFJ in *; rewrite HJ2; lia|].
  split; [exact Hnlt|].
  split; [exact HPN|].
  cbv zeta.
  unfold PB6W.expostW in Q14. cbv beta iota zeta in Q14. cbn [PMW.rm_step PMR.the_rm] in Q14.
  unfold PMW.inp_buf, pst in Q14. cbn [PML.ps_buf] in Q14.
  destruct (PNKW.end_number_textw _ (ParseNumberW_u5.text ps winb nx) (skipn nq winb) HDL2) as (QC & QE & QA & _ & QT & _).
  destruct Hf as [-> | ->]; cbn [PMR.rstep PMR.r_of0 PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.rm_match PMR.the_rm] in Q14;
    destruct Q14 as (Y1 & Y2 & Y3 & Y4);
    (split; [rewrite QC; exact Y1|]); (split; [rewrite QE; exact Y2|]); (split; [rewrite QA, QE; exact Y3|]);
    intros Hz; destruct (Y4 Hz) as (Y5 & _); destruct Y5 as (Y6 & _);
    destruct QT as (T1 & _ & _ & T4 & T5 & T6 & T7 & _); unfold PMR.rm_core in *; rewrite T1, T4, T5, T6, T7; exact Y6.
Qed.
Lemma exit_view : forall i c k ps1 cells' ml code g' pe ce pv,
  is_leaf i c k ps1 (CC.TOther PNC.RETPC) -> PB.exit_base_chk GT.NF PNC.RETPC c ps1 = true -> CH2.all_regs_chk ps1 = true ->
  (forall E' (M' : mem), know_ok RSEGS E' M' (SR.ps_cells ps1) -> env_agree GT.NF E0 E' -> know_ok RSEGS E' M' cells') ->
  PNC.view_chk ml cells' (nth i G.BLS []) = Some (pe, ce, pv) -> ml = 0 \/ ml = 1 ->
  (code = 0 <-> ml = 1) -> (g' = g \/ (g' = PML.LS2 /\ code <> 0)) ->
  forall g1 M0c, OKV M0c -> PNC.kind_of i <> PNC.KEnd -> PNC.foot_pre_chk c = true ->
  (forall E1 E' R' (M1 M' : mem) model1 buf, env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 -> SIM g1 i E1 M1 -> g1 = eg -> HAMBV g1 M0c i E1 M' model1 -> env_agree GT.NF E0 E' ->
      know_ok RSEGS E' M' cells' -> L5.defined M' E 16 ->
      PML.parser_at M' P (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) buf (Some (p, e))) ->
      Z.of_nat (length buf) = uv E' (PB2.pv_size pv) ->
      PML.ec_at M' E code /\ PML.ls_ok g' M' /\ p <= uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) <= e /\
      exists txt, PML.parser_at M' P (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) txt (Some (p, e))) /\
                  Z.of_nat (length txt) + (e - uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) <= B /\
                  (ml = 1 -> PML.num_prefix (uv E' (PB2.pv_nst pv)) txt /\ uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)) = e) /\
                  PNKW.w3n cw winb M' P ps (PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) txt (Some (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0)), e))) eg g1 code) ->
  CC.leaf_ok (hl_segs L) G.CPS (AMB3XV g1 M0c) K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 cells' ml code g' pe ce pv IL C1 C2 HCELLS HV Hml Hcode Hg' g1 M0c HOK Hk Hfoot PREM.
  intros fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH.
  destruct HA as [HAMB HXV].
  assert (Hg1 : g1 = eg).
  { destruct HXV as (_ & HGX & _). unfold ParseNumberW_u5.GX in HGX. destruct (PNC.kind_of i) eqn:Hki; try exact HGX. exfalso; exact (Hk eq_refl). }
  subst g1.
  pose proof HAMB as (Hmo1 & Hmbv & Hag0 & _).
  destruct (T_other_facts i c k ps1 PNC.RETPC IL) as (Hnx & Hbv).
  assert (SCGE : CH.hd_scr G.HDECL <= SCRC) by (rewrite ParseNumberW_u5.SCRV; vm_compute; discriminate).
  assert (STKC : hl_ceil L + SCRC <= sp).
  { pose proof T_SPF as (_ & _ & _ & _ & _ & _ & X). replace (2 ^ 23) with 8388608 in X by reflexivity. lia. }
  refine (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (LBr eg) sp G.HDECL W G.BLS (CredV eg) T_STKF T_SCRP T_NF32 T_U2 T_W_OK T_WRS_OK
            G.CPS G.TAGS K (XIv eg) (proj2 (proj2 HOK)) (fun _ => 0) (fun _ => 0) SCRC SCGE STKC (T_okV_defc M0c HOK) R T_EV0 r
            (proj1 Hentry) (proj1 (proj2 Hentry)) heap_ok3 PNC.RETPC i c k ps1 PNC.RETPC ParseNumberW_u5.ret_at IL C1
            fx' E1 R1 M1 model1 E' R' M' HAt HAMB Hag HLF _).
  intros HRP HHP HAMB' HAG.
  pose proof HAMB' as (_ & _ & _ & (cr' & HH' & HC') & _).
  pose proof (T_okV_hpres eg M0c M' HOK HHP) as HHPo.
  pose proof T_STKX as (X1 & X2 & X3 & X4).
  pose proof T_NUM as (ch & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 & N26 & N27 & N28).
  pose proof (HCELLS E' M' (T_leaf_know c ps1 E' R' M1 M' HLF) HAG) as HKC.
  pose proof (@ParseNumberW_u5.amb_def SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Hwin Hmore Hst HPA HWF HWIN HBB HPC pos0 winb Hwinb
                eg M0c HOK i E1 M' model1) as HAD.
  assert (HdP : L5.defined M' P 272).
  { pose proof T_OP as (Y1 & Y2 & _). apply (HAD P 272 HAMB' (ParseNumberW_u5.pa_def _ _ _ HPA)). left. lia. }
  assert (HdE : L5.defined M' E 16).
  { pose proof T_OE as (Y1 & Y2 & _). apply (HAD E 16 HAMB' (proj1 (proj2 HEC))). left. lia. }
  destruct (T_view_sound ml cells' (nth i G.BLS []) pe ce pv E' M' HV Hml HKC HAG HdP) as (HBLi & Hnst & buf & HPAb & Hlenb & Hce & Hpe & Hdpe).
  destruct (PREM E1 E' R' M1 M' model1 buf Hag HLF (proj1 HXV) (proj2 (proj2 (proj2 HXV))) eq_refl HAMB' HAG HKC HdE HPAb Hlenb)
    as (HEC' & HLS' & HR10 & txt & HPAt & Hlt & Hml1 & HW3).
  refine (Hcont fx' R' M' model1 (CH2.cur (LBr eg) G.BLS i E1) cr' LBo W HFP _ HRP HHPo Hmbv HH').
  set (a0v := uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) in *.
  pose (ps' := PML.PS 17 sst0 (uv E' (PB2.pv_nst pv)) (Z.eqb ml 1) (PML.ps_done ps) level (PML.ps_stack ps) sb scap (uv E' ce) (uv E' pe) txt (Some (a0v, e))).
  assert (Hden : CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps').
  { pose proof (T_FRZ E1 Hag0) as (_ & _ & _ & _ & F5 & _ & F7 & _).
    rewrite HBLi in Hbv |- *. cbn [CH2.blocks_vars_lt forallb fst snd] in Hbv.
    apply andb_prop in Hbv as [B1 _]. apply andb_prop in B1 as [B1 B2].
    rewrite !PB.den_cons. change (CH2.den E1 []) with (@nil (Z * Z)). unfold PML.ps_blocks, ps'. cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap].
    rewrite (PB.uv_agree _ E1 E' pe Hag B1), (PB.uv_agree _ E1 E' ce Hag B2), F5, F7. reflexivity. }
  assert (Hscap : In (PML.ps_scap ps') [66; 132; 264; 528; 1056]) by exact (proj1 (proj2 (proj2 (proj2 HWF)))).
  exists ps', code, g', eg.
  split; [rewrite Hwin; exact HPAt|].
  split.
  { unfold ps'. apply T_wf_upd; [exact Hnst|]. intros Hm. apply Z.eqb_eq in Hm. exact (proj1 (Hml1 Hm)). }
  split.
  { unfold PML.win_ok, ps'. cbn [PML.ps_win]. exists ch. split; [exact N1|]. split; [lia|]. split; [lia|].
    pose proof HH' as HH2. unfold CH2.cur, CH2V.LBr in HH2. rewrite Hden in HH2.
    destruct (hio_wf _ _ _ HIok _ _ _ _ HH2) as (HB & _).
    destruct (HB _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl N1))))) as (_ & Hdch & _). cbn [fst snd] in Hdch. eapply (L5.defined_sub _ _ _ _ _ Hdch); lia. }
  split.
  { unfold PML.buf_bound, PML.winlen, PML.buf_need, ps'. cbn [PML.ps_buf PML.ps_win PML.ps_more PML.ps_st].
    destruct (Z.eqb ml 1); cbn; lia. }
  split; [exact HEC'|].
  split.
  { intros Hc. unfold ps'. cbn [PML.ps_more]. destruct Hml as [-> | ->]; [reflexivity|]. exfalso. apply Hc. apply Hcode. reflexivity. }
  split; [exact HLS'|].
  split; [exact Hg'|].
  assert (HXK' : XIK.xinv V S2 M' eg).
  { exact (@ParseNumberW_u5.xinv_stretch SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb
             eg c E' M1 M' ltac:(apply orb_true_intro; left; exact Hfoot) HAG (CC.lf_frame _ _ _ _ _ _ _ HLF)
             (@ParseNumberW_u5.gblocks_amb SCFG_P L HI HIok LAY LBo sp r P V E S2 B kx (bx + PMES.benc L eg) ps R M model p e Hentry OBJS pos0 winb eg M0c i E1 M1 model1 HAMB)
             (proj1 (proj2 (proj2 HXV)))). }
  split; [exact (proj1 HXK')|].
  split; [exact (proj2 HXK')|].
  split.
  { intros _. destruct HSYNC as (HD & HKI). split; [exact HD|].
    unfold PMX.key_inv, ps'. cbn [PML.ps_st PML.ps_stack PML.ps_level PML.ps_more]. intros _ [Hks | (x & Hx1 & Hx2)].
    - exfalso. vm_compute in Hks. lia.
    - apply HKI; [exact Hmore|]. right. exists x. exact (conj Hx1 Hx2). }
  split; [unfold CH2.cur, CH2V.LBr; rewrite Hden; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact (proj1 (cred_of_blocks eg i E1 cr' ps' Hden Hscap) HC')|].
  split.
  { split; [unfold PMS.not_retreated, ps'; rewrite Hwin; cbn [PML.ps_win]; split; [reflexivity | lia]|].
    split.
    - exists a0v, e. split; [reflexivity|].
      pose proof (CH2.leaf_regs_ok L GT.NF sp G.HDECL T_STKF T_SCRP T_NF32 c ps1 E' R' M1 M' C2 HLF) as HRG.
      unfold PML.a0. erewrite (T_reg_at E' (CA.ps_reglist ps1) R' 10); [|exact HRG|reflexivity|reflexivity].
      subst a0v. unfold PB.uv. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - intros H0. pose proof (proj1 Hcode H0) as Hm1. subst ml.
      split; [reflexivity|]. split; [reflexivity|]. split; [|left; reflexivity].
      intros _. unfold PMS.win_exhausted, ps'. cbn [PML.ps_win]. exact (proj2 (Hml1 eq_refl)). }
  exact HW3.
Qed.
Lemma exit_end : forall i c k ps1, is_leaf i c k ps1 (CC.TOther PNC.RETPC) -> PNC.kind_of i = PNC.KEnd -> PNC.exit_end_chk i c ps1 = true ->
  forall g1 M0c, OKV M0c -> CC.leaf_ok (hl_segs L) G.CPS (AMB3XV g1 M0c) K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL Hk Hchk g1 M0c HOK.
  intros fx' E1 R1 M1 model1 E' R' M' HAt HA HFP Hag HLF HIH.
  destruct HA as [HAMB HXV].
  pose proof HAMB as (Hmo1 & Hmbv & Hag0 & _).
  unfold PNC.exit_end_chk in Hchk. cbv zeta in Hchk.
  apply andb_prop in Hchk as [Hchk C7]. apply andb_prop in Hchk as [Hchk C6]. apply andb_prop in Hchk as [Hchk C5].
  apply andb_prop in Hchk as [Hchk C4]. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2].
  apply Nat.ltb_lt in C6.
  assert (SCGE : CH.hd_scr G.HDECL <= SCRC) by (rewrite ParseNumberW_u5.SCRV; vm_compute; discriminate).
  assert (STKC : hl_ceil L + SCRC <= sp).
  { pose proof T_SPF as (_ & _ & _ & _ & _ & _ & X). replace (2 ^ 23) with 8388608 in X by reflexivity. lia. }
  refine (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (LBr g1) sp G.HDECL W G.BLS (CredV g1) T_STKF T_SCRP T_NF32 T_U2 T_W_OK T_WRS_OK
            G.CPS G.TAGS K (XIv g1) (proj2 (proj2 HOK)) (fun _ => 0) (fun _ => 0) SCRC SCGE STKC (T_okV_defc M0c HOK) R T_EV0 r
            (proj1 Hentry) (proj1 (proj2 Hentry)) heap_ok3 PNC.RETPC i c k ps1 PNC.RETPC ParseNumberW_u5.ret_at IL C1
            fx' E1 R1 M1 model1 E' R' M' HAt HAMB Hag HLF _).
  intros HRP HHP HAMB' HAG.
  pose proof HAMB' as (_ & _ & _ & (cr' & HH' & HC') & _).
  pose proof (T_okV_hpres g1 M0c M' HOK HHP) as HHPo.
  refine (Hcont fx' R' M' model1 (CH2.cur (LBr g1) G.BLS i E1) cr' LBo W HFP _ HRP HHPo Hmbv HH').
  unfold ParseNumberW_u5.XIv in HXV. destruct HXV as (_ & HGX & HXK & HSIM).
  unfold ParseNumberW_u5.GX in HGX. rewrite Hk in HGX.
  unfold ParseNumberW_u5.SIM in HSIM. rewrite (PNCW.WK_ret i ltac:(rewrite Hk; discriminate)), Hk in HSIM.
  unfold ParseNumberW_u5.SEND in HSIM.
  destruct HSIM as (ps2 & code & g' & n & kq & (S1 & S2w & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12) & S13 & S14 & S15 & S16 & S17 & S18 & S19).
  pose proof (CC.lf_frame _ _ _ _ _ _ _ HLF) as HLFF. pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as HGR.
  pose proof (frm_end c E' M1 M' C3 HAG HLFF) as HFR.
  pose proof T_STKX as (X1 & X2 & X3 & X4).
  pose proof (T_jv_agree _ E1 E' Hag C6) as HJV.
  assert (HB2 : forall b, In b (PML.ps_blocks ps2) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf _ _ _ HIok _ _ _ _ HH') as (HB & _).
    assert (Hin : In b (CH2.cur (LBr g1) G.BLS i E1)) by (unfold CH2.cur, CH2V.LBr; rewrite S12; apply in_or_app; left; exact Hb).
    exact (proj1 (HB b Hin)). }
  assert (Hscap : In (PML.ps_scap ps2) [66; 132; 264; 528; 1056]) by exact (proj1 (proj2 (proj2 (proj2 S4)))).
  exists ps2, code, g', g1.
  split.
  { apply (PB2.parser_at_fr _ M1 M' HFR HGR); [| | |exact S1].
    - pose proof T_OP as (Y1 & Y2 & _). apply out_hi; lia.
    - destruct (HB2 (PML.ps_bptr ps2, PML.ps_bcap ps2) (or_introl eq_refl)) as (Z1 & _ & _ & Z4 & Z5). cbn [fst snd] in Z1, Z4, Z5. apply out_lo; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; lia.
    - destruct (HB2 (PML.ps_sb ps2, PML.ps_scap ps2) (or_intror (or_introl eq_refl))) as (Z1 & _ & _ & Z4 & Z5). cbn [fst snd] in Z1, Z4, Z5. apply out_lo; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; lia. }
  split; [exact S4|].
  split; [exact (PB2.win_ok_fr M1 M' HGR LBo ps2 S5)|].
  split; [exact S6|].
  split.
  { apply (PB2.ec_at_fr _ M1 M' HFR HGR); [|exact S7]. pose proof T_OE as (Y1 & Y2 & _). apply out_hi; lia. }
  split; [exact S8|].
  split.
  { apply (PB2.ls_ok_fr _ M1 M' HFR); [| |exact S9].
    - destruct S10 as [-> | [-> _]]; [exact HG | discriminate].
    - apply out_lo; lia. }
  split; [exact S10|].
  assert (HXK' : XIK.xinv V S2 M' g1).
  { exact (@ParseNumberW_u5.xinv_stretch SCFG_P L HI HIok LAY LBo cr sp r P V E S2 B kx (bx + PMES.benc L eg) ps eg R M model p e HH Hentry Ha0 Ha1 Ha2 Ha3 Hwin Hmore Hst HPA HWF HWIN HBB HPC OBJS pos0 winb Hcpr Hwinb
             g1 c E' M1 M' ltac:(apply orb_true_intro; right; exact C3) HAG HLFF
             (@ParseNumberW_u5.gblocks_amb SCFG_P L HI HIok LAY LBo sp r P V E S2 B kx (bx + PMES.benc L g1) ps R M model p e Hentry OBJS pos0 winb g1 M0c i E1 M1 model1 HAMB) HXK). }
  split; [exact (proj1 HXK')|].
  split; [exact (proj2 HXK')|].
  assert (HST2 : code = 0 -> PML.ps_stack ps2 = PML.ps_stack ps).
  { intros H0. destruct (S19 H0) as (_ & _ & _ & _ & R5). rewrite <- R5, en_stack.
    destruct (PNKW.CI_fields cw (firstn n winb) kq) as (_ & _ & _ & _ & F5 & _). unfold ParseNumberW_u5.CI. rewrite F5.
    destruct HRM as ((_ & _ & _ & _ & Q5) & _). exact Q5. }
  split.
  { intros H0. destruct (S11 H0) as (Q1 & Q2 & Q3). split; [rewrite (HGX code S7 H0), Q1; reflexivity|].
    unfold PMX.key_inv. intros _ [Hks | (x & Hx1 & Hx2)].
    - exfalso. destruct Q3 as [Q3|[Q3|[]]]; rewrite <- Q3 in Hks; vm_compute in Hks; lia.
    - rewrite Q1. destruct HSYNC as (_ & HKI). apply HKI; [exact Hmore|]. right. exists x. rewrite <- (HST2 H0). exact (conj Hx1 Hx2). }
  split; [unfold CH2.cur, CH2V.LBr; rewrite S12; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact (proj1 (cred_of_blocks g1 i E1 cr' ps2 S12 Hscap) HC')|].
  split.
  { split; [unfold PMS.not_retreated; rewrite Hwin, S2w; split; [reflexivity | lia]|].
    split.
    - exists (e - uv E1 JV), e. split; [exact S2w|].
      pose proof (CH2.leaf_regs_ok L GT.NF sp G.HDECL T_STKF T_SCRP T_NF32 c ps1 E' R' M1 M' C2 HLF) as HRG.
      pose proof (PB.prove_ok _ _ _ _ (T_leaf_know c ps1 E' R' M1 M' HLF) C7) as HKR. cbn [kentry_ok] in HKR.
      pose proof (T_HCU E' HAG ltac:(rewrite HJV; lia)) as HC.
      unfold PML.a0. erewrite (T_reg_at E' (CA.ps_reglist ps1) R' 10); [|exact HRG|reflexivity|reflexivity].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' (nth 10 (CA.ps_reglist ps1) (ELit 0)))). f_equal.
      fold (uv E' (APC.esub (nth 10 (CA.ps_reglist ps1) (ELit 0)) PNC.CURJ)) in HKR. rewrite PB.uv_esub in HKR.
      pose proof (PB.uv_range E' (nth 10 (CA.ps_reglist ps1) (ELit 0))) as U1. pose proof (PB.uv_range E' PNC.CURJ) as U2.
      fold (uv E' (nth 10 (CA.ps_reglist ps1) (ELit 0))).
      rewrite (ParseNumberW_u5.mod64_zero _ _ U1 U2 ltac:(lia)). rewrite HC, HJV. reflexivity.
    - intros H0. destruct (S11 H0) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. split; [|right; exact Q3].
      intros Hn. exfalso. rewrite Hn in Q3. vm_compute in Q3. lia. }
  unfold ParseNumberW_u5.NOFJ in S13. pose proof (proj2 Hwinb) as HL.
  apply (PNKW.w3_end cw winb n kq M' P ps ps2 eg g1 code p e S14 S15 S16 S17 S18).
  - intros H0. destruct (S11 H0) as (Q1 & Q2 & Q3). split; [exact (S19 H0)|].
    split; intros Hs; rewrite Hs in Q3; vm_compute in Q3; lia.
  - exact Hwin.
  - exact HL.
  - rewrite S2w. f_equal. f_equal. lia.
  - intros _. unfold PMW.win_bytes. rewrite S2w.
    pose proof (win_bytes_M' M' (proj1 HHPo)) as HWB.
    replace (e - uv E1 JV) with (p + Z.of_nat n) by lia.
    split; [exact (PB3.bytes_at_skipn M' p winb n ltac:(lia) HWB)|].
    split; [rewrite length_skipn; lia|].
    apply Forall_forall. intros x Hx. assert (Hx' : In x winb) by (rewrite <- (firstn_skipn n winb); apply in_or_app; right; exact Hx).
    pose proof (proj1 (Forall_forall _ _) Hwinr x Hx') as Hx2. cbn beta in Hx2. lia.
Qed.
Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> forall g1 M0c, OKV M0c ->
  CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv G.CPS K PML.fp_ok g1 M0c i c ps1.
Proof.
  intros i c k ps1 pc IL g1 M0c HOK.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as HL.
  pose proof (CH2.leaves_all_sound _ _ _ PNCW.wl_ok _ _ _ _ _ IL) as HW.
  unfold PNC.leaf_chk in HL. cbv beta iota in HL.
  destruct (Z.eqb_spec pc PNC.RETPC) as [->|Hne].
  - rewrite ?Z.eqb_refl in HL. cbv iota in HL.
    apply CH2V.leaf_okV_of; [exact HOK|].
    destruct (PNC.kind_of i) eqn:Hki; rewrite ?Hki in HL; cbn iota in HL.
    + pose proof HL as HL0. unfold PNC.exit_pre_chk in HL. cbv zeta in HL.
      apply andb_prop in HL as [HL C6]. apply andb_prop in HL as [HL C5]. apply andb_prop in HL as [HL C4].
      apply andb_prop in HL as [HL Hfoot]. apply andb_prop in HL as [C1 C2].
      destruct (PNC.view_chk 1 (SR.ps_cells ps1) (nth i G.BLS [])) as [[[pe ce] pv]|] eqn:HV; [|rewrite ?HV in C6; exact (False_ind _ (diff_false_true C6))].
      exact (exit_view i c k ps1 (SR.ps_cells ps1) 1 0 g pe ce pv IL C1 C2 (fun _ _ HK _ => HK) HV (or_intror eq_refl)
               ltac:(split; intros; reflexivity) (or_introl eq_refl) g1 M0c HOK ltac:(rewrite Hki; discriminate) Hfoot
               (prem_pre i c k ps1 pe ce pv g1 M0c IL Hki HL0 HW HV HOK)).
    + pose proof HL as HL0. unfold PNC.exit_app_chk in HL. cbv zeta in HL.
      apply andb_prop in HL as [HL C5]. apply andb_prop in HL as [HL C4].
      apply andb_prop in HL as [HL Hfoot]. apply andb_prop in HL as [C1 C2].
      destruct (PNC.view_chk 1 (SR.ps_cells ps1) (nth i G.BLS [])) as [[[pe ce] pv]|] eqn:HV; [|rewrite ?HV in C5; exact (False_ind _ (diff_false_true C5))].
      exact (exit_view i c k ps1 (SR.ps_cells ps1) 1 0 g pe ce pv IL C1 C2 (fun _ _ HK _ => HK) HV (or_intror eq_refl)
               ltac:(split; intros; reflexivity) (or_introl eq_refl) g1 M0c HOK ltac:(rewrite Hki; discriminate) Hfoot
               (prem_app i c k ps1 pe ce pv g1 M0c IL Hki HL0 HW HV HOK)).
    + pose proof HL as HL0. unfold PNC.exit_setec_chk in HL. cbv zeta in HL.
      apply andb_prop in HL as [HL C5]. apply andb_prop in HL as [HL C4].
      apply andb_prop in HL as [HL Hfoot]. apply andb_prop in HL as [C1 C2].
      destruct (PNC.view_chk 0 (PNC.cells16 (SR.ps_cells ps1)) (nth i G.BLS [])) as [[[pe ce] pv]|] eqn:HV; [|rewrite ?HV in C5; exact (False_ind _ (diff_false_true C5))].
      rewrite ?HV in C5. cbn iota in C5.
      destruct (CAX.cell_at (PNC.cells16 (SR.ps_cells ps1)) PNC.Eb 0 4) as [[code| | | | | | |]|] eqn:HC; rewrite ?HC in C5; try exact (False_ind _ (diff_false_true C5)).
      cbn iota in C5.
      assert (Hc1 : 1 <= code) by (do 6 (apply andb_prop in C5 as [C5 _]); apply Z.leb_le in C5; exact C5).
      assert (HCELLS : forall E' (M' : mem), know_ok RSEGS E' M' (SR.ps_cells ps1) -> env_agree GT.NF E0 E' -> know_ok RSEGS E' M' (PNC.cells16 (SR.ps_cells ps1))).
      { intros E' M' HK HAG. pose proof T_OP as HOP. pose proof T_STKX as (X1 & X2 & X3 & X4). pose proof T_SPF as (Q1 & Q2 & _).
        pose proof (T_FRZ E' HAG) as (F1 & _). unfold PML.obj_on_stack in HOP.
        apply (ParseNumberW_u5.cells16_ok E' M' _ P HK F1); lia. }
      assert (Hcd : code = 0 <-> (0 : Z) = 1) by (split; intros H0; lia).
      assert (Hg' : PML.LS2 = g \/ (PML.LS2 = PML.LS2 /\ code <> 0)) by (right; split; [reflexivity | lia]).
      assert (Hk' : PNC.kind_of i <> PNC.KEnd) by (rewrite Hki; discriminate).
      exact (exit_view i c k ps1 (PNC.cells16 (SR.ps_cells ps1)) 0 code PML.LS2 pe ce pv IL C1 C2 HCELLS HV (or_introl eq_refl)
               Hcd Hg' g1 M0c HOK Hk' Hfoot
               (prem_setec i c k ps1 pe ce pv code g1 M0c IL Hki HL0 HW HV HC HOK)).
    + exact (exit_end i c k ps1 IL Hki HL g1 M0c HOK).
  - cbv iota in HL.
    apply andb_prop in HL as [HL HM]. apply andb_prop in HL as [Hfoot Hpc]. apply Z.eqb_eq in Hpc.
    destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|exact (False_ind _ (diff_false_true HM))].
    destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|exact (False_ind _ (diff_false_true HM))].
    destruct (Z.eqb_spec pc PNC.APPR) as [->|N1].
    + cbv iota in HM.
      apply andb_prop in HM as [HM HA]. apply andb_prop in HM as [HM HS]. apply andb_prop in HM as [HM Hi0]. apply andb_prop in HM as [K1 K2].
      apply PNC.kind_eqb_eq in K1, K2. apply Nat.ltb_lt in Hi0.
      destruct (PB3.appendr_chk GT.NF G.HDECL PNC.Pb 224 PNC.SEG PNC.WLEN 132 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hci;
        [|rewrite ?Hci in HS; exact (False_ind _ (diff_false_true HS))].
      apply CH2V.leaf_okV_of; [exact HOK|].
      exact (leaf_append i c k ps1 j cj ci IL Hret Hcj Hpc K1 K2 Hfoot Hi0 Hci HA g1 M0c HOK).
    + cbv iota in HM.
      destruct (Z.eqb_spec pc PNC.SETEC) as [->|N2].
      * cbv iota in HM.
        apply andb_prop in HM as [HM HS]. apply andb_prop in HM as [K1 K2]. apply PNC.kind_eqb_eq in K1, K2.
        destruct (PB2.setec_chk GT.NF G.HDECL PNC.Eb 0 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hci;
          [|rewrite ?Hci in HS; exact (False_ind _ (diff_false_true HS))].
        rewrite ?Hci in HS. cbn iota in HS. apply Nat.leb_le in HS.
        apply CH2V.leaf_okV_of; [exact HOK|].
        exact (leaf_setec i c k ps1 j cj ci IL Hret Hcj Hpc K1 K2 Hfoot Hci HS g1 M0c HOK).
      * cbv iota in HM.
        destruct (orb (Z.eqb pc PNC.ENDI) (Z.eqb pc PNC.ENDF)) eqn:HE; rewrite ?HE in HM; cbv iota in HM; [|exact (False_ind _ (diff_false_true HM))].
        apply andb_prop in HM as [HM HEnd]. apply andb_prop in HM as [HM HS]. apply andb_prop in HM as [K1 K2].
        apply PNC.kind_eqb_eq in K1, K2.
        destruct (PBX.ptrans_chkx GT.NF G.HDECL PNC.Eb 0 PNC.Pb 0 PNC.ENDNUM_SCR PNC.Vb PML.LIT_LO 12 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hci;
          [|rewrite ?Hci in HS; exact (False_ind _ (diff_false_true HS))].
        apply orb_prop in HE as [HE|HE]; apply Z.eqb_eq in HE; rewrite HE in IL, Hpc.
        -- exact (leaf_end PNC.ENDI PMW.FEndInt (or_introl eq_refl) (or_introl eq_refl) ENDI_OK
                    i c k ps1 j cj ci IL Hret Hcj Hpc K1 K2 Hfoot Hci HEnd g1 M0c HOK).
        -- exact (leaf_end PNC.ENDF PMW.FEndFrac (or_intror eq_refl) (or_intror eq_refl) ENDF_OK
                    i c k ps1 j cj ci IL Hret Hcj Hpc K1 K2 Hfoot Hci HEnd g1 M0c HOK).
Qed.
Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_NUMBER M model) K.
Proof using All.
  pose proof T_UU as (U2 & U10 & U11 & U12 & U13 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44).
  pose proof T_NUM as (ch & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 & N26 & N27 & N28).
  assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps).
  { change (nth 0 G.BLS []) with [(EVar 36, APC.escale 2 (EVar 34)); (EVar 37, EVar 39)]. rewrite !PB.den_cons. change (CH2.den E0 []) with (@nil (Z * Z)). unfold PML.ps_blocks.
    rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite U34, U36, U37, U39, <- N14. rewrite Z.mod_small by lia. reflexivity. }
  unfold PML.cfg. change PML.PC_PARSE_NUMBER with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv T_STKF T_SCRP T_NF32 T_U2 T_W_OK T_WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps1 j s IL E1 E' R' M1 M' cr1 Hag0 Hag HLF HC. exact (T_goto_cred i c kk ps1 j s IL E1 E' R' M1 M' cr1 Hag0 Hag HLF g1 HC).
  - intros g1 M0c OKV i c kk ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX.
    assert (Hki : PNC.kind_of i = PNC.KPre).
    { pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold PNC.leaf_chk, PNC.goto_chk in X.
      do 6 (apply andb_prop in X as [X _]). apply PNC.kind_eqb_eq in X. exact X. }
    assert (Hg : g1 = eg) by (destruct HX as (_ & HGX & _); unfold ParseNumberW_u5.GX in HGX; rewrite Hki in HGX; exact HGX).
    subst g1. exact (T_goto_xi eg M0c OKV i c kk ps1 j s IL E1 R1 E' R' M1 M' model1 HAt HA Hag HLF HX).
  - intros i c kk ps1 pc IL g1 M0c OKV. exact (leaves i c kk ps1 pc IL g1 M0c OKV).
  - reflexivity.
  - rewrite LS. exact T_At0.
  - apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv eg M 0%nat E0 M model (CH2V.okV_refl L M LBo sp G.HDECL W T_DEF0)).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur, CH2V.LBr; rewrite Hden0; exact HH|].
      apply (proj2 (cred_of_blocks eg 0 E0 cr ps Hden0 (proj1 (proj2 (proj2 (proj2 HWF)))))). exact HPC.
    + split; [|split; [unfold ParseNumberW_u5.GX; change (PNC.kind_of 0) with PNC.KPre; reflexivity | split; [exact (conj HINV HLIT) | exact I]]].
      split; [intros a _; reflexivity|].
      pose proof T_PAR as PAR. destruct PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _).
      destruct Hstr as ((_ & _ & _ & _ & Hbb & _) & _).
      split; [exact Hbb|].
      destruct HWF as (_ & _ & _ & _ & C0 & T0 & _ & _ & HWM). destruct (HWM Hmore) as (_ & _ & _ & _ & _ & HNP). exact (HNP Hst).
  - exact Hfp.
Qed.

End MainU.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPR_OK : PMS.str_append_range_spec L HI.
Hypothesis SETEC_OK : PMS.set_ec_spec L.
Hypothesis ENDI_OK : PMW.end_integer_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Hypothesis ENDF_OK : PMW.end_fraction_value_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Theorem parse_number_okwU : PMW.parse_number_specwU L HI PML.STRTOD_SCR_V PMES.WD_SCR_X PMR.the_rm.
Proof.
  unfold PMW.parse_number_specwU, PMW.ptrans_curxwU, PMW.ptrans_gxwU, PMW.ptrans_gbxwU. intros LBo cr sp r P V E S2 B kx bx g ps eg w x c. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & ((Ha0 & Ha2 & Ha3 & (p & e & Hwin & Ha1)) & Hmore & Hst) & HPA & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HINV & HLIT & HSYNC & Hkx & Hbx & HPC & OBJS & HWBY & HRM & HROOM) Hcont.
  pose proof (ParseNumberW_u5.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rp & Hp); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  unfold PMW.win_bytes in HWBY. rewrite Hwin in HWBY. destruct HWBY as (B1 & B2 & B3).
  assert (Hwinr : Forall (fun c0 => 0 <= c0 < 256) w) by (eapply Forall_impl; [|exact B3]; intros a Ha; cbn beta in *; lia).
  apply (main L HI HIok LAY FPM APPR_OK SETEC_OK ENDI_OK ENDF_OK LBo cr sp r P V E S2 B kx bx g ps eg fx R M model K p e HH Hmo HKnil Hfp Hentry Ha0 Ha1 Ha2 Ha3
           Hwin Hmore Hst HPA HWF HWIN HBB HVIS HEC HLS HG HINV HLIT HSYNC Hkx Hbx HPC OBJS pos0 w Hp Rp (conj B1 B2) Hwinr c HRM HROOM).
  intros fx' R' M' model' LB' cr' LBk W HFP' (ps' & code & g' & eg' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17) HRP HHP HMB HHI.
  apply (Hcont fx' R' M' model' LB' cr' LBk W HFP'); [|exact HRP | exact HHP | exact HMB | exact HHI].
  exists ps', code, g', eg'.
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj Q15 (conj Q16
          (PNKW.w3n_fold c w x M' P ps ps' eg eg' code Q17))))))))))))))))).
Qed.
End Final.
End PNWU.
