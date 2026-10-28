(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5
  PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5 PmRefRead_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ReadStretchX_u5 ReadBase_u5 TopKitX_u5 PsBase_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import TopSpecsW_u5 TopKitW_u5 PsKitW_u5 ReadKitXW_u5 ReadStretchXW_u5 ReadInvXW_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import ReadXWHU ReadRoomWU ReadXWUB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RDXWUW.
Local Strategy expand [TPSW.chunk_of TPSW.rest_of TPSW.chunk_w].
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Variable WD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis VPUSH : PMS.vec_push_spec L HI.
Hypothesis PSOMEWU : PMW.parse_some_specwU L HI STRTOD_SCR WD_SCR PMR.the_rm.
Hypothesis SKIPWSW : PMW.skip_whitespace_specw L HI STRTOD_SCR PMR.the_rm.
Hypothesis PCDW : PMW.parser_check_done_specw L HI STRTOD_SCR PMR.the_rm.
Hypothesis SETEC : PMS.set_ec_spec L.
Hypothesis RCHUNKW : TPSW.read_chunk_specw L.

Section Run.
Variables (LBo : list (Z * Z)) (sp r Rr IS V E S2 ch kx bx : Z) (rep : PML.srep) (g0 : PML.ls_state) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : ShapeAlg.TSet) (eg0 : PMES.eghost).
Let SS := PMX.READX_SCR STRTOD_SCR WD_SCR.
Let n := Z.of_nat (length (PML.srep_chars rep)).
Let D := PML.srep_data (IS + 80) rep.
Let P := Rr + 320.
Let LBk := lb_remove ch LBo.
Hypothesis Hn : n < 2 ^ 26.
Hypothesis HB : Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep).
Hypothesis G0 : g0 <> PML.LS0.
Hypothesis SPOK : RS.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis Prok : L5.ra_ok r.
Hypothesis OR : PML.obj_on_stack L sp Rr 592.
Hypothesis OI : PML.obj_on_stack L sp IS 272.
Hypothesis OV : PML.obj_on_stack L sp V 8.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP : PML.apart Rr 592 IS 272 /\ PML.apart Rr 592 V 8 /\ PML.apart Rr 592 E 16 /\ PML.apart IS 272 V 8 /\ PML.apart IS 272 E 16 /\ PML.apart V 8 E 16.
Hypothesis OVX : PML.obj_on_stack L sp V PMES.ENC_SIZE.
Hypothesis OS2 : PML.obj_on_stack L sp S2 24.
Hypothesis APX : PML.apart V PMES.ENC_SIZE S2 24 /\ PML.apart Rr 592 V PMES.ENC_SIZE /\ PML.apart Rr 592 S2 24 /\ PML.apart IS 272 V PMES.ENC_SIZE /\ PML.apart IS 272 S2 24 /\
                 PML.apart V PMES.ENC_SIZE E 16 /\ PML.apart S2 24 E 16.
Hypothesis KX0 : 0 <= kx.
Hypothesis INch : In (ch, 16384) LBo.
Hypothesis INrep : forall b, In b (PML.srep_blocks rep) -> In b LBo.
Hypothesis NEch : forall b, In b (PML.srep_blocks rep) -> fst b <> ch.
Hypothesis R0sp : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis R0tp : getr R0 4%bv = Z_to_bv 64 PML.TP.
Hypothesis HK0 : K [].
Hypothesis BX0 : 0 <= bx.
Hypothesis WR0 : PMW.wroomU eg0 (PMR.K (PML.srep_chars rep)) (PMR.ALLOW (PML.srep_chars rep)).
Let i_CONT0 (b : Z) : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
  PML.fp_ok fx' ->
  PML.source_at M' Rr ch -> PML.parser_at M' (Rr + 320) ps' -> PML.isrc_at M' IS rep gp' rdst' -> PML.ec_at M' E code -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.LS2 /\ code <> 0)) ->
  PMES.enc_inv M' V S2 eg' -> PML.lits_ok M' ->
  PML.pcredit_x L cr' ps' (kx + PMX.kenc L eg') b -> PML.wf_ps ps' ->
  False ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp SS (RIXW.Wr Rr IS V E S2) M0 M' -> model_but_vm model0 model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg') cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Proof. intros. contradiction. Defined.
Let i_al8 := @RIXW.al8 sp.
Let i_al16 := @RIXW.al16 sp.
Let i_al8_add := @RIXW.al8_add .
Let i_not_outside := @RIXW.not_outside .
Let i_in_lb_remove := @RIXW.in_lb_remove .
Let i_lb_remove_in := @RIXW.lb_remove_in .
Let i_lb_remove_fst := @RIXW.lb_remove_fst .
Let i_nodup_app_l := @RIXW.nodup_app_l .
Let i_nodup_app_disj := @RIXW.nodup_app_disj .
Let i_win_ok_setwin := @RIXW.win_ok_setwin ch.
Let i_win_ok_exh := @RIXW.win_ok_exh .
Let i_win_ok_mono := @RIXW.win_ok_mono .
Let i_ra_ok_lit := @RIXW.ra_ok_lit r.
Let i_CSv := @RIXW.CSv .
Let i_keeps_sub := @RIXW.keeps_sub .
Let i_keeps_pres := @RIXW.keeps_pres .
Let i_KSM_cs := @RIXW.KSM_cs .
Let i_KSA_cs := @RIXW.KSA_cs .
Let i_KSM_KSA := @RIXW.KSM_KSA .
Let i_KSM_KSW := @RIXW.KSM_KSW .
Let i_KSM_KS45 := @RIXW.KSM_KS45 .
Let i_KSM_KS01 := @RIXW.KSM_KS01 .
Let i_KSM_KS012 := @RIXW.KSM_KS012 .
Let i_KSM_KS06 := @RIXW.KSM_KS06 .
Let i_mk_entry := @RIXW.mk_entry L.
Let i_Wr := @RIXW.Wr Rr IS V E S2.
Let i_Wr_eq := @RIXW.Wr_eq Rr IS V E S2.
Let i_foot := @RIXW.foot Rr IS V E S2.
Let i_wfx := @RIXW.wfx .
Let i_ws_setwin := @RIXW.ws_setwin .
Let i_finish (b : Z) := @RIXW.finish SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_blk := @RIXW.blk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY Rr IS rep.
Let i_enc_inv_K := @RIXW.enc_inv_K L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_lits_K := @RIXW.lits_K .
Let i_enc_stack := @RIXW.enc_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_hpres_weaken := @RIXW.hpres_weaken L.
Let i_ginv_stack (b : Z) := @RIXW.ginv_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE OVX OS2 INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_foot_cases := @RIXW.foot_cases STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_foot_cases2 := @RIXW.foot_cases2 L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_wpar_foot := @RIXW.wpar_foot STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_wparx_foot := @RIXW.wparx_foot STRTOD_SCR WD_SCR Rr IS V E S2 rep.
Let i_wsi_parx := @RIXW.wsi_parx L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE OVX OS2.
Let i_out_parx := @RIXW.out_parx L STRTOD_SCR WD_SCR sp Rr IS V E S2 rep SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let i_mk_stk := @RIXW.mk_stk L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let i_mok_bv := @RIXW.mok_bv .
Let i_ginv_ptrans (b : Z) := @RIXW.ginv_ptrans SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let i_enc_pms (b : Z) := @RIXW.enc_pms SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let i_Wc := @RIXW.Wc Rr IS E ch.
Let i_hfacts := @RIXW.hfacts SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo Rr IS ch rep INch.
Let i_hfacts_enc := @RIXW.hfacts_enc SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo Rr IS ch rep INch.
Let i_ginv_chunk (b : Z) := @RIXW.ginv_chunk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch.
Let i_wf_setwin := @RIXW.wf_setwin .
Let i_pcredit_setwin := @RIXW.pcredit_setwin L.
Let i_ginv_setwin (b : Z) := @RIXW.ginv_setwin SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_We := @RIXW.We E.
Let i_ginv_setec (b : Z) := @RIXW.ginv_setec SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_ginv0 := @RIXW.ginv0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch rep M0 model0.
Let i_ginv0_entry (b : Z) := @RIXW.ginv0_entry SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let i_ginv_ptrans0 (b : Z) := @RIXW.ginv_ptrans0 SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let i_ginv_pcells (b : Z) := @RIXW.ginv_pcells SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp r Rr IS V E S2 ch kx b rep g0 R0 M0 model0 K Hn SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep NEch (fun (_ : PMES.eghost) (_ : Z) => False) (i_CONT0 b).
Let egacc := @RDXWHU.egacc eg0.
Let wfin := @RDXWHU.wfin rep eg0.
Let ginv (b : Z) := @RDXWHU.ginv L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let lay := @RDXWHU.lay L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let layx := @RDXWHU.layx L STRTOD_SCR WD_SCR sp Rr V S2 rep OVX OS2.
Let rsof := @RDXWHU.rsof IS rep.
Let wst := @RDXWHU.wst Rr.
Let rinvA := @RDXWHU.rinvA Rr IS rep eg0.
Let rinvP := @RDXWHU.rinvP Rr IS rep eg0.
Let rinvB0 := @RDXWHU.rinvB0 Rr IS rep eg0.
Let rinvB := @RDXWHU.rinvB Rr IS rep eg0.
Let rinvE := @RDXWHU.rinvE rep eg0.
Let rinvX := @RDXWHU.rinvX Rr IS rep eg0.
Let accC0 := @RDXWHU.accC0 rep eg0.
Let rinvC0 := @RDXWHU.rinvC0 Rr IS rep eg0.
Let rinvC := @RDXWHU.rinvC Rr IS rep eg0.
Let rinvPC := @RDXWHU.rinvPC Rr IS rep eg0.
Let rinvC00 := @RDXWHU.rinvC00 Rr IS rep eg0.
Let ginv_ptrans (b : Z) := @RDXWHU.ginv_ptrans SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let enc_pms (b : Z) := @RDXWHU.enc_pms SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX.
Let ginv_chunk (b : Z) := @RDXWHU.ginv_chunk SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch.
Let ginv0 := @RDXWHU.ginv0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch rep M0 model0.
Let ginv_ptrans0 (b : Z) := @RDXWHU.ginv_ptrans0 SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep.
Let hfacts := @RDXWHU.hfacts SCFG_P L HI HIok LAY LBo Rr ch rep INch.
Let mk_stk := @RDXWHU.mk_stk L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let mk_entry := @RDXWHU.mk_entry L STRTOD_SCR WD_SCR sp Rr IS V E rep SPOK Hceil Htop OR OI OV OE.
Let enc_sync_setwin := @RDXWHU.enc_sync_setwin .
Let oos := @RDXWHU.oos L STRTOD_SCR WD_SCR sp Rr IS rep.
Let ginv_ws (b : Z) := @RDXWHU.ginv_ws L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let ws_same := @RDXWHU.ws_same .
Let call_ptransw (b : Z) := @RDXWHU.call_ptransw SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 K G0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INrep HK0.
Let call_chunkw (b : Z) := @RDXWHU.call_chunkw SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY RCHUNKW LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 K Hn HB G0 SPOK Hceil Htop OR OI OV OE AP OVX OS2 APX INch INrep NEch HK0.
Let gcells (b : Z) := @RDXWHU.gcells SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE OVX OS2 INch.
Let blkW := @RDXWHU.blkW SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY Rr IS rep.
Let wst_x (b : Z) := @RDXWHU.wst_x SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE.
Let wst_stack (b : Z) := @RDXWHU.wst_stack SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0 SPOK Hceil Htop OR OI OV OE.
Let wst_len := @RDXWHU.wst_len Rr.
Let wst_nil := @RDXWHU.wst_nil Rr.
Let wst_cons := @RDXWHU.wst_cons STRTOD_SCR WD_SCR Rr IS rep.
Let exh_nil := @RDXWHU.exh_nil STRTOD_SCR WD_SCR Rr IS rep.
Let wst_core := @RDXWHU.wst_core Rr.
Let st_small := @RDXWHU.st_small STRTOD_SCR WD_SCR Rr IS rep.
Let chunk_post := @RDXWHU.chunk_post STRTOD_SCR WD_SCR Rr IS ch rep HB.
Let wst_rchunk := @RDXWHU.wst_rchunk L STRTOD_SCR WD_SCR sp Rr IS V E ch rep SPOK Hceil Htop OR OI OV OE AP.
Let wst_setwin := @RDXWHU.wst_setwin L STRTOD_SCR WD_SCR sp Rr IS V E ch rep SPOK Hceil Htop OR OI OV OE.
Let step_psome := @RDXWHU.step_psome .
Let step_pcd := @RDXWHU.step_pcd .
Let step_sws := @RDXWHU.step_sws .
Let egacc_app := @RDXWHU.egacc_app STRTOD_SCR WD_SCR Rr IS rep eg0.
Let egacc_nil := @RDXWHU.egacc_nil eg0.
Let wfin_A := @RDXWHU.wfin_A IS rep eg0.
Let wfin_B := @RDXWHU.wfin_B IS rep eg0.
Let wfin_C := @RDXWHU.wfin_C IS rep eg0.
Let wfin_Ceof := @RDXWHU.wfin_Ceof IS rep eg0.
Let b2z_t := @RDXWHU.b2z_t .
Let b2z_f := @RDXWHU.b2z_f .
Let b2z_0 := @RDXWHU.b2z_0 .
Let b2z_n0 := @RDXWHU.b2z_n0 .
Let weof_ne := @RDXWHU.weof_ne IS rep.
Let weof_nil := @RDXWHU.weof_nil IS rep.
Let rankz_in := @RDXWHU.rankz_in .
Let rankz_nin := @RDXWHU.rankz_nin .
Let rtail_break' := @RDXWHU.rtail_break' .
Let refill_eof_w := @RDXWHU.refill_eof_w IS rep.
Let st_mod (b : Z) := @RDXWHU.st_mod L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let rp_of := @RDXWHU.rp_of L STRTOD_SCR WD_SCR Rr IS V E S2 rep R0 Htop AP APX.
Let cd_frame_x := @RDXWHU.cd_frame_x L STRTOD_SCR WD_SCR sp r Rr IS V E rep R0 SPOK Hceil Hsptop Htop OR OI OV OE.
Let ee := @RDXWHU.ee .
Let ww := @RDXWHU.ww .
Let muC := @RDXWHU.muC IS rep.
Let land2 := @RDXWHU.land2 STRTOD_SCR WD_SCR Rr IS rep.
Let ra_lit := @RDXWHU.ra_lit .
Let ginv_g0 (b : Z) := @RDXWHU.ginv_g0 L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx b rep g0 M0 model0.
Let ee_range := @RDXWHU.ee_range STRTOD_SCR WD_SCR Rr IS rep.
Let ww_range := @RDXWHU.ww_range STRTOD_SCR WD_SCR Rr IS rep.
Let rd_frame := @RDXWHU.rd_frame sp r R0.
Let rd_frame_x := @RDXWHU.rd_frame_x L STRTOD_SCR WD_SCR sp r Rr IS V E rep R0 SPOK Hceil Hsptop Htop OR OI OV OE.
Let KSN_KSA := @RDXWHU.KSN_KSA L Rr IS V E S2 Htop AP APX.
Let KSN_KSW := @RDXWHU.KSN_KSW L Rr IS V E S2 Htop AP APX.
Let KSN_KS45 := @RDXWHU.KSN_KS45 L Rr IS V E S2 Htop AP APX.
Let KSN_rp := @RDXWHU.KSN_rp L Rr IS V E S2 Htop AP APX.
Let muB := @RDXWHU.muB IS rep.
Let rank := @RDXWHU.rank .
Let muA := @RDXWHU.muA IS rep.
Let rank_range := @RDXWHU.rank_range STRTOD_SCR WD_SCR Rr IS rep.
Let rank_in := @RDXWHU.rank_in .
Let rank_nin := @RDXWHU.rank_nin .
Let wp_setwin := @RDXWHU.wp_setwin .
Let we_setwin := @RDXWHU.we_setwin .
Let more_setwin := @RDXWHU.more_setwin .
Let st_setwin := @RDXWHU.st_setwin .
Let b2z_range := @RDXWHU.b2z_range STRTOD_SCR WD_SCR Rr IS rep.
Let b2z_nz := @RDXWHU.b2z_nz .
Let ginvU := @RDXWUB.ginvU L HI STRTOD_SCR WD_SCR LBo sp Rr IS V E S2 ch kx bx rep g0 M0 model0.
Hypothesis CONTU : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
  PML.fp_ok fx' ->
  PML.source_at M' Rr ch -> PML.parser_at M' (Rr + 320) ps' -> PML.isrc_at M' IS rep gp' rdst' -> PML.ec_at M' E code -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.LS2 /\ code <> 0)) ->
  PMES.enc_inv M' V S2 eg' -> PML.lits_ok M' ->
  PML.pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') -> PML.wf_ps ps' ->
  wfin eg' code ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp SS (RIXW.Wr Rr IS V E S2) M0 M' -> model_but_vm model0 model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg') cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Let finishU := @RDXWUB.finishU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 CONTU.
Let rd_after_stmtU := @RDXWUB.rd_after_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let rn_entry_stmtU := @RDXWUB.rn_entry_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let rn_regsU := @RDXWUB.rn_regsU sp Rr E R0.
Let rn_frU := @RDXWUB.rn_frU sp r R0.
Let rn_exit_stmtU := @RDXWUB.rn_exit_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let setec_stmtU := @RDXWUB.setec_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let ws1_stmtU := @RDXWUB.ws1_stmtU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let atAU := @RDXWUB.atAU SCFG_P L HI STRTOD_SCR WD_SCR LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0.
Let r1ok := @RDXWUB.r1ok Rr E R0.

Local Ltac kinX := vm_compute; repeat first [left; reflexivity | right].

(* Loop B invariant at LOOPB (READ_NEXT body, sp - 96; R1 = registers at READ_NEXT entry), measure muB. *)
Definition atBU (R1 : bvmap 5 word) (m : Z) : Prop := forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  muB gp rdst < m -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvB M ps gp rdst bof eg ->
  (PML.ps_more ps = true -> rdst = 2) -> rn_regsU R -> rn_frU R1 M ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPB M model) K.

(* Reader state after the skip_ws of loop B (rdst = 0): the window of ps holds the skip_whitespace result of (c, w). *)
Definition rinvW (M : mem) (ps : PML.pstate) (gp : Z) (bof : bool) (eg : PMES.eghost) : Prop :=
  exists tA c w F', PMR.rloop (PMR.rfuel (PML.srep_chars rep)) (PMRR.rs0 (PML.srep_chars rep)) = tA /\ PMRR.t_code tA = 0 /\
    egacc eg (PMRR.t_evs tA) (PMRR.t_al tA) /\ wst M ps (fst (PMR.skip_whitespace c w)) (snd (PMR.skip_whitespace c w)) /\
    PMR.rtail (PMR.rfuel (PML.srep_chars rep)) (PMR.sw (PMRR.t_rs tA)) = PMR.rtail F' (rsof c w gp bof 0) /\
    PMRR.nchunks (rsof c w gp bof 0) + 1 <= Z.of_nat F'.

(* At RN_R_WS2 (after the skip_ws of loop B). *)
Definition ws2U (R1 : bvmap 5 word) (m : Z) : Prop := forall (fx : FPState) R M model cr ps gp bof B eg,
  muB gp 0 < m -> PML.fp_ok fx -> ginvU M model cr ps gp 0 0 bof g0 B eg -> rinvW M ps gp bof eg -> PML.ps_more ps = false ->
  rn_regsU R -> rn_frU R1 M -> srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_WS2 M model) K.

Lemma KS06_cs : forall q, In q RS.KS06 -> In (Z.of_nat q) callee_saved_idx.
Proof.
  intros q Hq. unfold RS.KS06 in Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<-|Hq]; [kinX|]); destruct Hq.
Qed.

Lemma rn_regs_pres : forall R R' : bvmap 5 word, rn_regsU R -> regs_preserved R R' -> rn_regsU R'.
Proof.
  intros R R' (H2 & H8 & H9 & H18 & H6) RP.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - rewrite (RP 2%bv ltac:(kinX)). exact H2.
  - rewrite (RP 8%bv ltac:(kinX)). exact H8.
  - rewrite (RP 9%bv ltac:(kinX)). exact H9.
  - rewrite (RP 18%bv ltac:(kinX)). exact H18.
  - apply (TK.keepsR_trans _ _ _ _ H6). exact (TK.keepsR_preserved _ _ _ RP KS06_cs).
Qed.

Lemma rn_regs_ksa : forall R R' : bvmap 5 word, rn_regsU R -> TK.keepsR RS.KSA R R' -> getr R' 2%bv = Z_to_bv 64 (sp - 96) -> rn_regsU R'.
Proof.
  intros R R' (H2 & H8 & H9 & H18 & H6) HK H2'.
  refine (conj H2' (conj _ (conj _ (conj _ _)))).
  - rewrite (HK 8%bv ltac:(kinX)). exact H8.
  - rewrite (HK 9%bv ltac:(kinX)). exact H9.
  - rewrite (HK 18%bv ltac:(kinX)). exact H18.
  - apply (TK.keepsR_trans _ _ _ _ H6). apply (i_keeps_sub _ _ _ _ HK).
    intros q Hq. unfold RS.KS06 in Hq. cbn [In] in Hq.
    repeat (destruct Hq as [<-|Hq]; [kinX|]); destruct Hq.
Qed.

Lemma rn_fr_x : forall R1 (M M' : mem) lo, TK.samem (fun a => lo <= a < sp) M M' -> lo <= sp - 96 -> rn_frU R1 M -> rn_frU R1 M'.
Proof.
  intros R1 M M' lo HS Hlo (HN & HF).
  pose proof SPOK as SP0. unfold RS.spok in SP0.
  split; [| exact (rd_frame_x M M' lo HS ltac:(lia) HF)].
  destruct HN as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  unfold RS.rn_frame.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
    (eapply (TK.u64_samem _ M M' _ _ HS); [lia | intros i Hi; cbv beta; lia | eassumption]).
Qed.

(* ==== ws2_okU and its helpers (s-lib2): begin ==== *)
Lemma w2_mu : forall gp gp' rdst' m k, muB gp 0 < m + 1 -> gp <= gp' -> k <= gp' - gp -> (k = 0 -> rdst' = 2) -> 0 <= k -> muB gp' rdst' < m.
Proof.
  intros gp gp' rdst' m k Hmu H1 H2 H3 H4.
  cbv beta zeta delta [muB RDXWHU.muB] in Hmu |- *.
  assert (E0 : RDXWHU.ee 0 = 1) by reflexivity. rewrite E0 in Hmu.
  pose proof (ee_range rdst') as HE.
  destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
  - rewrite (H3 Hk0). assert (E2 : RDXWHU.ee 2 = 0) by reflexivity. rewrite E2. lia.
  - lia.
Qed.

Lemma w2_samem : forall M1 M2 : mem, TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M1 M2 -> TK.samem (fun a => sp - 96 <= a < sp) M1 M2.
Proof. intros M1 M2 HS a Ha Hin. pose proof lay as LY. apply HS; [exact Ha|]. cbv beta in Hin |- *. intros C. lia. Qed.

(* RN_R_WS2 leg of loop B: window left -> RN_EPI; window empty -> read_chunk, RN_R_CHUNKB, back to LOOPB at a smaller measure. *)
Lemma ws2_okU : forall R1, rn_exit_stmtU R1 -> forall m, atBU R1 m -> ws2U R1 (m + 1).
Proof.
  intros R1 HXT m IH fx R M model cr ps gp bof B eg Hmu Hfp GI HW Hm0 HR HF1.
  pose proof lay as LY. pose proof SPOK as SP0. unfold RS.spok in SP0.
  pose proof GI as GI'.
  destruct GI' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  destruct G11 as (Hh & Hl & _).
  pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp 0 0 bof g0 B eg GI) as
    (C240 & Cvt & C152w & C152 & Hrd & RO & C288 & C312 & C512 & C520 & Hwp & Hwe & CE & Hcode & D512 & C528 & C531 & C532 & Hgp).
  destruct (hfacts M model cr ps eg G10) as (_ & _ & _ & _ & HC0 & HC1 & _ & _ & (BR0 & _)).
  pose proof HR as (HR2 & HR8 & HR9 & HR18 & HK6).
  assert (SP32 : RS.spok (sp - 32)).
  { unfold RS.spok. split; [split; lia | apply i_al16; [exact (proj2 SP0) | reflexivity]]. }
  destruct HW as (tA & c & w & F' & E1 & E2 & E3 & E4 & E5 & E6).
  revert E4. destruct (PMR.skip_whitespace c w) as [c' w'] eqn:Esw. intros E4. cbn [fst snd] in E4.
  assert (SW : PMR.sw (rsof c w gp bof 0) = rsof c' w' gp bof 0) by exact (RKW.sw_rsof IS rep c w gp bof 0 c' w' Esw).
  destruct F' as [|F'']; [change (Z.of_nat 0) with 0 in E6; pose proof (PMRR.nchunks_nonneg (rsof c w gp bof 0)); lia |].
  refine (RS.s_rn_r_ws2 FPM fx R M model K (sp - 32) Rr (RB.wp ps) (RB.we ps) Hh Hl Hfp _ SP32 HR9 _ C512 C520 _ _ _ _).
  - rewrite HR2. f_equal. lia.
  - unfold RS.pok. lia.
  - lia.
  - lia.
  - intros Heq fx' R' Hfp' HR2' HRa' HR10' HR11' HKA.
    assert (HXe : PMS.win_exhausted ps) by exact (proj2 (RB.exhausted_iff ps) Heq).
    pose proof (wst_nil M ps c' w' E4 HXe) as Wn. subst w'.
    assert (HR2s : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite HR2'; f_equal; lia).
    assert (HR11e : getr R' 11%bv = Z_to_bv 64 E) by (rewrite HR11'; exact HR8).
    assert (Ww : PMR.r_w (PMR.sw (rsof c w gp bof 0)) = []) by (rewrite SW; reflexivity).
    refine (call_chunkw (bx + PMES.benc L eg) fx' R' M model cr ps gp 0 bof B eg (sp - 96) RT.RN_R_CHUNKB Hfp' GI HXe HRa' _ HR2s _ HR10' HR11e _ _ _ _).
    + apply ra_lit; unfold RT.RN_R_CHUNKB; [lia | reflexivity].
    + rewrite (HKA 4%bv ltac:(kinX)), (HK6 4%bv ltac:(kinX)). exact R0tp.
    + apply i_al16; [exact (proj2 SP0) | reflexivity].
    + first [lia | unfold SS in *; lia].
    + lia.
    + intros fx2 R2 M2 pc k gp' rdst' code' bof' g' Hfp2 HRP2 GI2 H102 H112 Hp0 Hpk Hk Hkch Hgp' Hkg Hc0 Hrd' H2b H0b HFB HGR HSM.
      pose proof (rn_regs_pres R' R2 (rn_regs_ksa R R' HR HKA HR2s) HRP2) as HR2r.
      pose proof HR2r as (HR22 & HR28 & HR29 & HR218 & HK62).
      assert (HF2 : rn_frU R1 M2) by exact (rn_fr_x R1 M M2 (sp - 96) HSM ltac:(lia) HF1).
      pose proof GI2 as GI2'.
      destruct GI2' as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & G9' & G10' & G11' & _).
      destruct G11' as (Hh2 & Hl2 & _).
      pose proof (gcells (bx + PMES.benc L eg) M2 model cr ps gp' rdst' code' bof' g' B eg GI2) as
        (C240' & Cvt' & C152w' & C152' & Hrd2 & RO' & C288' & C312' & C512' & C520' & Hwp' & Hwe' & CE' & Hcode' & D512' & C528' & C531' & C532' & Hgp2).
      destruct (chunk_post M2 c' gp 0 bof pc k gp' rdst' code' bof' Hgp (or_introl eq_refl) H2b H0b) as (w1 & Hrf & Hlw & Hbw & HFw & Hcw & Hnch).
      assert (WST2 : wst M2 ps c' []) by exact (wst_rchunk M M2 ps c' (sp - 96) E4 HXe HFB ltac:(lia) HC1).
      assert (Hrf' : PMR.refill (PMR.sw (rsof c w gp bof 0)) = (rsof c' w1 gp' bof' rdst', code')) by (rewrite SW; exact Hrf).
      assert (NB : PMRR.nchunks (rsof c' w1 gp' bof' rdst') + 1 <= Z.of_nat F'').
      { assert (N1 : PMRR.nchunks (rsof c' w1 gp' bof' rdst') <= PMRR.nchunks (rsof c w gp bof 0) - 1) by exact (Hnch eq_refl).
        rewrite Nat2Z.inj_succ in E6. lia. }
      refine (RS.s_rn_r_chunkB FPM fx2 R2 M2 model K (sp - 32) Rr E code' (RB.wp ps) (RB.we ps) pc k Hh2 Hl2 Hfp2 _ SP32 HR29 HR28 _ _ H102 H112 Hp0 ltac:(lia) ltac:(lia) _ CE' Hcode' C512' C520' ltac:(lia) ltac:(lia) D512' _ _ _).
      * rewrite HR22. f_equal. lia.
      * unfold RS.pok. lia.
      * unfold RS.pok. lia.
      * intros Hk0. destruct (Hkch ltac:(lia)) as (Q1 & Q2). unfold RS.pok. lia.
      * pose proof AP as (_ & _ & APE & _). destruct APE as [A1 | A1]; [left | right]; lia.
      * intros Hne fx3 R3 Hfp3 HR23 HK3.
        refine (HXT fx3 R3 M2 model cr ps gp' rdst' code' bof' g' B eg Hfp3 GI2 _ _ HF2).
        -- exists tA. split; [exact E1|]. split; [exact E3|]. right. split; [exact E2|].
           exists (rsof c' w1 gp' bof' rdst', code'). split.
           ++ rewrite E5. exact (PMRR.rtail_referr F'' (rsof c w gp bof 0) (rsof c' w1 gp' bof' rdst') code' eq_refl Ww Hrf' Hne).
           ++ left. split; [exact Hne | reflexivity].
        -- apply (rn_regs_ksa R2 R3 HR2r HK3). rewrite HR23. f_equal. lia.
      * intros Hz fx3 R3 M3 Hfp3 HR23 HK3 Hcase. subst code'.
        pose proof (ginv_g0 (bx + PMES.benc L eg) M2 model cr ps gp' rdst' bof' g' B eg GI2) as Eg. subst g'.
        assert (HR3 : rn_regsU R3) by (apply (rn_regs_ksa R2 R3 HR2r HK3); rewrite HR23; f_equal; lia).
        assert (Hrc : PMR.rtail (PMR.rfuel (PML.srep_chars rep)) (PMR.sw (PMRR.t_rs tA)) = PMR.rtail F'' (rsof c' w1 gp' bof' rdst')).
        { rewrite E5. exact (PMRR.rtail_cont F'' (rsof c w gp bof 0) (rsof c' w1 gp' bof' rdst') eq_refl Ww Hrf'). }
        destruct Hcase as [(Hk0 & ->) | (Hk0 & W512 & W520 & HSM3 & HGR3)].
        -- pose proof (Hc0 eq_refl Hk0) as Hr2. subst rdst'.
           destruct w1 as [|b1 w1]; [| cbn [length] in Hlw; lia].
           refine (IH fx3 R3 M2 model cr ps gp' 2 bof' B eg _ Hfp3 GI2 _ _ HR3 HF2).
           ++ apply (w2_mu gp gp' 2 m k Hmu Hgp' Hkg (fun _ => eq_refl)). lia.
           ++ exists tA, c', [], F''. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact WST2|]. split; [exact Hrc | exact NB].
           ++ intros _. reflexivity.
        -- destruct (Hkch ltac:(lia)) as (Q1 & Q2).
           destruct (i_ginv_setwin (bx + PMES.benc L eg) M2 M3 model cr ps gp' rdst' bof' g0 B eg pc k GI2 HXe HSM3 HGR3 W512 W520 ltac:(lia) Q1 Q2 ltac:(lia)) as (GI3 & _).
           assert (WST3 : wst M3 (PML.ps_set_win ps (Some (pc, pc + k))) c' w1).
           { apply (wst_setwin M2 M3 ps c' w1 pc k WST2 HSM3 (Hbw ltac:(lia)) Hlw HFw); lia. }
           assert (HF3 : rn_frU R1 M3) by exact (rn_fr_x R1 M2 M3 (sp - 96) (w2_samem M2 M3 HSM3) ltac:(lia) HF2).
           refine (IH fx3 R3 M3 model cr (PML.ps_set_win ps (Some (pc, pc + k))) gp' rdst' bof' (B + k) eg _ Hfp3 GI3 _ _ HR3 HF3).
           ++ apply (w2_mu gp gp' rdst' m k Hmu Hgp' Hkg (fun E0 => match Hk0 E0 with end)). lia.
           ++ exists tA, c', w1, F''. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact WST3|]. split; [exact Hrc | exact NB].
           ++ rewrite more_setwin, Hm0. intros Hm. discriminate Hm.
  - intros Hne fx' R' Hfp' HR2' HKA.
    assert (HNX : ~ PMS.win_exhausted ps) by (intros HXe; exact (Hne (proj1 (RB.exhausted_iff ps) HXe))).
    pose proof (wst_cons M ps c' w' E4 HNX) as Wne0.
    assert (Wne : PMR.r_w (PMR.sw (rsof c w gp bof 0)) <> []) by (rewrite SW; exact Wne0).
    refine (HXT fx' R' M model cr ps gp 0 0 bof g0 B eg Hfp' GI _ _ HF1).
    + exists tA. split; [exact E1|]. split; [exact E3|]. right. split; [exact E2|].
      exists (rsof c' w' gp bof 0, 0). split.
      * rewrite E5, (rtail_break' F'' (rsof c w gp bof 0) eq_refl Wne). rewrite SW. reflexivity.
      * right. split; [reflexivity|]. split; [reflexivity|]. exists c', w'. split; [exact E4 | reflexivity].
    + apply (rn_regs_ksa R R' HR HKA). rewrite HR2'. f_equal. lia.
Qed.
(* ==== ws2_okU and its helpers (s-lib2): end ==== *)

Lemma fuelB_S : forall z (F : nat), 0 <= z -> z + 1 <= Z.of_nat F -> exists F'', F = S F''.
Proof. intros z F H1 H2. destruct F as [|F'']; [cbn in H2; lia | exists F''; reflexivity]. Qed.

Lemma muB_nonneg : forall M model cr ps gp rdst code bof g B eg, ginvU M model cr ps gp rdst code bof g B eg -> 0 <= muB gp rdst.
Proof.
  intros M model cr ps gp rdst code bof g B eg GI.
  pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp rdst code bof g B eg GI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgp).
  pose proof (ee_range rdst) as HE.
  cbv beta zeta delta [muB RDXWHU.muB]. lia.
Qed.

Lemma loopB_stepU : forall R1, rn_exit_stmtU R1 -> forall m, atBU R1 m -> atBU R1 (m + 1).
Proof.
  intros R1 HX m IH fx R M model cr ps gp rdst bof B eg Hmu Hfp GI HBi Hmore HR HF1.
  pose proof lay as LY. pose proof layx as LX. pose proof SPOK as SP0. unfold RS.spok in SP0.
  pose proof GI as GI'.
  destruct GI' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  destruct G11 as (Hh & Hl & _).
  pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp rdst 0 bof g0 B eg GI) as
    (C240 & Cvt & C152w & C152 & Hrd & RO & C288 & C312 & C512 & C520 & Hwp & Hwe & CE & Hcode & D512 & C528 & C531 & C532 & Hgp).
  pose proof HR as (HR2 & HR8 & HR9 & HR18 & HK6).
  assert (SP32 : RS.spok (sp - 32)).
  { unfold RS.spok. split; [split; lia | apply i_al16; [exact (proj2 SP0) | reflexivity]]. }
  refine (RS.s_loopB FPM fx R M model K (sp - 32) Rr IS rdst Hh Hl Hfp _ SP32 HR9 _ _ _ RO C288 C240 Cvt C152 _ _ _).
  - rewrite HR2. f_equal. lia.
  - unfold RS.pok. lia.
  - unfold RS.pok. lia.
  - exact (proj2 (proj2 OI)).
  - destruct Hrd as [-> | ->]; lia.
  - (* rdst = 0: skip_ws, return to RN_R_WS2 *)
    intros Hz fx' R' Hfp' HR2' HRa' HR10' HKA.
    pose proof (proj1 (land2 rdst Hrd) Hz) as Hr0. subst rdst.
    assert (HR2s : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite HR2'; f_equal; lia).
    assert (Hm0 : PML.ps_more ps = false).
    { destruct (PML.ps_more ps) eqn:E0; [exfalso; pose proof (Hmore eq_refl); lia | reflexivity]. }
    destruct HBi as (tA & c & w & F' & E1 & E2 & E3 & E4 & E5 & E6).
    pose proof SKIPWSW as SW. unfold PMW.skip_whitespace_specw in SW.
    refine (call_ptransw (bx + PMES.benc L eg) _ _ _ _ _ SW fx' R' M model cr ps gp 0 bof B eg (sp - 96) RT.RN_R_WS2 c w Hfp' GI E4 HRa' _ HR2s _ _ _ _ _ _ _ _).
    + apply ra_lit; unfold RT.RN_R_WS2; [lia | reflexivity].
    + rewrite (HKA 4%bv ltac:(kinX)), (HK6 4%bv ltac:(kinX)). exact R0tp.
    + apply i_al16; [exact (proj2 SP0) | reflexivity].
    + unfold SS in *. unfold PMS.SKIPWS_SCR. lia.
    + lia.
    + unfold PMS.SKIPWS_SCR. lia.
    + refine (conj (eq_trans HR10' HR18) (conj _ _)).
      * exact (ginv_ws (bx + PMES.benc L eg) M model cr ps gp 0 bof g0 B eg GI).
      * intros Hm. rewrite Hm0 in Hm. discriminate Hm.
    + intros ps' code' R'' (_ & _ & _ & Hws) _. exact Hws.
    + intros fx'' R'' M' model' cr' ps' code' g' Hfp'' RP GI2 _ (Hc0 & _ & Hm' & _) (_ & _ & HW) SAM.
      subst code'.
      pose proof (ginv_g0 (bx + PMES.benc L eg) M' model' cr' ps' gp 0 bof g' B eg GI2) as Hg. subst g'.
      specialize (HW eq_refl). rewrite RKW.ctrl_sws, RKW.after_sws in HW.
      refine (ws2_okU R1 HX m IH fx'' R'' M' model' cr' ps' gp bof B eg Hmu Hfp'' GI2 _ _ _ _).
      * exists tA, c, w, F'. exact (conj E1 (conj E2 (conj E3 (conj HW (conj E5 E6))))).
      * rewrite Hm'. exact Hm0.
      * exact (rn_regs_pres R' R'' (rn_regs_ksa R R' HR HKA HR2s) RP).
      * exact (rn_fr_x R1 M M' (sp - 96) SAM ltac:(lia) HF1).
  - (* rdst = 2: RN_EPI *)
    intros Hnz fx' R' Hfp' HR2' HKA.
    assert (Hr2 : rdst = 2) by (destruct Hrd as [-> | ->]; [exfalso; apply Hnz; reflexivity | reflexivity]). subst rdst.
    refine (HX fx' R' M model cr ps gp 2 0 bof g0 B eg Hfp' GI _ _ HF1).
    + destruct HBi as (tA & c & w & F' & E1 & E2 & E3 & E4 & E5 & E6).
      destruct (fuelB_S _ _ (PMRR.nchunks_nonneg _) E6) as [F'' ->].
      exists tA. split; [exact E1|]. split; [exact E3|]. right. split; [exact E2|].
      exists (rsof c w gp bof 2, 0). split.
      * rewrite E5. apply PMRR.rtail_eof. reflexivity.
      * right. split; [reflexivity|]. split; [reflexivity|]. exists c, w. split; [exact E4 | reflexivity].
    + apply (rn_regs_ksa R R' HR HKA). rewrite HR2'. f_equal. lia.
Qed.

Lemma loopB_allU : forall R1, rn_exit_stmtU R1 -> forall k : nat, atBU R1 (Z.of_nat k).
Proof.
  intros R1 HX k. induction k as [|k IH].
  - intros fx R M model cr ps gp rdst bof B eg Hmu Hfp GI. exfalso.
    pose proof (muB_nonneg M model cr ps gp rdst 0 bof g0 B eg GI). lia.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r. exact (loopB_stepU R1 HX _ IH).
Qed.

(* Loop B of READ_NEXT (skip_ws / read_chunk at LOOPB, ubsan): deliver ws1_okU. *)
Lemma ws1_okU : (forall R1, r1ok R1 -> rn_exit_stmtU R1) -> forall R1, r1ok R1 -> ws1_stmtU R1.
Proof using All.
  intros HXA R1 Hr1 fx R M model cr ps gp rdst bof B eg Hfp GI HB0 Hmore HR HF1 HRa HR10.
  pose proof lay as LY. pose proof layx as LX. pose proof SPOK as SP0. unfold RS.spok in SP0.
  pose proof HR as (HR2 & HR8 & HR9 & HR18 & HK6).
  pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp rdst 0 bof g0 B eg GI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgp).
  destruct HB0 as (tA & c & w & E1 & E2 & E3 & E4 & E5).
  pose proof SKIPWSW as SW. unfold PMW.skip_whitespace_specw in SW.
  refine (call_ptransw (bx + PMES.benc L eg) _ _ _ _ _ SW fx R M model cr ps gp rdst bof B eg (sp - 96) RT.LOOPB c w Hfp GI E4 HRa _ HR2 _ _ _ _ _ _ _ _).
  - apply ra_lit; unfold RT.LOOPB; [lia | reflexivity].
  - rewrite (HK6 4%bv ltac:(kinX)). exact R0tp.
  - apply i_al16; [exact (proj2 SP0) | reflexivity].
  - unfold SS in *. unfold PMS.SKIPWS_SCR. lia.
  - lia.
  - unfold PMS.SKIPWS_SCR. lia.
  - refine (conj HR10 (conj _ _)).
    + exact (ginv_ws (bx + PMES.benc L eg) M model cr ps gp rdst bof g0 B eg GI).
    + intros Hm. exact (proj1 (Hmore Hm)).
  - intros ps' code' R' (_ & _ & _ & Hws) _. exact Hws.
  - intros fx' R' M' model' cr' ps' code' g' Hfp' RP GI2 _ (Hc0 & _ & Hm' & _) (_ & _ & HW) SAM.
    subst code'.
    pose proof (ginv_g0 (bx + PMES.benc L eg) M' model' cr' ps' gp rdst bof g' B eg GI2) as Hg. subst g'.
    specialize (HW eq_refl). rewrite RKW.ctrl_sws, RKW.after_sws in HW.
    pose proof (muB_nonneg M model cr ps gp rdst 0 bof g0 B eg GI) as HM0.
    refine (loopB_allU R1 (HXA R1 Hr1) (Z.to_nat (muB gp rdst + 1)) fx' R' M' model' cr' ps' gp rdst bof B eg _ Hfp' GI2 _ _ _ _).
    + rewrite Z2Nat.id by lia. lia.
    + exists tA, (fst (PMR.skip_whitespace c w)), (snd (PMR.skip_whitespace c w)), (PMR.rfuel (PML.srep_chars rep)).
      refine (conj E1 (conj E2 (conj E3 (conj HW (conj _ _))))).
      * rewrite E5. exact (f_equal (PMR.rtail (PMR.rfuel (PML.srep_chars rep))) (RKW.sw_rsof IS rep c w gp bof rdst _ _ (surjective_pairing _))).
      * pose proof (RKW.rfuel_ge IS rep (fst (PMR.skip_whitespace c w)) (snd (PMR.skip_whitespace c w)) gp bof rdst Hgp) as RF.
        unfold rsof, RDXWHU.rsof in *. lia.
    + intros Hm. rewrite Hm' in Hm. exact (proj2 (Hmore Hm)).
    + exact (rn_regs_pres R R' HR RP).
    + exact (rn_fr_x R1 M M' (sp - 96) SAM ltac:(lia) HF1).
Qed.
End Run.
End H.
End RDXWUW.
