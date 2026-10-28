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

Module RDXWUA.
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

Lemma pcredit_x_anti : forall cr ps kk b b', 0 <= b' <= b -> PML.pcredit_x L cr ps kk b -> PML.pcredit_x L cr ps kk b'.
Proof. intros cr ps kk b b' Hb H. unfold PML.pcredit_x, PML.pcredit in *. cbn [fst snd] in *. lia. Qed.

Lemma ginv_reserve : forall b1 b2 M model cr ps gp rdst code bof g B eg,
  ginv b1 M model cr ps gp rdst code bof g B eg -> PML.pcredit_x L cr ps (kx + PMX.kenc L eg) b2 ->
  ginv b2 M model cr ps gp rdst code bof g B eg.
Proof. intros. unfold ginv, RDXWHU.ginv, RIXW.ginv in *. tauto. Qed.

Lemma objs_x_at : forall spc, spc <= sp -> PMX.objs_x L spc P V E S2.
Proof.
  intros spc Hs. pose proof lay as Hl.
  assert (HP : P = Rr + 320) by reflexivity.
  assert (OP : PML.obj_on_stack L sp P 272).
  { destruct OR as (o1 & o2 & o3). unfold PML.obj_on_stack. rewrite HP. split; [lia|]. split; [lia|].
    replace (Rr + 320) with (Rr + 40 * 8) by lia. rewrite Z_mod_plus_full. exact o3. }
  pose proof APX as (a1 & a2 & a3 & a4 & a5 & a6 & a7).
  unfold PMX.objs_x.
  split; [exact (oos spc P 272 OP Hs)|]. split; [exact (oos spc V PMES.ENC_SIZE OVX Hs)|].
  split; [exact (oos spc S2 24 OS2 Hs)|]. split; [exact (oos spc E 16 OE Hs)|].
  split; [unfold PML.apart in a2 |- *; rewrite HP; destruct a2; lia|].
  split; [unfold PML.apart in a3 |- *; rewrite HP; destruct a3; lia|].
  split; [pose proof AP as (_ & _ & b3 & _); unfold PML.apart in b3 |- *; rewrite HP; destruct b3; lia|].
  split; [exact a1|]. split; [exact a6 | exact a7].
Qed.

Lemma call_ptransxwU : forall f pc scr Args Rel, PMW.ptransxwU L HI PMR.the_rm f PMW.inp_win pc scr Args Rel ->
  forall (fx : FPState) R M model cr ps gp rdst bof B eg spc rc c w,
  PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> PML.win_ok M LBo ps -> PMX.enc_sync ps eg -> wst M ps c w ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm f c w) ->
  getr R 1%bv = Z_to_bv 64 rc -> L5.ra_ok rc -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  spc mod 16 = 0 -> sp - SS <= spc - scr -> spc <= sp -> 0 <= scr ->
  Args R M P V E ps [] -> (forall ps' code' R', Rel ps ps' code' R' -> code' = 0 -> PML.ws_ok ps') ->
  (forall (fx' : FPState) R' M' model' cr' ps' code' g' eg', PML.fp_ok fx' -> regs_preserved R R' ->
      ginvU M' model' cr' ps' gp rdst code' bof g' B eg' -> (code' <> 0 -> PML.ps_more ps' = false) -> Rel ps ps' code' R' ->
      PML.win_ok M' LBo ps' -> (code' = 0 -> PMX.enc_sync ps' eg') ->
      (let rr := PMW.rm_step PMR.the_rm f c w in
       code' = PMW.r_code rr /\ PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (PMW.r_evs rr) /\
       (exists pay, 0 <= pay <= PMW.r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMW.r_evs rr) + pay) /\
       (code' = 0 -> wst M' ps' (PMW.r_ctrl rr) (PMW.w_after PMR.the_rm rr w))) ->
      TK.samem (fun a => spc <= a < sp) M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rc M' model') K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R pc M model) K.
Proof.
  intros f pc scr Args Rel HSPEC fx R M model cr ps gp rdst bof B eg spc rc c w Hfp HG Hwin Hsync Hwst Hroom
    HR1 Hra HR2 HR4 Hal Hsc1 Hsc2 Hsc3 HArgs HRelws HK.
  unfold PMW.ptransxwU, PMW.ptrans_gxwU, PMW.ptrans_gbxwU in HSPEC.
  pose proof HG as HG0.
  unfold ginvU, RDXWUB.ginvU, RDXWHU.ginv, RIXW.ginv in HG.
  destruct HG as (Hrdr & Hpar & Hwfx & Hwin2 & Hisrc & Hvis & Hec & Hls & Hgg & Hheap & Hmok & Hmbv & Hpc & Hbb & HBgp
    & HFR & Hfoot & Henc & Hlits).
  destruct HFR as [_ HSTK].
  unfold wst, RDXWHU.wst in Hwst. destruct Hwst as [Hrm Hwb].
  unfold RIXW.wfx in Hwfx. destruct Hwfx as [Hwf _].
  pose proof lay as Hlay. pose proof layx as Hlayx.
  pose proof (EK.benc_nonneg L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) eg) as Hbe.
  assert (Hblk : TK2.blocks_ok L LBo).
  { assert (Hbig : TK2.blocks_ok L (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg)) by (eapply TK2.blocks_ok_heap; eauto).
    intros b0 Hb0. apply Hbig. apply in_or_app. right. apply in_or_app. left. exact Hb0. }
  assert (Hstk : L5C.stk (hl_sptop L) M spc scr) by exact (mk_stk M spc scr HSTK Hal Hsc1 Hsc2 Hsc3).
  apply (HSPEC LBo cr spc rc P V E S2 B kx bx g0 ps eg w [] c fx R M model K Hheap Hmok HK0 Hfp).
  - split; [exact (mk_entry R M spc rc scr HR1 Hra HR2 HR4 HSTK Hal Hsc1 Hsc2 Hsc3)|].
    split; [exact HArgs|]. split; [exact Hpar|]. split; [exact Hwf|]. split; [exact Hwin|]. split; [exact Hbb|].
    split; [exact Hvis|]. split; [exact Hec|]. split; [exact Hls|]. split; [exact G0|]. split; [exact Henc|].
    split; [exact Hlits|]. split; [exact Hsync|]. split; [exact KX0|]. split; [exact BX0|]. split; [exact Hpc|].
    split; [exact (objs_x_at spc Hsc2)|]. split; [exact Hwb|]. split; [exact Hrm | exact Hroom].
  - intros fx' R' M' model' LB' cr' LBk' W Hfp' Hpost Hrp Hhp Hmbv' Hheap'.
    destruct Hpost as (ps' & code' & g' & eg' & Hpa' & Hwf' & Hwin' & Hbb' & Hec' & Hmore' & Hls' & Hgg' & Henc' & Hlits'
      & Hsync' & HLB & HLBk & HW & Hpc' & HRel & Hrr).
    subst LB' LBk' W. cbv zeta in Hrr. cbn [PMW.inp_win] in Hrr.
    pose proof (EK.benc_nonneg L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) eg') as Hbe'.
    assert (Hg1 : ginv bx M model cr ps gp rdst 0 bof g0 B eg).
    { apply (ginv_reserve (bx + PMES.benc L eg)); [exact HG0|]. apply (pcredit_x_anti cr ps _ (bx + PMES.benc L eg)); [lia | exact Hpc]. }
    assert (Hg2 : ginv bx M' model' cr' ps' gp rdst code' bof g' B eg').
    { apply (ginv_ptrans bx M M' model model' cr cr' ps ps' gp rdst bof code' g' B eg spc scr eg' Hg1 Hhp Hsc1 Hsc2 Hsc3 Hal Hmbv' Hheap' Hpa' Hwf'
        (HRelws ps' code' R' HRel)
        (i_win_ok_mono M' LBo (LBo ++ PMES.g_lbv eg') ps' (fun b0 Hb0 => in_or_app _ _ _ (or_introl Hb0)) Hwin')
        Hbb' Hec' Hls' Hgg'); [|exact Henc' | exact Hlits'].
      apply (pcredit_x_anti cr' ps' _ (bx + PMES.benc L eg')); [lia | exact Hpc']. }
    destruct Hrr as (Hcode & Hes & Hpay & Hc0).
    apply (HK fx' R' M' model' cr' ps' code' g' eg' Hfp' Hrp); try assumption.
    + apply (ginv_reserve bx (bx + PMES.benc L eg')); [exact Hg2 | exact Hpc'].
    + cbv zeta. split; [exact Hcode|]. split; [exact Hes|]. split; [exact Hpay|].
      intros H0. destruct (Hc0 H0) as (Hm & _ & Hb). unfold wst, RDXWHU.wst. split; [exact Hm | exact Hb].
    + apply (TK.samem_weaken (TK2.keepH L LBo (PMX.W_parx P V E S2) spc scr)); [eapply TK2.hpres_samem; eauto|].
      intros a Ha. split; [|left; lia].
      assert (HP : P = Rr + 320) by reflexivity.
      destruct Hlay as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & _).
      destruct Hlayx as (x1 & x2 & x3 & _).
      unfold L5.outside, PMX.W_parx, PML.W_par, PMES.W_enc, L5.in_rng. intros r0 Hr0.
      cbn [app] in Hr0.
      repeat destruct Hr0 as [<-|Hr0]; cbn [fst snd];
        try (unfold PMES.O_STACK, PMES.O_DEPTH, PML.LIT_LO, PML.LIT_HI); try rewrite HP; try lia; try (exfalso; exact Hr0).
Qed.

Local Ltac inl := vm_compute; repeat (first [left; reflexivity | right]).

Lemma keeps06_call : forall R R', TK.keepsR RS.KS06 R0 R -> regs_preserved R R' -> TK.keepsR RS.KS06 R0 R'.
Proof.
  intros R R' Hk Hp r0 Hr0.
  pose proof (i_keeps_pres RS.KS06 R R' Hp) as Hk2.
  rewrite Hk2; [exact (Hk r0 Hr0) | | exact Hr0].
  intros q Hq. cbn in Hq. repeat destruct Hq as [<-|Hq]; try inl. destruct Hq.
Qed.

Lemma rn_frU_x : forall R1 M M', TK.samem (fun a => sp - 96 <= a < sp) M M' -> rn_frU R1 M -> rn_frU R1 M'.
Proof.
  intros R1 M M' Hs Hfr. unfold rn_frU, RDXWUB.rn_frU in *. destruct Hfr as [Hf Hd].
  pose proof SPOK as Hsp. unfold RS.spok in Hsp. split.
  - destruct Hf as (f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8). unfold RS.rn_frame.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
      eapply TK.u64_samem; first [exact Hs | lia | (intros i Hi; cbn beta; lia) | eassumption].
  - exact (rd_frame_x M M' (sp - 96) Hs ltac:(lia) Hd).
Qed.

Definition atAm (m : Z) (R1 : bvmap 5 word) : Prop := forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  muA ps gp rdst < m -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvA M ps gp rdst bof eg ->
  PML.win_ok M LBo ps -> PMX.enc_sync ps eg -> rn_regsU R -> getr R 19%bv = Z_to_bv 64 1 -> getr R 20%bv = Z_to_bv 64 2 ->
  getr R 10%bv = Z_to_bv 64 (PML.b2z (PML.ps_more ps)) -> rn_frU R1 M ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPA M model) K.

Lemma muA_pos : forall M model cr ps gp rdst code bof g B eg, ginvU M model cr ps gp rdst code bof g B eg -> 0 < muA ps gp rdst.
Proof.
  intros M model cr ps gp rdst code bof g B eg HG.
  pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp rdst code bof g B eg HG)
    as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HD).
  pose proof (ee_range rdst). pose proof (ww_range ps). pose proof (rank_range ps).
  unfold muA, RDXWHU.muA. cbv zeta. unfold ee, ww, rank, D, n in *. lia.
Qed.

Ltac w3_isZ n := lazymatch n with Zpos _ => idtac | Z0 => idtac end.
Ltac w3_plits := repeat match goal with
  | |- context [(2 ^ ?n)%Z] => w3_isZ n; let v := eval vm_compute in (2 ^ n)%Z in change (2 ^ n)%Z with v
  | H : context [(2 ^ ?n)%Z] |- _ => w3_isZ n; let v := eval vm_compute in (2 ^ n)%Z in change (2 ^ n)%Z with v in H
  end.
Ltac w3_inlist := vm_compute; repeat (first [left; reflexivity | right]).
Lemma w3_gmod : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg -> m_halted model = None /\ m_vm_lazy model = [].
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hh & Hl & _) & _). split; assumption. Qed.
Lemma w3_ks06_ksa : forall q, In q RS.KS06 -> In q RS.KSA.
Proof. intros q Hq. unfold RS.KS06, RS.KSA in *. cbn [In] in *. tauto. Qed.
Lemma w3_rn_keep : forall R R' : bvmap 5 word, rn_regsU R -> TK.keepsR RS.KSA R R' -> getr R' 2%bv = Z_to_bv 64 (sp - 96) -> rn_regsU R'.
Proof.
  intros R R' (H2 & H8 & H9 & H18 & HK) HA H2'.
  split; [exact H2'|]. split; [rewrite (HA 8%bv ltac:(w3_inlist)); exact H8|]. split; [rewrite (HA 9%bv ltac:(w3_inlist)); exact H9|].
  split; [rewrite (HA 18%bv ltac:(w3_inlist)); exact H18|].
  intros q Hq. rewrite (HA q (w3_ks06_ksa _ Hq)). exact (HK q Hq).
Qed.

Lemma w3_spok32 : RS.spok (sp - 32).
Proof.
  pose proof SPOK as Hsp. unfold RS.spok in Hsp. pose proof lay as Hlay. pose proof Htop as T0. pose proof Hceil as C0.
  unfold RS.spok. split; [lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact (proj2 Hsp).
Qed.
Lemma w3_al96 : (sp - 96) mod 16 = 0.
Proof. pose proof SPOK as Hsp. unfold RS.spok in Hsp. replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact (proj2 Hsp). Qed.
Lemma w3_exh_eq : forall ps, PMS.win_exhausted ps -> RB.wp ps = RB.we ps.
Proof. intros ps. unfold PMS.win_exhausted, RB.wp, RB.we. destruct (PML.ps_win ps) as [[p e]|]; auto. Qed.
Lemma w3_eq_exh : forall ps, RB.wp ps = RB.we ps -> PMS.win_exhausted ps.
Proof. intros ps. unfold PMS.win_exhausted, RB.wp, RB.we. destruct (PML.ps_win ps) as [[p e]|]; auto. Qed.
Lemma w3_gheap : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg ->
  hi_heap HI (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr M (m_vmmaps model).
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HH & _). exact HH. Qed.
Lemma w3_gB : forall b M model cr ps gp rdst code bof g B eg, ginv b M model cr ps gp rdst code bof g B eg -> B <= gp - D.
Proof. intros b M model cr ps gp rdst code bof g B eg GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB0 & _). exact HB0. Qed.
Lemma w3_ks06_cs : forall q : reg, In (ridx q) RS.KS06 -> In (bv_unsigned q) callee_saved_idx.
Proof.
  intros q Hq. pose proof (bv_unsigned_in_range _ q) as Rq. change (bv_modulus 5) with 32 in Rq.
  unfold ridx, RS.KS06 in Hq. unfold callee_saved_idx. cbn [In] in Hq |- *. lia.
Qed.
Lemma w3_rn_keepq : forall qs (R R' : bvmap 5 word), rn_regsU R -> TK.keepsR qs R R' ->
  In 8%nat qs -> In 9%nat qs -> In 18%nat qs -> (forall q, In q RS.KS06 -> In q qs) ->
  getr R' 2%bv = Z_to_bv 64 (sp - 96) -> rn_regsU R'.
Proof.
  intros qs R R' (H2 & H8 & H9 & H18 & HK) HA I8 I9 I18 I06 H2'.
  split; [exact H2'|]. split; [rewrite (HA 8%bv I8); exact H8|]. split; [rewrite (HA 9%bv I9); exact H9|].
  split; [rewrite (HA 18%bv I18); exact H18|].
  intros q Hq. rewrite (HA q (I06 _ Hq)). exact (HK q Hq).
Qed.
Lemma w3_rn_pres : forall R R' : bvmap 5 word, rn_regsU R -> regs_preserved R R' -> rn_regsU R'.
Proof.
  intros R R' (H2 & H8 & H9 & H18 & HK) HP.
  split; [rewrite (HP 2%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H2|].
  split; [rewrite (HP 8%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H8|].
  split; [rewrite (HP 9%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H9|].
  split; [rewrite (HP 18%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H18|].
  intros q Hq. rewrite (HP q (w3_ks06_cs q Hq)). exact (HK q Hq).
Qed.
Lemma w3_rnfr_x : forall R1 M M', TK.samem (fun a => sp - 96 <= a < sp) M M' -> rn_frU R1 M -> rn_frU R1 M'.
Proof.
  intros R1 M M' HS (HF & HD).
  pose proof lay as (LY0 & LY1 & LY2 & _). pose proof Hsptop as HT1. pose proof Htop as HT2.
  split.
  - unfold RS.rn_frame in *. destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    repeat split.
    all: (eapply (TK.u64_samem _ M M' _ _ HS); [ w3_plits; lia | intros i Hi; cbv beta; lia | eassumption ]).
  - apply (rd_frame_x M M' (sp - 96) HS); [lia | exact HD].
Qed.
Lemma w3_samem_win : forall M1 M2 : mem, TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M1 M2 -> TK.samem (fun a => sp - 96 <= a < sp) M1 M2.
Proof. intros M1 M2 HS a Ha Hin. pose proof lay as (_ & _ & LY2 & _). apply HS; [exact Ha|]. cbv beta in Hin |- *. intros C. lia. Qed.
Lemma w3_rinvB0_of_A : forall M ps gp rdst bof eg, rinvA M ps gp rdst bof eg -> PML.ps_more ps = false -> rinvB0 M ps gp rdst bof eg.
Proof.
  intros M ps gp rdst bof eg (c & w & evs & al & F' & Hw & He & Ha) Hm.
  pose proof (wst_core M ps c w Hw) as (_ & Hcm & _).
  unfold rinvB0, RDXWHU.rinvB0.
  exists (PMRR.rpre evs al (rsof c w gp bof rdst, [], 0, 0)), c, w.
  split; [eapply (RKW.accA_end IS); [exact Ha | intros F'' ->; apply PMRR.rloop_stopped; unfold rsof, RDXWHU.rsof; rewrite RKW.r_c_rsof, Hcm; exact Hm] |].
  cbn [PMRR.rpre PMRR.t_code PMRR.t_evs PMRR.t_al PMRR.t_rs fst snd].
  split; [reflexivity|]. split; [rewrite app_nil_r, Z.add_0_r; exact He|]. split; [exact Hw | reflexivity].
Qed.

Lemma w3_ww_exh : forall ps, PMS.win_exhausted ps -> RDXWHU.ww ps = 0.
Proof. intros ps HX. unfold RDXWHU.ww. rewrite (w3_exh_eq ps HX), Z.eqb_refl. reflexivity. Qed.
Lemma w3_ww_ne : forall ps, RB.wp ps <> RB.we ps -> RDXWHU.ww ps = 1.
Proof. intros ps Hne. unfold RDXWHU.ww. destruct (Z.eqb_spec (RB.wp ps) (RB.we ps)); [contradiction | reflexivity]. Qed.
Lemma w3_muA_k0 : forall ps gp rdst gp', gp <= gp' -> muA ps gp' 2 <= muA ps gp rdst.
Proof.
  intros ps gp rdst gp' Hg. unfold muA, RDXWHU.muA. cbv zeta. unfold RDXWHU.ee. rewrite Z.eqb_refl.
  destruct (Z.eqb rdst 2); lia.
Qed.
Lemma w3_muA_k1 : forall ps gp gp' rdst' pc k, gp + k <= gp' -> 0 < k -> PMS.win_exhausted ps ->
  muA (PML.ps_set_win ps (Some (pc, pc + k))) gp' rdst' + 1 <= muA ps gp 0.
Proof.
  intros ps gp gp' rdst' pc k Hg Hk HX. unfold muA, RDXWHU.muA. cbv zeta.
  rewrite (w3_ww_exh ps HX), (w3_ww_ne (PML.ps_set_win ps (Some (pc, pc + k)))) by (rewrite wp_setwin, we_setwin; lia).
  unfold RDXWHU.rank. rewrite st_setwin. unfold RDXWHU.ee. cbn [Z.eqb].
  destruct (Z.eqb rdst' 2); lia.
Qed.
Lemma w3_ks06_ksw : forall q, In q RS.KS06 -> In q RS.KSW.
Proof. intros q Hq. unfold RS.KS06, RS.KSW in *. cbn [In] in *. tauto. Qed.
Lemma w3_ks06_kp : forall q, In q RS.KS06 -> In q [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat.
Proof. intros q Hq. unfold RS.KS06 in *. cbn [In] in *. tauto. Qed.

Lemma loopA_done : forall R1, ws1_stmtU R1 ->
  forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvB0 M ps gp rdst bof eg -> PML.ps_more ps = false ->
  rn_regsU R -> getr R 19%bv = Z_to_bv 64 1 -> getr R 20%bv = Z_to_bv 64 2 -> getr R 10%bv = Z_to_bv 64 0 -> rn_frU R1 M ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPA M model) K.
Proof.
  intros R1 HW fx R M model cr ps gp rdst bof B eg Hfp GI HB0 Hmore HR H19 H20 H10 Hfr.
  destruct (w3_gmod _ _ _ _ _ _ _ _ _ _ _ _ GI) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GI) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  pose proof OR as (OR1 & OR2 & OR3).
  pose proof OV as (OV1 & OV2 & OV3).
  pose proof HR as (H2 & H8 & H9 & H18 & HK).
  refine (RS.s_loopA FPM fx R M model K (sp - 32) Rr V (RB.wp ps) (RB.we ps) 0 Hh Hl Hfp _ _ H9 _ G312 G512 G520 _ _ _ _ _ H10 _ _ _ _).
  all: try (rewrite H2; f_equal; lia).
  all: try exact w3_spok32.
  all: pose proof SPOK as SP1; unfold RS.spok, RS.pok in *.
  all: try (w3_plits; lia).
  all: lazymatch goal with
    | |- (Z.land 0 1 = 0 -> _) =>
        intros _ fx' R' Hfp' H2' H1' H10' HK';
        assert (H2'' : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite H2'; f_equal; lia);
        apply (HW fx' R' M model cr ps gp rdst bof B eg Hfp' GI HB0); [| exact (w3_rn_keep R R' HR HK' H2'') | exact Hfr | exact H1' | rewrite H10'; exact H18];
        intros E1; rewrite Hmore in E1; discriminate E1
    | |- (Z.land 0 1 <> 0 -> _) => intros C; exfalso; apply C; reflexivity
    | |- ?G => fail 100 "open goal" G
    end.
Qed.

Lemma muA_ret : forall ps ps' gp rdst, PMS.win_exhausted ps' ->
  (PMS.win_exhausted ps -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) ->
  muA ps' gp rdst < muA ps gp rdst.
Proof.
  intros ps ps' gp rdst He' Hr.
  pose proof (proj1 (RB.exhausted_iff ps') He') as E'.
  assert (W' : ww ps' = 0) by (unfold ww, RDXWHU.ww; rewrite E', Z.eqb_refl; reflexivity).
  destruct (Z.eq_dec (RB.wp ps) (RB.we ps)) as [E0|Hne].
  - pose proof (proj2 (RB.exhausted_iff ps) E0) as He.
    assert (W0 : ww ps = 0) by (unfold ww, RDXWHU.ww; rewrite E0, Z.eqb_refl; reflexivity).
    destruct (Hr He) as [I1 I2]. pose proof (rank_in ps I1) as K1. pose proof (rank_nin ps' I2) as K2.
    unfold muA, RDXWHU.muA. cbv zeta. unfold ww, rank in *. lia.
  - assert (He : ~ PMS.win_exhausted ps) by (intros X; apply Hne; exact (proj1 (RB.exhausted_iff ps) X)).
    assert (W0 : ww ps = 1).
    { unfold ww, RDXWHU.ww. destruct (Z.eqb_spec (RB.wp ps) (RB.we ps)) as [E0|E0];
        [exfalso; apply He; apply RB.exhausted_iff; exact E0 | reflexivity]. }
    pose proof (rank_range ps). pose proof (rank_range ps').
    unfold muA, RDXWHU.muA. cbv zeta. unfold ww, rank in *. lia.
Qed.

Lemma regsU_after : forall R' R'' qs, getr R' 8%bv = Z_to_bv 64 E -> getr R' 9%bv = Z_to_bv 64 Rr ->
  getr R' 18%bv = Z_to_bv 64 (Rr + 320) -> TK.keepsR RS.KS06 R0 R' -> TK.keepsR qs R' R'' ->
  (forall q, In q (8 :: 9 :: 18 :: RS.KS06)%nat -> In q qs) -> getr R'' 2%bv = Z_to_bv 64 (sp - 96) -> rn_regsU R''.
Proof.
  intros R' R'' qs H8 H9 H18 Hk Hk' Hsub H2. unfold rn_regsU, RDXWUB.rn_regsU.
  split; [exact H2|].
  split; [rewrite (Hk' 8%bv); [exact H8 | apply Hsub; inl]|].
  split; [rewrite (Hk' 9%bv); [exact H9 | apply Hsub; inl]|].
  split; [rewrite (Hk' 18%bv); [exact H18 | apply Hsub; inl]|].
  intros r0 Hr0. rewrite (Hk' r0); [exact (Hk r0 Hr0) | apply Hsub; right; right; right; exact Hr0].
Qed.

Lemma keeps_combine : forall qa qb qs Ra Rb Rc, TK.keepsR qa Ra Rc -> TK.keepsR qa R0 Ra -> TK.keepsR qb Rb Rc ->
  TK.keepsR qb R0 Rb -> (forall q, In q qs -> In q qa \/ In q qb) -> TK.keepsR qs R0 Rc.
Proof.
  intros qa qb qs Ra Rb Rc H1 H2 H3 H4 Hs r0 Hr0.
  destruct (Hs _ Hr0) as [Ha|Hb]; [rewrite (H1 r0 Ha); exact (H2 r0 Ha) | rewrite (H3 r0 Hb); exact (H4 r0 Hb)].
Qed.

Lemma psome_ret : forall m R1, r1ok R1 -> rn_exit_stmtU R1 -> ws1_stmtU R1 -> setec_stmtU -> atAm m R1 ->
  forall ps gp rdst bof B eg (c : PMR.ctrl) w evs al F' w0 gp0 bof0 rdst0 (R : bvmap 5 word) (M : mem)
    (fx' : FPState) R' M' model' cr' ps' code' g' eg',
  muA ps gp rdst <= m -> PML.ps_more ps = true -> (PMS.win_exhausted ps -> rdst = 2) ->
  egacc eg evs al -> RKW.accA rep evs al F' (rsof c w0 gp0 bof0 rdst0) ->
  PMR.refill (rsof c w0 gp0 bof0 rdst0) = (rsof c w gp bof rdst, 0) -> wst M ps c w ->
  0 <= RB.wp ps /\ RB.wp ps <= RB.we ps /\ RB.we ps < 2 ^ 62 ->
  getr R 2%bv = Z_to_bv 64 (sp - 96) -> getr R 8%bv = Z_to_bv 64 E -> getr R 9%bv = Z_to_bv 64 Rr ->
  getr R 18%bv = Z_to_bv 64 (Rr + 320) -> getr R 19%bv = Z_to_bv 64 1 -> getr R 20%bv = Z_to_bv 64 2 ->
  getr R 22%bv = Z_to_bv 64 (RB.wp ps) -> getr R 21%bv = Z_to_bv 64 (RB.we ps) ->
  TK.keepsR RS.KS06 R0 R -> rn_frU R1 M ->
  PML.fp_ok fx' -> regs_preserved R R' -> ginvU M' model' cr' ps' gp rdst code' bof g' B eg' ->
  (code' <> 0 -> PML.ps_more ps' = false) ->
  (code' <> 0 \/ PML.ps_more ps' = false \/ PMS.win_exhausted ps') ->
  (PML.ps_st ps = PML.ST_ACCEPT -> code' = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) ->
  (PMS.win_exhausted ps -> code' = 0 -> PML.ps_more ps' = true ->
     In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) ->
  PML.win_ok M' LBo ps' -> (code' = 0 -> PMX.enc_sync ps' eg') ->
  code' = PMR.q_code (PMR.parse_some c w) -> PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (PMR.q_evs (PMR.parse_some c w)) ->
  (exists pay, 0 <= pay <= PMR.q_al (PMR.parse_some c w) /\
     PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMR.q_evs (PMR.parse_some c w)) + pay) ->
  (code' = 0 -> wst M' ps' (PMR.q_c (PMR.parse_some c w)) (PMR.q_w (PMR.parse_some c w))) ->
  TK.samem (fun a => sp - 96 <= a < sp) M M' ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_R_PSOME M' model') K.
Proof.
  intros m R1 Hr Hx Hw Hs HA ps gp rdst bof B eg c w evs al F' w0 gp0 bof0 rdst0 R M fx' R' M' model' cr' ps' code' g' eg'
    Hmu Hmore Hexh Hacc HaccA Hrf Hwst Hwpe H2 H8 H9 H18 H19 H20 H22 H21 Hks Hfr Hfp' Hrp HG' Hmore' Hr1 Hr2 Hr3 Hwin' Hsync'
    Hcode Hes' Hpay' Hc0 Hsam.
  set (q := PMR.parse_some c w) in *.
  assert (Hpr : forall r0 : bv 5, In (bv_unsigned r0) callee_saved_idx -> getr R' r0 = getr R r0) by exact Hrp.
  assert (R'2 : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite Hpr; [exact H2 | inl]).
  assert (R'8 : getr R' 8%bv = Z_to_bv 64 E) by (rewrite Hpr; [exact H8 | inl]).
  assert (R'9 : getr R' 9%bv = Z_to_bv 64 Rr) by (rewrite Hpr; [exact H9 | inl]).
  assert (R'18 : getr R' 18%bv = Z_to_bv 64 (Rr + 320)) by (rewrite Hpr; [exact H18 | inl]).
  assert (R'19 : getr R' 19%bv = Z_to_bv 64 1) by (rewrite Hpr; [exact H19 | inl]).
  assert (R'20 : getr R' 20%bv = Z_to_bv 64 2) by (rewrite Hpr; [exact H20 | inl]).
  assert (R'22 : getr R' 22%bv = Z_to_bv 64 (RB.wp ps)) by (rewrite Hpr; [exact H22 | inl]).
  assert (R'21 : getr R' 21%bv = Z_to_bv 64 (RB.we ps)) by (rewrite Hpr; [exact H21 | inl]).
  pose proof (keeps06_call R R' Hks Hrp) as Hks'.
  pose proof (rn_frU_x R1 M M' Hsam Hfr) as Hfr'.
  pose proof (gcells (bx + PMES.benc L eg') M' model' cr' ps' gp rdst code' bof g' B eg' HG')
    as (_ & _ & _ & _ & Hrd & _ & _ & _ & _ & _ & _ & _ & Hec' & Hcr' & _ & Hst' & Hmo' & Hdn' & _).
  pose proof SPOK as Hsp. unfold RS.spok in Hsp. pose proof lay as Hlay.
  pose proof HG' as HGm. unfold ginvU, RDXWUB.ginvU, RDXWHU.ginv, RIXW.ginv in HGm.
  destruct HGm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmok' & _). destruct Hmok' as (Hhalt & Hlazy & _).
  pose proof Hfr' as Hfr1. unfold rn_frU, RDXWUB.rn_frU in Hfr1. destruct Hfr1 as [Hrnf Hrdf].
  assert (Hcm0 : PMR.c_more (PMR.r_c (rsof c w0 gp0 bof0 rdst0)) = true).
  { pose proof (wst_core M ps c w Hwst) as (_ & Hcm & _). unfold rsof, RDXWHU.rsof. rewrite RKW.r_c_rsof. rewrite Hcm. exact Hmore. }
  assert (Hpq : PMR.parse_some (PMR.r_c (rsof c w gp bof rdst)) (PMR.r_w (rsof c w gp bof rdst)) = q).
  { unfold rsof, RDXWHU.rsof. rewrite RKW.r_c_rsof, RKW.r_w_rsof. reflexivity. }
  apply (RSW.s_rn_r_psomew FPM fx' R' M' model' K (sp - 32) Rr E code' (PML.ps_st ps' mod 256) (PML.b2z (PML.ps_done ps'))
           (PML.b2z (PML.ps_more ps')) (RB.wp ps) (RB.we ps) RT.RD_R_NEXT R1).
  - exact Hhalt.
  - exact Hlazy.
  - exact Hfp'.
  - rewrite R'2. f_equal. lia.
  - unfold RS.spok. split; [lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact (proj2 Hsp).
  - exact R'9.
  - exact R'8.
  - unfold RS.pok. lia.
  - unfold RS.pok. lia.
  - exact R'19.
  - exact R'20.
  - exact R'22.
  - exact R'21.
  - lia.
  - lia.
  - exact Hec'.
  - exact Hcr'.
  - exact Hst'.
  - exact Hdn'.
  - exact Hmo'.
  - pose proof (Z.mod_pos_bound (PML.ps_st ps') 256 ltac:(lia)). lia.
  - destruct (PML.ps_done ps'); cbn; lia.
  - destruct (PML.ps_more ps'); cbn; lia.
  - exact Hrnf.
  - unfold RT.RD_R_NEXT. lia.
  - (* LOOPB *) intros Hc0z [Hpe Hst1] fx'' R'' Hfp'' H2'' H1'' H10'' H19'' H20'' Hk''.
    revert Hcode. subst code'. intros Hcode.
    assert (Hg0 : g' = g0) by (eapply ginv_g0; exact HG'). subst g'.
    assert (Hstm : PML.ps_st ps' mod 256 = PML.ps_st ps') by (eapply st_mod; exact HG').
    pose proof (proj2 (RB.exhausted_iff ps) Hpe) as Hex.
    pose proof (wst_nil M ps c w Hwst Hex) as Hw0.
    pose proof (Hc0 eq_refl) as Hc0'.
    pose proof (wst_core M' ps' (PMR.q_c q) (PMR.q_w q) Hc0') as (Hcst & Hcmo & Hcdn).
    assert (Hloop : PMR.rloop (PMR.rfuel (PML.srep_chars rep)) (PMRR.rs0 (PML.srep_chars rep)) =
       (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, 0)).
    { eapply RKW.roundA_stop with (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
      all: first [exact HaccA | exact Hcm0 | exact Hrf | exact Hpq | (symmetry; exact Hcode) | exact IS
                 | (left; split; [unfold rsof, RDXWHU.rsof; rewrite RKW.weof_rsof, Hw0; reflexivity
                                 | rewrite Hcst; unfold PML.ST_START; lia])]. }
    apply (Hw fx'' R'' M' model' cr' ps' gp rdst bof B eg' Hfp'' HG').
    + unfold rinvB0, RDXWHU.rinvB0. exists (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, 0), (PMR.q_c q), (PMR.q_w q).
      split; [exact Hloop|]. cbn [PMRR.t_evs PMRR.t_al PMRR.t_code PMRR.t_rs fst snd].
      split; [reflexivity|]. split; [eapply egacc_app; [exact Hacc | exact Hes' | exact Hpay']|].
      split; [exact Hc0'|]. unfold rsof, RDXWHU.rsof. rewrite RKW.rs_after_rsof. reflexivity.
    + intros Hm. split; [|exact (Hexh Hex)]. destruct Hr1 as [Hc|[Hc|Hc]]; [lia | congruence | exact Hc].
    + eapply regsU_after; [exact R'8 | exact R'9 | exact R'18 | exact Hks' | exact Hk'' | | rewrite H2''; f_equal; lia].
      intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try inl. destruct Hq0.
    + exact Hfr'.
    + exact H1''.
    + rewrite H10''. exact R'18.
  - (* LOOPA *) intros Hc0z Hcond fx'' R'' Hfp'' H2'' H10'' H19'' H20'' Hk''.
    revert Hcode. subst code'. intros Hcode.
    assert (Hg0 : g' = g0) by (eapply ginv_g0; exact HG'). subst g'.
    assert (Hstm : PML.ps_st ps' mod 256 = PML.ps_st ps') by (eapply st_mod; exact HG').
    pose proof (Hc0 eq_refl) as Hc0'.
    pose proof (wst_core M' ps' (PMR.q_c q) (PMR.q_w q) Hc0') as (Hcst & Hcmo & Hcdn).
    assert (Hregs : rn_regsU R'').
    { eapply regsU_after; [exact R'8 | exact R'9 | exact R'18 | exact Hks' | exact Hk'' | | rewrite H2''; f_equal; lia].
      intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try inl. destruct Hq0. }
    destruct (PML.ps_more ps') eqn:Hm'.
    + (* ps_more ps' = true: next round, by induction *)
      assert (Hex' : PMS.win_exhausted ps') by (destruct Hr1 as [Hc|[Hc|Hc]]; [lia | congruence | exact Hc]).
      pose proof (wst_nil M' ps' (PMR.q_c q) (PMR.q_w q) Hc0' Hex') as HwN.
      assert (Hrc : PMRR.rcont (rsof c w gp bof rdst) q).
      { unfold PMRR.rcont. destruct (Z.eq_dec (RB.wp ps) (RB.we ps)) as [Hpe|Hne].
        - destruct (Hcond Hpe) as [Hn1 Hor]. right. split.
          + rewrite Hcst. unfold PML.ST_START. lia.
          + destruct Hor as [H2'|Hd']; [left; rewrite Hcst; unfold PML.ST_ACCEPT; lia | right; rewrite Hcdn; apply b2z_t; exact Hd'].
        - assert (Hnex : ~ PMS.win_exhausted ps) by (intros X; apply Hne; exact (proj1 (RB.exhausted_iff ps) X)).
          left. apply weof_ne. exact (wst_cons M ps c w Hwst Hnex). }
      assert (Hrk : PMR.r_w (rsof c w0 gp0 bof0 rdst0) = [] -> PMR.r_eof (rsof c w0 gp0 bof0 rdst0) = true ->
                    PMRR.rankz (PMR.r_c (rsof c w0 gp0 bof0 rdst0)) = 1 /\ PMRR.rankz (PMR.q_c q) = 0).
      { intros Hw0' He0'. unfold rsof, RDXWHU.rsof in Hw0', He0' |- *. rewrite RKW.r_w_rsof in Hw0'. rewrite RKW.r_eof_rsof in He0'.
        rewrite RKW.r_c_rsof. apply Z.eqb_eq in He0'. subst rdst0.
        pose proof (refill_eof_w c w0 gp0 bof0 w gp bof rdst Hrf) as Hww. rewrite Hw0' in Hww. subst w.
        pose proof (exh_nil M ps c Hwst) as Hex. destruct (Hr3 Hex eq_refl ltac:(first [exact Hm' | reflexivity])) as [I1 I2].
        pose proof (wst_core M ps c [] Hwst) as (Hcs0 & _ & _).
        split; [exact (rankz_in c (PML.ps_st ps) Hcs0 I1) | exact (rankz_nin (PMR.q_c q) (PML.ps_st ps') Hcst I2)]. }
      assert (Hacc' : exists F'', RKW.accA rep (evs ++ PMR.q_evs q) (al + PMR.q_al q) F'' (PMRR.rs_after q (rsof c w gp bof rdst))).
      { eapply RKW.roundA_cont with (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
        all: first [exact HaccA | exact Hcm0 | exact Hrf | exact Hpq | (symmetry; exact Hcode) | exact IS | exact Hrc | exact HwN
                   | (rewrite Hcmo; first [exact Hm' | reflexivity]) | exact Hrk]. }
      destruct Hacc' as [F'' Hacc'].
      apply (HA fx'' R'' M' model' cr' ps' gp rdst bof B eg').
      * pose proof (muA_ret ps ps' gp rdst Hex' (fun Hex => Hr3 Hex eq_refl ltac:(first [exact Hm' | reflexivity]))). lia.
      * exact Hfp''.
      * exact HG'.
      * unfold rinvA, RDXWHU.rinvA. exists (PMR.q_c q), (PMR.q_w q), (evs ++ PMR.q_evs q), (al + PMR.q_al q), F''.
        split; [exact Hc0'|]. split; [eapply egacc_app; [exact Hacc | exact Hes' | exact Hpay']|].
        unfold rsof, RDXWHU.rsof in Hacc' |- *. rewrite RKW.rs_after_rsof in Hacc'. exact Hacc'.
      * exact Hwin'.
      * exact (Hsync' eq_refl).
      * exact Hregs.
      * exact H19''.
      * exact H20''.
      * rewrite H10''. try rewrite Hm'. reflexivity.
      * exact Hfr'.
    + (* ps_more ps' = false: loop A ends, skip_ws *)
      assert (Hloop : PMR.rloop (PMR.rfuel (PML.srep_chars rep)) (PMRR.rs0 (PML.srep_chars rep)) =
         (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, 0)).
      { eapply RKW.roundA_stop with (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
        all: first [exact HaccA | exact Hcm0 | exact Hrf | exact Hpq | (symmetry; exact Hcode) | exact IS | idtac].
        right. split; [rewrite Hcmo; first [exact Hm' | reflexivity]|].
        intros Hwe. unfold rsof, RDXWHU.rsof in Hwe. rewrite RKW.weof_rsof in Hwe.
        destruct w as [|b0 w'] eqn:HwE; [|discriminate Hwe].
        pose proof (exh_nil M ps c Hwst) as Hex. pose proof (proj1 (RB.exhausted_iff ps) Hex) as Hpe.
        destruct (Hcond Hpe) as [Hn1 [H2'|Hd']]; [left; rewrite Hcst; unfold PML.ST_ACCEPT; lia | right; rewrite Hcdn; apply b2z_t; exact Hd']. }
      apply (loopA_done R1 Hw fx'' R'' M' model' cr' ps' gp rdst bof B eg' Hfp'' HG').
      * unfold rinvB0, RDXWHU.rinvB0. exists (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, 0), (PMR.q_c q), (PMR.q_w q).
        split; [exact Hloop|]. cbn [PMRR.t_evs PMRR.t_al PMRR.t_code PMRR.t_rs fst snd].
        split; [reflexivity|]. split; [eapply egacc_app; [exact Hacc | exact Hes' | exact Hpay']|].
        split; [exact Hc0'|]. unfold rsof, RDXWHU.rsof. rewrite RKW.rs_after_rsof. reflexivity.
      * exact Hm'.
      * exact Hregs.
      * exact H19''.
      * exact H20''.
      * rewrite H10''. try rewrite Hm'. reflexivity.
      * exact Hfr'.
  - (* RN_EPI *) intros Hc fx'' R'' Hfp'' H2'' Hk''.
    assert (Hcq : PMR.q_code q <> 0) by (rewrite <- Hcode; exact Hc).
    assert (Hloop : PMR.rloop (PMR.rfuel (PML.srep_chars rep)) (PMRR.rs0 (PML.srep_chars rep)) =
       (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, PMR.q_code q)).
    { eapply RKW.roundA_pserr_t with (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
      all: first [exact HaccA | exact Hcm0 | exact Hrf | exact Hpq | exact Hcq | exact IS]. }
    apply (Hx fx'' R'' M' model' cr' ps' gp rdst code' bof g' B eg' Hfp'' HG').
    + unfold rinvX, RDXWHU.rinvX. eexists. split; [exact Hloop|]. cbn [PMRR.t_evs PMRR.t_al PMRR.t_code fst snd]. split.
      * eapply egacc_app; [exact Hacc | exact Hes' | exact Hpay'].
      * left. split; [exact Hcq | exact Hcode].
    + eapply regsU_after; [exact R'8 | exact R'9 | exact R'18 | exact Hks' | exact Hk'' | | rewrite H2''; f_equal; lia].
      intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try inl. destruct Hq0.
    + exact Hfr'.
  - (* SET_EC *) intros Hc0z Hpe Hst1 Hst2 Hdn fx'' R'' Hfp'' H2'' H1'' H10'' H11'' Hk1 Hk2.
    revert Hcode. subst code'. intros Hcode.
    assert (Hg0 : g' = g0) by (eapply ginv_g0; exact HG'). subst g'.
    assert (Hstm : PML.ps_st ps' mod 256 = PML.ps_st ps') by (eapply st_mod; exact HG').
    pose proof (proj2 (RB.exhausted_iff ps) Hpe) as Hex.
    pose proof (wst_nil M ps c w Hwst Hex) as Hw0.
    pose proof (Hc0 eq_refl) as Hc0'.
    pose proof (wst_core M' ps' (PMR.q_c q) (PMR.q_w q) Hc0') as (Hcst & Hcmo & Hcdn).
    assert (Hloop : PMR.rloop (PMR.rfuel (PML.srep_chars rep)) (PMRR.rs0 (PML.srep_chars rep)) =
       (PMRR.rs_after q (rsof c w gp bof rdst), evs ++ PMR.q_evs q, al + PMR.q_al q, PMR.E_EOF)).
    { eapply RKW.roundA_ueof_t with (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
      all: first [exact HaccA | exact Hcm0 | exact Hrf | exact Hpq | (symmetry; exact Hcode) | exact IS
                 | (unfold rsof, RDXWHU.rsof; rewrite RKW.weof_rsof, Hw0; reflexivity)
                 | (rewrite Hcst; unfold PML.ST_START; lia) | (rewrite Hcst; unfold PML.ST_ACCEPT; lia)
                 | (rewrite Hcdn; apply b2z_f; exact Hdn)]. }
    pose proof Hr as Hr1'. unfold r1ok, RDXWUB.r1ok in Hr1'. destruct Hr1' as (HR18 & HR19 & HRks).
    apply (Hs fx'' R'' M' model' cr' ps' gp rdst bof B eg' Hfp'' HG').
    + unfold rinvE, RDXWHU.rinvE. eexists. split; [exact Hloop|]. cbn [PMRR.t_evs PMRR.t_al PMRR.t_code fst snd]. split.
      * eapply egacc_app; [exact Hacc | exact Hes' | exact Hpay'].
      * reflexivity.
    + exact Hrdf.
    + exact H2''.
    + exact H1''.
    + exact H10''.
    + exact H11''.
    + rewrite (Hk1 8%bv); [exact HR18 | inl].
    + rewrite (Hk1 9%bv); [exact HR19 | inl].
    + apply (keeps_combine [18; 19; 20; 21; 22]%nat RS.KS06 RS.KS01 R1 R' R'').
      * apply (i_keeps_sub _ _ _ _ Hk1). intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try inl. destruct Hq0.
      * apply (i_keeps_sub _ _ _ _ HRks). intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try inl. destruct Hq0.
      * exact Hk2.
      * exact Hks'.
      * intros q0 Hq0. cbn in Hq0. repeat destruct Hq0 as [<-|Hq0]; try first [solve [left; inl] | solve [right; inl]]. destruct Hq0.
Qed.

Lemma psome_callU : forall m R1, r1ok R1 -> rn_exit_stmtU R1 -> ws1_stmtU R1 -> setec_stmtU -> atAm m R1 ->
  forall (fx : FPState) R M model cr ps gp rdst bof B eg,
  muA ps gp rdst <= m -> PML.fp_ok fx -> ginvU M model cr ps gp rdst 0 bof g0 B eg -> rinvP M ps gp rdst bof eg ->
  PML.ps_more ps = true -> PML.win_ok M LBo ps -> PMX.enc_sync ps eg -> (PMS.win_exhausted ps -> rdst = 2) ->
  getr R 2%bv = Z_to_bv 64 (sp - 96) -> getr R 1%bv = Z_to_bv 64 RT.RN_R_PSOME ->
  getr R 10%bv = Z_to_bv 64 (Rr + 320) -> getr R 11%bv = Z_to_bv 64 V -> getr R 12%bv = Z_to_bv 64 E ->
  getr R 8%bv = Z_to_bv 64 E -> getr R 9%bv = Z_to_bv 64 Rr -> getr R 18%bv = Z_to_bv 64 (Rr + 320) ->
  getr R 19%bv = Z_to_bv 64 1 -> getr R 20%bv = Z_to_bv 64 2 ->
  getr R 22%bv = Z_to_bv 64 (RB.wp ps) -> getr R 21%bv = Z_to_bv 64 (RB.we ps) ->
  TK.keepsR RS.KS06 R0 R -> rn_frU R1 M ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_SOME M model) K.
Proof.
  intros m R1 Hr Hx Hw Hs HA fx R M model cr ps gp rdst bof B eg Hmu Hfp HG HP Hmore Hwin Hsync Hexh
    H2 H1 H10 H11 H12 H8 H9 H18 H19 H20 H22 H21 Hks Hfr.
  destruct HP as (c & w & evs & al & F' & w0 & gp0 & bof0 & rdst0 & Hwst & Hacc & HaccA & Hrf).
  pose proof Hacc as Hacc0. destruct Hacc as [Hes Hpay].
  pose proof HG as HGw. unfold ginvU, RDXWUB.ginvU, RDXWHU.ginv, RIXW.ginv in HGw.
  destruct HGw as (_ & _ & Hwfx & _). unfold RIXW.wfx in Hwfx. destruct Hwfx as [Hwf _].
  pose proof Hwst as Hwst0. unfold wst, RDXWHU.wst in Hwst0. destruct Hwst0 as [Hrm _].
  pose proof (wst_core M ps c w Hwst) as (_ & Hcm & _).
  pose proof lay as Hlay. pose proof SPOK as Hspok. unfold RS.spok in Hspok.
  pose proof PSOMEWU as HSPEC. unfold PMW.parse_some_specwU in HSPEC.
  apply (call_ptransxwU _ _ _ _ _ HSPEC fx R M model cr ps gp rdst bof B eg (sp - 96) RT.RN_R_PSOME c w Hfp HG Hwin Hsync Hwst).
  - unfold PMW.wroomrU. rewrite RKW.evs_psome, RKW.allow_psome.
    eapply (RRWU.round_room IS) with (eg0 := eg0) (evs := evs) (al := al) (F' := F') (rs := rsof c w0 gp0 bof0 rdst0) (rs1 := rsof c w gp bof rdst).
    all: try (unfold rsof, RDXWHU.rsof; rewrite ?RKW.r_c_rsof, ?RKW.r_w_rsof).
    all: first [exact HaccA | exact Hrf | exact Hes | exact Hpay | exact WR0 | reflexivity | (rewrite Hcm; exact Hmore)
               | exact (RRWU.rm_match_SIq c M P ps Hrm Hwf Hmore)].
  - exact H1.
  - apply ra_lit; unfold RT.RN_R_PSOME; [lia | reflexivity].
  - exact H2.
  - rewrite (Hks 4%bv); [exact R0tp | vm_compute; right; left; reflexivity].
  - replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact (proj2 Hspok).
  - unfold SS in *. lia.
  - lia.
  - unfold SS in *. lia.
  - cbv [PMW.ax]. split; [|exact Hmore]. unfold PMS.std_args, PML.a0, PML.a1, PML.a2. split; [exact H10|]. split; [exact H11 | exact H12].
  - intros ps' code' R' (_ & _ & _ & Hws) Hc. exact (Hws Hc).
  - intros fx' R' M' model' cr' ps' code' g' eg' Hfp' Hrp HG' Hmore' HRel Hwin' Hsync' Hrr Hsam.
    cbv zeta in Hrr. rewrite RKW.code_psome, RKW.evs_psome, RKW.allow_psome, RKW.ctrl_psome, RKW.after_psome in Hrr.
    destruct Hrr as (Hcode & Hes' & Hpay' & Hc0).
    destruct HRel as (Hr1 & Hr2 & Hr3 & _).
    pose proof (gcells (bx + PMES.benc L eg) M model cr ps gp rdst 0 bof g0 B eg HG) as (_&_&_&_&_&_&_&_&_&_&Hwpe&Hwe62&_).
    exact (psome_ret m R1 Hr Hx Hw Hs HA ps gp rdst bof B eg c w evs al F' w0 gp0 bof0 rdst0 R M fx' R' M' model' cr' ps' code' g' eg'
      Hmu Hmore Hexh Hacc0 HaccA Hrf Hwst ltac:(lia) H2 H8 H9 H18 H19 H20 H22 H21 Hks Hfr Hfp' Hrp HG' Hmore' Hr1 Hr2 Hr3 Hwin' Hsync'
      Hcode Hes' Hpay' Hc0 Hsam).
Qed.

Lemma loopA_stepU : forall m R1, r1ok R1 -> rn_exit_stmtU R1 -> ws1_stmtU R1 -> setec_stmtU -> atAm m R1 -> atAm (m + 1) R1.
Proof.
  intros m R1 Hr Hx Hw Hs HA fx R M model cr ps gp rdst bof B eg Hmu Hfp GI HrA Hwin Hsync HR H19 H20 H10 Hfr.
  destruct (PML.ps_more ps) eqn:Hm.
  2: { apply (loopA_done R1 Hw fx R M model cr ps gp rdst bof B eg Hfp GI (w3_rinvB0_of_A _ _ _ _ _ _ HrA Hm) Hm HR H19 H20); [rewrite H10; try rewrite Hm; reflexivity | exact Hfr]. }
  destruct (w3_gmod _ _ _ _ _ _ _ _ _ _ _ _ GI) as (Hh & Hl).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GI) as (G240 & GVT & G152 & G152b & Grd & Gro & G288 & G312 & G512 & G520 & Gwp & Gwe & GE & Gcode & Gdef & G528 & G531 & G532 & Ggp).
  pose proof lay as (LY0 & LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14).
  pose proof OR as (OR1 & OR2 & OR3).
  pose proof OV as (OV1 & OV2 & OV3).
  pose proof HR as (H2 & H8 & H9 & H18 & HK).
  assert (H10a : getr R 10%bv = Z_to_bv 64 1) by (rewrite H10; try rewrite Hm; reflexivity).
  refine (RS.s_loopA FPM fx R M model K (sp - 32) Rr V (RB.wp ps) (RB.we ps) 1 Hh Hl Hfp _ _ H9 _ G312 G512 G520 _ _ _ _ _ H10a _ _ _ _).
  all: try (rewrite H2; f_equal; lia).
  all: try exact w3_spok32.
  all: pose proof SPOK as SP1; unfold RS.spok, RS.pok in *.
  all: try (w3_plits; lia).
  all: lazymatch goal with
    | |- (Z.land 1 1 = 0 -> _) => intros C; exfalso; discriminate C
    | |- (Z.land 1 1 <> 0 -> _ <> _ -> _) =>
        intros _ Hne fx' R' Hfp' H2' H1' H10' H11' H12' H21' H22' HK';
        assert (H2'' : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite H2'; f_equal; lia);
        destruct HrA as (c & w & evs & al & F' & WST & EG & AC);
        assert (HNX : ~ PMS.win_exhausted ps) by (intros HX; exact (Hne (w3_exh_eq ps HX)));
        pose proof (wst_cons _ _ _ _ WST HNX) as Wne;
        destruct w as [|b0 w0]; [exfalso; exact (Wne eq_refl)|];
        assert (H8p : getr R' 8%bv = Z_to_bv 64 E) by (rewrite (HK' 8%bv ltac:(w3_inlist)); exact H8);
        assert (H9p : getr R' 9%bv = Z_to_bv 64 Rr) by (rewrite (HK' 9%bv ltac:(w3_inlist)); exact H9);
        assert (H18p : getr R' 18%bv = Z_to_bv 64 (Rr + 320)) by (rewrite (HK' 18%bv ltac:(w3_inlist)); exact H18);
        assert (H19p : getr R' 19%bv = Z_to_bv 64 1) by (rewrite (HK' 19%bv ltac:(w3_inlist)); exact H19);
        assert (H20p : getr R' 20%bv = Z_to_bv 64 2) by (rewrite (HK' 20%bv ltac:(w3_inlist)); exact H20);
        assert (HK06p : TK.keepsR RS.KS06 R0 R') by (intros q Hq; rewrite (HK' q (w3_ks06_kp _ Hq)); exact (HK q Hq));
        assert (H10p : getr R' 10%bv = Z_to_bv 64 (Rr + 320)) by (rewrite H10'; exact H18);
        assert (H12p : getr R' 12%bv = Z_to_bv 64 E) by (rewrite H12'; exact H8);
        apply (psome_callU m R1 Hr Hx Hw Hs HA fx' R' M model cr ps gp rdst bof B eg ltac:(lia) Hfp' GI)
    | |- (Z.land 1 1 <> 0 -> _ = _ -> _) => idtac
    | |- ?G => fail 100 "open goal" G
    end.
  all: try (unfold rinvP, RDXWHU.rinvP; exists c, (b0 :: w0), evs, al, F', (b0 :: w0), gp, bof, rdst; split; [exact WST|]; split; [exact EG|]; split; [exact AC|];
            unfold rsof, RDXWHU.rsof; apply RKW.refill_nonempty).
  all: try exact Hm.
  all: try exact Hwin.
  all: try exact Hsync.
  all: try (intros HX; exfalso; exact (HNX HX)).
  all: try exact H2''.
  all: try exact H1'.
  all: try exact H10p.
  all: try exact H11'.
  all: try exact H12p.
  all: try exact H8p.
  all: try exact H9p.
  all: try exact H18p.
  all: try exact H19p.
  all: try exact H20p.
  all: try exact H22'.
  all: try exact H21'.
  all: try exact HK06p.
  all: try exact Hfr.
  all: lazymatch goal with
    | |- (Z.land 1 1 <> 0 -> _ = _ -> _) => idtac
    | |- ?G => fail 100 "open goal (psome)" G
    end.
  intros _ Heq fx' R' Hfp' H2' H1' H10' H11' HK'.
  assert (HX : PMS.win_exhausted ps) by exact (w3_eq_exh ps Heq).
  destruct HrA as (c & w & evs & al & F' & WST & EG & AC).
  pose proof (wst_nil _ _ _ _ WST HX) as ->.
  pose proof (wst_core M ps c [] WST) as (_ & Hcm & _).
  assert (H2'' : getr R' 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite H2'; f_equal; lia).
  assert (HR' : rn_regsU R') by (apply (w3_rn_keepq RS.KSA R R' HR HK'); [w3_inlist | w3_inlist | w3_inlist | exact w3_ks06_ksa | exact H2'']).
  pose proof HR' as (H2r & H8r & H9r & H18r & HKr).
  assert (H19r : getr R' 19%bv = Z_to_bv 64 1) by (rewrite (HK' 19%bv ltac:(w3_inlist)); exact H19).
  assert (H20r : getr R' 20%bv = Z_to_bv 64 2) by (rewrite (HK' 20%bv ltac:(w3_inlist)); exact H20).
  rewrite H8 in H11'.
  destruct (hfacts M model cr ps eg (w3_gheap _ _ _ _ _ _ _ _ _ _ _ _ GI)) as (_ & _ & _ & _ & HC0 & HC1 & _ & _ & (BR0 & _)).
  pose proof AP as (_ & _ & APE & _).
  pose proof Hsptop as HT1. pose proof Htop as HT2. pose proof Hceil as HC2.
  apply (call_chunkw (bx + PMES.benc L eg) fx' R' M model cr ps gp rdst bof B eg (sp - 96) RT.RN_R_CHUNKA Hfp' GI HX H1'
           ltac:(apply ra_lit; unfold RT.RN_R_CHUNKA; [lia | reflexivity]) H2r ltac:(rewrite (HKr 4%bv ltac:(w3_inlist)); exact R0tp) H10' H11').
  1-3: first [exact w3_al96 | pose proof lay as Hlay; pose proof SPOK as Hsp; unfold RS.spok in Hsp; lia].
  intros fx2 R2 M2 pc k gp' rdst' code' bof' g' Hfp2 HRP2 GI2 H102 H112 Hp0 Hpk Hk Hkch Hgp' Hkg Hc0 Hrd' H2b H0b HFB HGR HSM.
  assert (HR2 : rn_regsU R2) by exact (w3_rn_pres R' R2 HR' HRP2).
  pose proof HR2 as (H22 & H82 & H92 & H182 & HK2).
  assert (H192 : getr R2 19%bv = Z_to_bv 64 1) by (rewrite (HRP2 19%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H19r).
  assert (H202 : getr R2 20%bv = Z_to_bv 64 2) by (rewrite (HRP2 20%bv ltac:(unfold callee_saved_idx; w3_inlist)); exact H20r).
  assert (HF2 : rn_frU R1 M2) by exact (w3_rnfr_x R1 M M2 HSM Hfr).
  destruct (w3_gmod _ _ _ _ _ _ _ _ _ _ _ _ GI2) as (Hh2 & Hl2).
  destruct (gcells _ _ _ _ _ _ _ _ _ _ _ _ GI2) as (G240' & GVT' & G152' & G152b' & Grd' & Gro' & G288' & G312' & G512' & G520' & Gwp' & Gwe' & GE' & Gcode' & Gdef' & G528' & G531' & G532' & Ggp').
  destruct (chunk_post M2 c gp rdst bof pc k gp' rdst' code' bof' Ggp Grd H2b H0b) as (w1 & Hrf & Hlw & Hbw & HFw & Hcw & Hnch).
  assert (WST2 : wst M2 ps c []) by exact (wst_rchunk M M2 ps c (sp - 96) WST HX HFB ltac:(lia) HC1).
  refine (RS.s_rn_r_chunkA FPM fx2 R2 M2 model K (sp - 32) Rr E code' V (RB.wp ps) (RB.we ps) pc k Hh2 Hl2 Hfp2 _ w3_spok32 H92 H82 _ _ H102 H112
            _ _ _ _ GE' Gcode' G312' G512' G520' _ _ _ _ _ Gdef' _ _ _).
  all: try (rewrite H22; f_equal; lia).
  all: try (unfold RS.pok; w3_plits; lia).
  all: try (w3_plits; lia).
  all: try (intros Hk0; destruct (Hkch ltac:(lia)) as (Q1 & Q2); unfold RS.pok; w3_plits; lia).
  all: try (destruct APE as [A1 | A1]; [left | right]; lia).
  all: lazymatch goal with
    | |- (_ <> 0 -> _) =>
        intros Hne fx3 R3 Hfp3 H23 HK3;
        apply (Hx fx3 R3 M2 model cr ps gp' rdst' code' bof' g' B eg Hfp3 GI2);
        [ unfold rinvX, RDXWHU.rinvX; eexists; split;
          [ eapply (RKW.roundA_referr_t IS); [exact AC | unfold rsof, RDXWHU.rsof; rewrite RKW.r_c_rsof, Hcm; exact Hm | exact Hrf | exact Hne] | ];
          cbn [PMRR.t_evs PMRR.t_al PMRR.t_code fst snd]; split; [exact EG|]; left; split; [exact Hne | reflexivity]
        | apply (w3_rn_keepq RS.KSW R2 R3 HR2 HK3); [w3_inlist | w3_inlist | w3_inlist | exact w3_ks06_ksw | rewrite H23; f_equal; lia]
        | exact HF2 ]
    | |- (_ = 0 -> _) => idtac
    | |- ?G => fail 100 "open goal (chunk)" G
    end.
  intros Hz fx3 R3 M3 pn en Hfp3 H23 H13 H103 H113 H123 H223 H213 HK3 Hcase.
  rewrite Hz in Hrf, GI2.
  assert (Eg : g' = g0) by (eapply ginv_g0; exact GI2). subst g'.
  assert (H23' : getr R3 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite H23; f_equal; lia).
  assert (HK06 : TK.keepsR RS.KS06 R0 R3) by (intros q Hq; rewrite (HK3 q (w3_ks06_kp _ Hq)); exact (HK2 q Hq)).
  assert (H83 : getr R3 8%bv = Z_to_bv 64 E) by (rewrite (HK3 8%bv ltac:(w3_inlist)); exact H82).
  assert (H93 : getr R3 9%bv = Z_to_bv 64 Rr) by (rewrite (HK3 9%bv ltac:(w3_inlist)); exact H92).
  assert (H183 : getr R3 18%bv = Z_to_bv 64 (Rr + 320)) by (rewrite (HK3 18%bv ltac:(w3_inlist)); exact H182).
  assert (H193 : getr R3 19%bv = Z_to_bv 64 1) by (rewrite (HK3 19%bv ltac:(w3_inlist)); exact H192).
  assert (H203 : getr R3 20%bv = Z_to_bv 64 2) by (rewrite (HK3 20%bv ltac:(w3_inlist)); exact H202).
  assert (H103' : getr R3 10%bv = Z_to_bv 64 (Rr + 320)) by (rewrite H103; exact H182).
  destruct Hcase as [(Hk0 & Hpn & Hen & HM) | (Hk0 & Hpn & Hen & W512 & W520 & HSM3 & HGR3)].
  - subst pn en M3.
    pose proof (Hc0 Hz Hk0) as Hrd2. subst rdst'.
    destruct w1 as [|b1 w1]; [| cbn [length] in Hlw; lia].
    apply (psome_callU m R1 Hr Hx Hw Hs HA fx3 R3 M2 model cr ps gp' 2 bof' B eg).
    all: try exact Hfp3.
    all: try exact GI2.
    all: try exact Hm.
    all: try exact (i_win_ok_exh M M2 LBo ps HX Hwin).
    all: try exact Hsync.
    all: try (intros _; reflexivity).
    all: try exact H23'.
    all: try exact H13.
    all: try exact H103'.
    all: try exact H113.
    all: try exact H123.
    all: try exact H83.
    all: try exact H93.
    all: try exact H183.
    all: try exact H193.
    all: try exact H203.
    all: try exact H223.
    all: try exact H213.
    all: try exact HK06.
    all: try exact HF2.
    all: try (pose proof (w3_muA_k0 ps gp rdst gp' Hgp'); lia).
    all: try (unfold rinvP, RDXWHU.rinvP; exists c, [], evs, al, F', [], gp, bof, rdst; split; [exact WST2|]; split; [exact EG|]; split; [exact AC | exact Hrf]).
    all: lazymatch goal with |- ?G => fail 100 "open goal (k0)" G end.
  - assert (Hrd0 : rdst = 0) by (destruct Grd as [E0 | E2]; [exact E0 | destruct (H2b E2) as (K0 & _); lia]).
    subst rdst.
    destruct (Hkch ltac:(lia)) as (Q1 & Q2).
    pose proof (w3_gB _ _ _ _ _ _ _ _ _ _ _ _ GI) as HBg.
    subst pn en.
    destruct (i_ginv_setwin (bx + PMES.benc L eg) M2 M3 model cr ps gp' rdst' bof' g0 B eg pc k GI2 HX HSM3 HGR3 W512 W520 ltac:(lia) Q1 Q2 ltac:(lia)) as (GI3 & WIN3).
    assert (WST3 : wst M3 (PML.ps_set_win ps (Some (pc, pc + k))) c w1).
    { apply (wst_setwin M2 M3 ps c w1 pc k WST2 HSM3 (Hbw ltac:(lia)) Hlw HFw); lia. }
    assert (HF3 : rn_frU R1 M3) by exact (w3_rnfr_x R1 M2 M3 (w3_samem_win M2 M3 HSM3) HF2).
    apply (psome_callU m R1 Hr Hx Hw Hs HA fx3 R3 M3 model cr (PML.ps_set_win ps (Some (pc, pc + k))) gp' rdst' bof' (B + k) eg).
    all: try exact Hfp3.
    all: try exact GI3.
    all: try (rewrite more_setwin; exact Hm).
    all: try exact WIN3.
    all: try exact (enc_sync_setwin _ _ _ Hsync).
    all: try (intros HX2; exfalso; apply w3_exh_eq in HX2; rewrite wp_setwin, we_setwin in HX2; lia).
    all: try exact H23'.
    all: try exact H13.
    all: try exact H103'.
    all: try exact H113.
    all: try exact H123.
    all: try exact H83.
    all: try exact H93.
    all: try exact H183.
    all: try exact H193.
    all: try exact H203.
    all: try (rewrite wp_setwin; exact H223).
    all: try (rewrite we_setwin; exact H213).
    all: try exact HK06.
    all: try exact HF3.
    all: try (pose proof (w3_muA_k1 ps gp gp' rdst' pc k ltac:(lia) ltac:(lia) HX); lia).
    all: try (unfold rinvP, RDXWHU.rinvP; exists c, w1, evs, al, F', [], gp, bof, 0; split; [exact WST3|]; split; [exact EG|]; split; [exact AC | exact Hrf]).
    all: lazymatch goal with |- ?G => fail 100 "open goal (k1)" G end.
Qed.

Lemma loopA_all : forall R1, r1ok R1 -> rn_exit_stmtU R1 -> ws1_stmtU R1 -> setec_stmtU -> forall k : nat, atAm (Z.of_nat k) R1.
Proof.
  intros R1 Hr Hx Hw Hs k. induction k as [|k IH].
  - intros fx R M model cr ps gp rdst bof B eg Hmu _ HG. exfalso. pose proof (muA_pos _ _ _ _ _ _ _ _ _ _ _ HG). cbn [Z.of_nat] in Hmu. lia.
  - rewrite Nat2Z.inj_succ. unfold Z.succ. exact (loopA_stepU _ R1 Hr Hx Hw Hs IH).
Qed.

(* Loop A of READ_NEXT (parse_some rounds at LOOPA, rotated loop, ubsan): deliver loopA_okU. *)
Lemma loopA_okU : (forall R1, r1ok R1 -> rn_exit_stmtU R1) -> (forall R1, r1ok R1 -> ws1_stmtU R1) -> setec_stmtU ->
  forall R1, r1ok R1 -> atAU R1.
Proof using All.
  intros Hx Hw Hs R1 Hr. unfold atAU, RDXWUB.atAU.
  intros fx R M model cr ps gp rdst bof B eg Hfp HG HA Hwin Hsync Hregs H19 H20 H10 Hfr.
  pose proof (muA_pos _ _ _ _ _ _ _ _ _ _ _ HG) as Hmu.
  apply (loopA_all R1 Hr (Hx R1 Hr) (Hw R1 Hr) Hs (S (Z.to_nat (muA ps gp rdst))) fx R M model cr ps gp rdst bof B eg);
    try assumption.
  rewrite Nat2Z.inj_succ, Z2Nat.id; lia.
Qed.
End Run.
End H.
End RDXWUA.
