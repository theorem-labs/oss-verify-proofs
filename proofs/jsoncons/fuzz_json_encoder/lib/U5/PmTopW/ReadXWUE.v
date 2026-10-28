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

Module RDXWUE.
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

Ltac ckin := vm_compute; repeat first [left; reflexivity | right].

(* State at RT.RN_R_PUSH after the vec_push of the zero byte (frame sp - 32 - 96). *)
Definition ret_stmt (R1 : bvmap 5 word) : Prop := forall (fx : FPState) R M model cr gp sb bptr eg,
  PML.fp_ok fx -> ginvU M model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg -> PMX.enc_sync (PMS.ps_init sb bptr) eg -> egacc eg [] 0 -> gp = D ->
  rn_frU R1 M -> L5.u64_at RSEGS M (sp - 32 - 72) 0x4723c -> L5.u64_at RSEGS M (sp - 32 - 80) E ->
  getr R 2%bv = Z_to_bv 64 (sp - 32 - 96) -> getr R 8%bv = Z_to_bv 64 (Rr + 320) -> getr R 9%bv = Z_to_bv 64 Rr -> getr R 18%bv = Z_to_bv 64 (Rr + 320) ->
  TK.keepsR RS.KS06 R0 R ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_PUSH M model) K.

(* State at PML.PC_VEC_PUSH after the outlined reader reset (M: memory at READ_NEXT entry, M': at the call). *)
Definition call_stmt (R1 : bvmap 5 word) : Prop := forall (fx : FPState) R M model cr gp sb bptr eg M',
  PML.fp_ok fx -> ginvU M model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg -> PMX.enc_sync (PMS.ps_init sb bptr) eg -> egacc eg [] 0 -> gp = D -> rd_frame M ->
  RS.rn_frame M' (sp - 32) RT.RD_R_NEXT R1 -> L5.u64_at RSEGS M' (sp - 32 - 72) 0x4723c -> L5.u64_at RSEGS M' (sp - 32 - 80) E ->
  L5.u8_at RSEGS M' (sp - 32 - 81) 0 -> L5.u64_at RSEGS M' (Rr + 576) sb ->
  TK.samem (fun a => ~ (sp - 32 - 96 <= a < sp - 32) /\ ~ (Rr + 576 <= a < Rr + 584)) M M' -> mem_grows M M' ->
  getr R 2%bv = Z_to_bv 64 (sp - 32 - 96) -> getr R 1%bv = Z_to_bv 64 RT.RN_R_PUSH -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  getr R 10%bv = Z_to_bv 64 (Rr + 568) -> getr R 11%bv = Z_to_bv 64 (sp - 32 - 81) ->
  getr R 8%bv = Z_to_bv 64 (Rr + 320) -> getr R 9%bv = Z_to_bv 64 Rr -> getr R 18%bv = Z_to_bv 64 (Rr + 320) -> TK.keepsR RS.KS06 R0 R ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_VEC_PUSH M' model) K.

Local Ltac bo_kcov := unfold TK2.cov; intros ?i ?Hi; cbv beta; repeat split; intro; lia.

Lemma bo_rnfr_x : forall (KK : Z -> Prop) M M' R1, TK.samem KK M M' -> (forall a, sp - 96 <= a < sp -> KK a) -> rn_frU R1 M -> rn_frU R1 M'.
Proof.
  intros KK M M' R1 HS HK (F & RF).
  pose proof lay as (LY1 & _).
  split.
  - unfold RS.rn_frame in F |- *. destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
      (eapply (TK.u64_samem KK M M' _ _ HS); [lia | intros i Hi; apply HK; lia | eassumption]).
  - apply (rd_frame_x M M' (sp - 32)); [| lia | exact RF].
    intros a Ha Hin. cbv beta in Hin. apply HS; [exact Ha|]. apply HK. lia.
Qed.

(* 3. return: RS.s_rn_r_push, reset parser fields, first LOOPA. *)
Lemma rn_ret : forall R1, atAU R1 -> ret_stmt R1.
Proof.
  intros R1 HA fx R M model cr gp sb bptr eg Hfp GI Hsync Hacc Hgp HFR H72 H80 H2 H8 H9 H18 HKS.
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & LY13 & LY14 & LYr).
  pose proof GI as (Grdr & GPA & Gwfx & Gwin & Gisrc & Gvis & Gec & Gls & Gg & GHH & (Hh & Hl & _) & _).
  pose proof GPA as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ GHH) as (Hwf & _).
  destruct (Hwf (bptr, 264) ltac:(apply in_or_app; left; cbn; left; reflexivity)) as ((BB1 & _ & _ & BB4 & BB5) & _).
  destruct (Hwf (sb, 66) ltac:(apply in_or_app; left; cbn; right; left; reflexivity)) as ((SB1 & _ & _ & SB4 & SB5) & _).
  cbn [fst snd] in BB1, BB4, BB5, SB1, SB4, SB5.
  assert (SPLO : 2 ^ 41 <= sp - 32 /\ sp <= 2 ^ 47).
  { pose proof Htop as T. pose proof Hsptop as T2. split; lia. }
  assert (SPM : (sp - 32) mod 16 = 0).
  { replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact LY2. }
  refine (RS.s_rn_r_push FPM fx R M model K (sp - 32) Rr E 1 Hh Hl Hfp H2 _ H9 H8 _ _ _ _ _ H72 H80 _ _).
  - unfold RS.spok. split; [lia | exact SPM].
  - unfold RS.pok. lia.
  - lia.
  - intros i Hi. replace (Rr + 464 + i) with (Rr + 320 + (144 + i)) by lia. exact (Adef (144 + i) ltac:(lia)).
  - replace (Rr + 531) with (Rr + 320 + 211) by lia. exact A211.
  - lia.
  - lia.
  - intros fx' R' M' Hfp' H2' H8' H10' H19' H20' HK' U528 U531 U532 U464 U480 U488 U496 HS HG.
    assert (DEF' : L5.defined M' (Rr + 320) 272) by (intros i Hi; apply HG; exact (Adef i Hi)).
    assert (HPA' : PML.parser_at M' (Rr + 320) (PMS.ps_init sb bptr)).
    { apply (RB.parser_at_patch _ M M' (Rr + 320) (PMS.ps_init sb bptr) GPA HS DEF' ltac:(lia)).
      - cbn [PML.ps_bptr PML.ps_bcap PMS.ps_init]. split; [lia|]. split; [lia|]. bo_kcov.
      - bo_kcov.
      - bo_kcov.
      - bo_kcov.
      - bo_kcov.
      - right. replace (Rr + 320 + 144) with (Rr + 464) by lia. exact U464.
      - right. replace (Rr + 320 + 208) with (Rr + 528) by lia. exact U528.
      - right. replace (Rr + 320 + 211) with (Rr + 531) by lia. exact U531.
      - right. replace (Rr + 320 + 212) with (Rr + 532) by lia. exact U532.
      - left. cbn [PML.ps_sb PML.ps_scap PMS.ps_init]. split; [bo_kcov|]. split; [lia|]. split; [lia|]. bo_kcov. }
    assert (GI' : ginvU M' model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg).
    { refine (i_ginv_pcells (bx + PMES.benc L eg) _ M M' model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg GI HS HG _ HPA').
      intros a Ha. cbv beta. repeat split; intro; lia. }
    apply (HA fx' R' M' model cr (PMS.ps_init sb bptr) gp 0 true 0 eg Hfp' GI').
    + hnf. exists PMR.ctrl0, [], [], 0. eexists.
      split; [split; [|exact eq_refl] | split; [exact Hacc|]].
      * unfold PMR.rm_match, PMR.rm_core. cbn. split; [repeat split|].
        unfold PML.ST_START, PML.ST_STRING, PML.ST_NUMBER. split; intros Hc; exfalso; lia.
      * unfold RDXWHU.rsof. subst gp. unfold D. rewrite (RKW.rsof_init IS rep). exact (RKW.accA_init IS rep).
    + exact I.
    + exact Hsync.
    + split; [|split; [exact H8'|split; [|split]]].
      * rewrite H2'. f_equal. lia.
      * rewrite (HK' 9%bv) by (vm_compute; lia). exact H9.
      * rewrite (HK' 18%bv) by (vm_compute; lia). exact H18.
      * apply (TK.keepsR_trans _ R0 R R' HKS). apply (i_keeps_sub _ _ R R' HK'). intros q Hq. unfold RS.KS06 in Hq. cbn [In] in Hq |- *. lia.
    + exact H19'.
    + exact H20'.
    + exact H10'.
    + refine (bo_rnfr_x _ M M' R1 HS _ HFR). intros a Ha. cbv beta. repeat split; intro; lia.
Qed.

(* 2. call: vec_push of the zero byte onto the emptied stack vector. *)
Lemma rn_call : forall R1, ret_stmt R1 -> call_stmt R1.
Proof.
  intros R1 HR fx R M model cr gp sb bptr eg M' Hfp GI ES EA HD HRF Hfr U72 U80 U81 U576' SAM MG H2 H1 H4 H10 H11 H8 H9 H18 K06.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & HSS & HPS & _).
  pose proof Htop as HT. pose proof Hsptop as HT2. pose proof OR as (_ & _ & HRm). pose proof OE as (OE1 & OE2 & _).
  pose proof AP as (_ & _ & AP3 & _). unfold PML.apart in AP3.
  assert (SSB : 9552 <= SS /\ SS = PMX.READX_SCR STRTOD_SCR WD_SCR) by (unfold SS in *; split; [lia | reflexivity]).
  destruct SSB as (SSB & SSE).
  assert (VS : PMS.VEC_SCR = 8368) by reflexivity.
  assert (AL : (sp - 32 - 96) mod 16 = 0).
  { replace (sp - 32 - 96) with (sp - 128) by lia. exact (i_al16 128 Y2 eq_refl). }
  pose proof GI as (_ & GP & (WF & WS) & _ & _ & _ & _ & _ & _ & GHH & _ & _ & GCR & GBB & GBD & _).
  pose proof GP as GP'. unfold PML.parser_at in GP'.
  destruct GP' as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ GHH) as (Hwf & ND & _).
  destruct (Hwf (bptr, 264) ltac:(apply in_or_app; left; cbn; left; reflexivity)) as ((BB1 & _ & _ & BB4 & BB5) & _).
  cbn [fst snd] in BB1, BB4, BB5.
  assert (NEb : bptr <> sb).
  { intros Heq. exact (i_nodup_app_disj [bptr] (sb :: map fst (LBo ++ PMES.g_lbv eg)) bptr ND (or_introl eq_refl) (or_introl (eq_sym Heq))). }
  assert (U568 : L5.u64_at RSEGS M (Rr + 568) sb).
  { replace (Rr + 568) with (Rr + 320 + 248) by lia. exact A248. }
  destruct (i_ginv0_entry (bx + PMES.benc L eg) M M' model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg (sp - 32 - 96) (sp - 32) GI SAM MG ltac:(lia) ltac:(lia) ltac:(lia)) as (G0E & EC' & LS').
  pose proof G0E as (_ & _ & _ & HH' & _ & MOK' & _ & (_ & FDEF') & _).
  assert (ENT : PML.entry L R M' (sp - 32 - 96) RT.RN_R_PUSH PMS.VEC_SCR).
  { apply (mk_entry R M' (sp - 32 - 96) RT.RN_R_PUSH PMS.VEC_SCR H1 (ra_lit RT.RN_R_PUSH ltac:(unfold RT.RN_R_PUSH; lia) eq_refl) H2 H4 FDEF' AL); lia. }
  pose proof ENT as (_ & _ & _ & _ & STK).
  apply (VPUSH (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg) cr (Rr + 568) sb 66 (sp - 32 - 81) 0 (sp - 32 - 96) RT.RN_R_PUSH []
           fx R M' model K HH' MOK' HK0 Hfp).
  { split; [exact ENT|]. split; [exact H10|]. split; [exact H11|]. split; [exact U81|]. split; [lia|].
    split; [apply (TK.u64_samem _ M M' _ _ SAM); [lia | intros i Hi; cbv beta; split; lia | exact U568]|].
    split; [cbn [length Z.of_nat]; rewrite Z.add_0_r; replace (Rr + 568 + 8) with (Rr + 576) by lia; exact U576'|].
    split; [replace (Rr + 568 + 16) with (Rr + 320 + 264) by lia; apply (TK.u64_samem _ M M' _ _ SAM); [lia | intros i Hi; cbv beta; split; lia | exact A264]|].
    split; [intros i Hi; cbn [length] in Hi; lia|].
    split; [apply in_or_app; left; cbn; right; left; reflexivity|].
    split; [cbn [length Z.of_nat]; lia|]. split; [cbn [length]; lia|].
    split; [split; [lia | split; [lia | exact (i_al8_add Rr 568 HRm eq_refl)]]|].
    intros X. exfalso. cbn [length Z.of_nat] in X. lia. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (-> & PU) RP2 HP2 BV2 HH2.
  destruct PU as [(_ & V0 & V8 & V16 & VB & -> & -> & ->) | (EQ & _)]; [| exfalso; cbn [length Z.of_nat] in EQ; lia].
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH') as BOK.
  assert (BOKr : TK2.blocks_ok L (lb_remove sb (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg))).
  { intros b0 Hb0. apply BOK. exact (i_lb_remove_in sb _ b0 Hb0). }
  pose proof (TK2.hpres_samem L LAY _ _ _ _ M' M2 HP2 BOKr STK ltac:(lia)) as AG.
  assert (KBs : forall a, sp - 32 - 96 <= a < sp ->
            TK2.keepH L (lb_remove sb (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg)) [(Rr + 568, 24)] (sp - 32 - 96) PMS.VEC_SCR a).
  { intros a Ha. unfold TK2.keepH. split; [unfold L5.outside; intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia | left; lia]. }
  assert (TC : TK.samem (fun a => (~ (sp - 32 - 96 <= a < sp - 32) /\ ~ (Rr + 576 <= a < Rr + 584)) /\
            TK2.keepH L (lb_remove sb (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg)) [(Rr + 568, 24)] (sp - 32 - 96) PMS.VEC_SCR a) M M2).
  { apply (TK.samem_trans _ M M' M2).
    - apply (TK.samem_weaken _ _ M M' SAM). intros a Ha. cbv beta in Ha |- *. exact (proj1 Ha).
    - apply (TK.samem_weaken _ _ M' M2 AG). intros a Ha. cbv beta in Ha |- *. exact (proj2 Ha). }
  assert (KCP : forall a, Rr + 320 <= a < Rr + 568 -> (~ (sp - 32 - 96 <= a < sp - 32) /\ ~ (Rr + 576 <= a < Rr + 584)) /\
            TK2.keepH L (lb_remove sb (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg)) [(Rr + 568, 24)] (sp - 32 - 96) PMS.VEC_SCR a).
  { intros a Ha. split; [split; lia|]. unfold TK2.keepH. split; [unfold L5.outside; intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia | left; lia]. }
  assert (DEF2 : L5.defined M2 (Rr + 320) 272).
  { intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Rr + 320 + i) HP2);
      [lia | right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | apply MG; exact (Adef i Hi)]. }
  assert (HPA2 : PML.parser_at M2 (Rr + 320) (PMS.ps_init sb bptr)).
  { apply (RB.parser_at_patch _ M M2 (Rr + 320) (PMS.ps_init sb bptr) GP TC).
    - exact DEF2.
    - lia.
    - change (PML.ps_bptr (PMS.ps_init sb bptr)) with bptr. change (PML.ps_bcap (PMS.ps_init sb bptr)) with 264.
      split; [lia | split; [lia |]]. unfold TK2.cov. intros i Hi. cbv beta. split; [split; lia|]. unfold TK2.keepH.
      split; [unfold L5.outside; intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia|].
      right. right. left. exists (bptr, 264). split; [|cbn [fst snd]; lia].
      apply i_in_lb_remove; [apply in_or_app; left; cbn; left; reflexivity | exact NEb].
    - unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - left. unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - left. unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - left. unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - left. unfold TK2.cov. intros i Hi. cbv beta. apply KCP. lia.
    - right. split; [replace (Rr + 320 + 248) with (Rr + 568) by lia; exact V0|].
      cbn [length Z.of_nat] in V8. rewrite Z.add_0_r in V8.
      split; [replace (Rr + 320 + 256) with (Rr + 568 + 8) by lia; exact V8|].
      split; [replace (Rr + 320 + 264) with (Rr + 568 + 16) by lia; exact V16 | exact VB]. }
  assert (GU2 : ginvU M2 model2 cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg).
  { refine (i_ginv_ptrans0 (bx + PMES.benc L eg) M' M2 model model2 _ cr cr (PMS.ps_init sb bptr) gp 0 true 0 g0 0 eg (sp - 32 - 96) PMS.VEC_SCR G0E
              _ _ _ _ _ BV2 HH2 HPA2 WF WS I GBB GBD _ _ (or_introl eq_refl) GCR).
    - apply (i_hpres_weaken _ _ _ _ _ _ M' M2 HP2).
      + intros b0 Hb0. apply i_in_lb_remove; [apply in_or_app; right; exact Hb0|]. intros Heq.
        apply (i_nodup_app_disj [bptr; sb] (map fst (LBo ++ PMES.g_lbv eg)) sb ND); [right; left; reflexivity | rewrite <- Heq; apply in_map; exact Hb0].
      + intros a Ho. unfold L5.outside in Ho |- *. intros w [<-|[]] Hin. apply (Ho (Rr + 320, 272)).
        * unfold PML.W_par. cbn [In]. left. reflexivity.
        * unfold L5.in_rng in Hin |- *. cbn [fst snd] in Hin |- *. lia.
    - lia.
    - lia.
    - lia.
    - exact AL.
    - apply (TK2.ec_at_x _ M' M2 AG); [lia | | exact EC'].
      unfold TK2.cov. intros i Hi. unfold TK2.keepH. split; [unfold L5.outside; intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia | left; lia].
    - apply (TK2.ls_ok_x _ M' M2 AG); [| exact LS'].
      apply TK2.statics_cov_keepH. intros a Ha. unfold L5.outside. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct Ha as [(iv & Hiv & Hr)|Ha];
        [unfold PML.ll_foot_xsrc in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]); destruct Hiv | unfold PML.IMG_RO_HI in Ha; lia]. }
  assert (FR2 : rn_frU R1 M2).
  { apply (bo_rnfr_x _ M' M2 R1 AG).
    - intros a Ha. apply KBs. lia.
    - split; [exact Hfr|]. apply (rd_frame_x M M' (sp - 32)); [| lia | exact HRF].
      intros a Ha Hin. cbv beta in Hin. apply SAM; [exact Ha|]. cbv beta. split; lia. }
  assert (U72' : L5.u64_at RSEGS M2 (sp - 32 - 72) 0x4723c).
  { apply (TK.u64_samem _ M' M2 _ _ AG); [lia | intros i Hi; apply KBs; lia | exact U72]. }
  assert (U80' : L5.u64_at RSEGS M2 (sp - 32 - 80) E).
  { apply (TK.u64_samem _ M' M2 _ _ AG); [lia | intros i Hi; apply KBs; lia | exact U80]. }
  refine (HR fx2 R2 M2 model2 cr gp sb bptr eg Hfp2 GU2 ES EA HD FR2 U72' U80' _ _ _ _ _).
  - rewrite (RP2 2%bv ltac:(ckin)). exact H2.
  - rewrite (RP2 8%bv ltac:(ckin)). exact H8.
  - rewrite (RP2 9%bv ltac:(ckin)). exact H9.
  - rewrite (RP2 18%bv ltac:(ckin)). exact H18.
  - apply (TK.keepsR_trans RS.KS06 R0 R R2 K06). apply (i_keeps_pres RS.KS06 R R2 RP2).
    intros q Hq. cbv [RS.KS06 In] in Hq. repeat (destruct Hq as [<-|Hq]; [ckin|]). destruct Hq.
Qed.

(* 1. walk: RS.s_rn_entry from READ_NEXT entry to the vec_push call. *)
Lemma rn_walk : (forall R1, r1ok R1 -> call_stmt R1) -> rn_entry_stmtU.
Proof.
  intros HN R1 fx M model cr gp sb bptr eg Ha8 Ha9 Hk01 Hfp GI ES EA HD HRF Ha2 Ha1 Ha10 Ha11.
  pose proof GI as (_ & GP & _ & _ & _ & _ & _ & _ & _ & GHH & Gmok & _ & _ & _ & _ & GFR & _ & _ & _).
  destruct Gmok as (Hh & Hlz & _).
  destruct GFR as (_ & Gdef).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & HSS & HPS & _).
  pose proof Htop as HT. pose proof OI as (_ & _ & HISm). pose proof AP as (AP1 & _). unfold PML.apart in AP1.
  pose proof (gcells (bx + PMES.benc L eg) M model cr _ gp 0 0 true g0 0 eg GI) as (G240 & GVT & _ & G152 & _ & Gro & _).
  pose proof GP as GP'. unfold PML.parser_at in GP'.
  destruct GP' as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  assert (Hsb : 0 <= sb /\ sb + 66 <= hl_ceil L /\ 4096 <= sb).
  { apply (blkW M model cr _ GHH (sb, 66)). apply in_or_app. left. cbn. right. left. reflexivity. }
  assert (U568 : L5.u64_at RSEGS M (Rr + 568) sb).
  { replace (Rr + 568) with (Rr + 320 + 248) by lia. exact A248. }
  assert (U576 : L5.u64_at RSEGS M (Rr + 576) (sb + 1)).
  { replace (Rr + 576) with (Rr + 320 + 256) by lia. exact A256. }
  assert (DEF576 : L5.defined M (Rr + 576) 8).
  { apply (L5.defined_sub M (Rr + 320) 272); [exact Adef | lia | lia]. }
  refine (RS.s_rn_entry FPM fx R1 M model K (sp - 32) Rr IS 0 sb (sb + 1) RT.RD_R_NEXT Hh Hlz Hfp Ha2 _ Ha10 Ha1 _ _ _ HISm Gro G240 GVT G152 _ _ U568 _ U576 _ _ DEF576 _ _ _ _).
  - unfold RS.spok in *. split; [split|]; [unfold SS in *; lia | lia | exact (i_al16 32 Y2 eq_refl)].
  - unfold RT.RD_R_NEXT. lia.
  - unfold RS.pok. lia.
  - unfold RS.pok. lia.
  - lia.
  - reflexivity.
  - lia.
  - right. unfold RS.pok. lia.
  - intros i Hi. apply Gdef. unfold SS in *. lia.
  - lia.
  - lia.
  - lia.
  - intros fx' R' M' Hfp' H2' H1' H10' H11' H8' H9' H18' Hk' Hfr U72 U80 U81 U576' SAM MG.
    rewrite Ha11, L5.unsigned_lit in U80 by lia.
    assert (TP' : getr R' 4%bv = Z_to_bv 64 PML.TP).
    { rewrite (Hk' 4%bv ltac:(ckin)), (Hk01 4%bv ltac:(ckin)). exact R0tp. }
    assert (K06 : TK.keepsR RS.KS06 R0 R').
    { apply (TK.keepsR_trans RS.KS06 R0 R1 R').
      - apply (i_keeps_sub RS.KS01 RS.KS06 R0 R1 Hk01). intros q Hq. cbv [RS.KS06 RS.KS01 In] in Hq |- *. tauto.
      - apply (i_keeps_sub RS.KS012 RS.KS06 R1 R' Hk'). intros q Hq. cbv [RS.KS06 RS.KS012 In] in Hq |- *. tauto. }
    exact (HN R1 (conj Ha8 (conj Ha9 Hk01)) fx' R' M model cr gp sb bptr eg M' Hfp' GI ES EA HD HRF Hfr U72 U80 U81 U576' SAM MG
             H2' H1' TP' H10' H11' H8' H9' H18' K06).
Qed.

(* READ_NEXT entry: reader reset outlined at 0x474d4, vec_push of the zero byte, first LOOPA (ubsan): deliver rn_entryU. *)
Lemma rn_entryU : (forall R1, r1ok R1 -> atAU R1) -> rn_entry_stmtU.
Proof using All.
  intros HA. apply rn_walk. intros R1 H1. exact (rn_call R1 (rn_ret R1 (HA R1 H1))).
Qed.
End Run.
End H.
End RDXWUE.
