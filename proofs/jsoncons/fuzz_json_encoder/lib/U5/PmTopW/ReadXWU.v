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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import ReadXWHU ReadRoomWU ReadXWUB ReadXWUC ReadXWUX ReadXWUW ReadXWUA ReadXWUE.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RDXWU.
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

(* READ entry (32-byte frame, ubsan) and the group lemmas assembled. *)
Let rd_afterU := @RDXWUC.rd_afterU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.
Let setec_okU := @RDXWUX.setec_okU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.
Let rn_exitU := @RDXWUX.rn_exitU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.
Let ws1_okU := @RDXWUW.ws1_okU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.
Let loopA_okU := @RDXWUA.loopA_okU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.
Let rn_entryU := @RDXWUE.rn_entryU SCFG_P L HI STRTOD_SCR WD_SCR HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW LBo sp r Rr IS V E S2 ch kx bx rep g0 R0 M0 model0 K eg0 Hn HB G0 SPOK Hceil Hsptop Htop Prok OR OI OV OE AP OVX OS2 APX KX0 INch INrep NEch R0sp R0tp HK0 BX0 WR0 CONTU.

Lemma rd_entryU : rn_entry_stmtU -> forall (fx : FPState) M model cr gp sb bptr eg,
  PML.fp_ok fx -> ginvU M model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg -> PMX.enc_sync (PMS.ps_init sb bptr) eg -> egacc eg [] 0 -> gp = D ->
  getr R0 1%bv = Z_to_bv 64 r -> getr R0 10%bv = Z_to_bv 64 Rr -> getr R0 11%bv = Z_to_bv 64 E ->
  srealizes RSEGS SCFG (@PML.cfg fx R0 PML.PC_READ M model) K.
Proof.
  intros HN fx M model cr gp sb bptr eg Hfp GI ES EA HD Hr Ha0 Ha1.
  pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gmok & _ & _ & _ & _ & GFR & _ & _ & _).
  destruct Gmok as (Hh & Hlz & _).
  destruct GFR as (_ & Gdef).
  pose proof lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSS & HPS & _).
  pose proof Prok as Hra. unfold L5.ra_ok in Hra.
  apply (RS.s_rd_entry FPM fx R0 M model K sp r Hh Hlz Hfp R0sp SPOK Hr ltac:(lia)).
  - intros i Hi. apply Gdef. unfold SS in *. lia.
  - intros fx' R' M' Hfp' Hsp' Hra' H10 H11 H8 H9 Hk U8 U16 U24 SAM MG.
    rewrite Ha1 in H11, H8. rewrite Ha0 in H10, H9.
    refine (HN R' fx' M' model cr gp sb bptr eg H8 H9 Hk Hfp' _ ES EA HD _ Hsp' Hra' H10 H11).
    + exact (i_ginv_stack (bx + PMES.benc L eg) M M' model cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg (sp - 32) sp GI SAM MG ltac:(unfold SS in *; lia) ltac:(lia)).
    + exact (conj U8 (conj U16 U24)).
Qed.

Lemma ginv_initU : forall cr gp sb bptr,
  hi_heap HI (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg0) cr M0 (m_vmmaps model0) -> PML.model_ok model0 ->
  PML.reader_at M0 Rr IS V ch true (PMS.ps_init sb bptr) -> PML.wf_ps (PMS.ps_init sb bptr) -> PML.isrc_at M0 IS rep gp 0 -> PML.vis_at M0 V -> PML.ec_at M0 E 0 ->
  PML.ls_ok g0 M0 -> PMES.enc_inv M0 V S2 eg0 -> PML.lits_ok M0 -> PML.pcredit_x L cr (PMS.ps_init sb bptr) (kx + PMES.kenc L eg0) (bx + PMES.benc L eg0) ->
  gp = D -> L5.defined M0 (sp - SS) SS ->
  ginvU M0 model0 cr (PMS.ps_init sb bptr) gp 0 0 true g0 0 eg0.
Proof.
  intros cr gp sb bptr Hh Hmok RAT WF ISRC VIS EC LS EI LIT CR HD DEF.
  destruct (RB.reader_split M0 Rr IS V ch true _ RAT) as (RDR & PAR & _).
  unfold ginvU, RDXWUB.ginvU, RDXWHU.ginv, RIXW.ginv.
  split; [exact RDR|]. split; [exact PAR|].
  split; [split; [exact WF | intros _; unfold PML.ws_ok, PMS.ps_init; cbn; intros Hm; discriminate] |].
  split; [unfold PML.win_ok, PMS.ps_init; cbn; exact I |].
  split; [exact ISRC|]. split; [exact VIS|]. split; [exact EC|]. split; [exact LS|]. split; [left; reflexivity|].
  split; [exact Hh|]. split; [exact Hmok|]. split; [apply L5C.model_but_vm_refl|]. split; [exact CR|].
  split; [unfold PML.buf_bound, PML.winlen, PML.buf_need, PMS.ps_init; cbn -[Z.pow]; split; [lia | apply Z.pow_pos_nonneg; lia] |].
  split; [lia|].
  split; [unfold TK2.FR; split; [intros; reflexivity | intros a Ha; replace a with (sp - SS + (a - (sp - SS))) by lia; apply DEF; lia] |].
  split; [intros a _ _ Hn0; exact Hn0|].
  split; [exact EI | exact LIT].
Qed.

Lemma read_runU : forall (fx : FPState) cr gp sb bptr,
  PML.fp_ok fx ->
  hi_heap HI (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv eg0) cr M0 (m_vmmaps model0) -> PML.model_ok model0 ->
  PML.reader_at M0 Rr IS V ch true (PMS.ps_init sb bptr) -> PML.wf_ps (PMS.ps_init sb bptr) -> PML.isrc_at M0 IS rep gp 0 -> PML.vis_at M0 V -> PML.ec_at M0 E 0 ->
  PML.ls_ok g0 M0 -> PMES.enc_inv M0 V S2 eg0 -> PML.lits_ok M0 -> PML.pcredit_x L cr (PMS.ps_init sb bptr) (kx + PMES.kenc L eg0) (bx + PMES.benc L eg0) ->
  gp = D -> L5.defined M0 (sp - SS) SS -> PMX.enc_sync (PMS.ps_init sb bptr) eg0 ->
  getr R0 1%bv = Z_to_bv 64 r -> getr R0 10%bv = Z_to_bv 64 Rr -> getr R0 11%bv = Z_to_bv 64 E ->
  srealizes RSEGS SCFG (@PML.cfg fx R0 PML.PC_READ M0 model0) K.
Proof using All.
  intros fx cr gp sb bptr Hfp Hh Hmok RAT WF ISRC VIS EC LS EI LIT CR HD DEF ES Hr Ha0 Ha1.
  pose proof (rn_exitU rd_afterU) as HX.
  pose proof (ws1_okU HX) as HW.
  pose proof (setec_okU rd_afterU) as HS.
  pose proof (loopA_okU HX HW HS) as HA.
  pose proof (rn_entryU HA) as HE.
  apply (rd_entryU HE fx M0 model0 cr gp sb bptr eg0 Hfp); [| exact ES | exact egacc_nil | exact HD | exact Hr | exact Ha0 | exact Ha1].
  exact (ginv_initU cr gp sb bptr Hh Hmok RAT WF ISRC VIS EC LS EI LIT CR HD DEF).
Qed.
End Run.
Theorem read_xw_okU : PMXW.read_specxwU L HI STRTOD_SCR WD_SCR.
Proof using HIok LAY FPM VPUSH PSOMEWU SKIPWSW PCDW SETEC RCHUNKW.
  intros LBo cr sp r Rr IS V E S2 ch gp sb bptr kx bx rep g eg ps.
  intros fx R M model K Hh Hmok HK Hfp PRE CONT.
  destruct PRE as (ENT & A0 & A1 & RP & HGP & NE & HN & HBr & LSOK & G0 & EI & LIT & ES & KX & BX & CR & OVX & OS2 & AVS & ARV & ARS & AIV & AIS & AVE & ASE & WR).
  destruct ENT as (Hr & Hra & Hsp & Htp & STK).
  destruct RP as (RAT & WF & ISRC & VIS & EC & INch & INrep & OR & OI & OV & OE & P1 & P2 & P3 & P4 & P5 & P6).
  destruct STK as (Hal & Hlo & Hhi & Htop & Hdef).
  assert (E23 : 2 ^ 23 = 8388608) by reflexivity. assert (E40 : 2 ^ 40 = 1099511627776) by reflexivity. assert (E47 : 2 ^ 47 = 140737488355328) by reflexivity.
  assert (S0 : 0 <= PMX.READX_SCR STRTOD_SCR WD_SCR).
  { unfold PMX.READX_SCR, PMX.READNEXTX_SCR, PMX.PSOMEX_SCR, PMX.PFX_SCR.
    match goal with |- context [Z.max (Z.max ?a ?b) ?c] => pose proof (Z.le_max_l (Z.max a b) c); pose proof (Z.le_max_l a b) end.
    unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *. lia. }
  assert (SPOK : RS.spok sp) by (unfold RS.spok; lia).
  assert (Hceil : hl_ceil L + PMX.READX_SCR STRTOD_SCR WD_SCR <= sp) by lia.
  refine (@read_runU LBo sp r Rr IS V E S2 ch kx bx rep g R M model K eg
    HN HBr G0 SPOK Hceil Hhi Htop Hra OR OI OV OE (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 P6))))) OVX OS2
    (conj AVS (conj ARV (conj ARS (conj AIV (conj AIS (conj AVE ASE)))))) KX INch INrep NE Hsp Htp HK BX WR _
    fx cr gp sb bptr Hfp Hh Hmok RAT WF ISRC VIS EC LSOK EI LIT CR HGP Hdef ES Hr A0 A1).
  intros fx' R' M' model' cr' ps' code gp' rdst' g' eg' Hfp' SA PA IA EA LS GG EI' LI CR' WF' WFIN RPR HP MB HH.
  destruct WFIN as (Hcode & Hes & Hpay).
  apply (CONT fx' R' M' model' (PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg') cr' (lb_remove ch LBo) (RIXW.Wr Rr IS V E S2) Hfp'); [| exact RPR | exact HP | exact MB | exact HH].
  exists ps', code, gp', rdst', g', eg'.
  refine (conj SA (conj PA (conj IA (conj EA (conj LS (conj GG (conj EI' (conj LI (conj eq_refl (conj eq_refl (conj CR' (conj WF' (conj (RIXW.Wr_eq Rr IS V E S2) _))))))))))))).
  cbv zeta. exact (conj Hcode (conj Hes Hpay)).
Qed.
End H.
End RDXWU.
