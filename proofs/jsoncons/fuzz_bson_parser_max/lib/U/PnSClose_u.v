(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnStatics PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     Bs0Opnew_u Bs0Opdel_u PnSMakeEc_u PnSrcSXsgetn_u Bs0PgSrcFill_u Bs0PgSrcFillTb_u Bs0PgSrcRead_u PnSResize_u Bs0PgSrd5_u Bs0PgRdSpan3_u PnValS_u PnSPushBack_u
     PnSReadCs_u PnSReadEn_u PnSReadStr_u PnSEnd_u PnSBdoc_u PnSBarr_u PnSVu8Grow_u PnSSrdV5_u PnSRdSpanV3_u PnSRdVal_u PnSDec128_u PnSParse_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSCL.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem parse_closed : PNRS.parse_spec L HI.
Proof.
  assert (OPN : PMS.opnew_spec L HI) by (eapply L5NEW.opnew_ok; eassumption).
  assert (OPD : PMS.opdel_spec L HI) by (eapply L5DEL.opdel_ok; eassumption).
  assert (MKE : PNRS.make_ec_spec L HI) by (eapply PNSME.make_ec_ok; eassumption).
  assert (XS : PMPSS.xsgetn_spec L HI) by (eapply PMSXG.xsgetn_ok; eassumption).
  assert (FB : PNRS.fill_buffer_spec L HI) by (eapply PGSFB.fill_buffer_okG; eassumption).
  assert (FBT : PNRS.fill_buffer_tb_spec L HI) by (eapply PGSFBT.fill_buffer_tb_okG; eassumption).
  assert (SRD : PNRS.src_read_spec L HI) by (eapply PGSRD.src_read_okG; eassumption).
  assert (RZ : PMS.str_resize_spec L HI) by (eapply PMSRZ.str_resize_ok; eassumption).
  assert (SR5 : PNRS.srd_read_spec L HI) by (eapply PGSSR5.srd_read_okG; eassumption).
  assert (RSP : PNRS.read_span_spec L HI) by (eapply PGSRS3.read_span_okG; eassumption).
  assert (VAL : PMS.validate_spec L) by (eapply PMVA.validate_ok; eassumption).
  assert (PB : PNRS.str_push_back_spec L HI) by (eapply PNSPB.str_push_back_ok; eassumption).
  assert (RCS : PNRS.read_cstring_spec L HI) by (eapply PNSCS.read_cstring_ok; eassumption).
  assert (REN : PNRS.read_e_name_spec L HI) by (eapply PNSEN.read_e_name_ok; eassumption).
  assert (RST : PNRS.read_string_spec L HI) by (eapply PNSRST.read_string_ok; eassumption).
  assert (ED : PNRS.end_document_spec L HI) by (eapply PNSEND.end_document_ok; eassumption).
  assert (EA : PNRS.end_array_spec L HI) by (eapply PNSEND.end_array_ok; eassumption).
  assert (BD : PNRS.begin_document_spec L HI) by (eapply PNSBD.begin_document_ok; eassumption).
  assert (BA : PNRS.begin_array_spec L HI) by (eapply PNSBA.begin_array_ok; eassumption).
  assert (VRZ : PNRS.vu8_resize_spec L HI) by (eapply PNSVG.vu8_resize_ok; eassumption).
  assert (SRV : PNRS.srd_read_v_spec L HI) by (eapply PNSSV5.srd_read_v_okG; eassumption).
  assert (RSV : PNRS.read_span_v_spec L HI) by (eapply PNSRSV3.read_span_v_okG; eassumption).
  assert (DEC : PNRS.dec128_spec L HI) by (eapply PNSDEC.dec128_closed; eassumption).
  assert (RV : PNRS.read_value_spec L HI) by (eapply PNSRVL.read_value_ok; eassumption).
  eapply PNSPA.parse_ok; eassumption.
Qed.

End WithHeap.
End PNSCL.
