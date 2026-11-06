(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU
PmParSpecs PmParSpecsU PmTxtSpecs
PmUParse PmURtv PmURdKey PmUEnd PmUGetLen PmURdSpan3 PmUSrd5 PmUResize PmSrcUFillTb PmSrcUFill PmSrcUPeek PmSrcUIgnore
PmSrcURead PmSrcUXsgetn PmValU PmB10U PmErrU Ju0Opnew Ju0Opdel PmURdVal PmBaUS PmBoUS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUClose () := ([""; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParSpecsU.PMPSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."], [["0HI"; "0L"; "1src_read_spec"; "2begin_array_spec"; "2begin_object_spec"; "2get_length_spec"; "2parse_spec"; "2read_span_spec"; "2read_value_spec"; "0SCFG_P"]]).
Module PMUCL.
Import PMU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Lemma src_read_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&2v9v1v0%43321").
Proof.
assert (XS : PMPSU.xsgetn_spec L HI) by (eapply PMUXG.xsgetn_ok; eassumption).
assert (FB : PMPSU.fill_buffer_spec L HI) by (eapply PMUFB.fill_buffer_ok; eassumption).
eapply PMUSRD.src_read_ok; eassumption.
Qed.
Lemma read_span_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&7v9v1v0%43321").
Proof.
assert (OPN : PMU.opnew_spec L HI) by (eapply L5NEWU.opnew_ok; eassumption).
assert (OPD : PMU.opdel_spec L HI) by (eapply L5DELU.opdel_ok; eassumption).
assert (XS : PMPSU.xsgetn_spec L HI) by (eapply PMUXG.xsgetn_ok; eassumption).
assert (FB : PMPSU.fill_buffer_spec L HI) by (eapply PMUFB.fill_buffer_ok; eassumption).
assert (FBT : PMTXS.fill_buffer_tb_spec RSEGS AD L HI) by (eapply PMUFBT.fill_buffer_tb_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
assert (RZ : PMU.str_resize_spec L HI) by (eapply PMURZ.str_resize_ok; eassumption).
assert (SRD : PMTXS.srd_read_spec RSEGS AD L HI) by (eapply PMUSR5.srd_read_ok; eassumption).
eapply PMURS3.read_span_ok; eassumption.
Qed.
Lemma get_length_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&5v9v1v0%43321").
Proof.
assert (MKE : PMU.make_ec_spec L HI) by (eapply PMERRU.make_ec_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
eapply PMUGL.get_length_ok; eassumption.
Qed.
Theorem parse_closed_rv : ltac2:(TCodec.tc2 tcn__PmUClose "8&8v9v1v0%43321&6%13543p031").
Proof.
intros RV.
assert (MKE : PMU.make_ec_spec L HI) by (eapply PMERRU.make_ec_ok; eassumption).
assert (XS : PMPSU.xsgetn_spec L HI) by (eapply PMUXG.xsgetn_ok; eassumption).
assert (FB : PMPSU.fill_buffer_spec L HI) by (eapply PMUFB.fill_buffer_ok; eassumption).
assert (PK : PMPSU.peek_spec L HI) by (eapply PMUPK.peek_ok; eassumption).
assert (IG : PMPSU.ignore_spec L HI) by (eapply PMUIG.ignore_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
assert (GL : PMU.get_length_spec L HI) by (apply get_length_closed).
assert (RS : PMU.read_span_spec L HI) by (apply read_span_closed).
assert (VA : PMU.validate_spec L) by (eapply PMVAU.validate_ok; eassumption).
assert (RT : PMU.rtv_spec L HI) by (eapply PMURT.rtv_ok; eassumption).
assert (RK : PMU.read_key_spec L HI) by (eapply PMURK.read_key_ok; eassumption).
assert (EA : PMU.end_array_spec L HI) by (eapply PMUEND.end_array_ok; eassumption).
assert (EO : PMU.end_object_spec L HI) by (eapply PMUEND.end_object_ok; eassumption).
eapply PMULP.parse_ok; eassumption.
Qed.
Theorem read_value_closed : ltac2:(TCodec.tc2 tcn__PmUClose ";&3v9v1v0%43321&4%13543&8%13765p031p061").
Proof.
intros BA BO.
assert (MKE : PMU.make_ec_spec L HI) by (eapply PMERRU.make_ec_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
assert (GL : PMU.get_length_spec L HI) by (apply get_length_closed).
assert (RS : PMU.read_span_spec L HI) by (apply read_span_closed).
assert (VA : PMU.validate_spec L) by (eapply PMVAU.validate_ok; eassumption).
assert (B10 : PMU.is_base10_spec L) by (eapply PMB10U.is_base10_ok; eassumption).
eapply PMURV.read_value_ok; eassumption.
Qed.
Lemma begin_array_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&3v9v1v0%43321").
Proof.
assert (MKE : PMU.make_ec_spec L HI) by (eapply PMERRU.make_ec_ok; eassumption).
assert (OPN : PMU.opnew_spec L HI) by (eapply L5NEWU.opnew_ok; eassumption).
assert (OPD : PMU.opdel_spec L HI) by (eapply L5DELU.opdel_ok; eassumption).
assert (XS : PMPSU.xsgetn_spec L HI) by (eapply PMUXG.xsgetn_ok; eassumption).
assert (FB : PMPSU.fill_buffer_spec L HI) by (eapply PMUFB.fill_buffer_ok; eassumption).
assert (PK : PMPSU.peek_spec L HI) by (eapply PMUPK.peek_ok; eassumption).
assert (IG : PMPSU.ignore_spec L HI) by (eapply PMUIG.ignore_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
assert (GL : PMU.get_length_spec L HI) by (apply get_length_closed).
eapply PMBAU.begin_array_ok; eassumption.
Qed.
Lemma begin_object_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&4v9v1v0%43321").
Proof.
assert (MKE : PMU.make_ec_spec L HI) by (eapply PMERRU.make_ec_ok; eassumption).
assert (OPN : PMU.opnew_spec L HI) by (eapply L5NEWU.opnew_ok; eassumption).
assert (OPD : PMU.opdel_spec L HI) by (eapply L5DELU.opdel_ok; eassumption).
assert (XS : PMPSU.xsgetn_spec L HI) by (eapply PMUXG.xsgetn_ok; eassumption).
assert (FB : PMPSU.fill_buffer_spec L HI) by (eapply PMUFB.fill_buffer_ok; eassumption).
assert (PK : PMPSU.peek_spec L HI) by (eapply PMUPK.peek_ok; eassumption).
assert (IG : PMPSU.ignore_spec L HI) by (eapply PMUIG.ignore_ok; eassumption).
assert (SR : PMPSU.src_read_spec L HI) by (apply src_read_closed).
assert (GL : PMU.get_length_spec L HI) by (apply get_length_closed).
eapply PMBOU.begin_object_ok; eassumption.
Qed.
Theorem parse_closed : ltac2:(TCodec.tc2 tcn__PmUClose "5&6v9v1v0%43321").
Proof. apply parse_closed_rv. apply read_value_closed; [apply begin_array_closed | apply begin_object_closed]. Qed.
Theorem parse_closed_bo : ltac2:(TCodec.tc2 tcn__PmUClose "8&4v9v1v0%43321&6%13543p031").
Proof. intros BO. apply parse_closed_rv. apply read_value_closed; [apply begin_array_closed | exact BO]. Qed.
Theorem parse_closed_ba_bo : ltac2:(TCodec.tc2 tcn__PmUClose ";&3v9v1v0%43321&4%13543&6%13765p031p061").
Proof. intros BA BO. apply parse_closed_rv. apply read_value_closed; assumption. Qed.
End WithHeap.
End PMUCL.
