(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS
PmParSpecs PmParSpecsS PmTxtSpecs
PmSParse PmSRtv PmSRdVal PmSRdKey PmSEnd PmSGetLen PmSRdSpan3 PmSSrd5 PmSResize PmSrcSFillTb PmSrcSFill PmSrcSPeek PmSrcSIgnore
PmSrcSRead PmSrcSXsgetn PmValS PmB10S PmBaS PmBoS PmErrS Js0Opnew Js0Opdel.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSCL.
Import PMS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem parse_closed : PMS.parse_spec L HI.
Proof.
assert (OPN : PMS.opnew_spec L HI) by (eapply L5NEW.opnew_ok; eassumption).
assert (OPD : PMS.opdel_spec L HI) by (eapply L5DEL.opdel_ok; eassumption).
assert (MKE : PMS.make_ec_spec L HI) by (eapply PMERR.make_ec_ok; eassumption).
assert (XS : PMPSS.xsgetn_spec L HI) by (eapply PMSXG.xsgetn_ok; eassumption).
assert (FB : PMPSS.fill_buffer_spec L HI) by (eapply PMSFB.fill_buffer_ok; eassumption).
assert (FBT : PMTXS.fill_buffer_tb_spec RSEGS AD L HI) by (eapply PMSFBT.fill_buffer_tb_ok; eassumption).
assert (PK : PMPSS.peek_spec L HI) by (eapply PMSPK.peek_ok; eassumption).
assert (IG : PMPSS.ignore_spec L HI) by (eapply PMSIG.ignore_ok; eassumption).
assert (SR : PMPSS.src_read_spec L HI) by (eapply PMSRD.src_read_ok; eassumption).
assert (GL : PMS.get_length_spec L HI) by (eapply PMSGL.get_length_ok; eassumption).
assert (RZ : PMS.str_resize_spec L HI) by (eapply PMSRZ.str_resize_ok; eassumption).
assert (SRD : PMTXS.srd_read_spec RSEGS AD L HI) by (eapply PMSSR5.srd_read_ok; eassumption).
assert (RS : PMS.read_span_spec L HI) by (eapply PMSRS3.read_span_ok; eassumption).
assert (VA : PMS.validate_spec L) by (eapply PMVA.validate_ok; eassumption).
assert (B10 : PMS.is_base10_spec L) by (eapply PMB10.is_base10_ok; eassumption).
assert (BA : PMS.begin_array_spec L HI) by (eapply PMBA.begin_array_ok; eassumption).
assert (BO : PMS.begin_object_spec L HI) by (eapply PMBO.begin_object_ok; eassumption).
assert (RV : PMS.read_value_spec L HI) by (eapply PMSRV.read_value_ok; eassumption).
assert (RT : PMS.rtv_spec L HI) by (eapply PMSRT.rtv_ok; eassumption).
assert (RK : PMS.read_key_spec L HI) by (eapply PMSRK.read_key_ok; eassumption).
assert (EA : PMS.end_array_spec L HI) by (eapply PMSEND.end_array_ok; eassumption).
assert (EO : PMS.end_object_spec L HI) by (eapply PMSEND.end_object_ok; eassumption).
eapply PMSLP.parse_ok; eassumption.
Qed.
End WithHeap.
End PMSCL.
