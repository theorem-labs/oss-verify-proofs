(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Lemma addrs_wf_S : PMST.addrs_wf AD.
Proof.
  constructor; cbn; try lia.
  - intros iv [<-|[<-|[]]]; cbn; lia.
  - eexists. cbn. split; [left; reflexivity| cbn; lia].
Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Definition make_ec_spec : Prop := PECS.make_ec_spec RSEGS AD EE L HI.
Definition rtv_spec : Prop := PECS.rtv_spec RSEGS AD EE L HI P.
Definition read_value_spec : Prop := PECS.read_value_spec RSEGS AD EE L HI P.
Definition read_key_spec : Prop := PECS.read_key_spec RSEGS AD EE L HI P.
Definition begin_array_spec : Prop := PECS.begin_array_spec RSEGS AD EE L HI P.
Definition begin_object_spec : Prop := PECS.begin_object_spec RSEGS AD EE L HI P.
Definition end_array_spec : Prop := PECS.end_array_spec RSEGS AD EE L HI P.
Definition end_object_spec : Prop := PECS.end_object_spec RSEGS AD EE L HI P.
Definition get_length_spec : Prop := PECS.get_length_spec RSEGS AD EE L HI P.
Definition parse_spec : Prop := PECS.parse_spec RSEGS AD EE L HI P.
Definition reader_read_spec : Prop := PECS.reader_read_spec RSEGS AD EE L HI P.
Definition v_null_spec : Prop := PECS.v_null_spec RSEGS AD EE L HI P.
Definition v_bool_spec : Prop := PECS.v_bool_spec RSEGS AD EE L HI P.
Definition v_uint64_spec : Prop := PECS.v_uint64_spec RSEGS AD EE L HI P.
Definition v_int64_spec : Prop := PECS.v_int64_spec RSEGS AD EE L HI P.
Definition v_double_spec : Prop := PECS.v_double_spec RSEGS AD EE L HI P.
Definition v_begin_arr_spec : Prop := PECS.v_begin_arr_spec RSEGS AD EE L HI P.
Definition v_begin_obj_spec : Prop := PECS.v_begin_obj_spec RSEGS AD EE L HI P.
Definition v_begin_arr_len_spec : Prop := PECS.v_begin_arr_len_spec RSEGS AD EE L HI P.
Definition v_begin_obj_len_spec : Prop := PECS.v_begin_obj_len_spec RSEGS AD EE L HI P.
Definition v_end_arr_spec : Prop := PECS.v_end_arr_spec RSEGS AD EE L HI P.
Definition v_end_obj_spec : Prop := PECS.v_end_obj_spec RSEGS AD EE L HI P.
Definition v_key_spec : Prop := PECS.v_key_spec RSEGS AD EE L HI P.
Definition v_string_spec : Prop := PECS.v_string_spec RSEGS AD EE L HI P.
Definition v_flush_spec : Prop := PECS.v_flush_spec RSEGS AD EE L HI P.
Definition put_length_spec : Prop := PECS.put_length_spec RSEGS AD EE L HI P.
Definition evec_alloc_spec : Prop := PECS.evec_alloc_spec RSEGS AD EE L HI.
Definition evec_sbdtor_spec : Prop := PECS.evec_sbdtor_spec RSEGS AD EE L HI.
Definition peek_spec : Prop := PECS.peek_spec RSEGS AD L HI.
Definition ignore_spec : Prop := PECS.ignore_spec RSEGS AD L HI.
Definition src_read_spec : Prop := PECS.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec : Prop := PECS.fill_buffer_spec RSEGS AD L HI.
Definition read_span_spec : Prop := PECS.read_span_spec RSEGS AD L HI.
Definition str_ctor_c_spec : Prop := PECS.str_ctor_c_spec RSEGS AD L HI.
Definition iss_ctor_c_spec : Prop := PECS.iss_ctor_c_spec RSEGS AD L HI.
Definition pay_in (Q : list byte -> Prop) : Prop := PECS.pay_in P Q.
Definition pay_out (Q : list byte -> Prop) : Prop := PECS.pay_out P Q.
End Names.
End PECSS.
