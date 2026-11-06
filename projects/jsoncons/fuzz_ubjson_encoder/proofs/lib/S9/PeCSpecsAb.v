(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Lemma addrs_wf_B : PMST.addrs_wf AD.
Proof.
  constructor; cbn; try lia.
  - intros iv [<-|[<-|[]]]; cbn; lia.
  - eexists. cbn. split; [left; reflexivity| cbn; lia].
Qed.

Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable P : PESKA.sink_policyA.
Definition make_ec_spec : Prop := @PECSPA.make_ec_spec SCFG_P RSEGS AD AAD EE L ar HI.
Definition rtv_spec : Prop := @PECSPA.rtv_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition read_value_spec : Prop := @PECSPA.read_value_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition read_key_spec : Prop := @PECSPA.read_key_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition begin_array_spec : Prop := @PECSPA.begin_array_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition begin_object_spec : Prop := @PECSPA.begin_object_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition end_array_spec : Prop := @PECSPA.end_array_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition end_object_spec : Prop := @PECSPA.end_object_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition get_length_spec : Prop := @PECSPA.get_length_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition parse_spec : Prop := @PECSPA.parse_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition reader_read_spec : Prop := @PECSPA.reader_read_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_null_spec : Prop := @PECSPA.v_null_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_bool_spec : Prop := @PECSPA.v_bool_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_uint64_spec : Prop := @PECSPA.v_uint64_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_int64_spec : Prop := @PECSPA.v_int64_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_double_spec : Prop := @PECSPA.v_double_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_arr_spec : Prop := @PECSPA.v_begin_arr_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_obj_spec : Prop := @PECSPA.v_begin_obj_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_arr_len_spec : Prop := @PECSPA.v_begin_arr_len_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_obj_len_spec : Prop := @PECSPA.v_begin_obj_len_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_end_arr_spec : Prop := @PECSPA.v_end_arr_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_end_obj_spec : Prop := @PECSPA.v_end_obj_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_key_spec : Prop := @PECSPA.v_key_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_string_spec : Prop := @PECSPA.v_string_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_flush_spec : Prop := @PECSPA.v_flush_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition put_length_spec : Prop := @PECSPA.put_length_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition evec_alloc_spec : Prop := @PECSPA.evec_alloc_spec SCFG_P RSEGS AD EE L ar HI.
Definition evec_sbdtor_spec : Prop := @PECSPA.evec_sbdtor_spec SCFG_P RSEGS AD EE L ar HI.
Definition peek_spec : Prop := @PECSPA.peek_spec SCFG_P RSEGS AD L ar HI.
Definition ignore_spec : Prop := @PECSPA.ignore_spec SCFG_P RSEGS AD L ar HI.
Definition src_read_spec : Prop := @PECSPA.src_read_spec SCFG_P RSEGS AD L ar HI 32.
Definition fill_buffer_spec : Prop := @PECSPA.fill_buffer_spec SCFG_P RSEGS AD L ar HI.
Definition read_span_spec : Prop := @PECSPA.read_span_spec SCFG_P RSEGS AD L ar HI.
Definition str_ctor_c_spec : Prop := @PECSPA.str_ctor_c_spec SCFG_P RSEGS AD L ar HI.
Definition iss_ctor_c_spec : Prop := @PECSPA.iss_ctor_c_spec SCFG_P RSEGS AD L ar HI.
Definition reset_spec : Prop := @PECSPA.reset_spec SCFG_P RSEGS AD L ar HI.
Definition reader_ctor_spec : Prop := @PECSPA.reader_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition pay_in (Q : list byte -> Prop) : Prop := @PECSPA.pay_in P Q.
Definition pay_out (Q : list byte -> Prop) : Prop := @PECSPA.pay_out P Q.

Definition push_mi_spec : Prop := @PMSAX.push_mi_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_miu_spec : Prop := @PMSAX.push_miu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_ms_spec : Prop := @PMSAX.push_ms_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_msu_spec : Prop := @PMSAX.push_msu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_shrink_spec : Prop := @PMSAX.ann_shrink_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_delete_spec : Prop := @PMSAX.ann_delete_spec SCFG_P RSEGS AD AAD L ar HI.
End Names.
End PECSB.
