(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmStatics PnLayout PnLayoutS PnStatics PnSpecsS PnRun.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNRS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PnLayoutS.ADDR_S.
Abbreviation AN := PnLayoutS.NADDR_S.

(* [comment removed for export] *)
Lemma addrs_wf_B : PNST.addrs_wf AD AN.
Proof.
  constructor; [exact PMS.addrs_wf_S| cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  (* [comment removed for export] *)
  cbn. repeat split; try lia. intros iv Hin. cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Definition begin_document_spec := PNR.begin_document_spec RSEGS AD AN L HI.
Definition begin_array_spec := PNR.begin_array_spec RSEGS AD AN L HI.
Definition end_document_spec := PNR.end_document_spec RSEGS AD AN L HI.
Definition end_array_spec := PNR.end_array_spec RSEGS AD AN L HI.
Definition read_e_name_spec := PNR.read_e_name_spec RSEGS AD AN L HI.
Definition read_value_spec := PNR.read_value_spec RSEGS AD AN L HI.
Definition read_cstring_spec := PNR.read_cstring_spec RSEGS AD AN L HI.
Definition read_string_spec := PNR.read_string_spec RSEGS AD AN L HI.
Definition parse_spec := PNR.parse_spec RSEGS AD AN L HI.
Definition reader_ctor_spec := PNR.reader_ctor_spec RSEGS AD AN L HI.
Definition reset_spec := PNR.reset_spec RSEGS AD AN L HI.
Definition make_ec_spec := PNR.make_ec_spec RSEGS AD AN L HI.
Definition str_push_back_spec := PNR.str_push_back_spec RSEGS AD AN L HI.
Definition str_push_back_short_spec := PNR.str_push_back_short_spec RSEGS AD AN L HI.
Definition from_int_spec := PNR.from_int_spec RSEGS AD AN L HI.
Definition dec128_spec := PNR.dec128_spec RSEGS AD AN L HI.
Definition src_read_spec := PNR.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec := PNR.fill_buffer_spec RSEGS AD L HI.
Definition fill_buffer_tb_spec := PNR.fill_buffer_tb_spec RSEGS AD L HI.
Definition read_span_spec := PNR.read_span_spec RSEGS AD L HI.
Definition srd_read_spec := PNR.srd_read_spec RSEGS AD L HI.
Definition read_span_v_spec := PNR.read_span_v_spec RSEGS AD AN L HI.
Definition srd_read_v_spec := PNR.srd_read_v_spec RSEGS AD AN L HI.
Definition vu8_resize_spec := PNR.vu8_resize_spec RSEGS AD AN L HI.
Definition vu8_append_spec := PNR.vu8_append_spec RSEGS AD AN L HI.
End Names.
End PNRS.
