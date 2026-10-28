(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs PmLayout PmLayoutA PmModel PmStatics PmStaticsA
     HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNRAa.
Abbreviation RSEGS := PMA.RSEGS.
Abbreviation AD := PMA.AD.
Abbreviation AAD := PMA.AAD.
Abbreviation AN := PMA.AN.
Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition begin_document_spec := @PNRA.begin_document_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition begin_array_spec := @PNRA.begin_array_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition end_document_spec := @PNRA.end_document_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition end_array_spec := @PNRA.end_array_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition read_e_name_spec := @PNRA.read_e_name_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition read_value_spec := @PNRA.read_value_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition read_cstring_spec := @PNRA.read_cstring_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition read_string_spec := @PNRA.read_string_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition parse_spec := @PNRA.parse_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition reader_ctor_spec := @PNRA.reader_ctor_spec SCFG_P RSEGS AD AN L ar HI.
Definition reset_spec := @PNRA.reset_spec SCFG_P RSEGS AD AN L ar HI.
Definition make_ec_spec := @PNRA.make_ec_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition str_push_back_spec := @PNRA.str_push_back_spec SCFG_P RSEGS AD AN L ar HI.
Definition str_push_back_short_spec := @PNRA.str_push_back_short_spec SCFG_P RSEGS AD AN L ar HI.
Definition from_int_spec := @PNRA.from_int_spec SCFG_P RSEGS AD AN L ar HI.
Definition dec128_spec := @PNRA.dec128_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition src_read_spec := @PNRA.src_read_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_spec := @PNRA.fill_buffer_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_tb_spec := @PNRA.fill_buffer_tb_spec SCFG_P RSEGS AD L ar HI.
Definition read_span_spec := @PNRA.read_span_spec SCFG_P RSEGS AD L ar HI.
Definition srd_read_spec := @PNRA.srd_read_spec SCFG_P RSEGS AD L ar HI.
Definition read_span_v_spec := @PNRA.read_span_v_spec SCFG_P RSEGS AD AN L ar HI.
Definition srd_read_v_spec := @PNRA.srd_read_v_spec SCFG_P RSEGS AD AN L ar HI.
Definition vu8_resize_spec := @PNRA.vu8_resize_spec SCFG_P RSEGS AD AN L ar HI.
Definition vu8_append_spec := @PNRA.vu8_append_spec SCFG_P RSEGS AD AN L ar HI.
Definition reader_read_spec := @PNRA.reader_read_spec SCFG_P RSEGS AD AN AAD L ar HI.
Definition vec_dtor_spec := @PNRA.vec_dtor_spec SCFG_P RSEGS AD AN L ar HI.
Definition vu8_dtor_spec := @PNRA.vu8_dtor_spec SCFG_P RSEGS AD AN L ar HI.
End Names.
End PNRAa.
