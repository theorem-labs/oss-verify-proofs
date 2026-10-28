(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMS.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PnLayoutS_u.ADDR_S.

(* [comment removed for export] *)
Record layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = RSEGS;
  ly_tp : hl_tp L = pa_tp AD;
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0xeb000;
  ly_stack : hl_stack L = 8224;
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  ly_errno : hl_errno L = 0xc9f1c;
  ly_static : forall a, hl_alloc_static L a -> 0xea3c8 <= a < 0xea770;        (* [comment removed for export] *)
  ly_kpm : 0 <= hl_k_per_malloc L <= 8;
  ly_bov : 0 <= hl_b_overhead L <= 6350523;
  ly_malloc : hl_malloc L = 0x9cdd4;                                          (* [comment removed for export] *)
  ly_free : hl_free L = 0x9cc94;
  ly_ro_foot : forall a, hl_alloc_ro L a -> ~ (0xb83f0 <= a < 0xea228)                 (* [comment removed for export] *)
}.

Lemma addrs_wf_S : PMST.addrs_wf AD.
Proof.
  constructor; cbn; try lia.
  - intros iv [<-|[<-|[]]]; cbn; lia.
  - exists (0xc87f2, 0xc8f30). cbn. split; [auto| lia].
Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Definition opnew_spec := PMSP.opnew_spec RSEGS AD L HI.
Definition opdel_spec := PMSP.opdel_spec RSEGS AD L HI.
Definition opdel_sized_spec := PMSP.opdel_sized_spec RSEGS AD L HI.
Definition str_ctor_spec := PMSP.str_ctor_spec RSEGS AD L HI.
Definition locale_ctor_spec := PMSP.locale_ctor_spec RSEGS AD L HI.
Definition locale_dtor_spec := PMSP.locale_dtor_spec RSEGS AD L.
Definition iss_ctor_spec := PMSP.iss_ctor_spec RSEGS AD L HI.
Definition reader_ctor_spec := PMSP.reader_ctor_spec RSEGS AD L HI.
Definition syscat_spec := PMSP.syscat_spec RSEGS AD L HI.
Definition reset_spec := PMSP.reset_spec RSEGS AD L HI.
Definition make_ec_spec := PMSP.make_ec_spec RSEGS AD L HI.
Definition src_dtor_spec := PMSP.src_dtor_spec RSEGS AD L HI.
Definition ios_dtor_spec := PMSP.ios_dtor_spec RSEGS AD L HI.
Definition rtv_spec := PMSP.rtv_spec RSEGS AD L HI.
Definition read_value_spec := PMSP.read_value_spec RSEGS AD L HI.
Definition read_key_spec := PMSP.read_key_spec RSEGS AD L HI.
Definition begin_array_spec := PMSP.begin_array_spec RSEGS AD L HI.
Definition begin_object_spec := PMSP.begin_object_spec RSEGS AD L HI.
Definition end_array_spec := PMSP.end_array_spec RSEGS AD L HI.
Definition end_object_spec := PMSP.end_object_spec RSEGS AD L HI.
Definition get_length_spec := PMSP.get_length_spec RSEGS AD L HI.
Definition read_span_spec := PMSP.read_span_spec RSEGS AD L HI.
Definition parse_spec := PMSP.parse_spec RSEGS AD L HI.
Definition peek_spec := PMSP.peek_spec RSEGS AD L HI.
Definition ignore_spec := PMSP.ignore_spec RSEGS AD L HI.
Definition src_read_spec := PMSP.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec := PMSP.fill_buffer_spec RSEGS AD L HI.
Definition validate_spec := PMSP.validate_spec RSEGS AD L.
Definition is_base10_spec := PMSP.is_base10_spec RSEGS AD L.
Definition str_resize_spec := PMSP.str_resize_spec RSEGS AD L HI.
End Names.
End PMS.
