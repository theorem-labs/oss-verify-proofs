(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmStatics PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import CatExec CatSim Hoare ShapeAlg SpinAlg PmModel PmSpecs PgV8 PnModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNRS.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PnLayoutS_u.ADDR_S.
Abbreviation AN := PnLayoutS_u.NADDR_S.

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
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PNM.bpst),
    hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> PMSP.entry AD L R M sp r 1 -> PMSP.frame_ok AD L sp fb ->
    getr R 10%bv = Z_to_bv 64 (PNR.o_p AD fb) -> PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) M (PNR.o_p AD fb) (PNR.o_is AD fb) s ->
    PGV8.v8_size (PNM.b_bb s) = 0 -> length (PNM.b_stk s) = 1%nat ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) M' (PNR.o_p AD fb) (PNR.o_is AD fb) (PNR.bpst_reset s) ->
        L5C.hpres L LBX sp (PMSP.pm_scr 1) [(PNR.o_p AD fb + 8, 8); (PNR.o_bb AD fb, 24); (PNR.o_nb AD fb, 24); (PNR.o_tb AD fb, 24); (PNR.o_stk AD fb, 24)] M M' ->
        hi_heap HI (PNM.bparser_own s ++ LBX) cr M' (m_vmmaps model) ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R (PNL.pn_reset AN) M model) K.
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
