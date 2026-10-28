(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAmc_b PnSpecsAX_b PnSpecsAXD_b PnSpecsAXR_b PnSpecsAXC_b PnRunA_b PnRunAa_b PnAImgGap_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PnAClosePkg_b PnAOpnew_b PnAOpdel_b PnAMakeEc_b PnASrcXsgetn_b Ba0PgSrcFill_b Ba0PgSrcFillTb_b Ba0PgSrcRead_b PnAResize_b Ba0PgSrd5_b Ba0PgRdSpan3_b PnAVal_b PnAPushBack_b
     PnAReadCs_b PnAReadEn_b PnAReadStr_b PnAAnn_b PnAEndDoc_b PnAEndArr_b PnAEmbC_b PnAEmbCF_b PnABegDoc_b PnABegDocU1E_b PnABegDocU1V_b PnABegDocU1P_b PnABegDocU1T_b PnABegArr_b PnABegArrU1A_b PnABegArrU1P_b Ba0PgV8Close_b PnARdVal_b PnAParse_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNACL.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.

(* [comment removed for export] *)
Hypothesis DEC128 : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNSAXD.dec128_spec RSEGS PMA.AD PMA.AN PMA.AAD L ar HIR.

(* [comment removed for export] *)
Section Inst.
Variables (ar : asan_run) (HIR : asan_iface).
Hypothesis IOK : PNACP.inst_ok L C IL ar HIR.
Let HIok : HAJ.asan_iface_okR L ar C SCFG HIR := proj1 IOK.
Let ICok : aicpt_ok L ar IL SCFG HIR := proj1 (proj2 IOK).
Let EXT : HAJ.asan_ext_ok L ar SCFG HIR PMA.EXT := proj1 (proj2 (proj2 IOK)).
Let GAP : PMAGAP.rt_img_gap HIR := proj2 (proj2 (proj2 IOK)).

Lemma opnew_c : PMA.opnew_spec L ar HIR.
Proof. exact (PMAOPN.opnew_ok L ar C HIR LY HIok). Qed.
Lemma opdel_c : PMA.opdel_spec L ar HIR.
Proof. exact (PMAOPD.opdel_ok L ar C HIR LY HIok). Qed.
Lemma make_ec_c : PNRAa.make_ec_spec L ar HIR.
Proof. exact (PNAMKE.make_ec_ok L ar C HIR LY HIok EXT). Qed.
Lemma xsgetn_c : PMA.xsgetn_spec L ar HIR.
Proof. exact (PMAXG.xsgetn_ok L ar C IL HIR LY HIok ICok ILY). Qed.
Lemma fill_buffer_c : PNRAa.fill_buffer_spec L ar HIR.
Proof. exact (PGSFBA.fill_buffer_okG L ar C HIR LY HIok IL ICok ILY xsgetn_c). Qed.
Lemma fill_buffer_tb_c : PNRAa.fill_buffer_tb_spec L ar HIR.
Proof. exact (PGSFBTA.fill_buffer_tb_okG L ar C HIR LY HIok IL ICok ILY xsgetn_c). Qed.
Lemma src_read_c : PNRAa.src_read_spec L ar HIR.
Proof. exact (PGSRDA.src_read_okG L ar C HIR LY HIok IL ICok ILY fill_buffer_c xsgetn_c). Qed.
Lemma str_resize_c : PMA.str_resize_spec L ar HIR.
Proof. exact (PMARZ.str_resize_ok L ar C IL HIR LY HIok ICok ILY opnew_c opdel_c). Qed.
Lemma srd_read_c : PNRAa.srd_read_spec L ar HIR.
Proof. exact (PGSSRA5.srd_read_okG L ar C HIR LY HIok IL ICok ILY str_resize_c src_read_c fill_buffer_tb_c). Qed.
Lemma read_span_c : PNRAa.read_span_spec L ar HIR.
Proof. exact (PGSRSA3.read_span_okG L ar C HIR LY HIok fill_buffer_c srd_read_c). Qed.
Lemma validate_c : PMA.validate_spec L ar HIR.
Proof. exact (PMAVAL.validate_ok L ar C HIR LY HIok GAP). Qed.
Lemma str_push_back_c : PNRAa.str_push_back_spec L ar HIR.
Proof. exact (PNAPB.str_push_back_ok L ar C IL HIR LY HIok ICok ILY opnew_c opdel_c). Qed.
Lemma read_cstring_c : PNRAa.read_cstring_spec L ar HIR.
Proof. exact (PNACS.read_cstring_ok L ar C HIR LY HIok src_read_c str_push_back_c make_ec_c). Qed.
Lemma read_e_name_c : PNRAa.read_e_name_spec L ar HIR.
Proof. exact (PNACEN.read_e_name_ok L ar C IL HIR LY HIok ICok ILY read_cstring_c validate_c make_ec_c). Qed.
Lemma read_string_c : PNRAa.read_string_spec L ar HIR.
Proof. exact (PNARST.read_string_ok L ar C HIR LY HIok src_read_c read_span_c make_ec_c). Qed.
Lemma ann_shrink_c : PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HIR 0xab89c.
Proof. exact (PNAANN.ann_shrink_ok L ar C HIR LY HIok EXT). Qed.
Lemma vec_clear_c : PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HIR 0xab740.
Proof. exact (PNAANN.vec_clear_ok L ar C HIR LY HIok EXT). Qed.
Lemma end_document_c : PNRAa.end_document_spec L ar HIR.
Proof. exact (PNAED.end_document_ok L ar C IL HIR LY HIok ICok ILY ann_shrink_c make_ec_c). Qed.
Lemma end_array_c : PNRAa.end_array_spec L ar HIR.
Proof. exact (PNAEA.end_array_ok L ar C IL HIR LY HIok ICok ILY ann_shrink_c make_ec_c). Qed.
Lemma push_cont_c : PNSAXR.push_cont_slow_spec RSEGS PMA.AD L ar HIR 0xb2758.
Proof. exact (PNAEC.push_cont_slow_ok L ar C HIR LY HIok EXT opnew_c opdel_c). Qed.
Lemma ann_grow_c : PNAECF.ann_grow_spec L ar HIR 0xad4b8.
Proof. exact (PNAECF.ann_grow_ok L ar C HIR LY HIok EXT). Qed.
Lemma begin_document_c : PNRAa.begin_document_spec L ar HIR.
Proof.
  exact (PNABD.begin_document_ok L ar C IL HIR LY HIok ICok ILY src_read_c make_ec_c push_cont_c ann_grow_c
           (PNABDU1E.bd_u1_elem_ok L ar C IL HIR LY HIok ICok ILY) (PNABDU1V.bd_u1_m3vis_ok L ar C IL HIR LY HIok ICok ILY)
           (PNABDU1P.bd_u1_push_ok L ar C HIR LY HIok) (PNABDU1T.bd_u1_tail_ok L ar C IL HIR LY HIok ICok ILY)).
Qed.
Lemma begin_array_c : PNRAa.begin_array_spec L ar HIR.
Proof.
  exact (PNABA.begin_array_ok L ar C IL HIR LY HIok ICok ILY src_read_c make_ec_c push_cont_c ann_grow_c
           (PNABAU1A.ba_u1_abaU_ok' L ar C IL HIR LY HIok ICok ILY) (PNABAU1P.ba_u1_push_ok L ar C HIR LY HIok)).
Qed.
Lemma read_span_v_c : PNRAa.read_span_v_spec L ar HIR.
Proof. exact (PGVCLA.read_span_v_closed L ar C HIR LY HIok EXT IL ICok ILY opnew_c opdel_c xsgetn_c). Qed.
Lemma read_value_c : PNRAa.read_value_spec L ar HIR.
Proof.
  exact (PNARVL.read_value_ok L ar C HIR LY HIok IL ICok ILY src_read_c make_ec_c begin_document_c begin_array_c read_string_c validate_c read_span_v_c
           str_push_back_c read_cstring_c str_resize_c (DEC128 ar HIR IOK)).
Qed.
Lemma parse_c : PNRAa.parse_spec L ar HIR.
Proof.
  exact (PNAPA.parse_ok L ar C IL HIR LY HIok ICok ILY begin_document_c read_value_c read_e_name_c end_document_c end_array_c src_read_c make_ec_c vec_clear_c).
Qed.
End Inst.

(* [comment removed for export] *)
Theorem parse_closed : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNRAa.parse_spec L ar HIR.
Proof. intros ar HIR IOK. exact (parse_c ar HIR IOK). Qed.
End Close.
End SCFG_1.
End PNACL.
