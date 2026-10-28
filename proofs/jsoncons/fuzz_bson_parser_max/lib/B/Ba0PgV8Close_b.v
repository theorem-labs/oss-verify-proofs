(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnSpecsAX_b PnSpecsAX8_b
     PnAAnnV8_b PnAAnnV8G_b Ba0PgSrcRead_b Ba0PgSrcFill_b Ba0PgSrcFillTb_b Ba0PgSrdV5_b Ba0PgRdSpanV3_b Ba0PgVu8Rz_b Ba0PgVu8Ap_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVCLA.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem vu8_append_closed : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI ->
  PGV8A.vu8_append_spec AsanUbsan.M.loaded_segments PMA.AD L ar HI PNRA.FCB (PNL.pn_vu8_append PMA.AN).
Proof.
  intros OPN OPD.
  exact (PGVAPA.vu8_append_ok L ar C HI LY HIok OPN OPD (PNAAV8G.ann_increase_v8_ok L ar C HI LY HIok EXT) (PNAAV8G.ann_new_v8_ok L ar C HI LY HIok EXT)
           (PNAAV8.ann_delete_v8_ok L ar C HI LY HIok EXT)).
Qed.

Theorem vu8_resize_closed : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PNRAa.vu8_resize_spec L ar HI.
Proof.
  intros OPN OPD. exact (PGVRZA.vu8_resize_ok L ar C HI LY HIok (vu8_append_closed OPN OPD) (PNAAV8.ann_shrink_v8_ok L ar C HI LY HIok EXT)).
Qed.

Section Icpt.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem srd_read_v_closed : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PMA.xsgetn_spec L ar HI -> PNRAa.srd_read_v_spec L ar HI.
Proof.
  intros OPN OPD XSG.
  pose proof (PGSFBA.fill_buffer_okG L ar C HI LY HIok IL ICok ILY XSG) as FB.
  exact (PGSSVA5.srd_read_v_okG L ar C HI LY HIok IL ICok ILY (vu8_resize_closed OPN OPD) (PGSRDA.src_read_okG L ar C HI LY HIok IL ICok ILY FB XSG)
           (PGSFBTA.fill_buffer_tb_okG L ar C HI LY HIok IL ICok ILY XSG)).
Qed.

Theorem read_span_v_closed : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PMA.xsgetn_spec L ar HI -> PNRAa.read_span_v_spec L ar HI.
Proof.
  intros OPN OPD XSG.
  exact (PGSRVA3.read_span_v_okG L ar C HI LY HIok (PGSFBA.fill_buffer_okG L ar C HI LY HIok IL ICok ILY XSG) (srd_read_v_closed OPN OPD XSG)
           (PNAAV8.clear_v8_ok L ar C HI LY HIok EXT)).
Qed.
End Icpt.
End WithHeap.
End PGVCLA.
