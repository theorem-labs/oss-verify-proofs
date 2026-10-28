(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PnAReaderCtorStmts_b PnAReaderCtor1_b PnAReaderCtor2_b PnAReaderCtor3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARC.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem reader_ctor_ok : PMA.locale_ctor_spec L ar HI -> PMA.opnew_spec L ar HI -> PNSAXR.push_root_slow_spec RSEGS PMA.AD L ar HI 0xad11c ->
  PNRAa.reader_ctor_spec L ar HI.
Proof.
  intros LOC NEW PSH. unfold PNRAa.reader_ctor_spec, PNRA.reader_ctor_spec.
  intros fx R M model K LB FF LK Aw cr sp r fb oo oa str sm HH AM K0 ENT FRM FRS FOK A10 A11 A12 A13 AOO OOAP OO8 ODEF ACC ACCO OO0 OO16 ISS BASE LOCb CRED KONT.
  unfold PNRA.o_p, PNRA.o_is, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is in *. cbn [PNL.pn_reader_ctor pa_off_p pa_off_is pa_vp_opts PNRAa.AD PNRAa.AN PMA.AD PMA.AN ADDR_A NADDR_A] in *.
  change PNM.MAX_DEPTH with 1024 in *. change PNM.PSIZE with 416 in *. change PNM.BSZ with 40 in *.
  assert (PRE : PNARCS.pre L ar HI R M model K LB FF LK Aw cr sp r fb oo oa str sm).
  { exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj A10 (conj A11 (conj A12 (conj A13 (conj AOO (conj OOAP (conj OO8 (conj ODEF (conj ACC
           (conj ACCO (conj OO0 (conj OO16 (conj ISS (conj BASE (conj LOCb CRED)))))))))))))))))))))). }
  assert (KT : PNARCS.kont L ar HI R M model K LB FF LK Aw cr sp r fb) by exact KONT.
  apply (PNARC1.head L ar C IL HI LY HIok ICok ILY LOC fx R M model K LB FF LK Aw cr sp r fb oo oa str sm PRE).
  intros fx1 R1 M1 model1 LK1 Aw1 MID1.
  apply (PNARC2.memsets L ar C IL HI LY HIok ICok ILY fx1 R M model K LB FF LK Aw cr sp r fb oo oa str sm R1 M1 model1 LK1 Aw1 PRE MID1).
  intros fx2 R2 M2 model2 LK2 Aw2 MID2.
  exact (PNARC3.tail L ar C IL HI LY HIok ICok ILY NEW PSH fx2 R M model K LB FF LK Aw cr sp r fb oo oa str sm R2 M2 model2 LK2 Aw2 PRE MID2 KT).
Qed.
End WithHeap.
End PNARC.
