(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PnLayout PnLayoutA PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs PmSpecsA PnSpecsAa PnSpecsAX PgSrc PgV8 PgSrcA PgV8A PnRun PnRunA PnRunAa
     PnAReaderCtorStmts PnAReaderCtor1 PnAReaderCtor2 PnAReaderCtor3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARC.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem reader_ctor_ok : PMA.locale_ctor_spec L ar HI -> PMA.opnew_spec L ar HI -> PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8 ->
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
