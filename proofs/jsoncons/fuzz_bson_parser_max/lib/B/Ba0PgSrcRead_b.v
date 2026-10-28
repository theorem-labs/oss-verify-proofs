(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgSrcRead32_b Ba0PgSrcRead16_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem src_read_okG : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PMA.xsgetn_spec L ar HI -> PGSA.src_read_specG RSEGS PMA.AD L ar HI PNRA.FCB.
Proof.
  intros FB XS. unfold PGSA.src_read_specG, PGSA.src_specG.
  intros O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra HH AM K0 ENT FRM FRS OFR A10 ARGS WX PA IA BASE INCS KONT.
  assert (AL : sp mod 32 = 0 \/ sp mod 32 = 16).
  { destruct ENT as (_ & _ & _ & _ & _ & (A16 & _) & _). clear - A16. lia. }
  destruct AL as [AL|AL].
  - exact (PGSRD32.src_read_ok32 L ar C HI LY HIok IL ICok ILY FB XS O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra
             HH AM K0 ENT FRM FRS OFR A10 (conj AL ARGS) WX PA IA BASE INCS KONT).
  - exact (PGSRD16.src_read_ok16 L ar C HI LY HIok IL ICok ILY FB XS O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra
             HH AM K0 ENT FRM FRS OFR A10 (conj AL ARGS) WX PA IA BASE INCS KONT).
Qed.

End WithHeap.
End PGSRDA.
