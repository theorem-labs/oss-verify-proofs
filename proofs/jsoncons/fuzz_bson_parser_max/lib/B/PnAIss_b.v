(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PnAIssStmts_b PnAIss1_b PnAIss2_b PnAIss3s_b PnAIss3l_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAISS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem iss_ctor_ok : PMA.locale_ctor_spec L ar HI -> PMA.opnew_spec L ar HI -> PMA.iss_ctor_spec L ar HI.
Proof.
  intros LOC NEW. unfold PMA.iss_ctor_spec, PMSPA.iss_ctor_spec.
  intros fx R M model K LB FF LK Aw cr ois os sp r s b HH AM K0 ENT FRM FRS A10 A11 A12 AO AOS EOS O8 OS8 ODEF ACC VS INCL SZ LNG BASE LOCb CRED KONT.
  rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  assert (PRE : PMAIS.pre L ar HI R M model K LB FF LK Aw cr ois os sp r s b).
  { exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj A10 (conj A11 (conj A12 (conj AO (conj AOS (conj EOS (conj O8 (conj OS8
           (conj ODEF (conj ACC (conj VS (conj INCL (conj SZ (conj LNG (conj BASE (conj LOCb CRED)))))))))))))))))))))). }
  assert (KT : PMAIS.kont L ar HI R M model K LB FF LK Aw cr ois sp r s b) by exact KONT.
  apply (PMAIS1.head L ar C IL HI LY HIok ICok ILY LOC fx R M model K LB FF LK Aw cr ois os sp r s b PRE).
  intros fx1 R1 M1 model1 LK1 Aw1 MID.
  apply (PMAIS2.memsets L ar C HI LY HIok fx1 R M model K LB FF LK Aw cr ois os sp r s b R1 M1 model1 LK1 Aw1 PRE MID).
  intros fx2 R2 M2 model2 LK2 Aw2 MID2.
  destruct s as [n|c0 n p0].
  - exact (PMAIS3S.short L ar C HI LY HIok fx2 R M model K LB FF LK Aw cr ois os sp r n b R2 M2 model2 LK2 Aw2 PRE KT MID2).
  - exact (PMAIS3L.long L ar C IL HI LY HIok ICok ILY NEW fx2 R M model K LB FF LK Aw cr ois os sp r c0 n p0 b R2 M2 model2 LK2 Aw2 PRE KT MID2).
Qed.
End WithHeap.
End PMAISS.
