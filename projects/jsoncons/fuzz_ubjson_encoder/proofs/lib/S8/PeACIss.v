(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAa PeAIssStmts PeAIss1 PeAIss2 PeACIss2 PeACIss3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEACISS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem iss_ctor_c_ok : PMSPA.locale_ctor_spec RSEGS PeCLayoutA.CADDR_A L ar HI -> PMSPA.opnew_spec RSEGS PeCLayoutA.CADDR_A L ar HI -> PECSA.iss_ctor_c_spec L ar HI.
Proof.
  intros LOC' NEW'. assert (LOC : PMA.locale_ctor_spec L ar HI) by exact LOC'. assert (NEW : PMA.opnew_spec L ar HI) by exact NEW'. clear LOC' NEW'.
  unfold PECSA.iss_ctor_c_spec, PECSPA.iss_ctor_c_spec. cbn [pa_iss_ctor PeCLayoutA.CADDR_A].
  intros fx R M model K LB FF LK Aw cr ois os sp r s b l HH AM K0 ENT FRM FRS A10 A11 A12 AO AOS EOS O8 OS8 ODEF ACC VS INCL SZ LNG LEN BYT BASE LOCb CRED KONT.
  rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  assert (PRE : PMAIS.pre L ar HI R M model K LB FF LK Aw cr ois os sp r s b).
  { exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj A10 (conj A11 (conj A12 (conj AO (conj AOS (conj EOS (conj O8 (conj OS8
           (conj ODEF (conj ACC (conj VS (conj INCL (conj SZ (conj LNG (conj BASE (conj LOCb CRED)))))))))))))))))))))). }
  assert (KT : PEACIS2.kont_c L ar HI R M model K LB FF LK Aw cr ois sp r s b l) by exact KONT.
  apply (PMAIS1.head L ar C IL HI LY HIok ICok ILY LOC fx R M model K LB FF LK Aw cr ois os sp r s b PRE).
  intros fx1 R1 M1 model1 LK1 Aw1 MID.
  apply (PMAIS2.memsets L ar C HI LY HIok fx1 R M model K LB FF LK Aw cr ois os sp r s b R1 M1 model1 LK1 Aw1 PRE MID).
  intros fx2 R2 M2 model2 LK2 Aw2 MID2.
  destruct s as [n|c0 n p0].
  - exact (PEACIS2.short_c L ar C HI LY HIok fx2 R M model K LB FF LK Aw cr ois os sp r n b R2 M2 model2 LK2 Aw2 l PRE KT LEN BYT MID2).
  - exact (PEACIS3.long_c L ar C IL HI LY HIok ICok ILY NEW fx2 R M model K LB FF LK Aw cr ois os sp r c0 n p0 b R2 M2 model2 LK2 Aw2 l PRE KT LEN BYT MID2).
Qed.
End WithHeap.
End PEACISS.
