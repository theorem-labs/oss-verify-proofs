(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PeSpecsBXJ PeBCRdCtorStmts PeBCRdCtor1 PeBCRdCtor2 PeBCRdCtor3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBRD.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem reader_ctor_ok : PMB.locale_ctor_spec L ar HI -> PMB.opnew_spec L ar HI -> PMBX.slow_mi_spec L ar HI -> PECSB.reader_ctor_spec L ar HI.
Proof.
  intros LOC NEW PSH. unfold PECSB.reader_ctor_spec, PMSPA.reader_ctor_spec.
  intros fx R M model K LB FF LK Aw cr sp r fb oo oa str sm HH AM K0 ENT FRM FRS FOK A10 A11 A12 A13 EOO ODEF ACC ACCO OO0 OO8 OO24 ISS BASE LOCb CRED KONT.
  unfold PMSPA.o_p, PMSPA.o_is in *. cbn [pa_off_p pa_off_is pa_reader_ctor PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *. subst oo.
  rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl13 in A13.
  replace (fb + 592 + 464 + 8) with (fb + 592 + 472) in OO8 by lia. replace (fb + 592 + 464 + 24) with (fb + 592 + 488) in OO24 by lia.
  assert (PRE : PMBRS.pre L ar HI R M model K LB FF LK Aw cr sp r fb oa str sm).
  { exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj A10 (conj A11 (conj A12 (conj A13 (conj ODEF (conj ACC (conj ACCO
           (conj OO0 (conj OO8 (conj OO24 (conj ISS (conj BASE (conj LOCb CRED)))))))))))))))))))). }
  assert (KT : PMBRS.kont L ar HI R M model K LB FF LK Aw cr sp r fb) by exact KONT.
  apply (PMBRD1.head L ar C IL HI LY HIok ICok ILY LOC fx R M model K LB FF LK Aw cr sp r fb oa str sm PRE).
  intros fx1 R1 M1 model1 LK1 Aw1 MID1.
  apply (PMBRD2.memsets L ar C IL HI LY HIok ICok ILY fx1 R M model K LB FF LK Aw cr sp r fb oa str sm R1 M1 model1 LK1 Aw1 PRE MID1).
  intros fx2 R2 M2 model2 LK2 Aw2 MID2.
  exact (PMBRD3.tail L ar C IL HI LY HIok ICok ILY NEW PSH fx2 R M model K LB FF LK Aw cr sp r fb oa str sm R2 M2 model2 LK2 Aw2 PRE MID2 KT).
Qed.
End WithHeap.
End PMBRD.
