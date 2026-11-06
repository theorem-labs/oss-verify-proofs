(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAb
PmBIssStmts PmBIss1 PmBIss2 PmBIss3s PmBIss3l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBISS.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Theorem iss_ctor_ok : PMB.locale_ctor_spec L ar HI -> PMB.opnew_spec L ar HI -> PMB.iss_ctor_spec L ar HI.
Proof.
intros LOC NEW. unfold PMB.iss_ctor_spec, PMSPA.iss_ctor_spec.
intros fx R M model K LB FF LK Aw cr ois os sp r s b HH AM K0 ENT FRM FRS A10 A11 A12 AO AOS EOS O8 OS8 ODEF ACC VS INCL SZ LNG BASE LOCb CRED KONT.
rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
assert (PRE : PMBIS.pre L ar HI R M model K LB FF LK Aw cr ois os sp r s b).
{ exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj A10 (conj A11 (conj A12 (conj AO (conj AOS (conj EOS (conj O8 (conj OS8
(conj ODEF (conj ACC (conj VS (conj INCL (conj SZ (conj LNG (conj BASE (conj LOCb CRED)))))))))))))))))))))). }
assert (KT : PMBIS.kont L ar HI R M model K LB FF LK Aw cr ois sp r s b) by exact KONT.
apply (PMBIS1.head L ar C IL HI LY HIok ICok ILY LOC fx R M model K LB FF LK Aw cr ois os sp r s b PRE).
intros fx1 R1 M1 model1 LK1 Aw1 MID.
apply (PMBIS2.memsets L ar C HI LY HIok fx1 R M model K LB FF LK Aw cr ois os sp r s b R1 M1 model1 LK1 Aw1 PRE MID).
intros fx2 R2 M2 model2 LK2 Aw2 MID2.
destruct s as [n|c0 n p0].
- exact (PMBIS3S.short L ar C HI LY HIok fx2 R M model K LB FF LK Aw cr ois os sp r n b R2 M2 model2 LK2 Aw2 PRE KT MID2).
- exact (PMBIS3L.long L ar C IL HI LY HIok ICok ILY NEW fx2 R M model K LB FF LK Aw cr ois os sp r c0 n p0 b R2 M2 model2 LK2 Aw2 PRE KT MID2).
Qed.
End WithHeap.
End PMBISS.
