(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep PmIssUStmts PmIssU1 PmIssU2 PmIssU3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMISSU.
Import PMU.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem iss_ctor_ok : PMU.locale_ctor_spec L HI -> PMU.opnew_spec L HI -> PMU.iss_ctor_spec L HI.
Proof.
intros LOC OPNEW. unfold PMU.iss_ctor_spec, PMSP.iss_ctor_spec.
intros fx R M model K LB cr ois os sp r s b HH MOK K0 ENT A10 A11 A12 Hspo Hoos Hostop Ho8 Hos8 DEFO VS INCL SZ LNG BASE LOCb CRED KONT.
rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
assert (PRE : PMISU.pre L HI R M model K LB cr ois os sp r s b).
{ unfold PMISU.pre. refine (conj HH (conj MOK (conj K0 (conj ENT (conj A10 (conj A11 (conj A12 (conj Hspo (conj Hoos (conj Hostop (conj Ho8 (conj Hos8
(conj DEFO (conj VS (conj INCL (conj SZ (conj LNG (conj BASE (conj LOCb CRED))))))))))))))))))). }
assert (KT : PMISU.kont L HI R M model K LB cr ois sp r s b) by exact KONT.
apply (PMISU1.head L HI LY HIok LOC fx R M model K LB cr ois os sp r s b PRE).
intros fx1 R1 M1 model1 MID.
destruct s as [n|c n p].
- apply (PMISU2.tail_short L HI LY HIok fx1 R M model K LB cr ois os sp r (PM.VShort n) b R1 M1 model1 n PRE KT eq_refl MID).
- apply (PMISU3.tail_long L HI LY HIok OPNEW fx1 R M model K LB cr ois os sp r (PM.VLong c n p) b R1 M1 model1 c n p PRE KT eq_refl MID).
Qed.
End Stage.
End PMISSU.
