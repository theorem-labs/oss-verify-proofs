(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_061.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co ch cm bj cs b5.

(* [comment removed for export] *)
Module SpineMallocSec6IEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS10A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2eG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Ba_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ba_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S30G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ba 1 (SLit 0)] [mkVNA Y6Ba 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Ba]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1eA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1eZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S20G0G1A3S3S0S1S22G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2fG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Bb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Bb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S31G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Bb 1 (SLit 0)] [mkVNA Y6Bb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Bb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1fA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1fZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S21G0G1A3S3S0S1S23G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IEW2.

(* [comment removed for export] *)
Module SpineMallocSec6JEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineMallocSec6IEW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S39R2A2S6F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S3aR2A2S6F_;F_;Fa;").

Theorem esec_tail_2ha_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (C5B := C5Ba) (Y6A := Y6Aa) (Y6B := Y6Ba) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (sB := s6Ba) (s6 := s6a)
    (R6 := R6a) (HC5A := HC5Aa_0) (HC5B := HC5Ba_0) (FBA := FBAa_0) (FBB := FBBa_0) (Cert6A := Cert6Aa_0) (Cert6B := Cert6Ba_0) (E6A := E6Aa_0) (I6A := I6Aa_0)
    (E6B := E6Ba_0) (I6B := I6Ba_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0) (FX6 := FX6a_0) (XC6 := XC6a_0)
    (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0) (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0) (NXE6B := NXE6Ba_0) (ECert6B := ECert6Ba_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  eapply esec_g44 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6a) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  eapply esec_g45 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7a) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  eapply esec_g46 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8a) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (T9 := T9fa) (iM := iMfa)
    (s9 := s9fa) (R9 := R9fa) (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (He9 := He9fa_0) (Hchk9 := Hchk9fa_0) (HT9 := HT9fa_0) (FBC9 := FBC9fa_0) (FBT9 := FBT9fa_0)
    (NXC9 := NXC9fa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fa_0.
    eapply esec_g48_P with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfa) (swc := swcfa) (c1 := c1fa) (c2 := c2fa) (c4 := c4fa) (c5 := c5fa) (mc := mcfa)
    (xc := xcfa) (tyb := tybfa) (SELF := SELFfa_0) (NDF := NDFfa_0) (BNDF := BNDFfa_0) (COVF := COVFfa_0) (XFn := XFnfa_0) (BFb := BFbfa_0) (FPF := FPFfa_0)
    (FXF := FXFfa_0) (FPAR := FPARfa_0) (Hc1 := Hc1fa_0) (Hmc := Hmcfa_0) (Htyb := Htybfa_0) (Hxc := Hxcfa_0) (WCU := WCUfa_0) (SELU := SELUfa_0) (NDU := NDUfa_0)
    (BNDU := BNDUfa_0) (COVU := COVUfa_0) (W9 := W9fa_0) (D9 := D9fa_0) (XB9 := XB9fa_0) (s9 := sFfa) (ENT9 := ENT9fa_0) (SID9 := SID9fa_0) (G110 := G110fa_0)
    (DF9 := D9fa) (CertF := CertFfa_0)
      (NXEF := NXEFfa_0) (ECertF := ECertFfa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (T9 := T9qa) (iM := iMqa)
    (s9 := s9qa) (R9 := R9qa) (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (He9 := He9qa_0) (Hchk9 := Hchk9qa_0) (HT9 := HT9qa_0) (FBC9 := FBC9qa_0) (FBT9 := FBT9qa_0)
    (NXC9 := NXC9qa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qa_0.
    eapply esec_g48_P with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_2ha : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_2ha_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_2hb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (C5B := C5Bb) (Y6A := Y6Ab) (Y6B := Y6Bb) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (sB := s6Bb) (s6 := s6b)
    (R6 := R6b) (HC5A := HC5Ab_0) (HC5B := HC5Bb_0) (FBA := FBAb_0) (FBB := FBBb_0) (Cert6A := Cert6Ab_0) (Cert6B := Cert6Bb_0) (E6A := E6Ab_0) (I6A := I6Ab_0)
    (E6B := E6Bb_0) (I6B := I6Bb_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0) (FX6 := FX6b_0) (XC6 := XC6b_0)
    (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0) (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0) (NXE6B := NXE6Bb_0) (ECert6B := ECert6Bb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  eapply esec_g44 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6b) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  eapply esec_g45 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7b) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  eapply esec_g46 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8b) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (T9 := T9fb) (iM := iMfb)
    (s9 := s9fb) (R9 := R9fb) (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (He9 := He9fb_0) (Hchk9 := Hchk9fb_0) (HT9 := HT9fb_0) (FBC9 := FBC9fb_0) (FBT9 := FBT9fb_0)
    (NXC9 := NXC9fb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fb_0.
    eapply esec_g48_P with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (T9 := T9qb) (iM := iMqb)
    (s9 := s9qb) (R9 := R9qb) (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (He9 := He9qb_0) (Hchk9 := Hchk9qb_0) (HT9 := HT9qb_0) (FBC9 := FBC9qb_0) (FBT9 := FBT9qb_0)
    (NXC9 := NXC9qb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qb_0.
    eapply esec_g48_P with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_2hb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_2hb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JEW2.

(* [comment removed for export] *)
Module SpineCallocSec6IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_X"; "entailsA"; "la_state"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "ss_objs"; "swf"; "SLit"; "SVar"; "sprop_below"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "nil"; "true"; "bool"; "cons"; "list"; "nat"; "prod"; "app"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "O_UBs"; "F_par"; "CPC"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6IL.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "perm9fa"; "perm9fb"; "perm9qa"; "perm9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb"; "c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "carveS"; "BR"; "O_2"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "V_NCH"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S12Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S13bSbSbG0Lb;La;M1Lop;M2G2S13cG1Lop;M3G3S22S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S10S2VF;A1A1S117S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS13aS13S129A1S13S128A1A3S20ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S137A2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S137A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S137A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3Sb9S20S3A1A3A4S23G0Sf9S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3Sb9S20S3A1M0A3S23S3Se1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S22S7Se1SadSe7A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S22S12cSe7VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S79A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SadA1S2S79A1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S79A1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S4SadS2S79A1A2S79A3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S79A1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S79A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S118S79S16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7fA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S7fS10dSd3A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S22S125S7fS10dSd3Sc3S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd3S10dS11bS7fSc3A5Sc9A3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S7fA1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2Sc9A1A1A1SfS2S7fA1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S7fA1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S124Sc9SfS2S7fA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S89A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S9fA1S2S89A1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S89A1A1SeS2S9fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S4S9fS2S89A1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S9fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S91A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S89A1S2S91A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S91A1A1SeS2S89A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S4S89S2S91A1A2S91A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S91S20S3A1A3A4S23G0SfbS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S91S20S3A1M0A3S23S3SafG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (CDepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (CDepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S4SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7bA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7bA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S118S7bS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2Sa9A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2Sa9A1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S12fSa9U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbbA1A1A2S9dA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9dA2Li;S49S9dA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9dA1A3Li;S3aU0S9dA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6cSbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbdA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S12eSbdU1A2S87A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S87S10dSd5A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S22S125S87S10dSd5Sc5S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd5S10dS11bS87Sc5A5ScbA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S87A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScbA1A1A1SfS2S87A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S87A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S124ScbSfS2S87A1A1A2Sa1A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa1A1S2S8bA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa1S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa1A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S93A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8bA1S2S93A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S4S8bS2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S93S20S3A1A3A4S23G0SfdS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S93S20S3A1M0A3S23S3Sb1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb1A1S2S7dA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S4Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7dA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7dA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S118S7dS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S81A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S81S122Sd7A3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S22S125S81S122Sd7Sc7S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd7S122S11cS81Sc7A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S81A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScdA1A1A1SfS2S81A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S81A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S124ScdSfS2S81A1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa3A1S2S8dA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa3S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa3A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S95A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8dA1S2S95A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S4S8dS2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S95S20S3A1A3A4S23G0SffS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S95S20S3A1M0A3S23S3Sd9S23S3S8fG0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S8fA1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S8fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S8fA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S118S8fS16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2SabA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT9q CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SabS20S3A1A3A4S23G0S101S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SabS20S3A1M0A3S23S3SdbG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S47Sd9Se3S12Z1800A1A3SddA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S47SddS2eSe3A1S12Z2800A1A3Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition perm9fa : list nat := Eval vm_compute in (S iMfa :: seq 0 (S iMfa) ++ seq (S (S iMfa)) (length (ss_objs (ax_S S9bfa)) - S (S iMfa))).
Definition D9fa : axst := Eval vm_compute in (ax_setS S9bfa (set_objs (ax_S S9bfa) (select (ss_objs (ax_S S9bfa)) perm9fa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa5S111S2Sa5A1M0S10fS10G0A1ScfA2A2A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Lemma NDpfa_0 : nodupN perm9fa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa5A1A1A2A2Li;ScfA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1ScfA3Li;S3aU0S2bSaS10S2Sa5A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3SbfS20S3A1A3A4S23G0S103S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3SbfS20S3A1M0A3S23S3S71G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S71A1A1S3fU0S2cA2A2S27SaS3dVW;S83A2S27SaS131S4eS2fS97SedSf1Sf5S75S107Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S71A1A1A2A2Li;S3fU0S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S2cA2A3Li;S3aG0S2bSaS10S2S71A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S71A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S71A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S97A3S1S30SdS4fS97A3S1S30SdS50S97A3S1S30SdS54S97A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S97A3S30SdS51S97A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S75A3S1S30SdS59S75A3S1S30SdS5aS75A3S1S30SdS56S75A3S1S30SdS57S75A3S1S30SdS55S2fA1S75A3S1S30SdS5dS75A3S1S30SdS5eSb5A1S75A3S1S30SdS5cS75A3S30SdS5bS75A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb5A2S135Sb5Z100A2A2S133S136Sb5Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S71A1S27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S83S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S71S3eVW;S83S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S71A1S3eVW;S83S2fA3M4A2S41S71G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S71A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S71S3eVW;S83S2fA3S2fA3S130VW;Vst;A2Se9A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : wsub_idc sFfa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12bSe9S116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdbSe5S12Z1800A1A3SdfA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdfS2eSe5A1S12Z2800A1A3Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition perm9qa : list nat := Eval vm_compute in (S iMqa :: seq 0 (S iMqa) ++ seq (S (S iMqa)) (length (ss_objs (ax_S S9bqa)) - S (S iMqa))).
Definition D9qa : axst := Eval vm_compute in (ax_setS S9bqa (set_objs (ax_S S9bqa) (select (ss_objs (ax_S S9bqa)) perm9qa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa7S111S2Sa7A1M0S10fS10G0A1Sd1A2A2A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Lemma NDpqa_0 : nodupN perm9qa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa7A1A1A2A2Li;Sd1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd1A3Li;S3aU0S2bSaS10S2Sa7A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc1S20S3A1A3A4S23G0S105S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc1S20S3A1M0A3S23S3S73G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S73A1A1S3fU0S21A2A2S27SaS3dVW;S85A2S27SaS131S4eS2fS99SefSf3Sf7S77S109Z20000S19S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S73A1A1A2A2Li;S3fU0S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S21A2A3Li;S3aG0S2bSaS10S2S73A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S73A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S99A3S1S30SdS4fS99A3S1S30SdS50S99A3S1S30SdS54S99A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S99A3S30SdS51S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S77A3S1S30SdS59S77A3S1S30SdS5aS77A3S1S30SdS56S77A3S1S30SdS57S77A3S1S30SdS55S2fA1S77A3S1S30SdS5dS77A3S1S30SdS5eSb7A1S77A3S1S30SdS5cS77A3S30SdS5bS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb7A2S135Sb7Z100A2A2S133S136Sb7Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S73A1S27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S73S3eVW;S85S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S73A1S3eVW;S85S2fA3M4A2S41S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S73A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S73S3eVW;S85S2fA3S2fA3S130VW;Vst;A2SebA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : wsub_idc sFqa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12bSebS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS13aS13S129A1S13S128A1A3A1S20ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S138A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S138A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S138A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3SbaS20S3A1A3A4S23G0SfaS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3SbaS20S3A1M0A3S23S3Se2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S22S7Se2SaeSe8A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S22S12cSe8VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SaeA1S2S7aA1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7aA1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S4SaeS2S7aA1A2S7aA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7aA1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7aA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S118S7aS16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S80A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S80S10dSd4A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S22S125S80S10dSd4Sc4S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd4S10dS11bS80Sc4A5ScaA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S80A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScaA1A1A1SfS2S80A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S80A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S124ScaSfS2S80A1A1A2Sa0A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa0A1S2S8aA1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8aA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa0S2S8aA1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa0A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S92A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8aA1S2S92A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2S8aA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S4S8aS2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S92S20S3A1A3A4S23G0SfcS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S92S20S3A1M0A3S23S3Sb0G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (CDepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (CDepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7cA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7cA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S118S7cS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SaaA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2SaaA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S12fSaaU1A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbcA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9eA2Li;S49S9eA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9eA1A3Li;S3aU0S9eA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6cSbcA1SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbeA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S12eSbeU1A2S88A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S88S10dSd6A3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S22S125S88S10dSd6Sc6S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd6S10dS11bS88Sc6A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S88A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SccA1A1A1SfS2S88A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S88A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S124SccSfS2S88A1A1A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa2A1S2S8cA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa2S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa2A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S94A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8cA1S2S94A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S4S8cS2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S94S20S3A1A3A4S23G0SfeS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S94S20S3A1M0A3S23S3Sb2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb2A1S2S7eA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7eA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7eA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S118S7eS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S82A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S82S122Sd8A3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S22S125S82S122Sd8Sc8S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd8S122S11cS82Sc8A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S82A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SceA1A1A1SfS2S82A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S82A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S124SceSfS2S82A1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa4A1S2S8eA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa4S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa4A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S96A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8eA1S2S96A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S4S8eS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S96S20S3A1A3A4S23G0S100S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S96S20S3A1M0A3S23S3SdaS23S3S90G0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S90A1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S90A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S118S90S16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SacA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT9q CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SacS20S3A1A3A4S23G0S102S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SacS20S3A1M0A3S23S3SdcG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S47SdaSe4S12Z1800A1A3SdeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S47SdeS2eSe4A1S12Z2800A1A3Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition perm9fb : list nat := Eval vm_compute in (S iMfb :: seq 0 (S iMfb) ++ seq (S (S iMfb)) (length (ss_objs (ax_S S9bfb)) - S (S iMfb))).
Definition D9fb : axst := Eval vm_compute in (ax_setS S9bfb (set_objs (ax_S S9bfb) (select (ss_objs (ax_S S9bfb)) perm9fb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa6S111S2Sa6A1M0S10fS10G0A1Sd0A2A2A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Lemma NDpfb_0 : nodupN perm9fb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa6A1A1A2A2Li;Sd0A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd0A3Li;S3aU0S2bSaS10S2Sa6A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc0S20S3A1A3A4S23G0S104S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc0S20S3A1M0A3S23S3S72G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S72A1A1S3fU0S2cA2A2S27SaS3dVW;S84A2S27SaS131S4eS2fS98SeeSf2Sf6S76S108Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S72A1A1A2A2Li;S3fU0S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S2cA2A3Li;S3aG0S2bSaS10S2S72A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S72A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S72A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S98A3S1S30SdS4fS98A3S1S30SdS50S98A3S1S30SdS54S98A3S1S30SdS52S13S128A1A1S98A3S30SdS51S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S76A3S1S30SdS59S76A3S1S30SdS5aS76A3S1S30SdS56S76A3S1S30SdS57S76A3S1S30SdS55S2fA1S76A3S1S30SdS5dS76A3S1S30SdS5eSb6A1S76A3S1S30SdS5cS76A3S30SdS5bS76A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb6A2S135Sb6Z100A2A2S133S136Sb6Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S72A1S27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S84S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S72S3eVW;S84S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S72A1S3eVW;S84S2fA3M4A2S41S72G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S72A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S72S3eVW;S84S2fA3S2fA3S130VW;Vst;A2SeaA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : wsub_idc sFfb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12bSeaS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S47SdcSe6S12Z1800A1A3Se0A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S47Se0S2eSe6A1S12Z2800A1A3Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition perm9qb : list nat := Eval vm_compute in (S iMqb :: seq 0 (S iMqb) ++ seq (S (S iMqb)) (length (ss_objs (ax_S S9bqb)) - S (S iMqb))).
Definition D9qb : axst := Eval vm_compute in (ax_setS S9bqb (set_objs (ax_S S9bqb) (select (ss_objs (ax_S S9bqb)) perm9qb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa8S111S2Sa8A1M0S10fS10G0A1Sd2A2A2A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Lemma NDpqb_0 : nodupN perm9qb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa8A1A1A2A2Li;Sd2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd2A3Li;S3aU0S2bSaS10S2Sa8A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc2S20S3A1A3A4S23G0S106S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc2S20S3A1M0A3S23S3S74G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S74A1A1S3fU0S21A2A2S27SaS3dVW;S86A2S27SaS131S4eS2fS9aSf0Sf4Sf8S78S10aZ8S15S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S74A1A1A2A2Li;S3fU0S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S21A2A3Li;S3aG0S2bSaS10S2S74A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S74A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S9aA3S1S30SdS4fS9aA3S1S30SdS50S9aA3S1S30SdS54S9aA3S1S30SdS52S13S128A1A1S9aA3S30SdS51S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S78A3S1S30SdS59S78A3S1S30SdS5aS78A3S1S30SdS56S78A3S1S30SdS57S78A3S1S30SdS55S2fA1S78A3S1S30SdS5dS78A3S1S30SdS5eSb8A1S78A3S1S30SdS5cS78A3S30SdS5bS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb8A2S135Sb8Z100A2A2S133S136Sb8Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S74A1S27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S74S3eVW;S86S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S74A1S3eVW;S86S2fA3M4A2S41S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S74A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S74S3eVW;S86S2fA3S2fA3S130VW;Vst;A2SecA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : wsub_idc sFqb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12bSecS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineCallocSec6IL.

(* [comment removed for export] *)
Module SpineCallocSec6ILW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_X"; "entailsA"; "la_state"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "ss_objs"; "swf"; "SLit"; "SVar"; "sprop_below"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "nil"; "true"; "bool"; "cons"; "list"; "nat"; "prod"; "app"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "O_UBs"; "F_par"; "CPC"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6ILW1.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "perm9fa"; "perm9fb"; "perm9qa"; "perm9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb"; "c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa";
"xcqb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "carveS"; "BR"; "O_2"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "V_NCH"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S12Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S13bSbSbG0Lb;La;M1Lop;M2G2S13cG1Lop;M3G3S22S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S10S2VF;A1A1S117S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS13aS13S129A1S13S128A1A3S20ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S137A2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S137A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S137A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3Sb9S20S3A1A3A4S23G0Sf9S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3Sb9S20S3A1M0A3S23S3Se1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S22S7Se1SadSe7A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S22S12cSe7VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S79A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SadA1S2S79A1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S79A1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S4SadS2S79A1A2S79A3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S79A1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU1S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S79A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S118S79S16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7fA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S7fS10dSd3A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S22S125S7fS10dSd3Sc3S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd3S10dS11bS7fSc3A5Sc9A3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S7fA1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2Sc9A1A1A1SfS2S7fA1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S7fA1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S124Sc9SfS2S7fA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S89A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S9fA1S2S89A1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S89A1A1SeS2S9fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S4S9fS2S89A1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S9fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S91A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S89A1S2S91A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S91A1A1SeS2S89A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S4S89S2S91A1A2S91A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S91S20S3A1A3A4S23G0SfbS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S91S20S3A1M0A3S23S3SafG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (CDepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (CDepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S4SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7bA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU1S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7bA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S118S7bS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2Sa9A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2Sa9A1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S12fSa9U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbbA1A1A2S9dA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9dA2Li;S49S9dA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9dA1A3Li;S3aU0S9dA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6cSbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbdA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S12eSbdU1A2S87A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S87S10dSd5A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S22S125S87S10dSd5Sc5S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd5S10dS11bS87Sc5A5ScbA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S87A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScbA1A1A1SfS2S87A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S87A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S124ScbSfS2S87A1A1A2Sa1A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa1A1S2S8bA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa1S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa1A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S93A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8bA1S2S93A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S4S8bS2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S93S20S3A1A3A4S23G0SfdS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S93S20S3A1M0A3S23S3Sb1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb1A1S2S7dA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S4Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7dA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU1S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7dA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S118S7dS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S81A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S81S122Sd7A3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S22S125S81S122Sd7Sc7S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd7S122S11cS81Sc7A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S81A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScdA1A1A1SfS2S81A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S81A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S124ScdSfS2S81A1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa3A1S2S8dA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa3S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa3A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S95A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8dA1S2S95A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S4S8dS2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S95S20S3A1A3A4S23G0SffS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S95S20S3A1M0A3S23S3Sd9S23S3S8fG0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S8fA1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU1S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S8fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S8fA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S118S8fS16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2SabA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT9q CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SabS20S3A1A3A4S23G0S101S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SabS20S3A1M0A3S23S3SdbG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S47Sd9Se3S12Z1800A1A3SddA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S47SddS2eSe3A1S12Z2800A1A3Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition perm9fa : list nat := Eval vm_compute in (S iMfa :: seq 0 (S iMfa) ++ seq (S (S iMfa)) (length (ss_objs (ax_S S9bfa)) - S (S iMfa))).
Definition D9fa : axst := Eval vm_compute in (ax_setS S9bfa (set_objs (ax_S S9bfa) (select (ss_objs (ax_S S9bfa)) perm9fa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa5S111S2Sa5A1M0S10fS10G0A1ScfA2A2A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Lemma NDpfa_0 : nodupN perm9fa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa5A1A1A2A2Li;ScfA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1ScfA3Li;S3aU0S2bSaS10S2Sa5A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3SbfS20S3A1A3A4S23G0S103S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3SbfS20S3A1M0A3S23S3S71G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 40 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 42 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 47 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 49 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S71A1A1S3fU1S2cA2A2S27SaS3dVW;S83A2S27SaS131S4eS2fS97SedSf1Sf5S75S107Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU1S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S71A1A1A2A2Li;S3fU1S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S3fU1S2cA2A3Li;S3aU0S2bSaS10S2S71A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S71A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S71A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S97A3S1S30SdS4fS97A3S1S30SdS50S97A3S1S30SdS54S97A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S97A3S30SdS51S97A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S75A3S1S30SdS59S75A3S1S30SdS5aS75A3S1S30SdS56S75A3S1S30SdS57S75A3S1S30SdS55S2fA1S75A3S1S30SdS5dS75A3S1S30SdS5eSb5A1S75A3S1S30SdS5cS75A3S30SdS5bS75A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb5A2S135Sb5Z100A2A2S133S136Sb5Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S71A1S27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3S40U1A1A2S3eVW;S83S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S40U1A1A3Li;S3aU0S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S71S3eVW;S83S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S71A1S3eVW;S83S2fA3M4A2S41S71G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S71A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S71S3eVW;S83S2fA3S2fA3S130VW;Vst;A2Se9A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : wsub_idc sFfa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12bSe9S116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdbSe5S12Z1800A1A3SdfA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdfS2eSe5A1S12Z2800A1A3Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition perm9qa : list nat := Eval vm_compute in (S iMqa :: seq 0 (S iMqa) ++ seq (S (S iMqa)) (length (ss_objs (ax_S S9bqa)) - S (S iMqa))).
Definition D9qa : axst := Eval vm_compute in (ax_setS S9bqa (set_objs (ax_S S9bqa) (select (ss_objs (ax_S S9bqa)) perm9qa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa7S111S2Sa7A1M0S10fS10G0A1Sd1A2A2A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Lemma NDpqa_0 : nodupN perm9qa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa7A1A1A2A2Li;Sd1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd1A3Li;S3aU0S2bSaS10S2Sa7A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc1S20S3A1A3A4S23G0S105S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc1S20S3A1M0A3S23S3S73G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 40 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 42 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 47 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 49 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S73A1A1S3fU1S21A2A2S27SaS3dVW;S85A2S27SaS131S4eS2fS99SefSf3Sf7S77S109Z20000S19S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU1S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S73A1A1A2A2Li;S3fU1S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S3fU1S21A2A3Li;S3aU0S2bSaS10S2S73A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S73A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S99A3S1S30SdS4fS99A3S1S30SdS50S99A3S1S30SdS54S99A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S99A3S30SdS51S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S77A3S1S30SdS59S77A3S1S30SdS5aS77A3S1S30SdS56S77A3S1S30SdS57S77A3S1S30SdS55S2fA1S77A3S1S30SdS5dS77A3S1S30SdS5eSb7A1S77A3S1S30SdS5cS77A3S30SdS5bS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb7A2S135Sb7Z100A2A2S133S136Sb7Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S73A1S27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3S40U1A1A2S3eVW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S40U1A1A3Li;S3aU0S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S73S3eVW;S85S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S73A1S3eVW;S85S2fA3M4A2S41S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S73A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S73S3eVW;S85S2fA3S2fA3S130VW;Vst;A2SebA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : wsub_idc sFqa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12bSebS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS13aS13S129A1S13S128A1A3A1S20ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S138A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S138A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S138A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3SbaS20S3A1A3A4S23G0SfaS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3SbaS20S3A1M0A3S23S3Se2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S22S7Se2SaeSe8A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S22S12cSe8VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SaeA1S2S7aA1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7aA1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S4SaeS2S7aA1A2S7aA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7aA1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU1S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7aA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S118S7aS16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S80A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S80S10dSd4A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S22S125S80S10dSd4Sc4S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd4S10dS11bS80Sc4A5ScaA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S80A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScaA1A1A1SfS2S80A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S80A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S124ScaSfS2S80A1A1A2Sa0A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa0A1S2S8aA1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8aA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa0S2S8aA1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa0A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S92A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8aA1S2S92A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2S8aA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S4S8aS2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S92S20S3A1A3A4S23G0SfcS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S92S20S3A1M0A3S23S3Sb0G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (CDepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (CDepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7cA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU1S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7cA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S118S7cS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SaaA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2SaaA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S12fSaaU1A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbcA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9eA2Li;S49S9eA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9eA1A3Li;S3aU0S9eA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6cSbcA1SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbeA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S12eSbeU1A2S88A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S88S10dSd6A3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S22S125S88S10dSd6Sc6S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd6S10dS11bS88Sc6A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S88A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SccA1A1A1SfS2S88A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S88A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S124SccSfS2S88A1A1A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa2A1S2S8cA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa2S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa2A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S94A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8cA1S2S94A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S4S8cS2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S94S20S3A1A3A4S23G0SfeS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S94S20S3A1M0A3S23S3Sb2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb2A1S2S7eA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7eA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU1S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7eA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S118S7eS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S82A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S82S122Sd8A3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S22S125S82S122Sd8Sc8S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd8S122S11cS82Sc8A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S82A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SceA1A1A1SfS2S82A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S82A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S124SceSfS2S82A1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa4A1S2S8eA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa4S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa4A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S96A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8eA1S2S96A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S4S8eS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S96S20S3A1A3A4S23G0S100S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S96S20S3A1M0A3S23S3SdaS23S3S90G0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S90A1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU1S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S90A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S118S90S16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SacA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT9q CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SacS20S3A1A3A4S23G0S102S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SacS20S3A1M0A3S23S3SdcG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S47SdaSe4S12Z1800A1A3SdeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S47SdeS2eSe4A1S12Z2800A1A3Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition perm9fb : list nat := Eval vm_compute in (S iMfb :: seq 0 (S iMfb) ++ seq (S (S iMfb)) (length (ss_objs (ax_S S9bfb)) - S (S iMfb))).
Definition D9fb : axst := Eval vm_compute in (ax_setS S9bfb (set_objs (ax_S S9bfb) (select (ss_objs (ax_S S9bfb)) perm9fb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa6S111S2Sa6A1M0S10fS10G0A1Sd0A2A2A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Lemma NDpfb_0 : nodupN perm9fb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa6A1A1A2A2Li;Sd0A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd0A3Li;S3aU0S2bSaS10S2Sa6A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc0S20S3A1A3A4S23G0S104S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc0S20S3A1M0A3S23S3S72G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 40 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 42 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 47 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 49 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S72A1A1S3fU1S2cA2A2S27SaS3dVW;S84A2S27SaS131S4eS2fS98SeeSf2Sf6S76S108Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU1S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S72A1A1A2A2Li;S3fU1S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S3fU1S2cA2A3Li;S3aU0S2bSaS10S2S72A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S72A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S72A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S98A3S1S30SdS4fS98A3S1S30SdS50S98A3S1S30SdS54S98A3S1S30SdS52S13S128A1A1S98A3S30SdS51S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S76A3S1S30SdS59S76A3S1S30SdS5aS76A3S1S30SdS56S76A3S1S30SdS57S76A3S1S30SdS55S2fA1S76A3S1S30SdS5dS76A3S1S30SdS5eSb6A1S76A3S1S30SdS5cS76A3S30SdS5bS76A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb6A2S135Sb6Z100A2A2S133S136Sb6Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S72A1S27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3S40U1A1A2S3eVW;S84S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S40U1A1A3Li;S3aU0S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S72S3eVW;S84S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S72A1S3eVW;S84S2fA3M4A2S41S72G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S72A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S72S3eVW;S84S2fA3S2fA3S130VW;Vst;A2SeaA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : wsub_idc sFfb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12bSeaS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S47SdcSe6S12Z1800A1A3Se0A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S47Se0S2eSe6A1S12Z2800A1A3Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition perm9qb : list nat := Eval vm_compute in (S iMqb :: seq 0 (S iMqb) ++ seq (S (S iMqb)) (length (ss_objs (ax_S S9bqb)) - S (S iMqb))).
Definition D9qb : axst := Eval vm_compute in (ax_setS S9bqb (set_objs (ax_S S9bqb) (select (ss_objs (ax_S S9bqb)) perm9qb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa8S111S2Sa8A1M0S10fS10G0A1Sd2A2A2A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Lemma NDpqb_0 : nodupN perm9qb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa8A1A1A2A2Li;Sd2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd2A3Li;S3aU0S2bSaS10S2Sa8A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc2S20S3A1A3A4S23G0S106S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc2S20S3A1M0A3S23S3S74G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 40 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 42 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 47 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 49 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S74A1A1S3fU1S21A2A2S27SaS3dVW;S86A2S27SaS131S4eS2fS9aSf0Sf4Sf8S78S10aZ8S15S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU1S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S74A1A1A2A2Li;S3fU1S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S3fU1S21A2A3Li;S3aU0S2bSaS10S2S74A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S74A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S9aA3S1S30SdS4fS9aA3S1S30SdS50S9aA3S1S30SdS54S9aA3S1S30SdS52S13S128A1A1S9aA3S30SdS51S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S78A3S1S30SdS59S78A3S1S30SdS5aS78A3S1S30SdS56S78A3S1S30SdS57S78A3S1S30SdS55S2fA1S78A3S1S30SdS5dS78A3S1S30SdS5eSb8A1S78A3S1S30SdS5cS78A3S30SdS5bS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb8A2S135Sb8Z100A2A2S133S136Sb8Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S74A1S27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3S40U1A1A2S3eVW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S40U1A1A3Li;S3aU0S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S74S3eVW;S86S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S74A1S3eVW;S86S2fA3M4A2S41S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S74A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S74S3eVW;S86S2fA3S2fA3S130VW;Vst;A2SecA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : wsub_idc sFqb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12bSecS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineCallocSec6ILW1.

(* [comment removed for export] *)
Module CallocHitTail1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "s9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1"; "Cert10a_0"; "Cert10b_0"; "Cert10pa_0"; "Cert10pb_0"; "Cert9a_0"; "Cert9b_0"; "Cert9pa_0"; "Cert9pb_0"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS6iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS7iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.CDepotCallHW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma HUS_shape : stopJ_stable (Wcan 1) UStopLeOrPc.
Proof. exact stopJ_stable_1pc. Qed.

Section ARMS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S3cS49R2A2S38F_;F_;Fa;").
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Definition arm_a : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U1A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S15S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S20G3S0Z3A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S20S1G0A1M2S0G1A3S2bG2S0G1A3S27G2S0G1A3S8dS23G2S0G1A3S5dS51S6dS91S55S7dSa5S9dS85S79S75S71S61S65S59S89S81S4dSa9S99S95Sa1S69A27").
Definition arm_b : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U1A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S15S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S20G3S0Z3A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S20S1G0A1M2S0G1A3S2cG2S0G1A3S28G2S0G1A3S8eS24G2S0G1A3S5eS52S6eS92S56S7eSa6S9eS86S7aS76S72S62S66S5aS8aS82S4eSaaS9aS96Sa2S6aA27").
Definition arm_pa : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U1A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S16S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S21G3S0Z3A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S21S1G0A1M2S0G1A3S2dG2S0G1A3S29G2S0G1A3S8fS25G2S0G1A3S5fS53S6fS93S57S7fSa7S9fS87S7bS77S73S63S67S5bS8bS83S4fSabS9bS97Sa3S6bA27").
Definition arm_pb : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U1A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S16S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S21G3S0Z3A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S21S1G0A1M2S0G1A3S2eG2S0G1A3S2aG2S0G1A3S90S26G2S0G1A3S60S54S70S94S58S80Sa8Sa0S88S7cS78S74S64S68S5cS8cS84S50SacS9cS98Sa4S6cA27").
End ARMS.

Section HIT0T.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S3cS49R2A2S38F_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S35S4cR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S6VAInv;VW;Vst;VA;VKc;S9PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 1.
Let st0 : ustop := UStopLeOrPc.

Definition KEEP (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S4bVCST;VXGL;VA;Va;A4").

Theorem calloc_hit_tail_1_P : ltac2:(tb__ "0|1|
S32OF_;S1aS2S8SfS30Q40A1A1SfS14S17S18A2M0A1S19Vsegs;S34R3R2R1A5S33S3dG0S13S17S18S3aVW0;Vst0;A2S39VCST;VXGL;R6R5A4A4R2A3S3R6A1S1eVsegs;R9S1cR7A1A3S48Vsegs;RaS1cR8A1A3S8S31Vsegs;RcS1dVsegs;S4aVW0;Vst0;RbRaR9A5S22VW0;Vst0;Z3A3R1R8A5R6A4FrhoX;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl.
  pose proof (depot_call_HD_1 CST XGL HCST HXGL HCSTD ok A Kc rho Q HKc Hokl Hokpl) as HD.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (exact HUS_shape).
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  set (nv := bv_unsigned (rw rho 12%positive)).

  apply (spine_s3p_tail 1%nat st0 3 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 ok A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.

  apply (spine_s4 1%nat st0 3 Cert4_0 (KEEP A) ok A Kc rho tp Q HUS HKc (Hokf A) HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  pose proof Hokl as HokA'.

  assert (K7 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 3) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s7 1%nat st0 3 Cert7_0 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt').
    - intros Hm0 rhoY8.
      apply (spine_s8c 1%nat st0 (C8 W0 st0 3) (C9 W0 st0 3) (E8n W0 st0 3) Cert8_0 s9e_0 ENT9e_0 SID9e_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9c_P 1%nat st0 CST XGL false (C9 W0 st0 3) NX9_0 FGC_0 (arm_a CST XGL HCST HXGL HCSTM) (arm_b CST XGL HCST HXGL HCSTM)
               ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (spine_s7p 1%nat st0 3 Cert7p_0 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY8.
      apply (spine_s8c 1%nat st0 (C8p W0 st0 3) (C9p W0 st0 3) (E8pn W0 st0 3) Cert8p_0 s9ep_0 ENT9ep_0 SID9ep_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9c_P 1%nat st0 CST XGL true (C9p W0 st0 3) NX9p_0 FGCp_0 (arm_pa CST XGL HCST HXGL HCSTM) (arm_pb CST XGL HCST HXGL HCSTM)
               ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }

  assert (K6 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 3) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s6 1%nat st0 3 Cert6_0 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    apply (spine_s6l 1%nat st0 3 Cert6l_0 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6_0 ok A' Kc rho' tpY Q HUS HKc HokA').
    intros rhoY6b tpY6b.
    apply (spine_s6b 1%nat st0 3 Cert6b_0 s7j_0 ENT7j_0 SID7j_0 ok A' Kc rho' tpY6b Q HUS HKc HokA'). exact (K7 tpY6b). }

  apply (spine_s5 1%nat st0 3 Cert5_0 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (spine_s5b 1%nat st0 3 Cert5b_0 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0
           ok A' Kc rho' tp' Q HUS HKc HokA').
  intros rhoX5c.
  apply (spine_s5c 1%nat st0 3 Cert5c_0 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0
           ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt').
  intros rhoX5d tp5d.
  apply (spine_s5d 1%nat st0 3 Cert5d_0 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0
           ok A' Kc rho' tp5d Q HUS HKc HokA' Hcnt').
  intros rhoX5e tp5e.
  apply (spine_s5e 1%nat st0 3 Cert5e_0 s6j_0 ENT6j_0 SID6j_0 ok A' Kc rho' tp5e Q HUS HKc HokA'). exact (K6 tp5e).
Qed.

Theorem calloc_hit_tail_1 : ltac2:(tb__ "0|0|
S32OF_;S1aS2S8SfS30Q40A1A1S19Vsegs;S34R2R1S3bVCST;VXGL;VW0;Vst0;R4R3A6A5S33S3R4A1S1eVsegs;R7S1cR5A1A3S48Vsegs;R8S1cR6A1A3S8S31Vsegs;RaS1dVsegs;S4aVW0;Vst0;R9R8R7A5S22VW0;Vst0;Z3A3R1R6A5R5A4FrhoX;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (calloc_hit_tail_1_P ok A Kc rho tp (PFc CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0T.
End CallocHitTail1.

(* [comment removed for export] *)
Module SpineCallocSec6I.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "cell"; "sprop"; "ss_next"; "ss_facts"; "ss_objs"; "swf"; "SLit"; "SVar"; "sprop_below"; "DUnknown"; "SPNot"; "mkObj"; "DZero"; "SAlu"; "sstate"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "entailsA"; "xr_below"; "la_state"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "nat"; "app"; "prod"; "option"; "length"; "pair"; "Some"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "O_UBs"; "F_par"; "UBs"; "F_A"; "F_B"; "CPC"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "osplit"; "O_3"; "perm7"; "L3"; "O_3b"; "PGST"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.SpineCallocSec6I.INST"; "FFfaA"; "FFfaB"; "FFfbA"; "FFfbB"; "FFqaA"; "FFqaB"; "FFqbA"; "FFqbB"; "mcfaA"; "mcfaB"; "mcfbA"; "mcfbB"; "mcqaA"; "mcqaB"; "mcqbA"; "mcqbB"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfaA"; "swcfaB"; "swcfbA"; "swcfbB"; "swcqaA"; "swcqaB"; "swcqbA"; "swcqbB"; "CM7a"; "CM7b"; "FXPa"; "FXPb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1faA"; "c1faB"; "c1fbA"; "c1fbB"; "c1qaA"; "c1qaB"; "c1qbA"; "c1qbB"; "n7a"; "n7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "E6a"; "E6b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfaA"; "tybfaB"; "tybfbA"; "tybfbB"; "tybqaA"; "tybqaB"; "tybqbA"; "tybqbB"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9faA"; "D9faB"; "D9fbA"; "D9fbB"; "D9qaA"; "D9qaB"; "D9qbA";
"D9qbB"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "perm9fa"; "perm9fb"; "perm9qa"; "perm9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "sFfaA"; "sFfaB"; "sFfbA"; "sFfbB"; "sFqaA"; "sFqaB"; "sFqbA"; "sFqbB"; "c2faA"; "c2faB"; "c2fbA"; "c2fbB"; "c2qaA"; "c2qaB"; "c2qbA"; "c2qbB"; "c4faA"; "c4faB"; "c4fbA"; "c4fbB"; "c4qaA"; "c4qaB"; "c4qbA"; "c4qbB"; "c5faA"; "c5faB"; "c5fbA"; "c5fbB"; "c5qaA"; "c5qaB"; "c5qbA"; "c5qbB"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfaA"; "runFfaB"; "runFfbA"; "runFfbB"; "runFqaA"; "runFqaB"; "runFqbA"; "runFqbB"; "xcfaA"; "xcfaB"; "xcfbA"; "xcfbB"; "xcqaA"; "xcqaB"; "xcqbA"; "xcqbB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "carveS"; "BR"; "O_2"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28S4A1S35Lx;S34S4S4S17S14R1A1SaZ17f1A1A2Lc;Vmc;A3S4S3S35Lx;S15R1A1S35R1Lt;S36Z0M0Li;S169S3S3G0Lb;La;M1Lop;M2G2S16aG1Lop;M3G3S21S37S3G0La;Lw;Lsgn;S36S3S35G0Lk;Li;Ll;X3x8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S16S6cS2Vi;S8S18VF;A1A1S150S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23S5S13S168SbS14fA1SbS14eA1A3S22S5A1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Definition C5Ba : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1S16eA2Sd6A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma HC5Ba_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1S16eA2Sd8A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ba)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16eA1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16eA1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd6S22S19A1A3A4S23G0S130S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd6S22S19A1M0A3S23S19S104G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Ba : option (list leafA) := Eval vm_compute in (runT6 C5Ba).
Lemma run6Ba__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd8S22S19A1A3A4S23G0S132S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ba]). Qed.
Definition Y6Ba : axst := Eval vm_compute in (leafS 0 run6Ba).
Lemma Cert6Ba_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd8S22S19A1M0A3S23S19S106G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ba] [Y6Ba] [run6Ba]); [exact run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S1dS104Sb8S10cA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S157S10cVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Ba : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ba) (ax_S E6a)).
Lemma E6Ba_0 : ltac2:(tb__ "0|0|
S0S21S1dS106Sb8S10eA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ba_0 : ltac2:(tb__ "0|0|
S0S21S157S10eVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sb8A1S18S8cA1A2S2bG3S2aG1G2S23G0S2aS3S3S65S2fA1S59A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8cA1A1S6S18Sb8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S19S1cSb8S18S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8cA1A1A4S6aS2G0S7bS26S2S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3S26S2S15bU0S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S8cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S19S151S8cSfS5cS2fA1SaZ0A1S59S22S4A1SdA5A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S92A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S92S14cSf6A3S2bG0Se6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S163S92S14cSf6Se6S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S19S165Sf6S14cS154S92Se6A5SecA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S92A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SecA1A1A1S7S18S92A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S92A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S19S162SecS7S18S92A1A1A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition U7a : axst := Eval vm_compute in (U7p nx0 D6a).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc2A1S18Sa4A1A2S2bG3S2aG1G2S22G0A1S5fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa4A1A1S6S18Sc2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc2S18Sa4A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa4S22S19A1A3A4S23G0S134S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa4S22S19A1M0A3S23S19Sc8G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (CDepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (CDepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc8A1S18S8eA1A2S2bG3S2aG1G2S23G0S2aS3S3S64S2fA1S152S2fA1A4S23G0S2aS3S3S66S2fA1S62A4S22G0A1A3A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8eA1A1S6S18Sc8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc8S18S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8eA1A1A4S6aS2G0S7bS26S2S23S2S57S2fA1S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU0S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S8eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S19S151S8eSfS152S2fA1SaZ0A1SaZ100A1S22S4A1SdA5A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18SbeA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S171S18SbeA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S19S16dSbeU1A2SdaA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S25S29S2S8S18SdaA1A1A2Sb2A3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S71S58Sb2A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1Sb2A2Li;S58Sb2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S58Sb2A1A3Li;S6bU0Sb2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S19S69SdaA1SdcA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S170S18SdcA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S19S16cSdcU1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S9eS14cSf8A3S2bG0Se8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S163S9eS14cSf8Se8S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S19S165Sf8S14cS154S9eSe8A5SeeA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S9eA1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SeeA1A1A1S7S18S9eA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S9eA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S19S162SeeS7S18S9eA1A1A2Sc4A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition U8a : axst := Eval vm_compute in (U8p nx0 D7a).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa6A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc4A1S18Sa6A1A2S2bG3S2aG1G2S22G0A1S60S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa6A1A1S6S18Sc4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc4S18Sa6A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa6S22S19A1A3A4S23G0S136S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa6S22S19A1M0A3S23S19ScaG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S90A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18ScaA1S18S90A1A2S2bG3S2aG1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S90A1A1S6S18ScaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S19S1cScaS18S90A1A2S90A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S90A1A1A4S6aS2G0S7bS26S2S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU0S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS90A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S19S151S90SfS5dS2fA1SaZ0A1S67S2fA1S22S4A1SdA5A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S94A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S94S160SfaA3S2bG0SeaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S163S94S160SfaSeaS6aS1aS19S1fS161A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S19S165SfaS160S155S94SeaA5Sf0A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S94A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sf0A1A1A1S7S18S94A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S94A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S19S162Sf0S7S18S94A1A1A2Sc6A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition U9a : axst := Eval vm_compute in (U9p nx0 D8a).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa8A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc6A1S18Sa8A1A2S2bG3S2aG1G2S22G0A1S61S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa8A1A1S6S18Sc6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc6S18Sa8A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3S23S19Sa8S22S19A1A3A4S23G0S138S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3VGS0;S23S19Sa8S22S19A1M0A3S23S19SfcS23S19Sa2G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18Sa2A1A1A4S6aS2G0S7bS26S2S23S2S63S2fA1S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3A3S26S2S15bU0S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18Sa2A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18Sa2A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30S5SeS40A1S7S18Sa2A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bSa2A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S19S151Sa2SfS5eS2fA1SaZ0A1SaZ1A1S22S4A1SdA5A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sc0A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT9q CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S22S35A1A3S23S19Sc0S22S19A1A3A4S23G0S13aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S22S35A1A3VGS0;S23S19Sc0S22S19A1M0A3S23S19SfeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S19S56SfcS108SaZ1800A1A3S100A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S19S56S100S2eS108A1SaZ2800A1A3SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition perm9fa : list nat := Eval vm_compute in (S iMfa :: seq 0 (S iMfa) ++ seq (S (S iMfa)) (length (ss_objs (ax_S S9bfa)) - S (S iMfa))).
Definition D9fa : axst := Eval vm_compute in (ax_setS S9bfa (set_objs (ax_S S9bfa) (select (ss_objs (ax_S S9bfa)) perm9fa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|1|
S0S19S1cSbaS72S18SbaA1M0S70S8G0A1Sf2A2A2A2Sb4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Lemma NDpfa_0 : nodupN perm9fa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbaA1A1A2A2Li;Sf2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf2A3Li;S6bU0S29S2S8S18SbaA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9faA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9fa).
Definition D9faB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9fa).
Lemma HD9Afa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb4A2SdeA3"). Proof. vm_cast_no_check (@eq_refl _ (D9faA)). Qed.
Lemma HD9Bfa_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb4A2SdfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9faB)). Qed.
Lemma FBA9fa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb4A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9fa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb4A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfaA : option (list leafA) := Eval vm_compute in (runTF D9faA).
Lemma runFfaA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19SdeS22S19A1A3A4S23G0S13cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfaA]). Qed.
Definition FFfaA : axst := Eval vm_compute in (leafS 0 runFfaA).
Lemma CertFfaA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19SdeS22S19A1M0A3S23S19S7cG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9faA] [FFfaA] [runFfaA]); [exact runFfaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfaA : list cell := Eval vm_compute in (cells_at 5 FFfaA).
Definition c1faA : list cell := Eval vm_compute in (cells_at 38 FFfaA).
Definition c2faA : list cell := Eval vm_compute in (cells_at 39 FFfaA).
Definition c4faA : list cell := Eval vm_compute in (cells_at 41 FFfaA).
Definition c5faA : list cell := Eval vm_compute in (cells_at 45 FFfaA).
Definition mcfaA : list cell := Eval vm_compute in (cells_at 46 FFfaA).
Definition xcfaA : list cell := Eval vm_compute in (cells_at 48 FFfaA).
Definition tybfaA : Z := Eval vm_compute in (tyb_of mcfaA).
Lemma SELFfaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7cA1A1S3bU0S2cA2A2S26S2S39VW;S96A2S26S2S159S45S2fSaaS118S120S128S84S144Z20000S10S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfaA ++ RT_m1 ++ RSF nx0 c1faA c2faA c4faA c5faA mcfaA xcfaA 131072 DZero false)). Qed.
Lemma NDFfaA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7cA1A1A2A2Li;S3bU0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfaA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S2cA2A3Li;S6bG0S29S2S8S18S7cA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfaA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfaA_0 : ax_base FFfaA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfaA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfaA_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfaA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7cA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1faA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSaaA3S1S30S4S46SaaA3S1S30S4S47SaaA3S1S30S4S4bSaaA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SaaA3S30S4S48SaaA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1faA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1faA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S84A3S1S30S4S50S84A3S1S30S4S51S84A3S1S30S4S4dS84A3S1S30S4S4eS84A3S1S30S4S4cS2fA1S84A3S1S30S4S54S84A3S1S30S4S55SceA1S84A3S1S30S4S53S84A3S30S4S52S84A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfaA) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfaA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfaA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0SceA2S15eSceZ100A2A2S15cS15fSceZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfaA_0 : In (xc_map nx0) xcfaA. Proof. exact (In_of_cellb (xc_map nx0) xcfaA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfaA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7cA1S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S96S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfaA nx0)). Qed.
Lemma NDUfaA_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfaA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9faA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7cS3aVW;S96S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9faA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7cA1S3aVW;S96S2fA3M4A2S3dS7cG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9faA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7cA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfaA : wsub := Eval vm_compute in (infer_sub NF (S2F FFfaA (KUB W swcfaA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9faA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7cS3aVW;S96S2fA3S2fA3S158VW;Vst;A2S110A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9faA_0 : wsub_idc sFfaA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110faA_0 : ltac2:(tb__ "0|0|
S0S3S156S110S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFfaB : option (list leafA) := Eval vm_compute in (runTF D9faB).
Lemma runFfaB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19SdfS22S19A1A3A4S23G0S13dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfaB]). Qed.
Definition FFfaB : axst := Eval vm_compute in (leafS 0 runFfaB).
Lemma CertFfaB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19SdfS22S19A1M0A3S23S19S7dG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9faB] [FFfaB] [runFfaB]); [exact runFfaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfaB : list cell := Eval vm_compute in (cells_at 5 FFfaB).
Definition c1faB : list cell := Eval vm_compute in (cells_at 38 FFfaB).
Definition c2faB : list cell := Eval vm_compute in (cells_at 39 FFfaB).
Definition c4faB : list cell := Eval vm_compute in (cells_at 41 FFfaB).
Definition c5faB : list cell := Eval vm_compute in (cells_at 45 FFfaB).
Definition mcfaB : list cell := Eval vm_compute in (cells_at 46 FFfaB).
Definition xcfaB : list cell := Eval vm_compute in (cells_at 48 FFfaB).
Definition tybfaB : Z := Eval vm_compute in (tyb_of mcfaB).
Lemma SELFfaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7dA1A1S3bU0S2cA2A2S26S2S39VW;S97A2S26S2S159S45S2fSabS119S121S129S85S145Z20000S10S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfaB ++ RT_m1 ++ RSF nx0 c1faB c2faB c4faB c5faB mcfaB xcfaB 131072 DZero false)). Qed.
Lemma NDFfaB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7dA1A1A2A2Li;S3bU0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfaB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S2cA2A3Li;S6bG0S29S2S8S18S7dA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfaB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfaB_0 : ax_base FFfaB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfaB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfaB_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfaB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7dA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1faB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSabA3S1S30S4S46SabA3S1S30S4S47SabA3S1S30S4S4bSabA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SabA3S30S4S48SabA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1faB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1faB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S85A3S1S30S4S50S85A3S1S30S4S51S85A3S1S30S4S4dS85A3S1S30S4S4eS85A3S1S30S4S4cS2fA1S85A3S1S30S4S54S85A3S1S30S4S55ScfA1S85A3S1S30S4S53S85A3S30S4S52S85A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfaB) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfaB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfaB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0ScfA2S15eScfZ100A2A2S15cS15fScfZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfaB_0 : In (xc_map nx0) xcfaB. Proof. exact (In_of_cellb (xc_map nx0) xcfaB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfaB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7dA1S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S97S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfaB nx0)). Qed.
Lemma NDUfaB_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfaB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9faB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7dS3aVW;S97S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9faB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7dA1S3aVW;S97S2fA3M4A2S3dS7dG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9faB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7dA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfaB : wsub := Eval vm_compute in (infer_sub NF (S2F FFfaB (KUB W swcfaB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9faB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7dS3aVW;S97S2fA3S2fA3S158VW;Vst;A2S111A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9faB_0 : wsub_idc sFfaB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110faB_0 : ltac2:(tb__ "0|0|
S0S3S156S111S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S19S56SfeS10aSaZ1800A1A3S102A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S19S56S102S2eS10aA1SaZ2800A1A3SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition perm9qa : list nat := Eval vm_compute in (S iMqa :: seq 0 (S iMqa) ++ seq (S (S iMqa)) (length (ss_objs (ax_S S9bqa)) - S (S iMqa))).
Definition D9qa : axst := Eval vm_compute in (ax_setS S9bqa (set_objs (ax_S S9bqa) (select (ss_objs (ax_S S9bqa)) perm9qa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|1|
S0S19S1cSbcS72S18SbcA1M0S70S8G0A1Sf4A2A2A2Sb6A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Lemma NDpqa_0 : nodupN perm9qa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbcA1A1A2A2Li;Sf4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf4A3Li;S6bU0S29S2S8S18SbcA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qaA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9qa).
Definition D9qaB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9qa).
Lemma HD9Aqa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb6A2Se2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qaA)). Qed.
Lemma HD9Bqa_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb6A2Se3A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qaB)). Qed.
Lemma FBA9qa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb6A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9qa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb6A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqaA : option (list leafA) := Eval vm_compute in (runTF D9qaA).
Lemma runFqaA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se2S22S19A1A3A4S23G0S140S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqaA]). Qed.
Definition FFqaA : axst := Eval vm_compute in (leafS 0 runFqaA).
Lemma CertFqaA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se2S22S19A1M0A3S23S19S80G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qaA] [FFqaA] [runFqaA]); [exact runFqaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqaA : list cell := Eval vm_compute in (cells_at 5 FFqaA).
Definition c1qaA : list cell := Eval vm_compute in (cells_at 38 FFqaA).
Definition c2qaA : list cell := Eval vm_compute in (cells_at 39 FFqaA).
Definition c4qaA : list cell := Eval vm_compute in (cells_at 41 FFqaA).
Definition c5qaA : list cell := Eval vm_compute in (cells_at 45 FFqaA).
Definition mcqaA : list cell := Eval vm_compute in (cells_at 46 FFqaA).
Definition xcqaA : list cell := Eval vm_compute in (cells_at 48 FFqaA).
Definition tybqaA : Z := Eval vm_compute in (tyb_of mcqaA).
Lemma SELFqaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S80A1A1S3bU0S20A2A2S26S2S39VW;S9aA2S26S2S159S45S2fSaeS11cS124S12cS88S148Z20000S10S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqaA ++ RT_m1 ++ RSF nx0 c1qaA c2qaA c4qaA c5qaA mcqaA xcqaA 131072 DZero true)). Qed.
Lemma NDFqaA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S80A1A1A2A2Li;S3bU0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqaA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S20A2A3Li;S6bG0S29S2S8S18S80A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqaA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqaA_0 : ax_base FFqaA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqaA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqaA_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqaA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S80A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSaeA3S1S30S4S46SaeA3S1S30S4S47SaeA3S1S30S4S4bSaeA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SaeA3S30S4S48SaeA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qaA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S88A3S1S30S4S50S88A3S1S30S4S51S88A3S1S30S4S4dS88A3S1S30S4S4eS88A3S1S30S4S4cS2fA1S88A3S1S30S4S54S88A3S1S30S4S55Sd2A1S88A3S1S30S4S53S88A3S30S4S52S88A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqaA) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqaA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqaA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd2A2S15eSd2Z100A2A2S15cS15fSd2Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqaA_0 : In (xc_map nx0) xcqaA. Proof. exact (In_of_cellb (xc_map nx0) xcqaA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqaA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S80A1S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S9aS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqaA nx0)). Qed.
Lemma NDUqaA_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqaA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qaA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS80S3aVW;S9aS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qaA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S80A1S3aVW;S9aS2fA3M4A2S3dS80G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qaA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S80A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqaA : wsub := Eval vm_compute in (infer_sub NF (S2F FFqaA (KUB W swcqaA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qaA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS80S3aVW;S9aS2fA3S2fA3S158VW;Vst;A2S114A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qaA_0 : wsub_idc sFqaA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qaA_0 : ltac2:(tb__ "0|0|
S0S3S156S114S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFqaB : option (list leafA) := Eval vm_compute in (runTF D9qaB).
Lemma runFqaB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se3S22S19A1A3A4S23G0S141S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqaB]). Qed.
Definition FFqaB : axst := Eval vm_compute in (leafS 0 runFqaB).
Lemma CertFqaB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se3S22S19A1M0A3S23S19S81G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qaB] [FFqaB] [runFqaB]); [exact runFqaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqaB : list cell := Eval vm_compute in (cells_at 5 FFqaB).
Definition c1qaB : list cell := Eval vm_compute in (cells_at 38 FFqaB).
Definition c2qaB : list cell := Eval vm_compute in (cells_at 39 FFqaB).
Definition c4qaB : list cell := Eval vm_compute in (cells_at 41 FFqaB).
Definition c5qaB : list cell := Eval vm_compute in (cells_at 45 FFqaB).
Definition mcqaB : list cell := Eval vm_compute in (cells_at 46 FFqaB).
Definition xcqaB : list cell := Eval vm_compute in (cells_at 48 FFqaB).
Definition tybqaB : Z := Eval vm_compute in (tyb_of mcqaB).
Lemma SELFqaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S81A1A1S3bU0S20A2A2S26S2S39VW;S9bA2S26S2S159S45S2fSafS11dS125S12dS89S149Z20000S10S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqaB ++ RT_m1 ++ RSF nx0 c1qaB c2qaB c4qaB c5qaB mcqaB xcqaB 131072 DZero true)). Qed.
Lemma NDFqaB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S81A1A1A2A2Li;S3bU0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqaB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S20A2A3Li;S6bG0S29S2S8S18S81A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqaB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS81A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqaB_0 : ax_base FFqaB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqaB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqaB_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqaB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S81A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSafA3S1S30S4S46SafA3S1S30S4S47SafA3S1S30S4S4bSafA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SafA3S30S4S48SafA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qaB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S89A3S1S30S4S50S89A3S1S30S4S51S89A3S1S30S4S4dS89A3S1S30S4S4eS89A3S1S30S4S4cS2fA1S89A3S1S30S4S54S89A3S1S30S4S55Sd3A1S89A3S1S30S4S53S89A3S30S4S52S89A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqaB) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqaB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqaB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd3A2S15eSd3Z100A2A2S15cS15fSd3Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqaB_0 : In (xc_map nx0) xcqaB. Proof. exact (In_of_cellb (xc_map nx0) xcqaB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqaB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S81A1S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S9bS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqaB nx0)). Qed.
Lemma NDUqaB_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqaB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qaB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS81S3aVW;S9bS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qaB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S81A1S3aVW;S9bS2fA3M4A2S3dS81G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qaB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S81A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqaB : wsub := Eval vm_compute in (infer_sub NF (S2F FFqaB (KUB W swcqaB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qaB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS81S3aVW;S9bS2fA3S2fA3S158VW;Vst;A2S115A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qaB_0 : wsub_idc sFqaB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qaB_0 : ltac2:(tb__ "0|0|
S0S3S156S115S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23S5SeS13S168SbS14fA1SbS14eA1A3A1S22S5A1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Definition C5Bb : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1S16fA2Sd7A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma HC5Bb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1S16fA2Sd9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Bb)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16fA1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16fA1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd7S22S19A1A3A4S23G0S131S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd7S22S19A1M0A3S23S19S105G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Bb : option (list leafA) := Eval vm_compute in (runT6 C5Bb).
Lemma run6Bb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd9S22S19A1A3A4S23G0S133S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Bb]). Qed.
Definition Y6Bb : axst := Eval vm_compute in (leafS 0 run6Bb).
Lemma Cert6Bb_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd9S22S19A1M0A3S23S19S107G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Bb] [Y6Bb] [run6Bb]); [exact run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S1dS105Sb9S10dA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S157S10dVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Bb : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Bb) (ax_S E6b)).
Lemma E6Bb_0 : ltac2:(tb__ "0|0|
S0S21S1dS107Sb9S10fA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Bb_0 : ltac2:(tb__ "0|0|
S0S21S157S10fVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sb9A1S18S8dA1A2S2bG3S2aG1G2S23G0S2aS3S3S65S2fA1S59A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8dA1A1S6S18Sb9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S19S1cSb9S18S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8dA1A1A4S6aS2G0S7bS26S2S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3S26S2S15bU0S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S8dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S19S151S8dSfS5cS2fA1SaZ0A1S59S22S4A1SdA5A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S93A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S93S14cSf7A3S2bG0Se7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S163S93S14cSf7Se7S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S19S165Sf7S14cS154S93Se7A5SedA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S93A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SedA1A1A1S7S18S93A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S93A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S19S162SedS7S18S93A1A1A2Sc3A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition U7b : axst := Eval vm_compute in (U7p nx0 D6b).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa5A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc3A1S18Sa5A1A2S2bG3S2aG1G2S22G0A1S5fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa5A1A1S6S18Sc3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc3S18Sa5A1A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa5S22S19A1A3A4S23G0S135S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa5S22S19A1M0A3S23S19Sc9G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (CDepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (CDepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc9A1S18S8fA1A2S2bG3S2aG1G2S23G0S2aS3S3S64S2fA1S152S2fA1A4S23G0S2aS3S3S66S2fA1S62A4S22G0A1A3A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8fA1A1S6S18Sc9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc9S18S8fA1A2S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8fA1A1A4S6aS2G0S7bS26S2S23S2S57S2fA1S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU0S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S19S151S8fSfS152S2fA1SaZ0A1SaZ100A1S22S4A1SdA5A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18SbfA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S171S18SbfA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S19S16dSbfU1A2SdbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S25S29S2S8S18SdbA1A1A2Sb3A3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S71S58Sb3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1Sb3A2Li;S58Sb3A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S58Sb3A1A3Li;S6bU0Sb3A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S19S69SdbA1SddA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S170S18SddA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S19S16cSddU1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S9fS14cSf9A3S2bG0Se9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S163S9fS14cSf9Se9S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S19S165Sf9S14cS154S9fSe9A5SefA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S9fA1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SefA1A1A1S7S18S9fA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S9fA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S19S162SefS7S18S9fA1A1A2Sc5A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition U8b : axst := Eval vm_compute in (U8p nx0 D7b).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa7A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc5A1S18Sa7A1A2S2bG3S2aG1G2S22G0A1S60S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa7A1A1S6S18Sc5A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc5S18Sa7A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa7S22S19A1A3A4S23G0S137S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa7S22S19A1M0A3S23S19ScbG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S91A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18ScbA1S18S91A1A2S2bG3S2aG1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S91A1A1S6S18ScbA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S19S1cScbS18S91A1A2S91A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S91A1A1A4S6aS2G0S7bS26S2S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU0S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS91A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S19S151S91SfS5dS2fA1SaZ0A1S67S2fA1S22S4A1SdA5A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S95A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S95S160SfbA3S2bG0SebA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S163S95S160SfbSebS6aS1aS19S1fS161A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S19S165SfbS160S155S95SebA5Sf1A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S95A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sf1A1A1A1S7S18S95A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S95A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S19S162Sf1S7S18S95A1A1A2Sc7A3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition U9b : axst := Eval vm_compute in (U9p nx0 D8b).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa9A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc7A1S18Sa9A1A2S2bG3S2aG1G2S22G0A1S61S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa9A1A1S6S18Sc7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc7S18Sa9A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3S23S19Sa9S22S19A1A3A4S23G0S139S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3VGS0;S23S19Sa9S22S19A1M0A3S23S19SfdS23S19Sa3G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18Sa3A1A1A4S6aS2G0S7bS26S2S23S2S63S2fA1S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3A3S26S2S15bU0S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18Sa3A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18Sa3A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30S5SeS40A1S7S18Sa3A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bSa3A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S19S151Sa3SfS5eS2fA1SaZ0A1SaZ1A1S22S4A1SdA5A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sc1A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT9q CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S22S35A1A3S23S19Sc1S22S19A1A3A4S23G0S13bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S22S35A1A3VGS0;S23S19Sc1S22S19A1M0A3S23S19SffG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S19S56SfdS109SaZ1800A1A3S101A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S19S56S101S2eS109A1SaZ2800A1A3SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition perm9fb : list nat := Eval vm_compute in (S iMfb :: seq 0 (S iMfb) ++ seq (S (S iMfb)) (length (ss_objs (ax_S S9bfb)) - S (S iMfb))).
Definition D9fb : axst := Eval vm_compute in (ax_setS S9bfb (set_objs (ax_S S9bfb) (select (ss_objs (ax_S S9bfb)) perm9fb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|1|
S0S19S1cSbbS72S18SbbA1M0S70S8G0A1Sf3A2A2A2Sb5A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Lemma NDpfb_0 : nodupN perm9fb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbbA1A1A2A2Li;Sf3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf3A3Li;S6bU0S29S2S8S18SbbA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fbA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9fb).
Definition D9fbB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9fb).
Lemma HD9Afb_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb5A2Se0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fbA)). Qed.
Lemma HD9Bfb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb5A2Se1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fbB)). Qed.
Lemma FBA9fb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb5A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9fb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb5A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfbA : option (list leafA) := Eval vm_compute in (runTF D9fbA).
Lemma runFfbA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se0S22S19A1A3A4S23G0S13eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfbA]). Qed.
Definition FFfbA : axst := Eval vm_compute in (leafS 0 runFfbA).
Lemma CertFfbA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se0S22S19A1M0A3S23S19S7eG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fbA] [FFfbA] [runFfbA]); [exact runFfbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfbA : list cell := Eval vm_compute in (cells_at 5 FFfbA).
Definition c1fbA : list cell := Eval vm_compute in (cells_at 38 FFfbA).
Definition c2fbA : list cell := Eval vm_compute in (cells_at 39 FFfbA).
Definition c4fbA : list cell := Eval vm_compute in (cells_at 41 FFfbA).
Definition c5fbA : list cell := Eval vm_compute in (cells_at 45 FFfbA).
Definition mcfbA : list cell := Eval vm_compute in (cells_at 46 FFfbA).
Definition xcfbA : list cell := Eval vm_compute in (cells_at 48 FFfbA).
Definition tybfbA : Z := Eval vm_compute in (tyb_of mcfbA).
Lemma SELFfbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7eA1A1S3bU0S2cA2A2S26S2S39VW;S98A2S26S2S159S45S2fSacS11aS122S12aS86S146Z8SdS2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfbA ++ RT_m1 ++ RSF nx0 c1fbA c2fbA c4fbA c5fbA mcfbA xcfbA 8 DUnknown false)). Qed.
Lemma NDFfbA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7eA1A1A2A2Li;S3bU0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfbA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S2cA2A3Li;S6bG0S29S2S8S18S7eA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfbA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfbA_0 : ax_base FFfbA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfbA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfbA_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfbA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7eA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSacA3S1S30S4S46SacA3S1S30S4S47SacA3S1S30S4S4bSacA3S1S30S4S49SbS14eA1A1SacA3S30S4S48SacA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fbA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S86A3S1S30S4S50S86A3S1S30S4S51S86A3S1S30S4S4dS86A3S1S30S4S4eS86A3S1S30S4S4cS2fA1S86A3S1S30S4S54S86A3S1S30S4S55Sd0A1S86A3S1S30S4S53S86A3S30S4S52S86A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfbA) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfbA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfbA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd0A2S15eSd0Z100A2A2S15cS15fSd0Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfbA_0 : In (xc_map nx0) xcfbA. Proof. exact (In_of_cellb (xc_map nx0) xcfbA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfbA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7eA1S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S98S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfbA nx0)). Qed.
Lemma NDUfbA_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfbA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fbA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7eS3aVW;S98S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fbA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7eA1S3aVW;S98S2fA3M4A2S3dS7eG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fbA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7eA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfbA : wsub := Eval vm_compute in (infer_sub NF (S2F FFfbA (KUB W swcfbA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fbA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7eS3aVW;S98S2fA3S2fA3S158VW;Vst;A2S112A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fbA_0 : wsub_idc sFfbA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fbA_0 : ltac2:(tb__ "0|0|
S0S3S156S112S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFfbB : option (list leafA) := Eval vm_compute in (runTF D9fbB).
Lemma runFfbB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se1S22S19A1A3A4S23G0S13fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfbB]). Qed.
Definition FFfbB : axst := Eval vm_compute in (leafS 0 runFfbB).
Lemma CertFfbB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se1S22S19A1M0A3S23S19S7fG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fbB] [FFfbB] [runFfbB]); [exact runFfbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfbB : list cell := Eval vm_compute in (cells_at 5 FFfbB).
Definition c1fbB : list cell := Eval vm_compute in (cells_at 38 FFfbB).
Definition c2fbB : list cell := Eval vm_compute in (cells_at 39 FFfbB).
Definition c4fbB : list cell := Eval vm_compute in (cells_at 41 FFfbB).
Definition c5fbB : list cell := Eval vm_compute in (cells_at 45 FFfbB).
Definition mcfbB : list cell := Eval vm_compute in (cells_at 46 FFfbB).
Definition xcfbB : list cell := Eval vm_compute in (cells_at 48 FFfbB).
Definition tybfbB : Z := Eval vm_compute in (tyb_of mcfbB).
Lemma SELFfbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7fA1A1S3bU0S2cA2A2S26S2S39VW;S99A2S26S2S159S45S2fSadS11bS123S12bS87S147Z8SdS2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfbB ++ RT_m1 ++ RSF nx0 c1fbB c2fbB c4fbB c5fbB mcfbB xcfbB 8 DUnknown false)). Qed.
Lemma NDFfbB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7fA1A1A2A2Li;S3bU0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfbB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S2cA2A3Li;S6bG0S29S2S8S18S7fA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfbB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfbB_0 : ax_base FFfbB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfbB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfbB_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfbB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSadA3S1S30S4S46SadA3S1S30S4S47SadA3S1S30S4S4bSadA3S1S30S4S49SbS14eA1A1SadA3S30S4S48SadA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fbB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S87A3S1S30S4S50S87A3S1S30S4S51S87A3S1S30S4S4dS87A3S1S30S4S4eS87A3S1S30S4S4cS2fA1S87A3S1S30S4S54S87A3S1S30S4S55Sd1A1S87A3S1S30S4S53S87A3S30S4S52S87A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfbB) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfbB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfbB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd1A2S15eSd1Z100A2A2S15cS15fSd1Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfbB_0 : In (xc_map nx0) xcfbB. Proof. exact (In_of_cellb (xc_map nx0) xcfbB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfbB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7fA1S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S99S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfbB nx0)). Qed.
Lemma NDUfbB_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfbB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fbB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7fS3aVW;S99S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fbB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7fA1S3aVW;S99S2fA3M4A2S3dS7fG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fbB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7fA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfbB : wsub := Eval vm_compute in (infer_sub NF (S2F FFfbB (KUB W swcfbB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fbB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7fS3aVW;S99S2fA3S2fA3S158VW;Vst;A2S113A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fbB_0 : wsub_idc sFfbB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fbB_0 : ltac2:(tb__ "0|0|
S0S3S156S113S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S19S56SffS10bSaZ1800A1A3S103A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S19S56S103S2eS10bA1SaZ2800A1A3SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition perm9qb : list nat := Eval vm_compute in (S iMqb :: seq 0 (S iMqb) ++ seq (S (S iMqb)) (length (ss_objs (ax_S S9bqb)) - S (S iMqb))).
Definition D9qb : axst := Eval vm_compute in (ax_setS S9bqb (set_objs (ax_S S9bqb) (select (ss_objs (ax_S S9bqb)) perm9qb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|1|
S0S19S1cSbdS72S18SbdA1M0S70S8G0A1Sf5A2A2A2Sb7A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Lemma NDpqb_0 : nodupN perm9qb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbdA1A1A2A2Li;Sf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf5A3Li;S6bU0S29S2S8S18SbdA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qbA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9qb).
Definition D9qbB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9qb).
Lemma HD9Aqb_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb7A2Se4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qbA)). Qed.
Lemma HD9Bqb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb7A2Se5A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qbB)). Qed.
Lemma FBA9qb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb7A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9qb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb7A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqbA : option (list leafA) := Eval vm_compute in (runTF D9qbA).
Lemma runFqbA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se4S22S19A1A3A4S23G0S142S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqbA]). Qed.
Definition FFqbA : axst := Eval vm_compute in (leafS 0 runFqbA).
Lemma CertFqbA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se4S22S19A1M0A3S23S19S82G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qbA] [FFqbA] [runFqbA]); [exact runFqbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqbA : list cell := Eval vm_compute in (cells_at 5 FFqbA).
Definition c1qbA : list cell := Eval vm_compute in (cells_at 38 FFqbA).
Definition c2qbA : list cell := Eval vm_compute in (cells_at 39 FFqbA).
Definition c4qbA : list cell := Eval vm_compute in (cells_at 41 FFqbA).
Definition c5qbA : list cell := Eval vm_compute in (cells_at 45 FFqbA).
Definition mcqbA : list cell := Eval vm_compute in (cells_at 46 FFqbA).
Definition xcqbA : list cell := Eval vm_compute in (cells_at 48 FFqbA).
Definition tybqbA : Z := Eval vm_compute in (tyb_of mcqbA).
Lemma SELFqbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S82A1A1S3bU0S20A2A2S26S2S39VW;S9cA2S26S2S159S45S2fSb0S11eS126S12eS8aS14aZ8SdS20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqbA ++ RT_m1 ++ RSF nx0 c1qbA c2qbA c4qbA c5qbA mcqbA xcqbA 8 DUnknown true)). Qed.
Lemma NDFqbA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S82A1A1A2A2Li;S3bU0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqbA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S20A2A3Li;S6bG0S29S2S8S18S82A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqbA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS82A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqbA_0 : ax_base FFqbA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqbA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S82A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqbA_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S82A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqbA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S82A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSb0A3S1S30S4S46Sb0A3S1S30S4S47Sb0A3S1S30S4S4bSb0A3S1S30S4S49SbS14eA1A1Sb0A3S30S4S48Sb0A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qbA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S8aA3S1S30S4S50S8aA3S1S30S4S51S8aA3S1S30S4S4dS8aA3S1S30S4S4eS8aA3S1S30S4S4cS2fA1S8aA3S1S30S4S54S8aA3S1S30S4S55Sd4A1S8aA3S1S30S4S53S8aA3S30S4S52S8aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqbA) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqbA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqbA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd4A2S15eSd4Z100A2A2S15cS15fSd4Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqbA_0 : In (xc_map nx0) xcqbA. Proof. exact (In_of_cellb (xc_map nx0) xcqbA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqbA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S82A1S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S9cS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqbA nx0)). Qed.
Lemma NDUqbA_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqbA_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qbA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS82S3aVW;S9cS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qbA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S82A1S3aVW;S9cS2fA3M4A2S3dS82G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qbA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S82A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqbA : wsub := Eval vm_compute in (infer_sub NF (S2F FFqbA (KUB W swcqbA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qbA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS82S3aVW;S9cS2fA3S2fA3S158VW;Vst;A2S116A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qbA_0 : wsub_idc sFqbA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qbA_0 : ltac2:(tb__ "0|0|
S0S3S156S116S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFqbB : option (list leafA) := Eval vm_compute in (runTF D9qbB).
Lemma runFqbB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se5S22S19A1A3A4S23G0S143S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqbB]). Qed.
Definition FFqbB : axst := Eval vm_compute in (leafS 0 runFqbB).
Lemma CertFqbB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se5S22S19A1M0A3S23S19S83G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qbB] [FFqbB] [runFqbB]); [exact runFqbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqbB : list cell := Eval vm_compute in (cells_at 5 FFqbB).
Definition c1qbB : list cell := Eval vm_compute in (cells_at 38 FFqbB).
Definition c2qbB : list cell := Eval vm_compute in (cells_at 39 FFqbB).
Definition c4qbB : list cell := Eval vm_compute in (cells_at 41 FFqbB).
Definition c5qbB : list cell := Eval vm_compute in (cells_at 45 FFqbB).
Definition mcqbB : list cell := Eval vm_compute in (cells_at 46 FFqbB).
Definition xcqbB : list cell := Eval vm_compute in (cells_at 48 FFqbB).
Definition tybqbB : Z := Eval vm_compute in (tyb_of mcqbB).
Lemma SELFqbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S83A1A1S3bU0S20A2A2S26S2S39VW;S9dA2S26S2S159S45S2fSb1S11fS127S12fS8bS14bZ8SdS20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqbB ++ RT_m1 ++ RSF nx0 c1qbB c2qbB c4qbB c5qbB mcqbB xcqbB 8 DUnknown true)). Qed.
Lemma NDFqbB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S83A1A1A2A2Li;S3bU0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqbB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3bU0M0S20A2A3Li;S6bG0S29S2S8S18S83A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqbB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS83A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqbB_0 : ax_base FFqbB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqbB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S83A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqbB_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S83A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqbB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S83A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSb1A3S1S30S4S46Sb1A3S1S30S4S47Sb1A3S1S30S4S4bSb1A3S1S30S4S49SbS14eA1A1Sb1A3S30S4S48Sb1A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qbB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S8bA3S1S30S4S50S8bA3S1S30S4S51S8bA3S1S30S4S4dS8bA3S1S30S4S4eS8bA3S1S30S4S4cS2fA1S8bA3S1S30S4S54S8bA3S1S30S4S55Sd5A1S8bA3S1S30S4S53S8bA3S30S4S52S8bA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqbB) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqbB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqbB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd5A2S15eSd5Z100A2A2S15cS15fSd5Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqbB_0 : In (xc_map nx0) xcqbB. Proof. exact (In_of_cellb (xc_map nx0) xcqbB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqbB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S83A1S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3S3cU0A1A2S3aVW;S9dS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqbB nx0)). Qed.
Lemma NDUqbB_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqbB_0 : ltac2:(tb__ "0|1|
S0S21S31S25S25S33S25S6dR1A1S3cU0M0A1A3Li;S6bG0S29S2S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qbB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS83S3aVW;S9dS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qbB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S83A1S3aVW;S9dS2fA3M4A2S3dS83G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qbB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S83A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqbB : wsub := Eval vm_compute in (infer_sub NF (S2F FFqbB (KUB W swcqbB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qbB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS83S3aVW;S9dS2fA3S2fA3S158VW;Vst;A2S117A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qbB_0 : wsub_idc sFqbB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qbB_0 : ltac2:(tb__ "0|0|
S0S3S156S117S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineCallocSec6I.

