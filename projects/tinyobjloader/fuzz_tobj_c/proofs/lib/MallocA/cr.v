(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm co.

(* [comment removed for export] *)
Module SpineMallocSec6IE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS10A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2eG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Ba_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ba_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S30G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ba 1 (SLit 0)] [mkVNA Y6Ba 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Ba]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1eA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1eZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S20G0G1A3S3S0S1S22G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2fG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Bb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Bb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S31G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Bb 1 (SLit 0)] [mkVNA Y6Bb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Bb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1fA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1fZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S21G0G1A3S3S0S1S23G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IE.

(* [comment removed for export] *)
Module SpineMallocSec6JE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSec6IE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S39R2A2S6F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S3aR2A2S6F_;F_;Fa;").

Theorem esec_tail_0ha_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (C5B := C5Ba) (Y6A := Y6Aa) (Y6B := Y6Ba) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (sB := s6Ba) (s6 := s6a)
    (R6 := R6a) (HC5A := HC5Aa_0) (HC5B := HC5Ba_0) (FBA := FBAa_0) (FBB := FBBa_0) (Cert6A := Cert6Aa_0) (Cert6B := Cert6Ba_0) (E6A := E6Aa_0) (I6A := I6Aa_0)
    (E6B := E6Ba_0) (I6B := I6Ba_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0) (FX6 := FX6a_0) (XC6 := XC6a_0)
    (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0) (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0) (NXE6B := NXE6Ba_0) (ECert6B := ECert6Ba_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6a) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7a) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8a) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (T9 := T9fa) (iM := iMfa)
    (s9 := s9fa) (R9 := R9fa) (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (He9 := He9fa_0) (Hchk9 := Hchk9fa_0) (HT9 := HT9fa_0) (FBC9 := FBC9fa_0) (FBT9 := FBT9fa_0)
    (NXC9 := NXC9fa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
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
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (T9 := T9qa) (iM := iMqa)
    (s9 := s9qa) (R9 := R9qa) (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (He9 := He9qa_0) (Hchk9 := Hchk9qa_0) (HT9 := HT9qa_0) (FBC9 := FBC9qa_0) (FBT9 := FBT9qa_0)
    (NXC9 := NXC9qa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0ha : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0ha_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0hb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (C5B := C5Bb) (Y6A := Y6Ab) (Y6B := Y6Bb) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (sB := s6Bb) (s6 := s6b)
    (R6 := R6b) (HC5A := HC5Ab_0) (HC5B := HC5Bb_0) (FBA := FBAb_0) (FBB := FBBb_0) (Cert6A := Cert6Ab_0) (Cert6B := Cert6Bb_0) (E6A := E6Ab_0) (I6A := I6Ab_0)
    (E6B := E6Bb_0) (I6B := I6Bb_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0) (FX6 := FX6b_0) (XC6 := XC6b_0)
    (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0) (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0) (NXE6B := NXE6Bb_0) (ECert6B := ECert6Bb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6b) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7b) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8b) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (T9 := T9fb) (iM := iMfb)
    (s9 := s9fb) (R9 := R9fb) (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (He9 := He9fb_0) (Hchk9 := Hchk9fb_0) (HT9 := HT9fb_0) (FBC9 := FBC9fb_0) (FBT9 := FBT9fb_0)
    (NXC9 := NXC9fb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (T9 := T9qb) (iM := iMqb)
    (s9 := s9qb) (R9 := R9qb) (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (He9 := He9qb_0) (Hchk9 := Hchk9qb_0) (HT9 := HT9qb_0) (FBC9 := FBC9qb_0) (FBT9 := FBT9qb_0)
    (NXC9 := NXC9qb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0hb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0hb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JE.

(* [comment removed for export] *)
Module SpineMallocSecOK0W2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JLW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JLW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS27R2A2S1aF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS2aR2A2S1aF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S10SdVCST;R1A2S1cS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S8S3S9SeQ40A1M0A1S23VAInv;R4R3R2R1A4S1bS9SbG0G0A2A1S25S24R2A1A1S22S0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem sec_ok_2h : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21ScSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U2S1S2cS8R1LX;RaR9R8R7A8S1dS2S1Z4A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.D2c SpineMallocSec4IW2.T4ac SpineMallocSec4IW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5bc
           sec_g12_2h sec_g3_2h sec_g41_2ha sec_g41_2hb (sec_tail_2ha CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_2hb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_2l : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21SaSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U2S1S2bS8R1LX;RaR9R8R7A8S1dS2S1Z4A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.D2c SpineMallocSec4ILW2.T4ac SpineMallocSec4ILW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5bc
           sec_g12_2l sec_g3_2l sec_g41_2la sec_g41_2lb (sec_tail_2la CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_2lb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_2 : ltac2:(tb__ "0|0|
S12OF_;S8S17S3S9SeQ40A1A1S18R3A1S7Vsegs;R6S5R4A1A3S15Vsegs;R7S5R5A1A3S3S11Vsegs;R9S6Vsegs;S29S2S1R8R7R6A5S26S2S1Z4Z8A4R1R5A5S14Vsegs;S13R6R5S19S16VAInv;VCST;VXGL;S2S1R8R7A8A5A4FrhoE;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl rhoE.
  apply (malloc_sec_2 CST XGL HCST HXGL HCSTM HCSTS law_res ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 (fun X : AA => X) A Kc rho a) rho tp HKc Hokl Hokpl).
  - intros rhoX tr ms md a Hsp HJG Hpl. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0.
    exact (grant_Jo 2%nat st0 4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. change (nxS W0 st0 4) with (nxS (Wcan 2) UStopLe 4). rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0.
    apply (cls_split 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 ok A Kc rho a (ES1g W0 st0 4) _ tp).
    + intros HC. exact (sec_ok_2h ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_2l ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0W2.

(* [comment removed for export] *)
Module SpineMallocSec6IELW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2"; "C5Aa"; "C5Ab"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.
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
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1eG0G1A3S3S0S1S20G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S22G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1fG0G1A3S3S0S1S21G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S23G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IELW2.

(* [comment removed for export] *)
Module SpineMallocSec6JELW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JLW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cr.SpineMallocSec6IELW2.
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

Theorem esec_tail_2la_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (Y6A := Y6Aa) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (s6 := s6a) (R6 := R6a) (FLOW := FLOWa_0) (HC5A := HC5Aa_0)
    (FBA := FBAa_0) (Cert6A := Cert6Aa_0) (E6A := E6Aa_0) (I6A := I6Aa_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0)
    (FX6 := FX6a_0) (XC6 := XC6a_0) (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0)
    (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_etriple 2%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6La) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_etriple 2%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7La) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_etriple 2%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8La) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
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

Theorem esec_tail_2la : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_2la_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_2lb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (Y6A := Y6Ab) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (s6 := s6b) (R6 := R6b) (FLOW := FLOWb_0) (HC5A := HC5Ab_0)
    (FBA := FBAb_0) (Cert6A := Cert6Ab_0) (E6A := E6Ab_0) (I6A := I6Ab_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0)
    (FX6 := FX6b_0) (XC6 := XC6b_0) (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0)
    (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_etriple 2%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6Lb) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_etriple 2%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7Lb) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_etriple 2%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 2%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8Lb) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
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

Theorem esec_tail_2lb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U2Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_2lb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JELW2.

(* [comment removed for export] *)
Module SpineMallocSecOK0SW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "JL_malloc_ok"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "false"; "pair"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JLW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineMallocSec6JLW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSec2S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSecOKP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS27R2A2S1eF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS2aR2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S16SeVCST;R1A2S1fS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variable PF : ltac2:(tb__ "0|0|
S1S9S11S12S1aS1cA2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S1S9S2dS12S1aS1cA2S14S1aS1cSdSbS3S2A3ScS26S0A1VCST;VXGL;R2R1A5A4VPF;R2R1A2A3FKc;FA;").

Theorem sec_ok_2h_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S15SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U2S2S2cS1R1LX;RaR9R8R7A8S20S3S2Z4A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 true CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.D2c SpineMallocSec4IW2.T4ac SpineMallocSec4IW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.C5bc
           sec_g12_2h sec_g3_2h sec_g41_2ha sec_g41_2hb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_2ha_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_2hb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_2l_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S13SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U2S2S2bS1R1LX;RaR9R8R7A8S20S3S2Z4A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.nx0 false CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 4)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2.D2c SpineMallocSec4ILW2.T4ac SpineMallocSec4ILW2.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.C5bc
           sec_g12_2l sec_g3_2l sec_g41_2la sec_g41_2lb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_2la_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_2lb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_2_S : ltac2:(tb__ "0|1|
S18OF_;S1S9S4S11S10Q40M0A1A1SaR3A1S8Vsegs;R6S6R4A1A3S1dVsegs;R7S6R5A1A3S25R7SfG0S5R5PcA2A2A2S4S17Vsegs;RaS7Vsegs;S29S3S2R9R8R7A5S24S3S2Z4Z8A4R1R6A5S1bVsegs;S19R7R6VPF;R9R8A2A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl HROOM rhoE.
  apply (sec_spine_S 2%nat st0 4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SWa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SDa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SWb_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SFB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.CertS1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.WC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.DC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NXC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.IC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R17_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R10_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R12_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R13_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R14_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R15_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.XC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.SK1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0 ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 (fun X : AA => X) A Kc rho a) rho tp _ ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HROOM).
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 2%nat st0 4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.Hnx_0.
    apply (cls_split 2%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.nx0 ok A Kc rho a (ES1g W0 st0 4) _ tp).
    + intros HC. exact (sec_ok_2h_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_2l_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0SW2.

