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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ku k3 k2.

(* [comment removed for export] *)
Module SpineCallocSec5JEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_next"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1"; "U4ac"; "U4bc"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ko.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSec5JW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSecE3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.
Lemma NXE5a_0 : ltac2:(tb__ "0|0|
S10S7S2cVGS0;S5S1aS23A1A1A2S9A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5a_0 : ltac2:(tb__ "0|3|
S10S7SfS1Ufa0S6S0S1eS8S0A1A3VGS0;S6SdSeS23Z1S3Z0M0A1M1A3S8SdA1M2A3S6SdSeS27G0G1A3G2A3A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4ac 1 (SLit 0)] [mkVNA X5ac 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.run5a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.run5a__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_1ha : ltac2:(tb__ "0|6|
S14S1fS2S19Q40M0A1M1S12OF_;S1dVW;Vst;A2S2aVW;Vst;A2S20R6A1S15S2S2SaG1A1M2ScS0S0A2M3S2bG3R1S22R5A1A3S21R2SbS0S0S18G0RbA2S29S18G0S4RcPcA2A2A1A4A2F_;Fbn;S1cR5RbR4A3S11S1S13S1S16U1M4Vst;S17S1bS14S2dR1A1LX;M5R6A2ReRdR5RbA8S25R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S11S1S13S1S16G4Vst;S17G5RbRaR9R8A8S2eR2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => bumpP X)) (T4 := T4ac) (U4 := U4ac) (X5 := X5ac) (C5 := C5ac)
    (WU4 := WU4a_0) (DU4 := DU4a_0) (NXU4 := NXU4a_0) (HU4 := HU4a_0) (Cert5 := Cert5a_0)
    (NXE5 := NXE5a_0) (ECert5 := ECert5a_0) (HDSE := depot_call_SE_1ha);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
Lemma NXE5b_0 : ltac2:(tb__ "0|0|
S10S7S2cVGS0;S5S1aS24A1A1A2S9A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert5b_0 : ltac2:(tb__ "0|3|
S10S7SfS1Ufa0S6S0S1eS8S0A1A3VGS0;S6SdSeS24Z1S3Z0M0A1M1A3S8SdA1M2A3S6SdSeS28G0G1A3G2A3A6S9A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [DPENT] GS0 [mkVNA U4bc 1 (SLit 0)] [mkVNA X5bc 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.run5b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.run5b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g41_1hb : ltac2:(tb__ "0|6|
S14S1fS2S19Q40M0A1M1S12OF_;S1dVW;Vst;A2S2aVW;Vst;A2S20R6A1S15S2S2SaG1A1M2ScS0S0A2M3S2bG3R1S22R5A1A3S21R2SbS0S0S18G0RbA2S29S18G0S4RcPcA2A2A1A4A2F_;Fbn;S1cR5RbR4A3S11S1S13S1S16U1M4Vst;S17S1bS14R1LX;M5R6A2ReRdR5RbA8S26R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S11S1S13S1S16G4Vst;S17G5RbRaR9R8A8S2fR2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCONT.
  eapply esec_g41 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := (fun X : AA => X)) (T4 := T4bc) (U4 := U4bc) (X5 := X5bc) (C5 := C5bc)
    (WU4 := WU4b_0) (DU4 := DU4b_0) (NXU4 := NXU4b_0) (HU4 := HU4b_0) (Cert5 := Cert5b_0)
    (NXE5 := NXE5b_0) (ECert5 := ECert5b_0) (HDSE := depot_call_SE_1hb);
    [exact HW | exact HUS | exact HKc | exact HCONT].
Qed.
End INST.
End SpineCallocSec5JEW1.

(* [comment removed for export] *)
Module SpineCallocSec6IELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "CPC"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1"; "C5Aa"; "C5Ab"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS3S8S10S5S8A1A3A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1fG0G1A3S3S0S1S21G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S23G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2eG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1eA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS3S8S10S5S8A1A3A3VGS0;S3S0S1S1eZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S20G0G1A3S3S0S1S22G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS5S8A1A3VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineCallocSec6IELW1.

(* [comment removed for export] *)
Module SpineCallocSec6IEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "CPC"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CO9pa"; "CO9pb"; "D9faA"; "D9faB"; "D9fbA"; "D9fbB"; "D9qaA"; "D9qaB"; "D9qbA"; "D9qbB"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfaA"; "FFfaB"; "FFfbA"; "FFfbB"; "FFqaA"; "FFqaB"; "FFqbA"; "FFqbB"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S37G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Ba_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ba_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S39G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ba 1 (SLit 0)] [mkVNA Y6Ba 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Ba]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1fA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1fZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS21A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S21Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS23A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS3S8S10S5S8A1A3A3VGS0;S3S0S1S23Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3S3S0S1S27G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS5S8A1A3VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfaA_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEFfaB_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfaA_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2fG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9faA 1 (SLit 0)] [mkVNA FFfaA 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfaA]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECertFfaB_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S30G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9faB 1 (SLit 0)] [mkVNA FFfaB 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfaB]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqaA_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEFqaB_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqaA_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S33G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qaA 1 (SLit 0)] [mkVNA FFqaA 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqaA]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECertFqaB_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S34G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qaB 1 (SLit 0)] [mkVNA FFqaB 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqaB]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S38G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Bb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Bb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S3aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Bb 1 (SLit 0)] [mkVNA Y6Bb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Bb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS20A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S20Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS22A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S22Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2eG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS24A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS3S8S10S5S8A1A3A3VGS0;S3S0S1S24Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3S3S0S1S28G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SfS5S8A1A3VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [CPC] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfbA_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEFfbB_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfbA_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S31G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fbA 1 (SLit 0)] [mkVNA FFfbA 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfbA]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECertFfbB_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S32G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fbB 1 (SLit 0)] [mkVNA FFfbB 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfbB]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFfbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqbA_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEFqbB_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1eA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqbA_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S35G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qbA 1 (SLit 0)] [mkVNA FFqbA 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqbA]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECertFqbB_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S1eZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S36G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qbB 1 (SLit 0)] [mkVNA FFqbB 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqbB]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1.runFqbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineCallocSec6IEW1.

(* [comment removed for export] *)
Module SpineCallocSec6JELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ku.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ko.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kq.SpineCallocSec6ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ku.SpineCallocSec6JLW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l2.SpineCallocSec6IELW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2bS37R2A2S5F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2bS38R2A2S5F_;F_;Fa;").

Theorem esec_tail_0la_P : ltac2:(tb__ "0|9|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S33VW;Vst;A2S32VCST;VXGL;R8R7A4A4R1A3S30VW;Vst;A2S28R9A1S1S2G1S7R9R1A2S7RaR1A2A3Fi;S1S2SbS1bQ8A1M4A1S9RaR1A2S9RbR1A2A3Fl;S29VCST;VXGL;RdRdS6RbA1S6RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S2cRaA1A3S2aR2ScS0S0S1cG0RdA2M6S2fS1cG0S7RePcA2A2A1M7A4A2F_;Fbn;S0S3S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S4S2S10G4A1S6RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11S31R1A1LX;RdA2R13R12R10RfA8S35R2R1A5S23SaS20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (Y6A := Y6Aa) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (s6 := s6a) (R6 := R6a) (FLOW := FLOWa_0) (HC5A := HC5Aa_0)
    (FBA := FBAa_0) (Cert6A := Cert6Aa_0) (E6A := E6Aa_0) (I6A := I6Aa_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0)
    (FX6 := FX6a_0) (XC6 := XC6a_0) (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0)
    (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_etriple 1%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6La) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_etriple 1%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7La) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_etriple 1%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8La) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with (nW := 1%nat) (st := st) (nx := nx0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (D9 := D9fa) (iM := iMfa) (perm := perm9fa)
      (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (HD9 := HD9fa_0) (NDp := NDpfa_0) (BNDp := BNDpfa_0) (COVp := COVpfa_0).
    intros rZ tZ.
    eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfa) (swc := swcfa) (c1 := c1fa) (c2 := c2fa) (c4 := c4fa) (c5 := c5fa) (mc := mcfa)
    (xc := xcfa) (tyb := tybfa) (SELF := SELFfa_0) (NDF := NDFfa_0) (BNDF := BNDFfa_0) (COVF := COVFfa_0) (XFn := XFnfa_0) (BFb := BFbfa_0) (FPF := FPFfa_0)
    (FXF := FXFfa_0) (FPAR := FPARfa_0) (Hc1 := Hc1fa_0) (Hmc := Hmcfa_0) (Htyb := Htybfa_0) (Hxc := Hxcfa_0) (WCU := WCUfa_0) (SELU := SELUfa_0) (NDU := NDUfa_0)
    (BNDU := BNDUfa_0) (COVU := COVUfa_0) (W9 := W9fa_0) (D9 := D9fa_0) (XB9 := XB9fa_0) (s9 := sFfa) (ENT9 := ENT9fa_0) (SID9 := SID9fa_0) (G110 := G110fa_0)
    (DF9 := D9fa) (CertF := CertFfa_0)
      (NXEF := NXEFfa_0) (ECertF := ECertFfa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with (nW := 1%nat) (st := st) (nx := nx0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (D9 := D9qa) (iM := iMqa) (perm := perm9qa)
      (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (HD9 := HD9qa_0) (NDp := NDpqa_0) (BNDp := BNDpqa_0) (COVp := COVpqa_0).
    intros rZ tZ.
    eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_1la : ltac2:(tb__ "0|8|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12S30VW;Vst;A2S28R7A1S1S2G1S7R7R1A2S7R8R1A2A3Fi;S1S2SbS1bQ8A1M3A1S9R8R1A2S9R9R1A2A3Fl;S29VCST;VXGL;RbRbS6R9A1S6R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S2cR8A1A3S2aR2ScS0S0S1cG0RbA2M5S2fS1cG0S7RcPcA2A2A1M6A4A2F_;Fbn;S0S3S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S4S2S10G3A1S6RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11S31R1A1LX;RbA2R11R10ReRdA8S35R2R1A5S23SaS20RfRcS34VCST;VXGL;VW;Vst;R11R10A6A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0la_P A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0lb_P : ltac2:(tb__ "0|9|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S33VW;Vst;A2S32VCST;VXGL;R8R7A4A4R1A3S30VW;Vst;A2S28R9A1S1S2G1S7R9R1A2S7RaR1A2A3Fi;S1S2SbS1bQ8A1M4A1S9RaR1A2S9RbR1A2A3Fl;S29VCST;VXGL;RdRdS6RbA1S6RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S2cRaA1A3S2aR2ScS0S0S1cG0RdA2M6S2fS1cG0S7RePcA2A2A1M7A4A2F_;Fbn;S0S3S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S4S2S10G4A1S6RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11R1LX;RdA2R13R12R10RfA8S36R2R1A5S23SaS20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (Y6A := Y6Ab) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (s6 := s6b) (R6 := R6b) (FLOW := FLOWb_0) (HC5A := HC5Ab_0)
    (FBA := FBAb_0) (Cert6A := Cert6Ab_0) (E6A := E6Ab_0) (I6A := I6Ab_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0)
    (FX6 := FX6b_0) (XC6 := XC6b_0) (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0)
    (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_etriple 1%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6Lb) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_etriple 1%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7Lb) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_etriple 1%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 1%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8Lb) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with (nW := 1%nat) (st := st) (nx := nx0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (D9 := D9fb) (iM := iMfb) (perm := perm9fb)
      (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (HD9 := HD9fb_0) (NDp := NDpfb_0) (BNDp := BNDpfb_0) (COVp := COVpfb_0).
    intros rZ tZ.
    eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with (nW := 1%nat) (st := st) (nx := nx0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (D9 := D9qb) (iM := iMqb) (perm := perm9qb)
      (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (HD9 := HD9qb_0) (NDp := NDpqb_0) (BNDp := BNDpqb_0) (COVp := COVpqb_0).
    intros rZ tZ.
    eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_1lb : ltac2:(tb__ "0|8|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12S30VW;Vst;A2S28R7A1S1S2G1S7R7R1A2S7R8R1A2A3Fi;S1S2SbS1bQ8A1M3A1S9R8R1A2S9R9R1A2A3Fl;S29VCST;VXGL;RbRbS6R9A1S6R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S2cR8A1A3S2aR2ScS0S0S1cG0RbA2M5S2fS1cG0S7RcPcA2A2A1M6A4A2F_;Fbn;S0S3S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S4S2S10G3A1S6RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11R1LX;RbA2R11R10ReRdA8S36R2R1A5S23SaS20RfRcS34VCST;VXGL;VW;Vst;R11R10A6A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0lb_P A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6JELW1.

(* [comment removed for export] *)
Module SpineCallocSec6JEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ku.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ko.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.SpineCallocSec6IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ku.SpineCallocSec6JW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l2.SpineCallocSec6IEW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2bS37R2A2S5F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S2bVCST;R1A2S2bS38R2A2S5F_;F_;Fa;").

Theorem esec_tail_0ha_P : ltac2:(tb__ "0|9|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S33VW;Vst;A2S32VCST;VXGL;R8R7A4A4R1A3S30VW;Vst;A2S28R9A1S1S2G1S7R9R1A2S7RaR1A2A3Fi;S1S2SbS1bQ8A1M4A1S9RaR1A2S9RbR1A2A3Fl;S29VCST;VXGL;RdRdS6RbA1S6RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S2cRaA1A3S2aR2ScS0S0S1cG0RdA2M6S2fS1cG0S7RePcA2A2A1M7A4A2F_;Fbn;S0S3S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S4S2S10G4A1S6RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11S31R1A1LX;RdA2R13R12R10RfA8S35R2R1A5S23SaS20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (C5B := C5Ba) (Y6A := Y6Aa) (Y6B := Y6Ba) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (sB := s6Ba) (s6 := s6a)
    (R6 := R6a) (HC5A := HC5Aa_0) (HC5B := HC5Ba_0) (FBA := FBAa_0) (FBB := FBBa_0) (Cert6A := Cert6Aa_0) (Cert6B := Cert6Ba_0) (E6A := E6Aa_0) (I6A := I6Aa_0)
    (E6B := E6Ba_0) (I6B := I6Ba_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0) (FX6 := FX6a_0) (XC6 := XC6a_0)
    (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0) (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0) (NXE6B := NXE6Ba_0) (ECert6B := ECert6Ba_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  eapply esec_g44 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6a) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  eapply esec_g45 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7a) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  eapply esec_g46 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8a) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47d with (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (D9 := D9fa) (iM := iMfa) (perm := perm9fa)
      (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (HD9 := HD9fa_0) (NDp := NDpfa_0) (BNDp := BNDpfa_0) (COVp := COVpfa_0) (BXg := BXg) (D9A := D9faA) (D9B := D9faB)
      (HD9A := HD9Afa_0) (HD9B := HD9Bfa_0) (FBA9 := FBA9fa_0) (FBB9 := FBB9fa_0).
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfaA) (swc := swcfaA) (c1 := c1faA) (c2 := c2faA) (c4 := c4faA) (c5 := c5faA) (mc := mcfaA)
    (xc := xcfaA) (tyb := tybfaA) (SELF := SELFfaA_0) (NDF := NDFfaA_0) (BNDF := BNDFfaA_0) (COVF := COVFfaA_0) (XFn := XFnfaA_0) (BFb := BFbfaA_0) (FPF := FPFfaA_0)
    (FXF := FXFfaA_0) (FPAR := FPARfaA_0) (Hc1 := Hc1faA_0) (Hmc := HmcfaA_0) (Htyb := HtybfaA_0) (Hxc := HxcfaA_0) (WCU := WCUfaA_0) (SELU := SELUfaA_0) (NDU := NDUfaA_0)
    (BNDU := BNDUfaA_0) (COVU := COVUfaA_0) (W9 := W9faA_0) (D9 := D9faA_0) (XB9 := XB9faA_0) (s9 := sFfaA) (ENT9 := ENT9faA_0) (SID9 := SID9faA_0) (G110 := G110faA_0)
    (DF9 := D9faA) (CertF := CertFfaA_0)
      (NXEF := NXEFfaA_0) (ECertF := ECertFfaA_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfaB) (swc := swcfaB) (c1 := c1faB) (c2 := c2faB) (c4 := c4faB) (c5 := c5faB) (mc := mcfaB)
    (xc := xcfaB) (tyb := tybfaB) (SELF := SELFfaB_0) (NDF := NDFfaB_0) (BNDF := BNDFfaB_0) (COVF := COVFfaB_0) (XFn := XFnfaB_0) (BFb := BFbfaB_0) (FPF := FPFfaB_0)
    (FXF := FXFfaB_0) (FPAR := FPARfaB_0) (Hc1 := Hc1faB_0) (Hmc := HmcfaB_0) (Htyb := HtybfaB_0) (Hxc := HxcfaB_0) (WCU := WCUfaB_0) (SELU := SELUfaB_0) (NDU := NDUfaB_0)
    (BNDU := BNDUfaB_0) (COVU := COVUfaB_0) (W9 := W9faB_0) (D9 := D9faB_0) (XB9 := XB9faB_0) (s9 := sFfaB) (ENT9 := ENT9faB_0) (SID9 := SID9faB_0) (G110 := G110faB_0)
    (DF9 := D9faB) (CertF := CertFfaB_0)
      (NXEF := NXEFfaB_0) (ECertF := ECertFfaB_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47d with (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (D9 := D9qa) (iM := iMqa) (perm := perm9qa)
      (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (HD9 := HD9qa_0) (NDp := NDpqa_0) (BNDp := BNDpqa_0) (COVp := COVpqa_0) (BXg := BXg) (D9A := D9qaA) (D9B := D9qaB)
      (HD9A := HD9Aqa_0) (HD9B := HD9Bqa_0) (FBA9 := FBA9qa_0) (FBB9 := FBB9qa_0).
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqaA) (swc := swcqaA) (c1 := c1qaA) (c2 := c2qaA) (c4 := c4qaA) (c5 := c5qaA) (mc := mcqaA)
    (xc := xcqaA) (tyb := tybqaA) (SELF := SELFqaA_0) (NDF := NDFqaA_0) (BNDF := BNDFqaA_0) (COVF := COVFqaA_0) (XFn := XFnqaA_0) (BFb := BFbqaA_0) (FPF := FPFqaA_0)
    (FXF := FXFqaA_0) (FPAR := FPARqaA_0) (Hc1 := Hc1qaA_0) (Hmc := HmcqaA_0) (Htyb := HtybqaA_0) (Hxc := HxcqaA_0) (WCU := WCUqaA_0) (SELU := SELUqaA_0) (NDU := NDUqaA_0)
    (BNDU := BNDUqaA_0) (COVU := COVUqaA_0) (W9 := W9qaA_0) (D9 := D9qaA_0) (XB9 := XB9qaA_0) (s9 := sFqaA) (ENT9 := ENT9qaA_0) (SID9 := SID9qaA_0) (G110 := G110qaA_0)
    (DF9 := D9qaA) (CertF := CertFqaA_0)
      (NXEF := NXEFqaA_0) (ECertF := ECertFqaA_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqaB) (swc := swcqaB) (c1 := c1qaB) (c2 := c2qaB) (c4 := c4qaB) (c5 := c5qaB) (mc := mcqaB)
    (xc := xcqaB) (tyb := tybqaB) (SELF := SELFqaB_0) (NDF := NDFqaB_0) (BNDF := BNDFqaB_0) (COVF := COVFqaB_0) (XFn := XFnqaB_0) (BFb := BFbqaB_0) (FPF := FPFqaB_0)
    (FXF := FXFqaB_0) (FPAR := FPARqaB_0) (Hc1 := Hc1qaB_0) (Hmc := HmcqaB_0) (Htyb := HtybqaB_0) (Hxc := HxcqaB_0) (WCU := WCUqaB_0) (SELU := SELUqaB_0) (NDU := NDUqaB_0)
    (BNDU := BNDUqaB_0) (COVU := COVUqaB_0) (W9 := W9qaB_0) (D9 := D9qaB_0) (XB9 := XB9qaB_0) (s9 := sFqaB) (ENT9 := ENT9qaB_0) (SID9 := SID9qaB_0) (G110 := G110qaB_0)
    (DF9 := D9qaB) (CertF := CertFqaB_0)
      (NXEF := NXEFqaB_0) (ECertF := ECertFqaB_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_1ha : ltac2:(tb__ "0|8|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12S30VW;Vst;A2S28R7A1S1S2G1S7R7R1A2S7R8R1A2A3Fi;S1S2SbS1bQ8A1M3A1S9R8R1A2S9R9R1A2A3Fl;S29VCST;VXGL;RbRbS6R9A1S6R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S2cR8A1A3S2aR2ScS0S0S1cG0RbA2M5S2fS1cG0S7RcPcA2A2A1M6A4A2F_;Fbn;S0S3S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S4S2S10G3A1S6RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11S31R1A1LX;RbA2R11R10ReRdA8S35R2R1A5S23SaS20RfRcS34VCST;VXGL;VW;Vst;R11R10A6A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0ha_P A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0hb_P : ltac2:(tb__ "0|9|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S33VW;Vst;A2S32VCST;VXGL;R8R7A4A4R1A3S30VW;Vst;A2S28R9A1S1S2G1S7R9R1A2S7RaR1A2A3Fi;S1S2SbS1bQ8A1M4A1S9RaR1A2S9RbR1A2A3Fl;S29VCST;VXGL;RdRdS6RbA1S6RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S2cRaA1A3S2aR2ScS0S0S1cG0RdA2M6S2fS1cG0S7RePcA2A2A1M7A4A2F_;Fbn;S0S3S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S4S2S10G4A1S6RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11R1LX;RdA2R13R12R10RfA8S36R2R1A5S23SaS20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : stopJ_w W st) by (hw_discharge).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (C5B := C5Bb) (Y6A := Y6Ab) (Y6B := Y6Bb) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (sB := s6Bb) (s6 := s6b)
    (R6 := R6b) (HC5A := HC5Ab_0) (HC5B := HC5Bb_0) (FBA := FBAb_0) (FBB := FBBb_0) (Cert6A := Cert6Ab_0) (Cert6B := Cert6Bb_0) (E6A := E6Ab_0) (I6A := I6Ab_0)
    (E6B := E6Bb_0) (I6B := I6Bb_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0) (FX6 := FX6b_0) (XC6 := XC6b_0)
    (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0) (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0) (NXE6B := NXE6Bb_0) (ECert6B := ECert6Bb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  eapply esec_g44 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6b) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  eapply esec_g45 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7b) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  eapply esec_g46 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8b) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47d with (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (D9 := D9fb) (iM := iMfb) (perm := perm9fb)
      (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (HD9 := HD9fb_0) (NDp := NDpfb_0) (BNDp := BNDpfb_0) (COVp := COVpfb_0) (BXg := BXg) (D9A := D9fbA) (D9B := D9fbB)
      (HD9A := HD9Afb_0) (HD9B := HD9Bfb_0) (FBA9 := FBA9fb_0) (FBB9 := FBB9fb_0).
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfbA) (swc := swcfbA) (c1 := c1fbA) (c2 := c2fbA) (c4 := c4fbA) (c5 := c5fbA) (mc := mcfbA) (xc := xcfbA) (tyb := tybfbA)
    (SELF := SELFfbA_0) (NDF := NDFfbA_0) (BNDF := BNDFfbA_0) (COVF := COVFfbA_0) (XFn := XFnfbA_0) (BFb := BFbfbA_0) (FPF := FPFfbA_0) (FXF := FXFfbA_0) (FPAR := FPARfbA_0)
    (Hc1 := Hc1fbA_0) (Hmc := HmcfbA_0) (Htyb := HtybfbA_0) (Hxc := HxcfbA_0) (WCU := WCUfbA_0) (SELU := SELUfbA_0) (NDU := NDUfbA_0) (BNDU := BNDUfbA_0) (COVU := COVUfbA_0)
    (W9 := W9fbA_0) (D9 := D9fbA_0) (XB9 := XB9fbA_0) (s9 := sFfbA) (ENT9 := ENT9fbA_0) (SID9 := SID9fbA_0) (G110 := G110fbA_0) (DF9 := D9fbA) (CertF := CertFfbA_0)
      (NXEF := NXEFfbA_0) (ECertF := ECertFfbA_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfbB) (swc := swcfbB) (c1 := c1fbB) (c2 := c2fbB) (c4 := c4fbB) (c5 := c5fbB) (mc := mcfbB) (xc := xcfbB) (tyb := tybfbB)
    (SELF := SELFfbB_0) (NDF := NDFfbB_0) (BNDF := BNDFfbB_0) (COVF := COVFfbB_0) (XFn := XFnfbB_0) (BFb := BFbfbB_0) (FPF := FPFfbB_0) (FXF := FXFfbB_0) (FPAR := FPARfbB_0)
    (Hc1 := Hc1fbB_0) (Hmc := HmcfbB_0) (Htyb := HtybfbB_0) (Hxc := HxcfbB_0) (WCU := WCUfbB_0) (SELU := SELUfbB_0) (NDU := NDUfbB_0) (BNDU := BNDUfbB_0) (COVU := COVUfbB_0)
    (W9 := W9fbB_0) (D9 := D9fbB_0) (XB9 := XB9fbB_0) (s9 := sFfbB) (ENT9 := ENT9fbB_0) (SID9 := SID9fbB_0) (G110 := G110fbB_0) (DF9 := D9fbB) (CertF := CertFfbB_0)
      (NXEF := NXEFfbB_0) (ECertF := ECertFfbB_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47d with (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (D9 := D9qb) (iM := iMqb) (perm := perm9qb)
      (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (HD9 := HD9qb_0) (NDp := NDpqb_0) (BNDp := BNDpqb_0) (COVp := COVpqb_0) (BXg := BXg) (D9A := D9qbA) (D9B := D9qbB)
      (HD9A := HD9Aqb_0) (HD9B := HD9Bqb_0) (FBA9 := FBA9qb_0) (FBB9 := FBB9qb_0).
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqbA) (swc := swcqbA) (c1 := c1qbA) (c2 := c2qbA) (c4 := c4qbA) (c5 := c5qbA) (mc := mcqbA) (xc := xcqbA) (tyb := tybqbA)
    (SELF := SELFqbA_0) (NDF := NDFqbA_0) (BNDF := BNDFqbA_0) (COVF := COVFqbA_0) (XFn := XFnqbA_0) (BFb := BFbqbA_0) (FPF := FPFqbA_0) (FXF := FXFqbA_0) (FPAR := FPARqbA_0)
    (Hc1 := Hc1qbA_0) (Hmc := HmcqbA_0) (Htyb := HtybqbA_0) (Hxc := HxcqbA_0) (WCU := WCUqbA_0) (SELU := SELUqbA_0) (NDU := NDUqbA_0) (BNDU := BNDUqbA_0) (COVU := COVUqbA_0)
    (W9 := W9qbA_0) (D9 := D9qbA_0) (XB9 := XB9qbA_0) (s9 := sFqbA) (ENT9 := ENT9qbA_0) (SID9 := SID9qbA_0) (G110 := G110qbA_0) (DF9 := D9qbA) (CertF := CertFqbA_0)
      (NXEF := NXEFqbA_0) (ECertF := ECertFqbA_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
    + intros rZ tZ.
      eapply esec_g48_P with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqbB) (swc := swcqbB) (c1 := c1qbB) (c2 := c2qbB) (c4 := c4qbB) (c5 := c5qbB) (mc := mcqbB) (xc := xcqbB) (tyb := tybqbB)
    (SELF := SELFqbB_0) (NDF := NDFqbB_0) (BNDF := BNDFqbB_0) (COVF := COVFqbB_0) (XFn := XFnqbB_0) (BFb := BFbqbB_0) (FPF := FPFqbB_0) (FXF := FXFqbB_0) (FPAR := FPARqbB_0)
    (Hc1 := Hc1qbB_0) (Hmc := HmcqbB_0) (Htyb := HtybqbB_0) (Hxc := HxcqbB_0) (WCU := WCUqbB_0) (SELU := SELUqbB_0) (NDU := NDUqbB_0) (BNDU := BNDUqbB_0) (COVU := COVUqbB_0)
    (W9 := W9qbB_0) (D9 := D9qbB_0) (XB9 := XB9qbB_0) (s9 := sFqbB) (ENT9 := ENT9qbB_0) (SID9 := SID9qbB_0) (G110 := G110qbB_0) (DF9 := D9qbB) (CertF := CertFqbB_0)
      (NXEF := NXEFqbB_0) (ECertF := ECertFqbB_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_1hb : ltac2:(tb__ "0|8|
S11S27S8S8S1bQ40M0A1M1SbG1A1M2S12S30VW;Vst;A2S28R7A1S1S2G1S7R7R1A2S7R8R1A2A3Fi;S1S2SbS1bQ8A1M3A1S9R8R1A2S9R9R1A2A3Fl;S29VCST;VXGL;RbRbS6R9A1S6R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S2cR8A1A3S2aR2ScS0S0S1cG0RbA2M5S2fS1cG0S7RcPcA2A2A1M6A4A2F_;Fbn;S0S3S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S4S2S10G3A1S6RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S8G2S1fSaS21SaS2dU1Vst;S2eS25S11R1LX;RbA2R11R10ReRdA8S36R2R1A5S23SaS20RfRcS34VCST;VXGL;VW;Vst;R11R10A6A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0hb_P A Kc rho0 rho a tp0 G2 (PFc CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineCallocSec6JEW1.

(* [comment removed for export] *)
Module SpineCallocSecOK0EW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ku.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CSecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineCallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSecE0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.SpineCallocSecE4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.SpineCallocSec3IEW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec4IEW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l2.SpineCallocSec5JEW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l2.SpineCallocSec6JEW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.SpineCallocSec3IELW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec4IELW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ku.SpineCallocSec5JELW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l2.SpineCallocSec6JELW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS21R2A2S15F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SdSaVCST;R1A2SaS23R2A2S15F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SdSaVCST;R1A2S17S22R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S5S2S6SbQ40A1M0A1S1dVAInv;R4R3R2R1A4S16S6S8G0G0A2A1S1fS1eR2A1A1S1cS4A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem esec_ok_1h : ltac2:(tb__ "0|2|
S5S13S2SbQ40M0A1M1S6G1A1S14R4A1S1aS9ScG0R3A2S1bScG0S3R4PcA2A2A1A3S2SeS4S10S4S19U1S0S25S5R1LX;R8R7R6R5A8S18S1S0Z3A3R1R4A5S11S4SfR6R4S12VCST;VXGL;S1S0R8R7A6A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 3)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.D2c SpineCallocSec4IW1.T4ac SpineCallocSec4IW1.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.C5bc
           esec_g12_1h esec_g3_1h esec_g41_1ha esec_g41_1hb (esec_tail_1ha CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_1hb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(hw_discharge) (stopJ_w_stable _ _ stopJ_w_1pc) HKc HC rhoX).
Qed.

Theorem esec_ok_1l : ltac2:(tb__ "0|2|
S5S13S2SbQ40M0A1M1S6G1A1S14R4A1S1aS7ScG0R3A2S1bScG0S3R4PcA2A2A1A3S2SeS4S10S4S19U1S0S24S5R1LX;R8R7R6R5A8S18S1S0Z3A3R1R4A5S11S4SfR6R4S12VCST;VXGL;S1S0R8R7A6A5A3FrhoX;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HKc HC rhoX.
  exact (esec_ok_chain 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 3)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1.D2c SpineCallocSec4ILW1.T4ac SpineCallocSec4ILW1.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1.C5bc
           esec_g12_1l esec_g3_1l esec_g41_1la esec_g41_1lb (esec_tail_1la CST XGL HCST HXGL HCSTM HCSTS) (esec_tail_1lb CST XGL HCST HXGL HCSTM HCSTS)
           A Kc rho a tp ltac:(hw_discharge) (stopJ_w_stable _ _ stopJ_w_1pc) HKc HC rhoX).
Qed.

Theorem ecalloc_sec_ok_1 : ltac2:(tb__ "0|0|
S5S13S2S6SbQ40A1A1S14R3A1S2SeVsegs;S10Vsegs;S26S1S0R6R5R4A5S20S1S0Z3Z8A4R1R3A5S11Vsegs;SfR4R3S12VCST;VXGL;S1S0R6R5A6A5A3FrhoE;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoE.
  eapply esec_spine with (nW := 1%nat) (st := st0) (tmax := 3) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM) (HCSTS := HCSTS) (law_res := law_res)
    (Wa := SWa_0) (Da := SDa_0) (Wb := SWb_0) (FB := SFB) (NXS0 := NXS0_0) (ECertS1 := ECertS1_0) (WC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.WC1_0) (DC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.DC1_0)
    (NXC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.NXC1_0) (IC1 := IC1_0) (R17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R17_0) (R11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R11_0) (R12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R12_0) (R13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R13_0)
    (R14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R14_0) (R15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R15_0) (NX1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.NX1_0) (NXS1f := NXS1f_0) (ECertSf := ECertSf_0) (FC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.FC1_0)
    (RN := RN_0) (WRn := WRn_0) (DKRn := DKRn_0) (NXRn := NXRn_0) (ENTn := ENTn_0) (IDn := IDn_0)
    (R10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R10_0) (XC1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.XC1_0) (SK1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.SK1_0)
    (Jo := fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGsC 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.nx0 (fun X : AA => X) A Kc rho a).
  - hw_discharge.
  - exact (stopJ_w_stable _ _ stopJ_w_1pc).
  - exact HKc.
  - unfold PFc. left. reflexivity.
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 1%nat st0 3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_w_stable _ _ stopJ_w_1pc) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.Hnx_0.
    apply (ecls_split 1%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.nx0 A Kc rho a (ES1g W0 st0 3) _ tp).
    + intros HC. exact (esec_ok_1h A Kc rho a tp HKc HC _).
    + intros HC. exact (esec_ok_1l A Kc rho a tp HKc HC _).
Qed.
End OK0E.
End SpineCallocSecOK0EW1.

