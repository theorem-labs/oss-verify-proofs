(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_055.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1 ca c4.

(* [comment removed for export] *)
Module SpineCallocSec4IELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S25A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S24A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ7050cS0SbZ40f5cS2SbA1A3A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2bG0G1A3S0S8S9S2cG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x7050c; 0x40f5c] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineCallocSec4ILW1.run3]); [exact SpineCallocSec4ILW1.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ40f5cS2SbA1A3VGS0;S0S8S9S25Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2aG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x40f5c] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineCallocSec4ILW1.run3a]); [exact SpineCallocSec4ILW1.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineCallocSec4ILW1.run4a]); [exact SpineCallocSec4ILW1.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S24Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineCallocSec4ILW1.run4b]); [exact SpineCallocSec4ILW1.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_1l : ltac2:(tb__ "0|8|
S1dS3bS10S18Q40M0A1M1S1bOF_;S32VW;Vst;A2S3cR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S3aS17G0R6A2A1M2R1A2S34R1S33G2S35S31S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S31S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U1M6Vst;S22S1dS39R1A1LX;RdRcR4RaA8S28R3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S29R2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [hw_discharge | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineCallocSec4IELW1.

(* [comment removed for export] *)
Module SpineMallocSec5JL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0la : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0lb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0lb).
Qed.
End INST.
End SpineMallocSec5JL.

(* [comment removed for export] *)
Module SpineMallocSec5JLW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_2la : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_2la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_2la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_2lb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_2lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_2lb).
Qed.
End INST.
End SpineMallocSec5JLW2.

(* [comment removed for export] *)
Module SpineMallocSec5JW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_2ha : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_2ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_2ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_2hb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_2hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_2hb).
Qed.
End INST.
End SpineMallocSec5JW2.

(* [comment removed for export] *)
Module SpineMallocSec6I.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "F_B"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6I.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "E6a"; "E6b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I"; "C5ac"; "C5bc"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S143SbSbG0Lb;La;M1Lop;M2G2S144G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S13S2VF;A1A1S125S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS142S14S134A1S14S133A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Definition C5Ba : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13bA2Sb6A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma HC5Ba_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13bA2Sb8A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ba)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb6S22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb6S22S3A1M0A3S23S3SecG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Ba : option (list leafA) := Eval vm_compute in (runT6 C5Ba).
Lemma run6Ba__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb8S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ba]). Qed.
Definition Y6Ba : axst := Eval vm_compute in (leafS 0 run6Ba).
Lemma Cert6Ba_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb8S22S3A1M0A3S23S3SeeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ba] [Y6Ba] [run6Ba]); [exact run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SecSa0Sf4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S12dSf4VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Ba : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ba) (ax_S E6a)).
Lemma E6Ba_0 : ltac2:(tb__ "0|0|
S0S21S8SeeSa0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ba_0 : ltac2:(tb__ "0|0|
S0S21S12dSf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7cA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S127S7cS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S82S3cSd6A3S2aG0Sc2A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11fS82S3cSd6Sc2S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd6S3cS126S82Sc2A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SccA1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSccSfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition U7a : axst := Eval vm_compute in (U7p nx0 D6a).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S92A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa6A1S2S92A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa6S2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S92S22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S92S22S3A1M0A3S23S3SacG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SacA1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2SacA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S6SacS2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7eA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S127S7eS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa2A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa2A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSa2U1A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbaA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9eA2Li;S4eS9eA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9eA1A3Li;S3aU0S9eA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S72SbaA1SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbcA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S139SbcU1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8aS3cSd8A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11fS8aS3cSd8Sc4S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd8S3cS126S8aSc4A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SceA1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSceSfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition U8a : axst := Eval vm_compute in (U8p nx0 D7a).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S94A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa8A1S2S94A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa8S2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S94S22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S94S22S3A1M0A3S23S3SaeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaeA1S2S80A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S6SaeS2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S80A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S127S80S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S84S131SdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11fS84S131SdaSc6S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S121SdaS131S12aS84Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd0A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd0SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition U9a : axst := Eval vm_compute in (U9p nx0 D8a).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S96A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaaA1S2S96A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S6SaaS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S96S22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S96S22S3A1M0A3S23S3Se4S23S3S90G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S90A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S90A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S127S90S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa4S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa4S22S3A1M0A3S23S3Se6G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe4Sf0S11Z1800A1A3Se8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe8S2eSf0A1S11Z2800A1A3S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8cS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8cS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S121SdcS3cS126S8cSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8cA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd2A1A1A1SfS2S8cA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8cA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd2SfS2S8cA1A1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbeS22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbeS22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S74A1A1S41U0S2cA2A2S26SaS3fVW;S86A2S26SaS136S54S2fS98Sf8SfcS100S78S114Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S74A1A1A2A2Li;S41U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S2cA2A3Li;S3aG0S2bSaS13S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S98A3S1S30SdS55S98A3S1S30SdS56S98A3S1S30SdS5aS98A3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S98A3S30SdS57S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S78A3S1S30SdS5fS78A3S1S30SdS60S78A3S1S30SdS5cS78A3S1S30SdS5dS78A3S1S30SdS5bS2fA1S78A3S1S30SdS63S78A3S1S30SdS64Sb2A1S78A3S1S30SdS62S78A3S30SdS61S78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb2A2S13fSb2Z100A2A2S13dS140Sb2Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S74A1S26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S74S40VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S74A1S40VW;S86S2fA3M4A2S43S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S74S40VW;S86S2fA3S2fA3S11cS11bVW;Vst;A3Se0A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe0S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe0S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe6Sf2S11Z1800A1A3SeaA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSeaS2eSf2A1S11Z2800A1A3S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8eS3cSdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8eS3cSdeScaS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S121SdeS3cS126S8eScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8eA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd4A1A1A1SfS2S8eA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8eA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd4SfS2S8eA1A1A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc0S22S3A1A3A4S23G0S112S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc0S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S76A1A1S41U0S20A2A2S26SaS3fVW;S88A2S26SaS136S54S2fS9aSfaSfeS102S7aS116Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S76A1A1A2A2Li;S41U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S20A2A3Li;S3aG0S2bSaS13S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9aA3S1S30SdS55S9aA3S1S30SdS56S9aA3S1S30SdS5aS9aA3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S9aA3S30SdS57S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60S7aA3S1S30SdS5cS7aA3S1S30SdS5dS7aA3S1S30SdS5bS2fA1S7aA3S1S30SdS63S7aA3S1S30SdS64Sb4A1S7aA3S1S30SdS62S7aA3S30SdS61S7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb4A2S13fSb4Z100A2A2S13dS140Sb4Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S76A1S26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S76S40VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S76A1S40VW;S88S2fA3M4A2S43S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S76S40VW;S88S2fA3S2fA3S11cS11bVW;Vst;A3Se2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe2S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe2S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS142S14S134A1S14S133A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Definition C5Bb : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13cA2Sb7A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma HC5Bb_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13cA2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Bb)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb7S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb7S22S3A1M0A3S23S3SedG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Bb : option (list leafA) := Eval vm_compute in (runT6 C5Bb).
Lemma run6Bb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb9S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Bb]). Qed.
Definition Y6Bb : axst := Eval vm_compute in (leafS 0 run6Bb).
Lemma Cert6Bb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb9S22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Bb] [Y6Bb] [run6Bb]); [exact run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8SedSa1Sf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S12dSf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Bb : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Bb) (ax_S E6b)).
Lemma E6Bb_0 : ltac2:(tb__ "0|0|
S0S21S8SefSa1Sf7A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Bb_0 : ltac2:(tb__ "0|0|
S0S21S12dSf7VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7dA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S127S7dS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S83S3cSd7A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11fS83S3cSd7Sc3S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd7S3cS126S83Sc3A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScdA1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11eScdSfS2S83A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition U7b : axst := Eval vm_compute in (U7p nx0 D6b).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S93A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa7A1S2S93A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa7S2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S93S22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S93S22S3A1M0A3S23S3SadG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SadA1S2S7fA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S6SadS2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7fA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S127S7fS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa3A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSa3U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbbA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9fA2Li;S4eS9fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9fA1A3Li;S3aU0S9fA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S72SbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbdA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S139SbdU1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8bS3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11fS8bS3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd9S3cS126S8bSc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8bA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScfA1A1A1SfS2S8bA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8bA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11eScfSfS2S8bA1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition U8b : axst := Eval vm_compute in (U8p nx0 D7b).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S95A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa9A1S2S95A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa9S2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S95S22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S95S22S3A1M0A3S23S3SafG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SafA1S2S81A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S81A1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S6SafS2S81A1A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S81A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S81A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S127S81S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S85A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S85A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S85S131SdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11fS85S131SdbSc7S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S121SdbS131S12aS85Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S85A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd1A1A1A1SfS2S85A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S85A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSd1SfS2S85A1A1A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition U9b : axst := Eval vm_compute in (U9p nx0 D8b).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SabA1S2S97A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2SabA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S6SabS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S97S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S97S22S3A1M0A3S23S3Se5S23S3S91G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S91A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S91A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S91A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S127S91S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa5A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa5S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa5S22S3A1M0A3S23S3Se7G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe5Sf1S11Z1800A1A3Se9A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe9S2eSf1A1S11Z2800A1A3S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8dS3cSddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8dS3cSddSc9S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S121SddS3cS126S8dSc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8dA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd3A1A1A1SfS2S8dA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8dA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd3SfS2S8dA1A1A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbfS22S3A1A3A4S23G0S111S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbfS22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S75A1A1S41U0S2cA2A2S26SaS3fVW;S87A2S26SaS136S54S2fS99Sf9SfdS101S79S115Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S75A1A1A2A2Li;S41U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S2cA2A3Li;S3aG0S2bSaS13S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S99A3S1S30SdS55S99A3S1S30SdS56S99A3S1S30SdS5aS99A3S1S30SdS58S14S133A1A1S99A3S30SdS57S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S79A3S1S30SdS5fS79A3S1S30SdS60S79A3S1S30SdS5cS79A3S1S30SdS5dS79A3S1S30SdS5bS2fA1S79A3S1S30SdS63S79A3S1S30SdS64Sb3A1S79A3S1S30SdS62S79A3S30SdS61S79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb3A2S13fSb3Z100A2A2S13dS140Sb3Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S75A1S26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S75S40VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S75A1S40VW;S87S2fA3M4A2S43S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S75S40VW;S87S2fA3S2fA3S11cS11bVW;Vst;A3Se1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe1S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe1S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe7Sf3S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSebS2eSf3A1S11Z2800A1A3S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8fS3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8fS3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S121SdfS3cS126S8fScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8fA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd5A1A1A1SfS2S8fA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8fA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd5SfS2S8fA1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S113S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S77G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S77A1A1S41U0S20A2A2S26SaS3fVW;S89A2S26SaS136S54S2fS9bSfbSffS103S7bS117Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S77A1A1A2A2Li;S41U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S20A2A3Li;S3aG0S2bSaS13S2S77A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S77A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S77A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9bA3S1S30SdS55S9bA3S1S30SdS56S9bA3S1S30SdS5aS9bA3S1S30SdS58S14S133A1A1S9bA3S30SdS57S9bA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7bA3S1S30SdS5fS7bA3S1S30SdS60S7bA3S1S30SdS5cS7bA3S1S30SdS5dS7bA3S1S30SdS5bS2fA1S7bA3S1S30SdS63S7bA3S1S30SdS64Sb5A1S7bA3S1S30SdS62S7bA3S30SdS61S7bA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb5A2S13fSb5Z100A2A2S13dS140Sb5Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S77A1S26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S89S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S77S40VW;S89S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S77A1S40VW;S89S2fA3M4A2S43S77G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S77A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S77S40VW;S89S2fA3S2fA3S11cS11bVW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe3S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe3S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6I.

(* [comment removed for export] *)
Module SpineMallocSec6IL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "ax_X"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "ss_objs"; "sprop_below"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "omrg"; "oreb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S144SbSbG0Lb;La;M1Lop;M2G2S145G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S12S2VF;A1A1S122S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS143S14S135A1S14S134A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S140A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S140A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S140A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbbS22S3A1A3A4S23G0S103S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbbS22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SefSafSf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S132Sf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S5SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7bA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7bA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S124S7bS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS81S3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11cS81S3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd9S3cS123S81Sc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S81A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2ScfA1A1A1SfS2S81A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S81A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11bScfSfS2S81A1A1A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa5A1S2S8bA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa5A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa5S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa5A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8bA1S2S97A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S5S8bS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S97S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S97S22S3A1M0A3S23S3Sb1G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7dA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S124S7dS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SabA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SabA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13bSabU1A2SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbdA1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa3A2Li;S4bSa3A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa3A1A3Li;S3aU0Sa3A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6eSbdA1SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2SbfA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSbfU1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS89S3cSdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11cS89S3cSdbSc7S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSdbS3cS123S89Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S89A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd1A1A1A1SfS2S89A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S89A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd1SfS2S89A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa7A1S2S8dA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa7S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa7A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S99A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8dA1S2S99A1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S99A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S5S8dS2S99A1A2S99A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S99S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S99S22S3A1M0A3S23S3Sb3G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb3A1S2S7fA1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2Sb3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb3S2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7fA1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S124S7fS16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS83S130SddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11cS83S130SddSc9S39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSddS130S127S83Sc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd3A1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd3SfS2S83A1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa9A1S2S8fA1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8fA1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa9S2S8fA1A2S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa9A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8fA1S2S9bA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9bA1A1SeS2S8fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S5S8fS2S9bA1A2S9bA3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9bS22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9bS22S3A1M0A3S23S3Se7S23S3S95G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S95A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S95A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S95A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S124S95S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SadA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SadA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SadS22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SadS22S3A1M0A3S23S3Se9G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S49Se7Sf1S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S49SebS2eSf1A1S11Z2800A1A3S91A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS91S3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11cS91S3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSdfS3cS123S91ScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S91A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd5A1A1A1SfS2S91A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S91A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd5SfS2S91A1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S73G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S73A1A1S42U0S2cA2A2S26SaS40VW;S85A2S26SaS137S50S2fS9dSf7SfbSffS77S111Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S73A1A1A2A2Li;S42U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S2cA2A3Li;S3aG0S2bSaS12S2S73A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S73A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9dA3S1S30SdS51S9dA3S1S30SdS52S9dA3S1S30SdS56S9dA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9dA3S30SdS53S9dA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S77A3S1S30SdS5bS77A3S1S30SdS5cS77A3S1S30SdS58S77A3S1S30SdS59S77A3S1S30SdS57S2fA1S77A3S1S30SdS5fS77A3S1S30SdS60Sb7A1S77A3S1S30SdS5eS77A3S30SdS5dS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb7A2S13eSb7Z100A2A2S13cS13fSb7Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S73A1S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S73S41VW;S85S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S73A1S41VW;S85S2fA3M4A2S44S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S73A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S73S41VW;S85S2fA3S2fA3S119S118VW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S132Se3S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS133Se3S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S49Se9Sf3S11Z1800A1A3SedA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S49SedS2eSf3A1S11Z2800A1A3S93A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS93S3cSe1A3S2aG0ScdA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11cS93S3cSe1ScdS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSe1S3cS123S93ScdA5Sd7A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S93A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd7A1A1A1SfS2S93A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S93A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd7SfS2S93A1A1A2Sc3A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc3S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc3S22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S75A1A1S42U0S20A2A2S26SaS40VW;S87A2S26SaS137S50S2fS9fSf9SfdS101S79S113Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S75A1A1A2A2Li;S42U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S20A2A3Li;S3aG0S2bSaS12S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9fA3S1S30SdS51S9fA3S1S30SdS52S9fA3S1S30SdS56S9fA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9fA3S30SdS53S9fA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S79A3S1S30SdS5bS79A3S1S30SdS5cS79A3S1S30SdS58S79A3S1S30SdS59S79A3S1S30SdS57S2fA1S79A3S1S30SdS5fS79A3S1S30SdS60Sb9A1S79A3S1S30SdS5eS79A3S30SdS5dS79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb9A2S13eSb9Z100A2A2S13cS13fSb9Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S75A1S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S75S41VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S75A1S41VW;S87S2fA3M4A2S44S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S75S41VW;S87S2fA3S2fA3S119S118VW;Vst;A3Se5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S132Se5S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS133Se5S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS143S14S135A1S14S134A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S141A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S141A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S141A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbcS22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbcS22S3A1M0A3S23S3Sf0G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8Sf0Sb0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S132Sf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7cA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S124S7cS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS82S3cSdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11cS82S3cSdaSc6S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdaS3cS123S82Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd0A1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd0SfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa6A1S2S8cA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa6S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa6A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S98A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8cA1S2S98A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S98A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S5S8cS2S98A1A2S98A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S98S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S98S22S3A1M0A3S23S3Sb2G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb2A1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7eA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S124S7eS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SacA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SacA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13bSacU1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbeA1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa4A2Li;S4bSa4A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa4A1A3Li;S3aU0Sa4A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6eSbeA1Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2Sc0A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSc0U1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS8aS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11cS8aS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdcS3cS123S8aSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd2A1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd2SfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa8A1S2S8eA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa8S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa8A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9aA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8eA1S2S9aA1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9aA1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S5S8eS2S9aA1A2S9aA3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S9aS22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S9aS22S3A1M0A3S23S3Sb4G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb4A1S2S80A1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2Sb4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb4S2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S80A1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S124S80S16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS84S130SdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11cS84S130SdeScaS39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdeS130S127S84ScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd4A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd4SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S90A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SaaA1S2S90A1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S90A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S5SaaS2S90A1A2S90A3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2SaaA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S90A1S2S9cA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9cA1A1SeS2S90A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S5S90S2S9cA1A2S9cA3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9cS22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9cS22S3A1M0A3S23S3Se8S23S3S96G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S96A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S96A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S96A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S124S96S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SaeA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SaeA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SaeS22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SaeS22S3A1M0A3S23S3SeaG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S49Se8Sf2S11Z1800A1A3SecA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S49SecS2eSf2A1S11Z2800A1A3S92A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS92S3cSe0A3S2aG0SccA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11cS92S3cSe0SccS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe0S3cS123S92SccA5Sd6A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S92A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd6A1A1A1SfS2S92A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S92A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd6SfS2S92A1A1A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc2S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc2S22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S74A1A1S42U0S2cA2A2S26SaS40VW;S86A2S26SaS137S50S2fS9eSf8SfcS100S78S112Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S74A1A1A2A2Li;S42U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S2cA2A3Li;S3aG0S2bSaS12S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9eA3S1S30SdS51S9eA3S1S30SdS52S9eA3S1S30SdS56S9eA3S1S30SdS54S14S134A1A1S9eA3S30SdS53S9eA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S78A3S1S30SdS5bS78A3S1S30SdS5cS78A3S1S30SdS58S78A3S1S30SdS59S78A3S1S30SdS57S2fA1S78A3S1S30SdS5fS78A3S1S30SdS60Sb8A1S78A3S1S30SdS5eS78A3S30SdS5dS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb8A2S13eSb8Z100A2A2S13cS13fSb8Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S74A1S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S74S41VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S74A1S41VW;S86S2fA3M4A2S44S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S74S41VW;S86S2fA3S2fA3S119S118VW;Vst;A3Se4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S132Se4S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS133Se4S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeaSf4S11Z1800A1A3SeeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeeS2eSf4A1S11Z2800A1A3S94A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS94S3cSe2A3S2aG0SceA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11cS94S3cSe2SceS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe2S3cS123S94SceA5Sd8A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S94A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd8A1A1A1SfS2S94A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S94A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd8SfS2S94A1A1A2Sc4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc4S22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc4S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S76A1A1S42U0S20A2A2S26SaS40VW;S88A2S26SaS137S50S2fSa0SfaSfeS102S7aS114Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S76A1A1A2A2Li;S42U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S20A2A3Li;S3aG0S2bSaS12S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS55Sa0A3S1S30SdS51Sa0A3S1S30SdS52Sa0A3S1S30SdS56Sa0A3S1S30SdS54S14S134A1A1Sa0A3S30SdS53Sa0A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S7aA3S1S30SdS5bS7aA3S1S30SdS5cS7aA3S1S30SdS58S7aA3S1S30SdS59S7aA3S1S30SdS57S2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60SbaA1S7aA3S1S30SdS5eS7aA3S30SdS5dS7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0SbaA2S13eSbaZ100A2A2S13cS13fSbaZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S76A1S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S76S41VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S76A1S41VW;S88S2fA3M4A2S44S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S76S41VW;S88S2fA3S2fA3S119S118VW;Vst;A3Se6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S132Se6S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS133Se6S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6IL.

