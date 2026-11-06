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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp F0A_drain.

(* [comment removed for export] *)
Module SpineCallocSec3IEL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1.
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
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1bA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1cSfS11S1aA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1bZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S1fG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1cSfS11S1aA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S20G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S22VW;Vst;A2S26R6A1S29S4S12G0R5A2S21S12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S21S12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U0M4Vst;S1dS19R1LX;M5RdRcR4RaA8S1eR3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1dG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 0%nat) (st := st) (tmax := tmax) (hi := false) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [hw_discharge | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineCallocSec3IEL.

(* [comment removed for export] *)
Module F0A_hbN_stepU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "rm"; "valuation"; "holds"; "sprop"; "ss_objs"; "agree_below"; "eval"; "rw"; "ss_facts"; "@Corelib.Init.Datatypes"; "nat"; "list"; "pair"; "prod"; "length"; "app"; "bool"; "option"; "true"; "@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dspec"; "dobj"; "keepN"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "in_zoneW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "s_C"; "s_bs"; "s_Cd"; "s_F"; "s_M"; "s_N"; "s_T"; "s_ZDn"; "s_ZDo"; "s_k"; "s_okU"; "strans"; "unk_ok"; "uobj"; "@Stdlib.Lists.List"; "Forall2"; "In"; "combine"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step"; "ro_condW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "carve_okq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegQS_lib F0A_zones F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section StepUW.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HST : ltac2:(tb__ "0|0|
S28S5S2dVJ;A3").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S45S5VZn;VTZ;VJ;A4").
Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S11S11S3dS11R2VZU;A3M0G0S3S1S11R4R3A3A1S4S23S22Vzb;R5A1M1Vzhi;R5A1A2S22Vzb;R4A1M2Vzlo;R4A1A2A2S23S22G2Vzhi;R4A1A2S22G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_stepUW : ltac2:(tb__ "0|8|
S39S14S14S7S7A2S7A2S24S12S1fA1S12S3fQ40A1M0A1M1S9G1S12S42A1M2S40S41S1S17S38RaR9R8A3S19A3S1S12S6A1ScS29S2eRbA1M3A1A1S16S6S21G3S37RbA1A2S1cS1fS6S20R8A4A3A3S1S11S15G0R8A2S15S1aS2fRcA1A2A3S27S5VJWn;S2eRdA1R8R7S13G2S25R6S26R5R4A2A4A6S1bS1fS46VTZ;R9A2RbA3S43RaS1cS1fS6S20RcA4S44R6R9R7A3A3S9S47R1S3eS1aG0S2fR10A1RcA4A2S9S1S1eS1dS5S8R2A1A2S1dS5S8RcA1A2A3VJWn;R2RcRbR9A4S0S3aR3R12A2S0S1bS2bS48R3A1S33R13A1M4A3S0S2aR3Vzb;Vzlo;Vzhi;VZU;S3bR12A1R11A7S0S3cS6S24S2aR3Vzb;Vzlo;Vzhi;VZU;A5M5S1cS2bS6S2cG4A4S35R13A1A5S0S3cS6S24G5ScS29S30R13A1A1M6A1S36R13A1A5S1bSbSaR3A1S10G6A1A3S1bSbSaR4A1S31R14A1A3F_;A2A2A2A2A2F_;F_;S2S9S9S0S27S5VJWn;S34R13A1R1RdS13G2S25RcS26RbRaA2A4A6S0S1aS7S3dS14S1aS7A2S13S1aS7R2R1A4S32R15A1A3S1G0SfR4R3A2SeR6R2A2A3F_;Fe;Fv;S0S1G0S18S3fQ8A1A1F_;S8R1A1S8R4A1M7A3S0SdS2dR3R1A3S1S1eS1dS5G7A2S1dS5S8ReA1A2A3A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fvals;FdsD;Fzdu;Fu;Ft;").
Proof.
  intros t u zdu dsD vals rho tp tr ms md HOK HOBJ HLEN HS HDC rho3 rho4 HCONT.
  pose proof (JW_stable segsA NPRE Zn TZ J HST) as HSTW. fold JWn in HSTW.
  unfold s_okU in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (zdisjb zdu) _ = true |- _ => rename H into OKZU end.
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf (with_objs _ [uobj u]) = true |- _ => rename H into OKSWF1 end.
  match goal with H : swf (with_objs _ (map carve_obj _)) = true |- _ => rename H into OKSWF2 end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolveW Zn TZ J (s_C t) (keepN (s_C t) (s_k t)) dsD rho tp tr ms md HOBJ HS HDC) as (H1 & RW3 & RL3 & EV).
  fold rho3 in H1, RW3, RL3, EV. change (SPA segsA JWn (s_Cd t) rho3 tp (tr, mkCfg ms md)) in H1.
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA JWn (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HSTW); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  destruct (HCONT EV (proj2 H2)) as (UOK & CC & ZUo & ZN & ZO & HFN).
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  destruct u as [[ub ulo] uhi]. cbn [uobj unk_ok] in *. destruct UOK as (U1 & U2 & U3 & U4 & U5).
  assert (H2u : SPA segsA JWn (s_Cu t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_unk segsA JWn rho4 (s_Cd t) tp (tr, mkCfg ms md) ub ulo uhi (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF1.
    - apply Pos.le_refl.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact U4.
    - pose proof (zonesW_cross rho4 zb zlo zhi ZU Hsep [mkObj ub ulo uhi [] DUnknown] [zdu] _ _ (Forall2_cons _ _ ZUo (Forall2_nil _)) ZO ltac:(cbn [forallb]; rewrite OKZU; reflexivity)) as ZC.
      apply Forall_cons_iff in ZC as [ZC _]. exact ZC.
    - exact U5.
    - assert (HXd : ax_X (s_Cd t) = []) by exact HX. intros rr y j Hin. rewrite HXd in Hin. destruct Hin. }
  assert (H3 : SPA segsA JWn (s_CaU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA JWn rho4 (s_Cu t (ub, ulo, uhi)) tp _ (s_N t) (ss_next (ax_S (s_Cu t (ub, ulo, uhi)))) H2u) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF2.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - apply (zonesW_cross rho4 zb zlo zhi ZU Hsep _ _ (ss_objs (ax_S (s_Cd t)) ++ [mkObj ub ulo uhi [] DUnknown]) (s_ZDo t ++ [zdu]) ZN); [|exact OKZX]. apply Forall2_app; [exact ZO | exact (Forall2_cons _ _ ZUo (Forall2_nil _))].
    - exact (zonesW_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA JWn (s_CcU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { unfold s_CcU, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA JWn _ (s_T t) (s_M t) rho4 tp _ OKENT HSTW H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End StepUW.
End F0A_hbN_stepU.

(* [comment removed for export] *)
Module F0A_masm.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "junkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_live"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "cons"; "fst"; "nat"; "nil"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "set_inited"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_free"; "L_free"; "UStopLe"; "Wcan"; "KcA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull"; "rt_zone2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rho_sets_id : ltac2:(tb__ "0|2|
S12S14S1SfQ40A1M0A2M1A1S2S30G1G1S5G0S3R2S16S1G0R1A3A2S1aS1G0R1A3A3Liv;R2A3S5S2S33R2R3A2R2A3F_;Frho;Fl;").
Proof.
  induction l as [|[i v] t IH]; intros rho HF; [reflexivity|]. cbn [rho_sets].
  pose proof (Forall_inv HF) as H1. pose proof (Forall_inv_tail HF) as H2. cbn [fst snd] in H1.
  assert (E : rho_set_rw rho i v = rho).
  { destruct rho as [w l0 m]. unfold rho_set_rw. cbn [rw rl rm] in *. f_equal. apply functional_extensionality. intros j.
    destruct (Pos.eqb_spec j i) as [->|NE]; [symmetry; exact H1 | reflexivity]. }
  rewrite E. apply IH. exact H2.
Qed.

Lemma rhoF_of_id : ltac2:(tb__ "0|0|
ScS2S2S0S0S0SbS27S9SaR7R6R4R3R2R1A6R5A3S5S2SaS20R8A1R6R5R4R3R2A6R6A3F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv [Hw _]. unfold rhoF_of at 1. apply rho_sets_id.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite <- Hw by (unfold GW; lia); reflexivity).
Qed.

Lemma mid_link_pn : ltac2:(tb__ "0|3|
ScS2S2S0S0S0SbS29R7SaR7R6R4R3R2R1A6R5A3S6S5S0S10Q40M0S3R6PcM1A2A2S10G0S3R7G1A2A2A3S5S0S10G0S3R6PdM2A2A2S10G0S3R7G2A2A2A3A2F_;Fjv;Ft;Fn;Fp;Frho2;Frho;FA;").
Proof.
  intros A rho rho2 p n t jv ([Hw _] & _). split; [rewrite <- (Hw 12%positive) by (unfold GW; lia) | rewrite <- (Hw 13%positive) by (unfold GW; lia)]; reflexivity.
Qed.

Section MASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S0S34VCST;R1A2S6S7S6S23S21R2A2S24R2S22A2A2A1S7S6S23Z180e88R2A2S24R2Z180e8cA2A2A1A2F_;Fa;").

Lemma tjv_ok_mid : ltac2:(tb__ "0|0|
ScS2S2S12SfQ40A1A1S26S0S0S0SbS1fS8R9R8R6R5A5S35S14S0S0A2S13S0S0R5R4A4SeRaA1A3S29RbSaRbRaR6R5R4R3A6R9A3S28RcRbR7R6R5R4A6S28S20RdA1RbR8R7R6R5A6F_;F_;F_;F_;Fjv;Ft;Fn;Fp;Fmd;Ftp;Frho2;Frho0;FA;").
Proof.
  intros A rho0 rho2 tp md p n t jv HA HL (_ & VQ & _) ((T1 & T2 & T3 & T4) & (J1 & J2 & J3 & J4 & C1 & C2 & C3)).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (Hsep & _). destruct (Hsep p n HL) as (S1 & S2 & _). unfold IMG_HI in S2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  assert (Erm : rm (rhoF_of A rho0 p n t jv) = rm rho0) by reflexivity. rewrite Erm in VQ.
  assert (X : forall c, (forall k, (k < c_w c)%nat -> ~ ia_zone (c_addr c + Z.of_nat k)) -> cell_ok (view segsA (rm rho0)) c -> cell_ok (view segsA (rm rho2)) c).
  { intros c Hc Hok. eapply cell_ok_agree; [|exact Hok]. intros k Hk. apply VQ. exact (Hc k Hk). }
  unfold tjv_ok. change (aa_geom (set_inited A)) with (aa_geom A). change (aa_q_thread (set_inited A)) with (aa_q_thread A).
  split; [split; [exact T1|]; split; [exact T2|]; split|].
  - apply X; [|exact T3]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - apply X; [|exact T4]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
  - split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [|split].
    + apply X; [|exact C1]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END, QG. lia.
    + apply X; [|exact C2]. cbn [c_addr c_w]. intros k Hk. unfold ia_zone, IA_BEG, IA_END. lia.
    + intros HE. destruct (C3 HE) as [C3a C3b]. split; (apply X; [|assumption]); cbn [c_addr c_w]; intros k Hk; unfold ia_zone, IA_BEG, IA_END; lia.
Qed.

Lemma post_mid : ltac2:(tb__ "0|6|
S17ScS2fS2S2S12SfQ40M0A1A1M1G1S26S31S1fS8R8R6R3R2A5S27S1bR7R6A3S0S6S23Z0R1A2S24R1S25Z2Z40A2A2A2S7S32SdRcA1R2A2A1S5S19SfQ8A1A1S4RaS11G0R3A2M2A2S4RbG2A2A3F_;F_;Fa;S1eS8S1bR8R7S15S14S1cS1dA2M3S13S1cS1dS2cS2aS2eRcA1S2dA3S2bS1fS8A1M4VCST;VXGL;S20RbA1RaA5A4S18G3A1M5A3R4A6S1eS8S1bRaR8S15G3S13S1cS1dS2cS2aS2eRdA1S2dA3S2bG4VCST;VXGL;RcRbA5A4G5A3R5A6F_;F_;F_;F_;Fw;Fmd0;Ftp0;Ftp;Frho2;Frho0;FKc;FA;FnW;").
Proof.
  intros nW A Kc rho0 rho2 tp tp0 md0 w HA0 [AGw AGl] RMO (L & JL & rho' & tp' & Hin & [Hw' Hl'] & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-.
  pose proof HA0 as (HG & _ & HF & HRest & _). pose proof (proj1 HRest) as Hsep.
  exists (L_free AE_A (Wcan nW) UStopLe), (JL_free (AInvA segsA) CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [split; [intros i Hi; rewrite (AGw i Hi); exact (Hw' i Hi) | intros l; rewrite (AGl l); exact (Hl' l)]|]. split; [exact Hsm|].
  destruct HJL as (A' & l1 & l2 & HA' & ELV & ELV' & EF & EV & EKm & EKf & EG & MK & HKc & CK).
  exists A', l1, l2. split; [exact HA'|].
  split; [rewrite (AGw 12%positive) by (unfold NF; lia); rewrite (AGw 13%positive) by (unfold NF; lia); exact ELV|].
  split; [exact ELV'|]. split; [exact EF|]. split; [exact EV|]. split; [exact EKm|]. split; [exact EKf|]. split; [exact EG|].
  split; [|split; [exact HKc | exact CK]].
  destruct MK as [MK1 MK2]. change (client_addrA CST (set_inited A)) with (client_addrA CST A) in MK1, MK2.
  change (client_shadowA CST XGL (set_inited A)) with (client_shadowA CST XGL A) in MK1.
  split.
  - intros a Ba Hcl.
    assert (NZ : ~ rt_zone2 (aa_geom A) a).
    { destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt2 CST HCST HCST2 A a _ HG HF Hsep C1)|].
      pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B. exact (shadow_not_rt2 A a HG B). }
    rewrite <- (RMO a Ba NZ). apply MK1; [exact Ba|].
    destruct Hcl as [H1|(H1 & H2 & H3)]; [left; exact H1 | right; split; [exact H1|]; split; [exact H2|]; rewrite (RMO a Ba NZ); exact H3].
  - intros x j Hx Hj Hdef. apply (MK2 x j Hx Hj).
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. rewrite RMO; [exact Hdef | lia |].
    apply (shadow_not_rt2 A _ HG). lia.
Qed.
End MASM.
End F0A_masm.

(* [comment removed for export] *)
Module F0A_qL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_qL0Be"; "Cd_L0Be"; "XMd_L0Be"; "RQ_L0Be"; "XR2_L0Be"; "sQ_L0Be"; "RESTd_L0Be"; "TQ_L0Be"; "TQr_L0Be"; "XKd_L0Be"; "XM2_L0Be"; "KEPTd_L0Be"; "Xf2_L0Be"; "run7_L0Be"; "run7r_L0Be"; "nkd_L0Be"; "sX2_L0Be"; "Edr_nf_L0Be"; "XEX2_L0Be"; "XEXd_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBe"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L0Be : axst := Eval vm_compute in Edr_L0Be.
Lemma Edr_eq_L0Be : Edr_L0Be = Edr_nf_L0Be. Proof. vm_cast_no_check (eq_refl Edr_nf_L0Be). Qed.

Definition XEXd_L0Be : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L0Be))].
Definition XMd_L0Be : axst := Eval vm_compute in (axf Edr_nf_L0Be XEXd_L0Be).
Lemma AXEd_L0Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L0Be)). Qed.
Definition nkd_L0Be : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L0Be) + 0 + 2)%nat.
Definition KEPTd_L0Be : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L0Be : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L0Be : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L0Be : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L0Be : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L0Be : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L0Be : rcivb RESTd_L0Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L0Be : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L0Be : rwrb RESTd_L0Be = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L0Be : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L0Be : axst := Eval vm_compute in (ax_with_facts XKd_L0Be (ss_facts (ax_S XKd_L0Be) ++ [F_cne])).
Lemma ECd_L0Be : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L0Be). Qed.
Lemma FBCd_L0Be : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L0Be : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L0Be) (ax_S PreQ3)).
Definition RQ_L0Be : list sobj := Eval vm_compute in (optR (entails_frA Cd_L0Be PreQ3 sQ_L0Be)).
Lemma HEQ_L0Be : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L0Be)). Qed.
Lemma HCK_L0Be : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L0Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0Be PreQ3 PostQ3 Cd_L0Be RQ_L0Be) (ss_facts (ax_S Cd_L0Be))).
Lemma HTQ_L0Be : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L0Be). Qed.
Lemma QCHK_L0Be : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L0Be : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0Be PreQ3 PostQ3r Cd_L0Be RQ_L0Be) (ss_facts (ax_S Cd_L0Be))).
Lemma HTQr_L0Be : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L0Be). Qed.
Lemma QCHKr_L0Be : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L0Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L0Be).
Lemma RUN7_L0Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L0Be). Qed.
Definition Xf2_L0Be : axst := Eval vm_compute in (leaf 0 run7_L0Be).
Lemma L7_L0Be : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0Be)]. Qed.
Lemma NX7_L0Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L0Be : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L0Be).
Lemma RUN7r_L0Be : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L0Be). Qed.
Lemma L7r_L0Be : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0Be)]. Qed.
Lemma NX7r_L0Be : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L0Be : list axform := Eval vm_compute in (XEX_of Xf2_L0Be).
Definition XM2_L0Be : axst := Eval vm_compute in (axf Xf2_L0Be XEX2_L0Be).
Lemma AXE2_L0Be : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L0Be)). Qed.
Definition XR2_L0Be : axst := Eval vm_compute in (XR_of XM2_L0Be).
Definition sX2_L0Be : wsub := Eval vm_compute in (sX_of XR2_L0Be (Wcan 0) UStopLe).
Lemma WXR2_L0Be : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L0Be : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L0Be : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L0Be))). Qed.
Lemma EQR2_L0Be : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L0Be). Qed.
Lemma ENT2_L0Be : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L0Be : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L0Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L0Be (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L0Be : drain_stmt_L0Be Edr_L0Be.
Proof.
  rewrite Edr_eq_L0Be.
  exact (f0_drain 0%nat QBe CST XGL HCST HXGL HCSTQ Cd_L0Be TQ_L0Be TQr_L0Be sQ_L0Be RQ_L0Be HEQ_L0Be HCK_L0Be HTQ_L0Be HTQr_L0Be QCHK_L0Be QCHKr_L0Be Xf2_L0Be XM2_L0Be XR2_L0Be XEX2_L0Be sX2_L0Be run7_L0Be
           NX7_L0Be RUN7_L0Be L7_L0Be run7r_L0Be NX7r_L0Be RUN7r_L0Be L7r_L0Be AXE2_L0Be WXR2_L0Be DXR2_L0Be NXR2_L0Be EQR2_L0Be ENT2_L0Be SID2_L0Be HCSTF Edr_nf_L0Be XMd_L0Be XKd_L0Be KEPTd_L0Be RESTd_L0Be XEXd_L0Be
           AXEd_L0Be OBJSd_L0Be EQKd_L0Be RCLSd_L0Be RCIVd_L0Be RCELLd_L0Be RWRd_L0Be RSHPd_L0Be ECd_L0Be FBCd_L0Be).
Qed.
Theorem ef0_drain_L0Be : edrain_stmt_L0Be Edr_L0Be.
Proof.
  rewrite Edr_eq_L0Be.
  exact (ef0_drain 0%nat QBe CST XGL HCST HXGL HCSTQ Cd_L0Be TQ_L0Be TQr_L0Be sQ_L0Be RQ_L0Be HEQ_L0Be HCK_L0Be HTQ_L0Be HTQr_L0Be QCHK_L0Be QCHKr_L0Be Xf2_L0Be XM2_L0Be XR2_L0Be XEX2_L0Be sX2_L0Be run7_L0Be
           NX7_L0Be RUN7_L0Be L7_L0Be run7r_L0Be NX7r_L0Be RUN7r_L0Be L7r_L0Be AXE2_L0Be WXR2_L0Be DXR2_L0Be NXR2_L0Be EQR2_L0Be ENT2_L0Be SID2_L0Be HCSTF Edr_nf_L0Be XMd_L0Be XKd_L0Be KEPTd_L0Be RESTd_L0Be XEXd_L0Be
           AXEd_L0Be OBJSd_L0Be EQKd_L0Be RCLSd_L0Be RCIVd_L0Be RCELLd_L0Be RWRd_L0Be RSHPd_L0Be ECd_L0Be FBCd_L0Be).
Qed.
End QL0Be.
End F0A_qL0Be.

(* [comment removed for export] *)
Module F0A_qL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_qL0A"; "Cd_L0A"; "XMd_L0A"; "RQ_L0A"; "XR2_L0A"; "sQ_L0A"; "RESTd_L0A"; "TQ_L0A"; "TQr_L0A"; "XKd_L0A"; "XM2_L0A"; "KEPTd_L0A"; "Xf2_L0A"; "run7_L0A"; "run7r_L0A"; "nkd_L0A"; "sX2_L0A"; "Edr_nf_L0A"; "XEX2_L0A"; "XEXd_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs";
"rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L0A : axst := Eval vm_compute in Edr_L0A.
Lemma Edr_eq_L0A : Edr_L0A = Edr_nf_L0A. Proof. vm_cast_no_check (eq_refl Edr_nf_L0A). Qed.

Definition XEXd_L0A : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L0A))].
Definition XMd_L0A : axst := Eval vm_compute in (axf Edr_nf_L0A XEXd_L0A).
Lemma AXEd_L0A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L0A)). Qed.
Definition nkd_L0A : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L0A) + 0 + 2)%nat.
Definition KEPTd_L0A : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L0A : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L0A : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L0A : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L0A : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L0A : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L0A : rcivb RESTd_L0A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L0A : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L0A : rwrb RESTd_L0A = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L0A : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L0A : axst := Eval vm_compute in (ax_with_facts XKd_L0A (ss_facts (ax_S XKd_L0A) ++ [F_cne])).
Lemma ECd_L0A : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L0A). Qed.
Lemma FBCd_L0A : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L0A : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L0A) (ax_S PreQ3)).
Definition RQ_L0A : list sobj := Eval vm_compute in (optR (entails_frA Cd_L0A PreQ3 sQ_L0A)).
Lemma HEQ_L0A : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L0A)). Qed.
Lemma HCK_L0A : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L0A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0A PreQ3 PostQ3 Cd_L0A RQ_L0A) (ss_facts (ax_S Cd_L0A))).
Lemma HTQ_L0A : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L0A). Qed.
Lemma QCHK_L0A : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L0A : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0A PreQ3 PostQ3r Cd_L0A RQ_L0A) (ss_facts (ax_S Cd_L0A))).
Lemma HTQr_L0A : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L0A). Qed.
Lemma QCHKr_L0A : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L0A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L0A).
Lemma RUN7_L0A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L0A). Qed.
Definition Xf2_L0A : axst := Eval vm_compute in (leaf 0 run7_L0A).
Lemma L7_L0A : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0A)]. Qed.
Lemma NX7_L0A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L0A : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L0A).
Lemma RUN7r_L0A : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L0A). Qed.
Lemma L7r_L0A : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0A)]. Qed.
Lemma NX7r_L0A : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L0A : list axform := Eval vm_compute in (XEX_of Xf2_L0A).
Definition XM2_L0A : axst := Eval vm_compute in (axf Xf2_L0A XEX2_L0A).
Lemma AXE2_L0A : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L0A)). Qed.
Definition XR2_L0A : axst := Eval vm_compute in (XR_of XM2_L0A).
Definition sX2_L0A : wsub := Eval vm_compute in (sX_of XR2_L0A (Wcan 0) UStopLe).
Lemma WXR2_L0A : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L0A : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L0A : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L0A))). Qed.
Lemma EQR2_L0A : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L0A). Qed.
Lemma ENT2_L0A : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L0A : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L0A (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L0A (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L0A : drain_stmt_L0A Edr_L0A.
Proof.
  rewrite Edr_eq_L0A.
  exact (f0_drain 0%nat QA CST XGL HCST HXGL HCSTQ Cd_L0A TQ_L0A TQr_L0A sQ_L0A RQ_L0A HEQ_L0A HCK_L0A HTQ_L0A HTQr_L0A QCHK_L0A QCHKr_L0A Xf2_L0A XM2_L0A XR2_L0A XEX2_L0A sX2_L0A run7_L0A
           NX7_L0A RUN7_L0A L7_L0A run7r_L0A NX7r_L0A RUN7r_L0A L7r_L0A AXE2_L0A WXR2_L0A DXR2_L0A NXR2_L0A EQR2_L0A ENT2_L0A SID2_L0A HCSTF Edr_nf_L0A XMd_L0A XKd_L0A KEPTd_L0A RESTd_L0A XEXd_L0A
           AXEd_L0A OBJSd_L0A EQKd_L0A RCLSd_L0A RCIVd_L0A RCELLd_L0A RWRd_L0A RSHPd_L0A ECd_L0A FBCd_L0A).
Qed.
Theorem ef0_drain_L0A : edrain_stmt_L0A Edr_L0A.
Proof.
  rewrite Edr_eq_L0A.
  exact (ef0_drain 0%nat QA CST XGL HCST HXGL HCSTQ Cd_L0A TQ_L0A TQr_L0A sQ_L0A RQ_L0A HEQ_L0A HCK_L0A HTQ_L0A HTQr_L0A QCHK_L0A QCHKr_L0A Xf2_L0A XM2_L0A XR2_L0A XEX2_L0A sX2_L0A run7_L0A
           NX7_L0A RUN7_L0A L7_L0A run7r_L0A NX7r_L0A RUN7r_L0A L7r_L0A AXE2_L0A WXR2_L0A DXR2_L0A NXR2_L0A EQR2_L0A ENT2_L0A SID2_L0A HCSTF Edr_nf_L0A XMd_L0A XKd_L0A KEPTd_L0A RESTd_L0A XEXd_L0A
           AXEd_L0A OBJSd_L0A EQKd_L0A RCLSd_L0A RCIVd_L0A RCELLd_L0A RWRd_L0A RSHPd_L0A ECd_L0A FBCd_L0A).
Qed.
End QL0A.
End F0A_qL0A.

(* [comment removed for export] *)
Module F0A_qL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "false"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sobj"; "ss_next"; "rw"; "ss_facts"; "sv"; "ss_objs"; "ss_lenient"; "SLit"; "SVar"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_qL0Bf"; "Cd_L0Bf"; "XMd_L0Bf"; "RQ_L0Bf"; "XR2_L0Bf"; "sQ_L0Bf"; "RESTd_L0Bf"; "TQ_L0Bf"; "TQr_L0Bf"; "XKd_L0Bf"; "XM2_L0Bf"; "KEPTd_L0Bf"; "Xf2_L0Bf"; "run7_L0Bf"; "run7r_L0Bf"; "nkd_L0Bf"; "sX2_L0Bf"; "Edr_nf_L0Bf"; "XEX2_L0Bf"; "XEXd_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QBf"; "RETF"; "FUELF"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "L_free"; "Wcan"; "JL_free"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_postA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "budget_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "PreQ3"; "PostQ3"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "F_cne"; "qchkb"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf.
Import ListNotations.
Open Scope Z_scope.

Definition Edr_nf_L0Bf : axst := Eval vm_compute in Edr_L0Bf.
Lemma Edr_eq_L0Bf : Edr_L0Bf = Edr_nf_L0Bf. Proof. vm_cast_no_check (eq_refl Edr_nf_L0Bf). Qed.

Definition XEXd_L0Bf : list axform := Eval vm_compute in [AXSelect (exit_perm (ax_S Edr_nf_L0Bf))].
Definition XMd_L0Bf : axst := Eval vm_compute in (axf Edr_nf_L0Bf XEXd_L0Bf).
Lemma AXEd_L0Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS34S36A2SeS12S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some XMd_L0Bf)). Qed.
Definition nkd_L0Bf : nat := Eval vm_compute in (n_pieces (ax_S Edr_nf_L0Bf) + 0 + 2)%nat.
Definition KEPTd_L0Bf : list sobj := ltac2:(tb__ "0|0|
S6eS19S32S1eS13S25A1A1A3").
Definition RESTd_L0Bf : list sobj := ltac2:(tb__ "0|0|
S6fS19S32S1eS13S25A1A1A3").
Lemma OBJSd_L0Bf : ltac2:(tb__ "0|0|
S0SbS19A1S1eS13S25A1A1S11S19S2eS29A3A3"). Proof. symmetry. apply firstn_skipn. Qed.
Definition XKd_L0Bf : axst := ltac2:(tb__ "0|0|
S14S25S59S13S25A1S2eA2A2").
Lemma EQKd_L0Bf : ltac2:(tb__ "0|0|
S0S12S14S25S59S13S25A1S2eA2A2S2cA3"). Proof. reflexivity. Qed.
Lemma RCLSd_L0Bf : ltac2:(tb__ "0|0|
S0S7S78S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCIVd_L0Bf : rcivb RESTd_L0Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RCELLd_L0Bf : ltac2:(tb__ "0|0|
S0S7S77S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RWRd_L0Bf : rwrb RESTd_L0Bf = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RSHPd_L0Bf : ltac2:(tb__ "0|0|
S0S7S79S37S29A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition Cd_L0Bf : axst := Eval vm_compute in (ax_with_facts XKd_L0Bf (ss_facts (ax_S XKd_L0Bf) ++ [F_cne])).
Lemma ECd_L0Bf : ltac2:(tb__ "0|0|
S0S12S24S56S2cS11S17S1cS13S2cA1A1S9S17S60SaS17A1A3A3A2A3"). Proof. vm_cast_no_check (eq_refl Cd_L0Bf). Qed.
Lemma FBCd_L0Bf : ltac2:(tb__ "0|1|
S0S7S6cS17S22S1aS13S2cA1M0A1A1S11S17S1cG0A1S9S17S60SaS17A1A3A3A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sQ_L0Bf : wsub := Eval vm_compute in ((156%positive, SAlu ALU_ADD (SVar 155) (SLit kSpaceSize)) :: infer_sub 1 (ax_S Cd_L0Bf) (ax_S PreQ3)).
Definition RQ_L0Bf : list sobj := Eval vm_compute in (optR (entails_frA Cd_L0Bf PreQ3 sQ_L0Bf)).
Lemma HEQ_L0Bf : ltac2:(tb__ "0|1|
S0S10SbS19A1M0A1S48S24S51S28A3SeG0S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some RQ_L0Bf)). Qed.
Lemma HCK_L0Bf : ltac2:(tb__ "0|0|
S0S7S47S24S51S28S26S9S12S52S9S12S58SaS12A1A3A3A5S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition TQ_L0Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0Bf PreQ3 PostQ3 Cd_L0Bf RQ_L0Bf) (ss_facts (ax_S Cd_L0Bf))).
Lemma HTQ_L0Bf : ltac2:(tb__ "0|0|
S0S12S2aS56S46S28S51S52S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQ_L0Bf). Qed.
Lemma QCHK_L0Bf : ltac2:(tb__ "0|0|
S0S7S61U0S24S52S2aS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition TQr_L0Bf : axst := Eval vm_compute in (ax_with_facts (import_postA sQ_L0Bf PreQ3 PostQ3r Cd_L0Bf RQ_L0Bf) (ss_facts (ax_S Cd_L0Bf))).
Lemma HTQr_L0Bf : ltac2:(tb__ "0|0|
S0S12S2bS56S46S28S51S58S24S26A5S1cS13S24A1A1A2A3"). Proof. vm_cast_no_check (eq_refl TQr_L0Bf). Qed.
Lemma QCHKr_L0Bf : ltac2:(tb__ "0|0|
S0S7S61U0S24S58S2bS28S26A6S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Definition run7_L0Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQ_L0Bf).
Lemma RUN7_L0Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2aA3S30A3"). Proof. vm_cast_no_check (eq_refl run7_L0Bf). Qed.
Definition Xf2_L0Bf : axst := Eval vm_compute in (leaf 0 run7_L0Bf).
Lemma L7_L0Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS30S9S5S38SaS5A1A3A2S8A3S0S12S68U0S30A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0Bf)]. Qed.
Lemma NX7_L0Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2aA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition run7r_L0Bf : list leafA := Eval vm_compute in (runA FUELF [RETF] TQr_L0Bf).
Lemma RUN7r_L0Bf : ltac2:(tb__ "0|0|
S0SbS15A1S69S39S9S5S38SaS5A1A3S2bA3S31A3"). Proof. vm_cast_no_check (eq_refl run7r_L0Bf). Qed.
Lemma L7r_L0Bf : ltac2:(tb__ "0|0|
S1S0S7S3aS31S9S5S38SaS5A1A3A2S8A3S0S12S68U0S31A2S2fA3A2"). Proof. split; [vm_cast_no_check (eq_refl true) | vm_cast_no_check (eq_refl Xf2_L0Bf)]. Qed.
Lemma NX7r_L0Bf : ltac2:(tb__ "0|1|
S1S0S7S1fS13S2bA1M0A1SfA3S0S7S6dS5eS1aG0A1A2S8A3A2"). Proof. split; [vm_cast_no_check (eq_refl false) | vm_cast_no_check (eq_refl true)]. Qed.
Definition XEX2_L0Bf : list axform := Eval vm_compute in (XEX_of Xf2_L0Bf).
Definition XM2_L0Bf : axst := Eval vm_compute in (axf Xf2_L0Bf XEX2_L0Bf).
Lemma AXE2_L0Bf : ltac2:(tb__ "0|0|
S0S10S12A1S5dS2fS35A2SeS12S2dA2A3"). Proof. vm_cast_no_check (eq_refl (Some XM2_L0Bf)). Qed.
Definition XR2_L0Bf : axst := Eval vm_compute in (XR_of XM2_L0Bf).
Definition sX2_L0Bf : wsub := Eval vm_compute in (sX_of XR2_L0Bf (Wcan 0) UStopLe).
Lemma WXR2_L0Bf : ltac2:(tb__ "0|0|
S0S7S23S13S27A1A1S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DXR2_L0Bf : ltac2:(tb__ "0|4|
S0S10SdSbSdS1dS1dA2M0A1M1SbS17A1M2A2M3A1S73S13S2dA1S13S27A1A2SeG3ScG1G2S9G0ScS1dS1dS20S75A1S21P18A1A4SaG0A1A3SaS17A1A4A2A3"). Proof. vm_cast_no_check (eq_refl (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma NXR2_L0Bf : ltac2:(tb__ "0|0|
S0S6S1aS13S27A1A1S1aS13S2dA1A1A3"). Proof. vm_cast_no_check (eq_refl (ss_next (ax_S XM2_L0Bf))). Qed.
Lemma EQR2_L0Bf : ltac2:(tb__ "0|0|
S0S12S14S2dS13S27A1A2S27A3"). Proof. vm_cast_no_check (eq_refl XR2_L0Bf). Qed.
Lemma ENT2_L0Bf : ltac2:(tb__ "0|0|
S0S7S16S27S3dS3cS3eU0A1S3bA3S33A3S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID2_L0Bf : ltac2:(tb__ "0|0|
S0S7S74S33S55A2S8A3"). Proof. vm_cast_no_check (eq_refl true). Qed.

Section QL0Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S4S7cR2A1A1F_;Fa;").
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S57VCST;R1A2S2S57S76R2A2S1S7dS7aR2A2S7eR2S7bA2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition drain_stmt_L0Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S72OF_;S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S5cVsegs;RbS5bR9A1A3S62RcRaA2S50RcA1S0S5S53G0S1bRbPcA2A2R9A3S0S5S53G0S1bRcPdA2A2R9A3S6bSdS5S5A2ScS5S5RbRaA4S4fRfA1A3S5fRcRbA2S0S7S4eR11A1S8A3S4cS37R12A2S66R11S49R13R11RfReRdRcA6A2S0S5S4aRdA1S67A3S5S2S42VCST;R16R1A3S43VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S4dS18S18G1S65R1aR4A2S6aR13S49R1bR19R17R16R15R14A6R4A3S71Vsegs;R1dS5aVsegs;S64U0M2S3bSfR6R1bR5A6VE;R4R3A5S45Vsegs;S55R1aR19S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1cR1bA5A4SaG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition edrain_stmt_L0Bf (E : axst) : Prop := ltac2:(tb__ "0|4|
S4dS40S18SbS54Q40M0A1A1M1S5S5S5S4bS5OF_;S41R8A1S63R9A1S50RbA1S0S5S53G0S1bRaPcA2A2R8A3S0S5S53G0S1bRbPdA2A2R8A3S6bSdS5S5A2ScS5S5RaR9A4S4fReA1A3S5fRbRaA2S0S7S4eR10A1S8A3S4cS37R11A2S66R10S49R12R10ReRdRcRbA6A2S0S5S4aRcA1S67A3S5S2S42VCST;R15R1A3S43VCST;VXGL;R15R1A4A2ReR2A1F_;Fa;S4dS18S18G1S65R19R4A2S6aR12S49R1aR18R16R15R14R13A6R4A3S70Vsegs;S5aVsegs;S64U0M2S3bSfR6R1aR5A6VE;R4R3A5S45Vsegs;S55R19R18S9SdS12S44A2M3ScS12S44S3dS3cS3eG2A1S3bA3S3fVAInv;VCST;VXGL;R1bR1aA5A4SaG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Theorem f0_drain_L0Bf : drain_stmt_L0Bf Edr_L0Bf.
Proof.
  rewrite Edr_eq_L0Bf.
  exact (f0_drain 0%nat QBf CST XGL HCST HXGL HCSTQ Cd_L0Bf TQ_L0Bf TQr_L0Bf sQ_L0Bf RQ_L0Bf HEQ_L0Bf HCK_L0Bf HTQ_L0Bf HTQr_L0Bf QCHK_L0Bf QCHKr_L0Bf Xf2_L0Bf XM2_L0Bf XR2_L0Bf XEX2_L0Bf sX2_L0Bf run7_L0Bf
           NX7_L0Bf RUN7_L0Bf L7_L0Bf run7r_L0Bf NX7r_L0Bf RUN7r_L0Bf L7r_L0Bf AXE2_L0Bf WXR2_L0Bf DXR2_L0Bf NXR2_L0Bf EQR2_L0Bf ENT2_L0Bf SID2_L0Bf HCSTF Edr_nf_L0Bf XMd_L0Bf XKd_L0Bf KEPTd_L0Bf RESTd_L0Bf XEXd_L0Bf
           AXEd_L0Bf OBJSd_L0Bf EQKd_L0Bf RCLSd_L0Bf RCIVd_L0Bf RCELLd_L0Bf RWRd_L0Bf RSHPd_L0Bf ECd_L0Bf FBCd_L0Bf).
Qed.
Theorem ef0_drain_L0Bf : edrain_stmt_L0Bf Edr_L0Bf.
Proof.
  rewrite Edr_eq_L0Bf.
  exact (ef0_drain 0%nat QBf CST XGL HCST HXGL HCSTQ Cd_L0Bf TQ_L0Bf TQr_L0Bf sQ_L0Bf RQ_L0Bf HEQ_L0Bf HCK_L0Bf HTQ_L0Bf HTQr_L0Bf QCHK_L0Bf QCHKr_L0Bf Xf2_L0Bf XM2_L0Bf XR2_L0Bf XEX2_L0Bf sX2_L0Bf run7_L0Bf
           NX7_L0Bf RUN7_L0Bf L7_L0Bf run7r_L0Bf NX7r_L0Bf RUN7r_L0Bf L7r_L0Bf AXE2_L0Bf WXR2_L0Bf DXR2_L0Bf NXR2_L0Bf EQR2_L0Bf ENT2_L0Bf SID2_L0Bf HCSTF Edr_nf_L0Bf XMd_L0Bf XKd_L0Bf KEPTd_L0Bf RESTd_L0Bf XEXd_L0Bf
           AXEd_L0Bf OBJSd_L0Bf EQKd_L0Bf RCLSd_L0Bf RCIVd_L0Bf RCELLd_L0Bf RWRd_L0Bf RSHPd_L0Bf ECd_L0Bf FBCd_L0Bf).
Qed.
End QL0Bf.
End F0A_qL0Bf.

