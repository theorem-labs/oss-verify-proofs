(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL jq SpineMallocSec4ILW2 SpineMallocSec4IW2.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.

(* [comment removed for export] *)
Module SpineMallocSec4IEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4IL.run3]); [exact SpineMallocSec4IL.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4IL.run3a]); [exact SpineMallocSec4IL.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4IL.run4a]); [exact SpineMallocSec4IL.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4IL.run4b]); [exact SpineMallocSec4IL.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0l : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IEL.

(* [comment removed for export] *)
Module SpineCallocOvi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "KcA"; "Kc_ok"; "Pre_callocI"; "unwind_stopJ"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "prod"; "pair"; "cons"; "option"; "Some"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "ss_next"; "sv"; "sobj"; "valuation"; "SLit"; "sprop_below"; "swf"; "SVar"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv"; "ov_cuts"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocSec2 SpineMallocI SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SpineCallocS1i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocOvA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wb_o : ltac2:(tb__ "0|0|
S15SaS2aS5cS1U0A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma Fb_o : ltac2:(tb__ "0|0|
S15SaS38S22S29S57A1S5aS1U0A1S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma RN_o : ltac2:(tb__ "0|0|
S15S9S26A1S33S1U0A1S0A2S12S26S58S42S56S26S55S32A4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_o : ltac2:(tb__ "0|0|
S15SaS2aS2eS1U0A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma DKRn_o : ltac2:(tb__ "0|5|
S15S10SdS9SdS25S25A2M0A1M1S9S22A1M2A2M3A1S52S1cS31S1U0A1M4S0A2A1S2eG4S0A2A2S11G3SeG1G2SfG0SeS25S25S28S59A1S2bP18A1A4ScG0A1A3ScS22A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma NXRn_o : ltac2:(tb__ "0|1|
S15S1aS24S2eS1U0A1M0S0A2A1S24S1cS31G0S0A2A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_o : ltac2:(tb__ "0|1|
S15SaS1dS34S1U0A1M0S0A2S3S2G0S0A3S30G0S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma IDn_o : ltac2:(tb__ "0|0|
S15SaS53S30S1U0A1S0A2S3bA2SbA3"). Proof. MemoFast.vmc. Qed.
Definition CertO_o__runs : ltac2:(tb__ "0|0|
S9S10S9S1eA1A1A1") := ltac2:(tb__ "0|0|
S54S13Ufa0ScS19A1S2dU0S0A2A4").
Lemma CertO_o : ltac2:(tb__ "0|1|
S15SaS3fS13Ufa0ScS19A1S14S2dU0M0S0A2SfS1bS2fS1G0A1S0A2ScS1bA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GW (ov_cuts 0 UStopLe) [EXo (Wcan 0) UStopLe] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma ECertO_o : ltac2:(tb__ "0|3|
S15SaS40S13Ufa0ScS19A1S14S42S1bS3cS1bS3dR1Z1S28Z0M0A1M1A3Lc;S2dU0M2S0A2A4SfS3cS3dS2fS1G2A1S0A2G0G1A3ScS3cA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) (ov_cuts 0 UStopLe)) [mkVNA (EXo (Wcan 0) UStopLe) 0 (SLit 0)] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma NXcuts_o : ltac2:(tb__ "0|0|
S1bS37S1bR1S2dU0S0A2A3S5dS14S24S1cR2A1A1A2F_;FC;").
Proof. intros C HC. apply Pos.leb_le. unfold ov_cuts in HC. destruct HC as [<-|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCUT_o : ltac2:(tb__ "0|4|
S41S27S8S1U0M0A1M1S0S4aR2R1A2A3S18S9S22A1M2G2S17S37S1bS3eR1S5bG1S0A2M3A2S2dG0S0A2A3S17S43S22S2cS4aR4R3A2A1R1A3S15SaS38S22S29S24S1cG3A1A1A1R1A3SbA3A2A2Lsx;A2F_;Frho;FA;").
Proof. intros A rho _. exists []. split; [left; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [constructor | reflexivity]]. Qed.

Theorem calloc_ov_0 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S51OF_;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S46S13R7S45R5A1A3S37G2SeS1bS35S3S2S1U0A1M3S0A3S4S47S13A1ReRdR7R6A5A4R3A3S4cS4eZ2Z40A2S4dS39G1S23R6PcA2A2S39G1S23R6PdA2A2A2A2S50S13RaS44S13S49G3S0R9R8A4S7S2G3S0A3R7R6A5S36S13S3bR7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (calloc_ov 0 UStopLe CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts 0 UStopLe) HCUT_o CertO_o).
Qed.
Theorem ecalloc_ov_0 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S37G2SeS1bS35S3S2S1U0A1M3S0A3S4S47S13A1RcRbR6R5A5A4R2A3S4cS4eZ2Z40A2S4dS39G1S23R5PcA2A2S39G1S23R5PdA2A2A2A2S4fS13S44S13S49G3S0R8R7A4S7S2G3S0A3R6R5A5S36S13S3bR6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (ecalloc_ov 0 UStopLe CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts 0 UStopLe) HCUT_o NXcuts_o ECertO_o).
Qed.
End SpineCallocOvi.

(* [comment removed for export] *)
Module SpineMallocSec4IELW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4ILW2.run3]); [exact SpineMallocSec4ILW2.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4ILW2.run3a]); [exact SpineMallocSec4ILW2.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4ILW2.run4a]); [exact SpineMallocSec4ILW2.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4ILW2.run4b]); [exact SpineMallocSec4ILW2.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_2l : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U2M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IELW2.

(* [comment removed for export] *)
Module SpineMallocSec4IEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4IW2.run3]); [exact SpineMallocSec4IW2.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4IW2.run3a]); [exact SpineMallocSec4IW2.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4IW2.run4a]); [exact SpineMallocSec4IW2.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4IW2.run4b]); [exact SpineMallocSec4IW2.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_2h : ltac2:(tb__ "0|8|
S1dS3aS10S18Q40M0A1M1S1bOF_;S25VW;Vst;A2S3bR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S39S17G0R6A2A1M2R1A2S34R1S33G2S35S24S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S24S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U2M6Vst;S22S1dS3cR1A1LX;RdRcR4RaA8S2aR3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S2bR2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 2%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineMallocSec4IEW2.

(* [comment removed for export] *)
Module SpineCallocOviW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "Wcan"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "KcA"; "Kc_ok"; "Pre_callocI"; "unwind_stopJ"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "prod"; "pair"; "cons"; "option"; "Some"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "ss_next"; "sv"; "sobj"; "valuation"; "SLit"; "sprop_below"; "swf"; "SVar"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv"; "ov_cuts_pcs"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocSec2 SpineMallocI SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SpineCallocS1iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocOvA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wb_o : ltac2:(tb__ "0|0|
S15SaS2aS5cS1U1A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma Fb_o : ltac2:(tb__ "0|0|
S15SaS38S22S29S57A1S5aS1U1A1S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma RN_o : ltac2:(tb__ "0|0|
S15S9S26A1S33S1U1A1S0A2S12S26S58S42S56S26S55S32A4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_o : ltac2:(tb__ "0|0|
S15SaS2aS2eS1U1A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma DKRn_o : ltac2:(tb__ "0|5|
S15S10SdS9SdS25S25A2M0A1M1S9S22A1M2A2M3A1S52S1cS31S1U1A1M4S0A2A1S2eG4S0A2A2S11G3SeG1G2SfG0SeS25S25S28S59A1S2bP18A1A4ScG0A1A3ScS22A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma NXRn_o : ltac2:(tb__ "0|1|
S15S1aS24S2eS1U1A1M0S0A2A1S24S1cS31G0S0A2A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_o : ltac2:(tb__ "0|1|
S15SaS1dS34S1U1A1M0S0A2S3S2G0S0A3S30G0S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma IDn_o : ltac2:(tb__ "0|0|
S15SaS53S30S1U1A1S0A2S3bA2SbA3"). Proof. MemoFast.vmc. Qed.
Definition CertO_o__runs : ltac2:(tb__ "0|0|
S9S10S9S1eA1A1A1") := ltac2:(tb__ "0|0|
S54S13Ufa0ScS19A1S2dU1S0A2A4").
Lemma CertO_o : ltac2:(tb__ "0|1|
S15SaS3fS13Ufa0ScS19A1S14S2dU1M0S0A2SfS1bS2fS1G0A1S0A2ScS1bA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GW (ov_cuts_pcs 1 UStopLeOrPc) [EXo (Wcan 1) UStopLeOrPc] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma ECertO_o : ltac2:(tb__ "0|3|
S15SaS40S13Ufa0ScS19A1S14S42S1bS3cS1bS3dR1Z1S28Z0M0A1M1A3Lc;S2dU1M2S0A2A4SfS3cS3dS2fS1G2A1S0A2G0G1A3ScS3cA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) (ov_cuts_pcs 1 UStopLeOrPc)) [mkVNA (EXo (Wcan 1) UStopLeOrPc) 0 (SLit 0)] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma NXcuts_o : ltac2:(tb__ "0|0|
S1bS37S1bR1S2dU1S0A2A3S5dS14S24S1cR2A1A1A2F_;FC;").
Proof. intros C HC. apply Pos.leb_le. unfold ov_cuts_pcs in HC. destruct HC as [<-|[<-|[]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCUT_o : ltac2:(tb__ "0|4|
S41S27S8S1U1M0A1M1S0S4aR2R1A2A3S18S9S22A1M2G2S17S37S1bS3eR1S5bG1S0A2M3A2S2dG0S0A2A3S17S43S22S2cS4aR4R3A2A1R1A3S15SaS38S22S29S24S1cG3A1A1A1R1A3SbA3A2A2Lsx;A2F_;Frho;FA;").
Proof.
  intros A rho HST. unfold unwind_stopJ in HST.
  assert (HWne : (Wcan 1) <> []) by discriminate.
  destruct (Wcan 1) as [|l W'] eqn:EW; [contradiction HWne; reflexivity|]. rewrite <- EW in *.
  destruct (last_link (SVar 28) (Wcan 1)) as [[bp nbp] pc] eqn:EL. destruct HST as [Hp|Hl].
  - exists (stop_pc (Wcan 1)). split; [left; reflexivity|]. split; [apply (stop_pc_holds 1); rewrite EL; exact Hp | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - exists (stop_le (Wcan 1)). split; [right; left; reflexivity|]. split; [apply (stop_le_holds 1); rewrite EL; exact Hl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.

Theorem calloc_ov_1 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S51OF_;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S46S13R7S45R5A1A3S37G2SeS1bS35S3S2S1U1A1M3S0A3S4S47S13A1ReRdR7R6A5A4R3A3S4cS4eZ2Z40A2S4dS39G1S23R6PcA2A2S39G1S23R6PdA2A2A2A2S50S13RaS44S13S49G3S0R9R8A4S7S2G3S0A3R7R6A5S36S13S3bR7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (calloc_ov 1 UStopLeOrPc CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts_pcs 1 UStopLeOrPc) HCUT_o CertO_o).
Qed.
Theorem ecalloc_ov_1 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S37G2SeS1bS35S3S2S1U1A1M3S0A3S4S47S13A1RcRbR6R5A5A4R2A3S4cS4eZ2Z40A2S4dS39G1S23R5PcA2A2S39G1S23R5PdA2A2A2A2S4fS13S44S13S49G3S0R8R7A4S7S2G3S0A3R6R5A5S36S13S3bR6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (ecalloc_ov 1 UStopLeOrPc CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts_pcs 1 UStopLeOrPc) HCUT_o NXcuts_o ECertO_o).
Qed.
End SpineCallocOviW1.

(* [comment removed for export] *)
Module SpineCallocSec4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "aa_ptr_committed"; "sec_chunk"; "ag_pab"; "ageom"; "budget_bound"; "ag_top"; "topG"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "prod"; "app"; "nil"; "pair"; "option"; "length"; "Some"; "None"; "fst"; "snd"; "andb"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_objs"; "SVar"; "ss_facts"; "holds"; "SLit"; "eval"; "rm"; "reg_sv"; "rw"; "SPBranch"; "obj_range"; "obj_holds"; "ranges_disjoint"; "sprop_below"; "swf"; "SPNot"; "rl"; "DUnknown"; "cell"; "enc_bytes"; "image_byte"; "mkObj"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "sub"; "div"; "mul"; "lxor"; "land"; "eqb"; "ge"; "leb"; "log2"; "ltb"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "alloc_top"; "vm_maps"; "vm_reserved"; "region_free"; "m_vm_lazy"; "map_contains"; "maps_subtract"; "vm_limit"; "vm_noaccess"; "vm_forget_range"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "kPtrArrayCommit"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "genL"; "Bw"; "F_g3"; "F_l2"; "x11e3"; "O_1"; "O_2"; "O_blk"; "a0e3"; "O_w"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4.SEC4"; "slink4"; "AXP"; "JGo"; "nopab"; "O_nres"; "range_nopab"; "rtint"; "xor63_okb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "Build_machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "ALU_XOR"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "O_seci"; "msx"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI";
"stopJ_stable"; "secmapsize"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "SKEL0"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "vms"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "rt_zoneG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC4.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.

Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S6Sb0VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S12Sc4Sc9Vnx;A2S13A3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S7S0SdS8VAX;R1A1A1S8R1A1A3FX;").
Hypothesis AXs : ltac2:(tb__ "0|0|
S7S0S11SbA1S9VAX;R1A1A1S9R1A1A3FX;").
Hypothesis AXp : ltac2:(tb__ "0|0|
S7S0S5SaVAX;R1A1A1SaR1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S7S0S5SeVAX;R1A1A1SeR1A1A3FX;").

Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.

Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SbcVnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.slink.

Definition AXP : AA -> AA := fun X => bumpP (AX X).
Lemma AXPg : ltac2:(tb__ "0|0|
S7S0SdS8S98R1A1A1S8R1A1A3FX;").
Proof. intros X. unfold AXP. cbn [aa_geom bumpP]. apply AXg. Qed.

Definition rtint (G : ageom) (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S1S47S96Vx;A2S49Vx;S48S96Z40A2A2A2S1S47ScVG;A1M0Vx;A2S49Vx;S48G0S7bA2A2A2A2").

Definition slink4 (G : ageom) (ua L : Z) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|a|
S1S6S0S58Q40M0A1M1S2fVrho';R1A2S2fVrho;R1A2A3Fi;S1S6S0S11S58Q8A1M2A1S37Vrho';R1A2S37Vrho;R1A2A3Fl;S1G1S4S0S19G2A1M3S2dVrho';R1A2M4S2dVrho;R1A2M5A3S4S1S0G3G5S1cG2A1M6A3S1S0G3S3bS92R1A2G6A3S1S47S7dS59G0R1A2M7A2S49G7S7cA2A2A2A2S4S1S1S47S7eVua;A1M8G7A2S49G7S48G8S4eVL;Z8A2A2M9A2A2S3S0G3G4G6A3A1A2S9dVG;G7A2A2A2A2Fa;S5S1S47G8R1A2S49R1G9A2A2S3S0G3S2dVrho';S5aG0R2A2A2G6A3A1F_;Fz;A2A2A2").

Lemma slink_slink4 : ltac2:(tb__ "0|0|
SdS5S5S22S22Vslink;R4R3R2R1A4S97R6R5R4R3R2A5F_;Fr2;Fr1;FL;Fua;FG;").
Proof.
  intros G ua L r1 r2 (W1 & L1 & M1 & D1). split; [exact W1|]. split; [exact L1|]. split; [|exact D1].
  intros a. destruct (M1 a) as [E|[X|X]]; [left; exact E | right; left; exact X | right; right; left; exact X].
Qed.
Lemma slink4_trans : ltac2:(tb__ "0|0|
SdS5S5S22S22S22S97R6R5R4R3R2A5S97R7R6R5R3R2A5S97R8R7R6R5R3A5F_;F_;Fr3;Fr2;Fr1;FL;Fua;FG;").
Proof.
  intros G ua L r1 r2 r3 (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2).
  split; [intros i; rewrite W2; apply W1|]. split; [intros l; rewrite L2; apply L1|]. split; [|exact D2].
  intros a. destruct (M2 a) as [E2|[(N2 & I2 & B2)|[(R2 & S2)|T2]]].
  - rewrite E2. destruct (M1 a) as [E1|[X|[X|X]]]; [left; exact E1 | right; left; exact X | right; right; left; exact X | right; right; right; exact X].
  - destruct (M1 a) as [E1|[(N1 & I1 & B1)|[(R1 & S1)|T1]]].
    + right. left. rewrite <- E1. exact (conj N2 (conj I2 B2)).
    + right. left. exact (conj N1 (conj I2 B2)).
    + exfalso. exact (S1 N2).
    + right. right. right. exact T1.
  - right. right. left. exact (conj R2 S2).
  - right. right. right. exact T2.
Qed.

Definition msOf (f : word -> option byte) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
Sa0Sa4Vms;A1Sa2Vms;A1Sa3Vms;A1Sa7Vms;A1Sa5Vms;A1Sa1Vms;A1Vf;Sa6Vms;A1A8").

Definition ens_mem (v : Z) : word -> option byte := ltac2:(tb__ "0|6|
S58Q40M0A1S12S19S58Q8M1A1M2A1L_;S1fS54S48S96Z30A2M3S59G0R1A2M4A2S56G4S48S96Z38A2A2A2S1bG2S76G2S57S4dG4G3A2A1S3aU8S5aG0Vv;A2A2S5aG1Z0A2M5A4A2S1bG2G5A2X12x2La;").

Definition O_nres : sobj := ltac2:(tb__ "0|0|
S3cS2bS48S96Z30A2A1S2bZ0A1S2bZ8A1S17S39A1S38A5").
Definition R_ens : list sobj := ltac2:(tb__ "0|0|
S14S23S9bS14S23S89S17S23A1A3A3").

Lemma JG_sec_nums : ltac2:(tb__ "0|9|
S7S7Fx;S7S5bS22S58Q40A1M0S22S11G0A1S11S61A1S60S7S0SdS8RaR1A1A1S8R1A1A3FX;S7S0S11SbA1S9RbR1A1A1S9R1A1A3FX;S7S0S5SaRcR1A1A1SaR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S8RcA1SdSaRdA1S5S1S47S80ScR2A1M1A2S1S47S48G1S7bA2M2S10R2A1M3A2S1S0S5S4cG1S81A2Z0M4A3S1S4S47G2S7dA2S47S7cG1A2A2S1S1S47S4fZ8M5S4aS1aSbS9ReA1A2A1A2R1A2S47R1S7bA2A2S1S0S5S4cR1S7fA2G4A3S1S0S5G3SfR2A1M6A3S1S0S5S63S62R7A1A1G6A3S5S1S47S48ScR3A1M7S4fG5S4aS1aSbS9RfA1A2A1A2A2R1A2S49R1S48G7R2A2A2A2S2S58Q8A1M8G8S0S19G8A1Sc3S92S2dRdA1R3A3S1bG8R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ.
  destruct HJ as (Hagr & Ha & HA & _).
  pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. exact X.
Qed.

Lemma F_g3_hold : ltac2:(tb__ "0|1|
S7S7F_;S7S5bS22S58Q40A1M0S22S11G0A1S11S61A1S60VJG;R9R8R7R6R5R4R3R2R1A9S49S48S4aS1aSbS9R9A1A2A1Z1A2S4bZ2Z14A2A2S74S25S2aR6A1S84A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ Hok.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E147 & _).
  unfold F_g3. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite E147, !u64_lit by lia. lia.
Qed.

Definition xor63_okb (c : Z) : bool := ltac2:(tb__ "0|1|
S52S50Vc;Z3fM0A2S4dG0Vc;A2A2").
Lemma xor63_all : ltac2:(tb__ "0|0|
S0S12S95S5S9eS75S21S5S4aS77U0U40A2A4A3S13A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma xor63 : ltac2:(tb__ "0|1|
S5S1S47Z0R1A2S47R1Z3fM0A2A2S0S5S50R2G0A2S4dG0R2A2A3F_;Fc;").
Proof.
  intros c Hc. pose proof (proj1 (forallb_forall _ _) xor63_all c) as X. apply Z.eqb_eq. apply X.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma xor_valE : ltac2:(tb__ "0|2|
S58Q40M0A1M1G1S0S5S59G0Sc6SaaR2R1A3A2S50S59G0R2A2S59G0R1A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.
Lemma land_m4096E : ltac2:(tb__ "0|0|
S5S1S47Z0R1A2S49R1S4bZ2Z40A2A2A2S0S5S51R2Zfffffffffffff000A2S4dR2S4cR2Z1000A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask by lia. reflexivity. Qed.
Lemma land_m8E : ltac2:(tb__ "0|0|
S5S1S47Z0R1A2S49R1S4bZ2Z40A2A2A2S0S5S51R2Zfffffffffffffff8A2S4dR2S4cR2Z8A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. reflexivity. Qed.

Lemma msx_val : ltac2:(tb__ "0|2|
S7S7F_;S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1S60VJG;R9R8R7R6R5R4R3R2R1A9S0S5S59G0S2cR5SafA2A2Sb2S59G0S2fR7PcA2A2A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  cbn zeta in HN, SMB, SMM, ENS, EMS, R8M, R8B.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (VNS := secneeded nv) in *.
  assert (VB : 68609 <= VNS <= nv + 4103) by (clear -ENS R8B HN; lia).
  unfold msx. cbn [eval]. rewrite E141. fold VNS.
  rewrite add_val, and_val, add_val, !u64_lit by lia.
  rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite land_m4096E by lia.
  assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = secmapsize nv).
  { rewrite EMS. unfold round_up, PG. replace (VNS + 4095) with (VNS + 4096 - 1) by lia. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). lia. }
  rewrite ERU. apply Z.mod_small. lia.
Qed.

Lemma x11e3_val : ltac2:(tb__ "0|3|
S7S7F_;S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1S60VJG;R9R8R7R6R5R4R3R2R1A9S1S0S5S59G0S2cR5S86A2A2M2S55Sb2S59G0S2fR7PcA2A2A1A1A3S1S47Z10G2A2S47G2Z28A2A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (msx_val BX A Kc rho a r tp tr md HJ) as EM.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _). cbn zeta in HN, SMB.
  set (MS := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  pose proof (clz_sv_val r msx ltac:(rewrite EM; lia)) as CL. rewrite EM in CL.
  assert (L1 : 16 <= Z.log2 MS) by (apply Z.log2_le_pow2; lia).
  assert (L2 : Z.log2 MS <= 39) by (apply Z.lt_succ_r; apply Z.log2_lt_pow2; lia).
  unfold x11e3. cbn [eval]. rewrite xor_valE, CL, u64_lit by lia. rewrite xor63 by lia. lia.
Qed.

Lemma ens_site : ltac2:(tb__ "0|4|
S7S7Fx;S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1S60S7S0SdS8RaR1A1A1S8R1A1A3FX;S7S0S11SbA1S9RbR1A1A1S9R1A1A3FX;S7S0S5SaRcR1A1A1SaR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S2aR8S30Sa8S28SacA1S28SadA1A3A2S74S25S2aR9A1S84A3S8ReA1SdSaRfA1S5S48ScR2A1R1A2S5S1S0S5S4fZ8S4aS1aSbS9R11A1A2A1A2R2A3S1S47S48R2S7fA2S7bA2S1S0S5S59G0S2cRdS8aA2A2R1A3S1S0S5S59G0S2cRdS83A2A2R1A3S1S0S5S4cR1Z1000A2Z0M2A3S1S47S80ScR3A1M3A2S1S47S48G3S7bA2S63S62RaA1A1A2S47G2R2A2A2A2A2A2A2A2A2TPB;Tc;TG;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HBR HF.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  pose proof (JG_sec_nums BX A Kc rho a r tp tr md BXg BXs BXp HJ) as (P1 & P2 & P3 & P4 & P5 & P6 & GT & TOP & _).
  cbn zeta in P1, P2, P3, P4, P5, P6, GT, TOP |- *.
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  cbn [holds eval] in HBR. rewrite E147, E146 in HBR. fold c in HBR.
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(lia) ltac:(lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HBR by lia. apply Z.eqb_eq in HBR.
  unfold F_g3 in HF. apply Forall_inv in HF. cbn [holds eval] in HF. rewrite E147, !u64_lit in HF by lia.
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite P6, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HBR; lia).
  assert (HcR : c + 2 ^ 17 <= 2 ^ 23).
  { rewrite X. set (q := c / 2 ^ 17) in *. clear -HF HcN X. lia. }
  assert (C4 : c mod 4096 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 5 * (c / 2 ^ 17)) * 4096) by lia; apply Z_mod_mult).
  assert (PB4 : (ag_pab G + c) mod 4096 = 0) by (rewrite Z.add_mod, P3, C4 by lia; reflexivity).
  assert (R64 : 0 <= ag_pab G + Z.of_nat (length (aa_sec A)) * 8 < 2 ^ 64) by (clear -P1 P2 TG HcN HcR NN; lia).
  assert (EBw : bv_unsigned (eval r Bw) = ag_pab G + c).
  { unfold Bw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G. rewrite !u64_lit by lia.
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by lia. rewrite (Z.mod_small _ _ R64). lia. }
  assert (EA0 : bv_unsigned (eval r a0e3) = ag_pab G + c).
  { unfold a0e3. cbn [eval]. rewrite E145, E147, and_val, add_val, sll_val. fold G. rewrite !u64_lit by lia.
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by lia.
    replace (Z.of_nat (length (aa_sec A)) * 8 + ag_pab G) with (ag_pab G + c) by lia.
    rewrite (Z.mod_small (ag_pab G + c)) by lia.
    rewrite land_m4096E by lia. rewrite PB4. lia. }
  repeat split; try assumption; try lia.
Qed.

Definition nopab (G : ageom) (x : Z) : Prop := ltac2:(tb__ "0|1|
S3S1S47ScVG;A1M0Vx;A2S49Vx;S48G0S7bA2A2A2A1").
Definition range_nopab (G : ageom) (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S5S1S47S1dS5S5Vr;A3R1A2S49R1S1eS5S5Vr;A3A2A2S9aVG;R2A2F_;Fx;").

Lemma rt_zoneG_nopab : ltac2:(tb__ "0|1|
S7S7Fx;S7S5bS22S58Q40A1M0S22S11G0A1S11S61A1S60S5S7S0SdS8RbR1A1A1S8R1A1A3FX;S7S0S11SbA1S9RcR1A1A1S9R1A1A3FX;S7S0S5SaRdR1A1A1SaR1A1A3FX;VJG;RdRcRbRaR9R8R7R6R5A9ScaS8RdA1R5A2S9aS8ReA1R6A2F_;F_;F_;F_;F_;Fx;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md x BXg BXs BXp HJ Hz.
  pose proof (JG_sec_nums BX A Kc rho a r tp tr md BXg BXs BXp HJ) as (P1 & _). cbn zeta in P1.
  destruct HJ as (Hagr & Ha & HA & _). pose proof (AInvA_pabsep _ _ _ _ HA) as (_ & PT & PF & PC & PD).
  rewrite BXg in PT, PF, PC, PD. cbn [aa_geom bumpV] in PT, PF, PC, PD.
  unfold nopab. unfold rt_zoneG in Hz. rewrite FS_total_val in *. unfold IMG_HI, kPtrArrayReserve in *.
  destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]]; [clear -Z1 P1; lia | clear -Z2 PT; lia | clear -Z3 PC; lia | clear -Z4 PD; lia | clear -Z5 PF; lia].
Qed.

Lemma objs_nopab : ltac2:(tb__ "0|4|
S41S11S23A1M0G0S7S5bS22S58Q40A1M1S22S11G1A1S11S61A1S60S9fS91VW;Vst;A2VJG;VAX;RaR9R8R7R6R5R4R3A9S74S25S2aR7A1S29S40ReA1A1A3S74S23S32Vsegs;R8R4A3S27S40RfA1A1A3S0S11S15S15S24S24A2S24A2M2A1M3S75S23G2S73S27S40R10A1A1A4S75S23G2S73S16S23RfS16S23SbbVnW;Vnx;A2ReA3A3A4A3S93S25S16S25S5fVW;Vst;A2S5eS5dA1A3S29S40R11A1A1A3S2G0G0S2G0G0S2G0G0S1S0G0S27S40R15A1A1S16S23R3S16S23R2R1A3A3A3S1S0G3S75S23G2S73R3A4S75S23G2S73R14A4A3S1S0G3S75S23G2S73R1A4S75S23G2S73R13A4A3S74S23S23S9cS8R13A1S31RfR1A2A2Lo;R2A3A2A2A2Ll2;A2Ll1;A2Ll0;A2F_;F_;F_;F_;F_;F_;FmsX;Fmd;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp tr md msX HW HJ HFall HallX SKP FC.
  rewrite map_app in SKP. destruct (map_eq_app _ _ _ _ SKP) as (l0 & l12 & EO0 & SK0' & SKP').
  rewrite map_app in SKP'. destruct (map_eq_app _ _ _ _ SKP') as (l1 & l2 & EO12 & SK & SK2).
  exists l0, l1, l2. split; [rewrite EO0, EO12; reflexivity|]. split; [exact SK0'|]. split; [exact SK2|].
  pose proof (JGs_rigidS nW st tmax nx Hnx AX A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & _).
  pose proof (JG_sec_nums AX A Kc rho a rhoX tp tr md AXg AXs AXp HJ) as (P1 & P2 & _). cbn zeta in P1, P2.
  assert (RTZ : forall x, rt_zoneG (aa_geom A) x -> nopab (aa_geom A) x) by (intros x; exact (rt_zoneG_nopab AX A Kc rho a rhoX tp tr md x AXg AXs AXp HJ)).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  pose proof HA as (HG & _). rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & T1 & T2 & T0' & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (FC p Hp)). }
  assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
  assert (Hall : Forall (obj_holds segs rhoX msX) l1).
  { rewrite EO0, EO12 in HallX. apply Forall_app in HallX as [_ Hall]. apply Forall_app in Hall as [Hall _]. exact Hall. }
  unfold SKEL0 in SK. cbn [app] in SK.
  destruct (skel_head _ sw_s1 _ SK) as (o0 & rest & EO & SK0 & SKR).
  subst l1.
  pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
  constructor.
  { intros x Hx. unfold nopab. clear -SW0 P2 Hx. lia. }
  apply (Forall_ranges_skel rhoX (range_nopab (aa_geom A)) _ _ SKR).
  apply Forall_app. split.
  2:{
    apply Forall_cons; [|apply Forall_nil].
    pose proof HP as (_ & _ & HL & _ & _ & _ & _ & _ & _ & SPP & _). unfold sepZ in SPP. cbn [fst snd] in SPP.
    pose proof (secmapsize_bounds (bv_unsigned (rw rho 12%positive)) ltac:(clear -HN; lia)) as [SMB _].
    assert (SO : soff rhoX (SVar V_MS) = secmapsize (bv_unsigned (rw rho 12%positive))).
    { unfold soff. cbn [eval]. rewrite E142, signed_lit. unfold snorm. rewrite Z.mod_small by (clear -SMB HN; lia).
      destruct (Z.ltb_spec (secmapsize (bv_unsigned (rw rho 12%positive))) (2 ^ 63)); clear -SMB HN H; lia. }
    intros x Hx. unfold obj_range, obj_lo_of, obj_hi_of in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx.
    rewrite SO, soff_lit_small in Hx by lia. cbn [eval] in Hx. rewrite Enx in Hx.
    unfold nopab. clear -SPP Hx. lia. }
  apply Forall_app. split.
  2:{
    unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
    intros x Hx. apply RTZ. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(clear -T1 T2 TG; lia) Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
    intros x Hx. apply RTZ. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
      intros x Hx; rewrite obj_range_mk in Hx by lia; cbn [fst snd eval] in Hx; rewrite u64_lit in Hx by lia;
      unfold nopab, IMG_HI in *; clear -Hx P1; lia. }

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -TG; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
    apply HFX. apply in_or_app; left. exact Hp'. }
  eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
  intros x Hx. rewrite obj_range_mk in Hx by (clear -B; lia). cbn [fst snd] in Hx. unfold nopab. clear -B Hx P2. lia.
Qed.

Lemma pab_piece_disjoint : ltac2:(tb__ "0|6|
S41S11S23A1M0G0S7S5bS22S58Q40A1M1S22S11G1A1S11S61A1S60S9fS5S5S91VW;Vst;A2VJG;VAX;RcRbRaR9R8R7R6R5A9S74S25S2aR9A1S29S40R10A1A1A3S74S23S32Vsegs;RaR6A3S27S40R11A1A1A3S0S11S15S15S24S24A2S24A2M2A1M3S75S23G2S73S27S40R12A1A1A4S75S23G2S73S16S23R11S16S23SbbVnW;Vnx;A2R10A3A3A4A3S93S25S16S25S5fVW;Vst;A2S5eS5dA1A3S29S40R13A1A1A3S47ScS8R11A1A1R8A2S47R8S48ScS8R12A1A1S7bA2A2G0S0G3S75S23G2S73R1A4S75S23G2S73R16A4A3M4S74S23S23S33S31R12R1A2S18S5S5RdRcA4A2Lo;M5R2A3F_;Fl;G0G4S74S23S23S33S31R13R1A2S18S5S5ReRdA4A2Lo;R2A3F_;Fl;S74S23G5S27S40R18A1A1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fh2;Flo;FmsX;Fmd;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp tr md msX lo h2 HW HJ HFall HallX SK FC HLO HHI HP0 HP.
  destruct (objs_nopab X P0 P A Kc rho a rhoX tp tr md msX HW HJ HFall HallX SK FC) as (l0 & l1 & l2 & EO & SK0' & SK2 & NB).
  rewrite EO. apply Forall_app. split; [exact (HP0 l0 SK0')|]. apply Forall_app. split; [|exact (HP l2 SK2)].
  eapply Forall_impl; [|exact NB]. intros o Ho. unfold ranges_disjoint, range_nopab, nopab in *. cbn [fst snd].
  destruct (obj_range rhoX o) as [olo ohi]. cbn [fst snd] in Ho |- *.
  destruct (Z_le_dec ohi olo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec ohi lo) as [E2|E2]; [right; right; left; exact E2|].
  destruct (Z_le_dec h2 olo) as [E3|E3]; [right; right; right; exact E3|].
  destruct (Z_le_dec h2 lo) as [E4|E4]; [right; left; exact E4|].
  exfalso. apply (Ho (Z.max olo lo) ltac:(clear -E E2 E3 E4; lia)). clear -E E2 E3 E4 HLO HHI. lia.
Qed.

Lemma SPA_parts : ltac2:(tb__ "0|2|
S71S41S22S11S58Q40A1A1S11S61A1M0S9fS60S6eVsegs;R7R6R5R4S18G0Sb3R3Sb4R2R1A2A4A6S1S74S25S2aR6A1S29S40R7A1M1A1A3S1S74S23S32Vsegs;R6Sc1R2R5R3A3A3S27G1A1A3R8R6R5R4R2A4A2A2F_;Fmd;Fms;Ftr;Ftp;Fr;FX;FJ;").
Proof.
  intros J X r tp tr ms md Hsp. pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  split; [exact (smatch_facts_hold _ _ _ _ Hsm)|]. split; [|exact (proj2 Hsp)].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall.
Qed.
Lemma pending_parts : ltac2:(tb__ "0|2|
S41S22S11S58Q40A1A1S11S61A1M0S9fS60Sb8Vsegs;R5R4R6S18G0Sb3R3Sb4R2R1A2A4A5S1S74S25S2aR6A1S29S40R7A1M1A1A3S74S23S32Vsegs;R6Sc1R2R5R3A3A3S27G1A1A3A2F_;Fmd;Fms;Ftr;Ftp;Fr;FX;").
Proof.
  intros X r tp tr ms md Hsp. pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm.
  split; [exact (smatch_pending_facts _ _ _ _ _ _ Hsm)|].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall.
Qed.

Lemma JG_K : ltac2:(tb__ "0|1|
S7S7F_;S7S5bS22S58Q40A1M0S22S11G0A1S11S61A1S60VJG;R9R8R7R6R5R4R3R2R1A9R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof. intros BX A Kc rho a r tp tr md HJ. exact (JGs_K nW st nx BX A Kc rho a r tp tr md HJ). Qed.
Lemma JG_okf : ltac2:(tb__ "0|0|
S7S7F_;S78OF_;S7S11S61A1S60OF_;F_;S22S58Q40A1S70Vsegs;R5S6fR3A1A3S70Vsegs;R6VJG;R7R5R4R3R2A5A3F_;Fa;Frho;FKc;FA;Fok;FBX;").
Proof. intros BX ok A Kc rho a Hokl r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). exact (JG_K _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma JG_okp : ltac2:(tb__ "0|0|
S7S7F_;S78OF_;S7S11S61A1S60OF_;F_;S22S58Q40A1Sb7Vsegs;R5S6fR3A1A3Sb7Vsegs;R6VJG;R7R5R4R3R2A5A3F_;Fa;Frho;FKc;FA;Fok;FBX;").
Proof. intros BX ok A Kc rho a Hokp. apply (ok_pframeA_liftKA segs ok Kc). exact Hokp. intros r t tr md HJ. exact (JG_K _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma JG_stable : ltac2:(tb__ "0|0|
S7S7F_;S7S5bS22S58Q40A1Sb1VW;Vst;A2S5cR4A1S72Vsegs;VGS;VJG;R7R6R5R4R3A5A3F_;F_;Fa;Frho;FKc;FA;FBX;").
Proof. intros BX A Kc rho a HUS HKc. exact (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc). Qed.

Lemma gen_x11 : ltac2:(tb__ "0|1|
S7S7F_;S7S5bS22S58Q40A1M0S41S41S90S22S11G0A1S78Sb1VW;Vst;A2S5cRaA1S0S12S42R8S82R8A1R6A3S13A3S0S12S8dR7VGS;A2S13A3S0S24S8eR8S26S40RaA1A1A2S86A3S0S12S95S25S34S26S40S82RbA1A1A1A1S85S26S40RbA1A1A1A3S13A3S0S41Sb6S85S26S40RcA1A1A1S82RcA1A2RbA3S6eVsegs;VJG;R12R11R10RfReA5RdRaR9R8A6S6eVsegs;VJG;R13R12R11R10RfA5RdS8fRbRcA2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;Fs;FL;FX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a X L s r tp w HUS HKc HE HID HG HFB HL Hsp. rewrite <- HL.
  apply (SPA_entails_sem segs (JG BX A Kc rho a) GS X (genL X) (F_l2 (ss_next (ax_S X))) s r tp w HE HID (JG_stable BX A Kc rho a HUS HKc) HFB); [|exact Hsp].
  intros rr t' tr' md' HJ _. destruct (x11e3_val BX A Kc rho a rr t' tr' md' HJ) as [_ B].
  unfold F_l2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds eval rho_sub rw]; rewrite HG, u64_lit by lia; clear -B; lia.
Qed.

Lemma join4 : ltac2:(tb__ "0|1|
S7S7F_;S7S5bS22S58Q40A1M0S41S41S90S22S11G0A1S78Sb1VW;Vst;A2S5cRaA1S0S12S42R8R7R6A3S13A3S0S12S8dR7VGS;A2S13A3S6eVsegs;VJG;RfReRdRcRbA5RaR7R6R5A6S6eVsegs;VJG;R10RfReRdRcA5RaS8fR8R9A2R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fr;Fs;FT;FY;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a Y T s r tp w HUS HKc HE HID Hsp.
  exact (SPA_entails0 segs (JG BX A Kc rho a) GS Y T s r tp w HE HID (JG_stable BX A Kc rho a HUS HKc) Hsp).
Qed.

Definition JGo (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|7|
S22S11S58Q40A1M0A1S11S61A1S60S8VA;A1SdS48ScR1A1SaVA;A1A2S5S2S60S60S1VJG;VAX;VA;VKc;Vrho;Va;R7R6R5R1A9S1S2aR7S30Sa8S28SacA1S28SadA1A3A2S1S74S25S2aR7A1S84A3S1S0S11S15G0G0A2A1M1S64S62R4A1M2A1S64S62R1A1M3A1A3S1S0G1S65G2A1S65G3A1A3S1S0G1S6bG2A1S69S6bG3A1M4R2S48R2S7fA2M5A3A3S1S0G1S67R4A1S69S67R1A1M6R2G5A3A3S1S0S5S6aG2A1S6aG3A1A3S1S0S5S63G2A1S63G3A1A3S1SbeG4A1S1SbeG6A1S1S47Sc0R4R6A2S48Sc0R1R6A2S7fA2A2VKc;R5R4A2A2A2A2A2A2A2A2A2A2A2A2A2Lmd0;A2TPB;TG;Lmd';Ltr;Ltp;Lr;").

Section G3.

Variables (D2 U2 X3a X3b CS3 G3 X3a3 L3a L3b CO3b T4a T4b Y4a0 Y4a1 Y4b0 Y4b1 : axst).
Variables (sLa sLb s4a0 s4a1 s4b0 s4b1 : wsub).

Hypothesis WU2 : ltac2:(tb__ "0|0|
S0S12S35S40VU2;A1A1S13A3").
Hypothesis DU2 : ltac2:(tb__ "0|4|
S0S19S15S11S15S24S24A2M0A1M1S11S25A1M2A2M3A1SbdS40VD2;A1S40VU2;A1A2S1bG3S18G1G2S17G0A1S84A4A2A3").
Hypothesis NXU2 : ltac2:(tb__ "0|0|
S0S6S26S40VU2;A1A1S26S40VD2;A1A1A3").
Hypothesis HU2 : ltac2:(tb__ "0|0|
S0S41S43VD2;S40VU2;A1A2VU2;A3").

Hypothesis Cert3 : ltac2:(tb__ "0|1|
S0S12Sb5S92Ufa0S14S5Z706a0S14S5Z410f0S17S5A1A3A3VGS;S14S41VU2;S17S41A1M0A3S14S41VX3a;S14S41VX3b;G0A3A3A6S13A3").

Hypothesis WC3 : ltac2:(tb__ "0|0|
S0S12S35S40VCS3;A1A1S13A3").
Hypothesis DC3 : ltac2:(tb__ "0|4|
S0S19S15S11S15S24S24A2M0A1M1S11S25A1M2A2M3A1SbdS40VX3a;A1S40VCS3;A1A2S1bG3S18G1G2S14G0S18S24S24S8aS83A4S17G0A1A3S17S25A1A4A2A3").
Hypothesis NXC3 : ltac2:(tb__ "0|0|
S0S6S26S40VCS3;A1A1S26S40VX3a;A1A1A3").
Hypothesis HC3 : ltac2:(tb__ "0|0|
S0S41S43VX3a;S40VCS3;A1A2VCS3;A3").
Hypothesis FX3a : ltac2:(tb__ "0|0|
S93S25S16S25S14S25S30Sa8S28SacA1S28SadA1A3S17S25A1A3S84A3S29S40VX3a;A1A1A3").
Hypothesis IC3 : ltac2:(tb__ "0|0|
S0S19Sa9A1Sc8S92S3eS40VCS3;A1A1A2S1bSa9SabA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1Z11A2S2bZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZaA2S83A3").
Hypothesis BBw : ltac2:(tb__ "0|0|
S0S12S3fS26S40VCS3;A1A1S83A2S13A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZbA2S2bZ20000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZcA2S2bZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZdA2S2bZ32A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZeA2S2bZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZfA2S2bZ0A1A3").
Hypothesis XC3 : ax_X CS3 = [].
Hypothesis SK3 : ltac2:(tb__ "0|2|
S0S11S15S15S24S24A2S24A2M0A1S75S23G0S73S27S40VCS3;A1A1A4S75S23G0S73S16S23S14S23S88Vnx;A1S14S23S87Vnx;A1S17S23A1M1A3A3S16S23SbbVnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC3 : ltac2:(tb__ "0|0|
S93S25S16S25S5fVW;Vst;A2S5eS5dA1A3S29S40VCS3;A1A1A3").
Hypothesis FCS3 : ltac2:(tb__ "0|0|
S93S25S16S25S14S25S30Sa8S28SacA1S28SadA1A3S17S25A1A3S84A3S29S40VCS3;A1A1A3").
Hypothesis NXS3 : ltac2:(tb__ "0|0|
S0S12Sc4VGS;S26S40VCS3;A1A1A2S13A3").

Hypothesis HG3 : ltac2:(tb__ "0|1|
S0S41S43VCS3;Sc7S40VCS3;A1M0S83S16S23S27G0A1S14S23S89S17S23A1A3A3S26G0A1A4A2VG3;A3").

Hypothesis Cert3a : ltac2:(tb__ "0|1|
S0S12Sb5S92Ufa0S14S5Z410f0S17S5A1A3VGS;S14S41VG3;S17S41A1M0A3S14S41VX3a3;G0A3A6S13A3").

Hypothesis ELa : ltac2:(tb__ "0|0|
S0S12S42VX3a3;S82VX3a3;A1VsLa;A3S13A3").
Hypothesis IDa : ltac2:(tb__ "0|0|
S0S12S8dVsLa;VGS;A2S13A3").
Hypothesis GLa : ltac2:(tb__ "0|0|
S0S24S8eVsLa;S26S40VX3a3;A1A1A2S86A3").
Hypothesis FBLa : ltac2:(tb__ "0|0|
S0S12S95S25S34S26S40S82VX3a3;A1A1A1A1S85S26S40VX3a3;A1A1A1A3S13A3").
Hypothesis HL3a : ltac2:(tb__ "0|0|
S0S41Sb6S85S26S40VX3a3;A1A1A1S82VX3a3;A1A2VL3a;A3").
Hypothesis ELb : ltac2:(tb__ "0|0|
S0S12S42VX3b;S82VX3b;A1VsLb;A3S13A3").
Hypothesis IDb : ltac2:(tb__ "0|0|
S0S12S8dVsLb;VGS;A2S13A3").
Hypothesis GLb : ltac2:(tb__ "0|0|
S0S24S8eVsLb;S26S40VX3b;A1A1A2S86A3").
Hypothesis FBLb : ltac2:(tb__ "0|0|
S0S12S95S25S34S26S40S82VX3b;A1A1A1A1S85S26S40VX3b;A1A1A1A3S13A3").
Hypothesis HL3b : ltac2:(tb__ "0|0|
S0S41Sb6S85S26S40VX3b;A1A1A1S82VX3b;A1A2VL3b;A3").

Hypothesis HCOb : ltac2:(tb__ "0|0|
S0S41S8cVL3b;S8bA2VCO3b;A3").
Hypothesis WCOb : ltac2:(tb__ "0|0|
S0S12S35S40VCO3b;A1A1S13A3").
Hypothesis XCb : ax_X L3b = [].
Hypothesis SKb : ltac2:(tb__ "0|2|
S0S11S15S15S24S24A2S24A2M0A1S75S23G0S73S27S40VL3b;A1A1A4S75S23G0S73S16S23S14S23S88Vnx;A1S14S23S87Vnx;A1S17S23A1M1A3A3S16S23SbbVnW;Vnx;A2G1A3A3A4A3").
Hypothesis FCb : ltac2:(tb__ "0|0|
S93S25S16S25S5fVW;Vst;A2S5eS5dA1A3S29S40VL3b;A1A1A3").
Hypothesis FXb : ltac2:(tb__ "0|0|
S93S25S14S25S36S30Sa8S28SacA1S28SadA1A3A1S17S25A1A3S29S40VL3b;A1A1A3").

Hypothesis Cert4a : ltac2:(tb__ "0|1|
S0S12Sb5S92Ufa0S14S5Z3c614S17S5A1A3VGS;S14S41VL3a;S17S41A1M0A3S14S41VY4a0;S14S41VY4a1;G0A3A3A6S13A3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0S12S42VY4a0;VT4a;Vs4a0;A3S13A3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0S12S8dVs4a0;VGS;A2S13A3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0S12S42VY4a1;VT4a;Vs4a1;A3S13A3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0S12S8dVs4a1;VGS;A2S13A3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0S12Sb5S92Ufa0S14S5Z3c614S17S5A1A3VGS;S14S41VCO3b;S17S41A1M0A3S14S41VY4b0;S14S41VY4b1;G0A3A3A6S13A3").
Hypothesis E4b0 : ltac2:(tb__ "0|0|
S0S12S42VY4b0;VT4b;Vs4b0;A3S13A3").
Hypothesis I4b0 : ltac2:(tb__ "0|0|
S0S12S8dVs4b0;VGS;A2S13A3").
Hypothesis E4b1 : ltac2:(tb__ "0|0|
S0S12S42VY4b1;VT4b;Vs4b1;A3S13A3").
Hypothesis I4b1 : ltac2:(tb__ "0|0|
S0S12S8dVs4b1;VGS;A2S13A3").

Lemma RSU : ltac2:(tb__ "0|1|
S7S5bS22S58Q40A1M0S22S11G0A1S78S49S48S4aS1aSbS9R7A1A2A1Z1A2S4bZ2Z14A2A2S6eVsegs;VJG;VAX;R8R7R6R5A5VD2;R4R3R2A6S6eVsegs;VJG;VAX;R9R8R7R6A5VU2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hok Hw. destruct w as [tr [ms md]]. rewrite <- HU2.
  eapply SPA_restate; [exact WU2 | exact DU2 | exact NXU2 | constructor | | exact Hw].
  exact (F_g3_hold AX A Kc rho a rhoX tp tr md (proj2 Hw) Hok).
Qed.

Lemma SPA_facts : ltac2:(tb__ "0|0|
S71S41S22S11S58Q40A1A1S78S11S25A1S6eVsegs;R6R5R4R3R2A6S93S25R2S29S40R6A1A1A3S74S25S2aR6A1R3A3F_;F_;FF;Fw;Ftp;Fr;FX;FJ;").
Proof.
  intros J X r tp w F Hsp HF.
  pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFall.
  apply Forall_forall. intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (HF p Hp)).
Qed.

Lemma RS3 : ltac2:(tb__ "0|1|
S7S5bS22S58Q40A1M0S22S11G0A1S78S6eVsegs;VJG;VAX;R7R6R5R4A5VX3a;R3R2R1A6S6eVsegs;VJG;VAX;R8R7R6R5A5VCS3;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HC3.
  pose proof (SPA_facts _ _ _ _ _ _ Hw FX3a) as HF. apply Forall_app in HF as [HB HF]. apply Forall_inv in HB.
  destruct (ens_site AX A Kc rho a rhoX tp tr md AXg AXs AXp (proj2 Hw) HB HF) as (_ & _ & EA0 & EBw & _).
  eapply SPA_restate; [exact WC3 | exact DC3 | exact NXC3 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq. rewrite EA0, EBw. reflexivity.
Qed.

Lemma region_free_of_apart : ltac2:(tb__ "0|2|
S11S15S58Q40A1M0G0A2M1A1G0G0G1S94G1R1R4A3Sb9S18G0G0R4R3A4R2A2F_;Fe;S0S12S66R4R3R2A3S13A3F_;Fn;Fa;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite (IH a n) by (intros e He; apply H; right; exact He). rewrite andb_true_r.
  pose proof (H (b, s) (or_introl eq_refl)) as X. unfold apartW in X. cbn [fst snd] in X.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct X as [X|X]; [right|left]; apply Z.ltb_ge; lia.
Qed.
Lemma apartW_sub : ltac2:(tb__ "0|4|
S58Q40M0A1M1G1S15G1G1A2M2G2S47S59G0S1dG1G1R2A3A2S59G0R4A2M3A2S47S48S59G0R5A2G3A2S48S59G0S1dG1G1R3A3A2S59G0S1eG1G1R3A3A2A2A2Sb9R4R3A2Sb9S18G1G1R7R6A4R4A2F_;F_;F_;Fe';Fe;Fn;Fa;").
Proof. intros a n e e' H1 H2 [X|X]; unfold apartW in *; cbn [fst snd] in *; [left|right]; lia. Qed.

Lemma maps_disjoint_pick : ltac2:(tb__ "0|4|
S11S15S58Q40A1M0G0A2M1A1M2G2G1G2SbaS16G1R4S16G1R3S14G1R2R1A3A3A3A1S1G1S94G1R1R6A3Sb9R5R2A2M3F_;Fe';G1S94G1R1S16G1R5R3A3A3G3F_;Fe';A2F_;Fl2;Fe;Fl1;FR;").
Proof.
  intros R l1 e l2 H. unfold maps_disjoint in H.
  apply ranges_apart_app in H as (_ & H12 & XR). apply ranges_apart_app in H12 as (_ & H2 & X1). cbn in H2. destruct H2 as [F2 _].
  split.
  - intros e' He'. apply apartW_sym. apply (XR e' e He'). apply in_or_app. right. left. reflexivity.
  - intros e' He'. apply in_app_or in He' as [He'|He'].
    + apply apartW_sym. apply (X1 e' e He'). left. reflexivity.
    + exact (proj1 (Forall_forall _ _) F2 e' He').
Qed.

Lemma ens_model : ltac2:(tb__ "0|7|
S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1S60G1G1VJG;VAX;RaR9R8R7R6R5R4R3A9S8RbA1SdS47ScR1A1S59G0R4A2M2A2S47S48S59G0R5A2M3G2A2S48ScR2A1S7bA2A2S1S0S12S66S65S62R7A1M4A1R6R5A3S13A3S1S0S12S68S64G4A1M5R6R5A3S13A3S47SbfG5S59G0R6A2M6S48G6G3A2A3G3A2A2A2F_;F_;TG;F_;Fn0;Fa0;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md a0 n0 HJ G H1 H2.
  destruct HJ as (Hagr & Ha & HA & _). pose proof HA as (_ & _ & _ & _ & HM & _).
  destruct HM as (VG & _ & _ & _ & _ & _ & _ & LI). destruct VG as (_ & _ & _ & _ & _ & _ & N7 & _). destruct LI as (_ & _ & L3 & _).
  rewrite AXg in N7. cbn [aa_geom bumpV] in N7. fold G in N7. destruct N7 as (e & He & B1 & B2).
  destruct (in_split _ _ He) as (l1 & l2 & EM). rewrite EM in L3.
  destruct (maps_disjoint_pick _ _ _ _ L3) as [XR XM].
  assert (SUB : forall e', apartW e e' -> apartW (a0, n0) e') by (intros e' X; apply (apartW_sub a0 n0 e e'); [lia | lia | exact X]).
  split; [apply region_free_of_apart; intros e' He'; apply SUB; exact (XR e' He')|].
  split.
  - unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; lia.
  - rewrite EM. apply overlap_sum_split_le. apply region_free_of_apart. intros e' He'. apply SUB. exact (XM e' He').
Qed.

Lemma pieces12_off : ltac2:(tb__ "0|2|
S7S7F_;S7S5bS22S58Q40A1M0S22S11G0A1S11S61A1S60S5S5VJG;RbRaR9R8R7R6R5R4R3A9S4S47R2S7dA2S47S7cR3A2A2S11S23A1S0S11S15S15S24S24A2S24A2M1A1S75S23G1S73R1A4S75S23G1S73S14S23S88Vnx;A1S14S23S87Vnx;A1S17S23A1A3A3A4A3S74S23S23S33S31RbR1A2S18S5S5R7R6A4A2Lo;R2A3F_;Fl;F_;F_;Fh2;Flo;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md lo h2 HJ HB l EE.
  destruct l as [|o2 [|o1 [|? ?]]]; try discriminate EE.
  assert (E2 : skel o2 = skel (O_2 nx)) by (cbn in EE; congruence).
  assert (E1 : skel o1 = skel (O_1 nx)) by (cbn in EE; congruence).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EB1 & EL1 & _).
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & TOP & ENS & _ & _ & R8B). cbn zeta in HN, SMB, AL, IMG, TOP, ENS, R8B.
  pose proof (urange a) as Ra.
  assert (SHB : SHADOW_BAND_LO <= Sh (bv_unsigned a) /\ Sh (bv_unsigned a) + secmapsize (bv_unsigned (rw rho 12%positive)) / 8 <= SHADOW_BAND_HI).
  { unfold PG in AL.
    set (ua := bv_unsigned a) in *. set (MS := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
    pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. rewrite AL, Z.add_0_r in X.
    assert (E : Sh ua + MS / 8 = (ua + MS) / 8 + SHADOW_OFF).
    { unfold Sh. rewrite X at 2. replace (4096 * (ua / 4096) + MS) with ((512 * (ua / 4096)) * 8 + MS) by lia. rewrite Z.div_add_l by lia.
      rewrite X at 1. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    rewrite E. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *.
    pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (ua + MS) 140737479966720 8 ltac:(lia) TOP) as D. cbn in D. clear -H D. lia. }
  assert (V8 : secneeded (bv_unsigned (rw rho 12%positive)) / 8 >= 0) by (apply Z.le_ge; apply Z.div_pos; [rewrite ENS; clear -R8B HN; lia | lia]).
  pose proof (Z.div_le_mono 73728 (secmapsize (bv_unsigned (rw rho 12%positive))) 8 ltac:(lia) ltac:(clear -SMB; lia)) as D8. cbn in D8.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - rewrite (obj_range_skel r o2 (O_2 nx) E2). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite soff_lit_small by lia. replace (soff r L2) with (bv_unsigned (eval r L2)) by (unfold soff; rewrite signed_small; [reflexivity | rewrite EL2; clear -BL2; lia]).
    rewrite EB2, EL2. unfold ranges_disjoint. cbn [fst snd]. clear -HB SHB BL2 V8. destruct HB; [right; right; right | right; right; left]; lia.
  - rewrite (obj_range_skel r o1 (O_1 nx) E1). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
    unfold ranges_disjoint. cbn [fst snd]. clear -HB SHB D8. destruct HB; [right; right; right | right; right; left]; lia.
Qed.

Lemma ens_oblig : ltac2:(tb__ "0|c|
S7S5bS22S58Q40M0A1M1S22S11G1A1S91VW;Vst;A2S5cR6A1S49S48S4aS1aSbS9R8A1A2A1Z1A2S4bZ2Z14A2A2S11S61A1M2S9fS60Sb8Vsegs;R8R7VCS3;S18G2Sb3R3Sb4R2R1A2A4A5VJG;VAX;RdRcRbRaR9R8R4R2A9S2cRaS83A2G1S59G0R1A2M3S5Z20000S5S1S0S5S4cR2Z1000A2Z0M4A3S1S49G4R2A2S1S47S48R2R1A2M5S63S62R6A1M6A1A2S1S0S12S66S65G6A1R3S5aG0R1A2M7A3S13A3S1S0S12S68S64G6A1M8R3G7A3S13A3S1S47SbfG8R2G5A3R1A2S1S53Sc2R6RcA2R1A2S1S23S94S23R1S27S40VCS3;A1A1A3S33S31RfR2A2S18S5S5R4S48R4R3A2A4A2F_;Fo;S1G1S1S47R3G3A2S49G3S48R3R2A2A2A2S0S12S3dVsegs;R2A2S20A3F_;Fx;S1S15S24S24A2M9S5S94G9R2S44VCS3;A1A3S1S47S59G0S2cR10S1dS24S24R3A3A2A2MaR2A2S49R2S48GaS59G0S2cR10S1eS24S24R3A3A2A2A2A2A2S3S1S47R6S59G0S46S59G0S2cR11S45VCS3;A1A2A2R3A2A2MbA2S49GbS48R6R5A2A2A2A1F_;F_;Fy;Frr;S99R11R10RfReRdRcR8S6cR2G5S6dSc5G6R3G7A3R6A2A3A8A2A2A2A2A2A2A2A2A2A2Tnlit;Tua;Ta0;F_;F_;Fmd;Fms;Ftr;F_;F_;F_;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp HW HKc Hok tr ms md Hsp HJ a0 ua nlit.
  destruct (pending_parts CS3 rhoX tp tr ms md Hsp) as [HFall HallX].
  assert (HF : Forall (holds rhoX) ([SPBranch BC_EQ (SVar V_NCH) (SVar V_NRES)] ++ F_g3)).
  { apply Forall_forall. intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (FCS3 p Hp)). }
  apply Forall_app in HF as [HB HF]. apply Forall_inv in HB.
  pose proof (ens_site AX A Kc rho a rhoX tp tr md AXg AXs AXp HJ HB HF) as (HcN & HcR & _ & EBw & PB4 & P1 & PT & C0). cbn zeta in HcN, HcR, EBw, PB4, P1, PT, C0.
  pose proof (JG_sec_nums AX A Kc rho a rhoX tp tr md AXg AXs AXp HJ) as (_ & _ & _ & PBND & P4 & _). cbn zeta in PBND, P4.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  assert (Eua : ua = ag_pab (aa_geom A) + aa_ptr_committed A) by (unfold ua, a0; exact EBw).
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (unfold nlit; apply u64_lit; lia).
  unfold kPtrArrayCommit, kPtrArrayReserve in *.
  destruct (ens_model A Kc rho a rhoX tp tr md a0 (Z_to_bv 64 nlit) HJ ltac:(fold ua; rewrite Eua; lia) ltac:(fold ua; rewrite Un, Eua; unfold kPtrArrayReserve, nlit; lia)) as (RF & MC & OV).
  fold ua in OV. rewrite Un in OV.
  split; [rewrite Eua; exact PB4|]. split; [rewrite Eua; unfold IMG_HI in P1; lia|]. split; [rewrite Eua; unfold nlit; lia|].
  split; [exact RF|]. split; [exact MC|]. split; [exact OV|].
  split.
  { destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HBud).
    pose proof (ensure_headroom _ rhoX tp md HA ltac:(rewrite AXs, AXp; exact HcN)) as HR. unfold kPtrArrayCommit in HR. unfold nlit. apply HR.
    rewrite AXb. unfold budget_bound. unfold budget_ok_alloc, limit_ok_alloc in HBud. cbn [aa_V aa_Km aa_Kf bumpV]. unfold BETA_M in *. clear -HBud. lia. }
  split.
  { intros o Ho. revert o Ho. apply Forall_forall.
    apply (pab_piece_disjoint CS3 [O_2 nx; O_1 nx] [] A Kc rho a rhoX tp tr md _ ua (ua + nlit) HW HJ HFall HallX SK3 FC3);
      [rewrite Eua; lia | rewrite Eua; unfold nlit, kPtrArrayReserve; clear -HcR C0; lia | | intros [|? ?] EE; [constructor | discriminate EE]].
    apply (pieces12_off AX A Kc rho a rhoX tp tr md). { exact HJ. } rewrite Eua. unfold nlit. clear -PBND HcR C0. lia. }
  split.
  { intros x Hx. unfold ro_addr. rewrite find_segment_A_off; [reflexivity|]. rewrite Eua in Hx. unfold IMG_HI in P1. clear -Hx P1 C0. lia. }
  split; [intros rr y Hin; rewrite XC3 in Hin; destruct Hin|].

  exists md. split; [exact HJ|]. split; [exact HB|]. split; [exact HF|].
  rewrite !m_vmmaps_vm_forget_range, !m_vmmaps_with_vmmaps, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  fold ua. rewrite <- Eua. replace (ua + 131072) with (ua + nlit) by reflexivity.
  split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [mmap_fixed_rw_next vm_noaccess]; fold ua; rewrite Un; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  pose proof (MI_ivs_wf segs _ _ HMI) as (Wm & Wn & Wl).
  split; [exact Wn|]. split; [exact Wl|].
  split.
  {
    set (h' := mmap_fixed_rw_next (m_vmmaps md) a0 (Z_to_bv 64 nlit)). set (md1 := with_vmmaps h' md).
    assert (Hwf1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact Wl).
    pose proof (used_commit_le md h' a0 (Z_to_bv 64 nlit) (conj Wm (conj Wn Wl)) eq_refl eq_refl) as PU1. fold md1 in PU1. fold ua in PU1. rewrite Un in PU1.
    pose proof (unpaid_forget_le md1 ua (ua + nlit) tp Hwf1 (MI_nodupT segs _ _ HMI)) as PU2. apply Nat2Z.inj_le in PU2.
    assert (PU3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite PU3 in PU2.
    unfold paid. pose proof page_size_pos. unfold kPtrArrayCommit. clear -PU1 PU2 OV H. nia. }

  destruct HJ as (_ & _ & _ & _ & HK & _). unfold vm_forget_range. rewrite with_vm_backing_with_vm. apply HKc.
  match goal with |- Kc _ (with_vmmaps ?h ?m) =>
    replace (with_vmmaps h m) with (with_vm (mkVmState h (m_vm_lazy m) (m_vm_materialized m)) m) by (destruct m; reflexivity) end.
  apply HKc. exact HK.
Qed.

Lemma OG3 : ltac2:(tb__ "0|0|
S0S11S23A1S27S40VG3;A1A1S16S23S27S40VCS3;A1A1S14S23S89S17S23A1A3A3A3").
Proof. rewrite <- HG3. reflexivity. Qed.
Lemma XG3 : ax_X G3 = [].
Proof. rewrite <- HG3. cbn. exact XC3. Qed.
Lemma OSECI : ltac2:(tb__ "0|0|
S2S23S23S1S94S23R1S27S40VCS3;A1A1A3S0S15S15S24S24A2S24A2S73R1A1S73SaeA1A3A2Lo;A2").
Proof.
  assert (IN : In (skel O_seci) (map skel (ss_objs (ax_S CS3)))).
  { rewrite SK3. rewrite !map_app. apply in_or_app. right. apply in_or_app. left. unfold SKEL0. rewrite !map_app.
    apply in_or_app. left. apply in_or_app. right. unfold RT_sec, N_sec, O_seci. cbn. left. reflexivity. }
  apply in_map_iff in IN as (o & Ho & Hin). exists o. split; [exact Hin | exact Ho].
Qed.

Lemma range_seci : ltac2:(tb__ "0|0|
S22S0S15S5S5A2S31R1SaeA2S18S5S5S96S48S96Z40A2A4A3Fr;").
Proof.
  intros r. unfold O_seci, RT_sec, N_sec. cbn -[carve_obj SEC_INST Z.add].
  rewrite (carve_range r _ (proj1 (Forall_forall _ _) N_sec_small _ ltac:(unfold N_sec; left; reflexivity))).
  unfold spec_range. cbn [fst snd eval]. rewrite u64_lit by lia. f_equal; lia.
Qed.

Lemma ensure_post : ltac2:(tb__ "0|5|
S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1M2S9fS60S91VW;Vst;A2S59G0S2fR8PcA2A2S5S59G0R8A2S5Sb2R2A1S5S5S1S47S7eR3A1M3R1A2S49R1S48G3S4eR2Z8A2A2A2A2S3S0S19S58Q8A1M4A1S2dRdS5aG0R2A2A2S1cG4A1A3A1F_;Fz;S6eVsegs;S99ReRdRcRbA4VG3;RaR9S18G2Sb3R8Sb4R7R6A2A4A6S2S22S22S2S22S22S1S97S8R11A1R6R5RfR1A5S6eVsegs;VJG;S98R11R10R1ReA5VG3;R2RcS18G2Sb3RbSb4RaR9A2A4A6A2Lrho'';A2Lr2;A2F_;F_;TL;Tua;Tnv;F_;Fmd';Fms;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr ms md' HW nv ua L RUNDEF Hsp.
  pose proof (proj2 Hsp) as HJo. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJo.
  destruct HJo as (md0 & HJ & HB & HF & EM & ER & EN & EL & ELIM & ETOP & WN & WL & HPAID & HK').
  pose proof (ens_site AX A Kc rho a r tp tr md0 AXg AXs AXp HJ HB HF) as (HcN & HcR & _ & EBw & PB4 & P1 & PT & C0). cbn zeta in HcN, HcR, EBw, PB4, P1, PT, C0.
  pose proof (JG_sec_nums AX A Kc rho a r tp tr md0 AXg AXs AXp HJ) as (_ & P2 & _). cbn zeta in P2. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (JGs_rigidS nW st tmax nx Hnx AX A Kc rho a r tp tr md0 HJ) as (E12 & Enx & _ & _ & _ & _ & _ & _ & _ & _ & Erm & Erl).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *. set (PB := ag_pab G + c) in *.
  set (v := (c + kPtrArrayCommit) / 8).
  set (r2 := rho_absorb r R_ens (msOf (ens_mem v) ms)).
  set (rho'' := mkVal (rw rho) (rl rho) (rm r2)).

  assert (RN : obj_range r O_nres = (SEC_INST + 48, SEC_INST + 56)).
  { unfold O_nres. rewrite obj_range_mk by (unfold SEC_INST; lia). cbn [eval fst snd]. rewrite u64_lit by (unfold SEC_INST; lia). unfold SEC_INST. reflexivity. }
  assert (RB : obj_range r O_blk = (PB, PB + kPtrArrayCommit)).
  { unfold O_blk. rewrite obj_range_mk by (unfold kPtrArrayCommit; lia). rewrite EBw. fold PB. unfold kPtrArrayCommit. f_equal; lia. }
  assert (INR : forall x, in_ranges r R_ens x -> (SEC_INST + 48 <= bv_unsigned x < SEC_INST + 56) \/ (PB <= bv_unsigned x < PB + kPtrArrayCommit)).
  { intros x (o & [<-|[<-|[]]] & Hr); [rewrite RN in Hr | rewrite RB in Hr]; cbn [fst snd] in Hr; [left | right]; exact Hr. }
  assert (RM2 : forall x, rm r2 x = if in_ranges_dec r R_ens x then ens_mem v x else rm r x) by (intros x; reflexivity).
  assert (RMout : forall x, ~ in_ranges r R_ens x -> rm r2 x = rm r x).
  { intros x Hx. rewrite RM2. destruct (in_ranges_dec r R_ens x) as [i|n]; [exfalso; exact (Hx i) | reflexivity]. }
  assert (RMin : forall x, in_ranges r R_ens x -> rm r2 x = ens_mem v x).
  { intros x Hx. rewrite RM2. destruct (in_ranges_dec r R_ens x) as [i|n]; [reflexivity | exfalso; exact (n Hx)]. }
  assert (INnres : forall z, SEC_INST + 48 <= z < SEC_INST + 56 -> in_ranges r R_ens (Z_to_bv 64 z)).
  { intros z Hz. exists O_nres. split; [left; reflexivity|]. rewrite RN. cbn [fst snd]. rewrite u64_lit by (unfold SEC_INST in *; lia). exact Hz. }
  assert (INblk : forall z, PB <= z < PB + kPtrArrayCommit -> in_ranges r R_ens (Z_to_bv 64 z)).
  { intros z Hz. exists O_blk. split; [right; left; reflexivity|]. rewrite RB. cbn [fst snd].
    rewrite u64_lit by (unfold PB, IMG_HI, kPtrArrayCommit, kPtrArrayReserve in *; clear -Hz P1 P2 TG C0 HcR; lia). exact Hz. }
  exists r2, rho''. split.
  {
    split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    - intros x. cbn [rho'' rm]. destruct (in_ranges_dec r R_ens x) as [i|n].
      + right; right; right. unfold rtint. fold G. destruct (INR x i) as [X|X]; [left; clear -X; lia | right]. unfold PB in X. clear -X C0 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
      + left. rewrite (RMout x n). rewrite <- (Erm x). reflexivity.
    - intros z Hz. cbn [rho'' rm]. destruct (in_ranges_dec r R_ens (Z_to_bv 64 z)) as [i|n].
      + rewrite (RMin _ i). unfold ens_mem. destruct (_ && _); discriminate.
      + rewrite (RMout _ n), (Erm (Z_to_bv 64 z)). cbn [rhoM_of rho_sets rm]. exact (RUNDEF z Hz). }

  apply (SPA_absorb_any segs (JGo A Kc rho a) (JG AXP A Kc rho'' a) r G3 R_ens (msOf (ens_mem v) ms) tp (tr, mkCfg ms md') XG3).
  { intros o x Ho Hx. rewrite OG3.
    destruct Ho as [<-|[<-|[]]].
    - destruct OSECI as (o' & Ho' & Es). exists o'. split; [apply in_or_app; left; exact Ho'|].
      rewrite (obj_range_skel r o' O_seci Es), range_seci. rewrite RN in Hx. cbn [fst snd] in Hx |- *. clear -Hx. unfold SEC_INST in *. lia.
    - exists O_blk. split; [apply in_or_app; right; left; reflexivity | exact Hx]. }
  { exact Hsp. }

  cbn [w_tr w_cfg cfg_model cfg_ms fst snd]. fold r2.
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HBud).
  unfold JG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGs. cbn [rw rho'']. fold nv.
  split.
  { destruct Hagr as (A1 & A2 & A3). split; [|split].
    - intros i Hi. transitivity (rw (rhoM_of A rho) i); [reflexivity|]. rewrite (A1 i Hi). reflexivity.
    - intros l. transitivity (rl (rhoM_of A rho) l); [reflexivity|]. rewrite (A2 l). reflexivity.
    - intros x. reflexivity. }
  split; [exact Ha|].
  split.
  {
    unfold AXP. apply (AInvA_ensure (AX (bumpV A nv)) r r2 tp md0 md'); rewrite ?AXg, ?AXs, ?AXp; cbn [aa_geom aa_sec aa_ptr_committed bumpV]; fold G c PB.
    - exact HA. - exact HcN. - exact HcR. - exact EM. - exact ER. - exact EN. - exact EL. - exact ELIM. - exact ETOP. - exact WN. - exact WL. - exact HPAID.
    - intros z Hz. apply view_agree. intros Rz. apply RMout. intros i. apply Hz. unfold zens. rewrite ?AXg, ?AXp. cbn [aa_geom aa_ptr_committed bumpV]. fold G c PB.
      destruct (INR _ i) as [X|X]; rewrite u64_lit in X by exact Rz; [left | right]; exact X.
    - intros k Hk. cbn [c_addr c_w RtCells.c_val]. cbn [c_w] in Hk.
      rewrite view_in by (unfold SEC_INST; lia). unfold rd_of. rewrite (RMin _ (INnres (SEC_INST + 48 + Z.of_nat k) ltac:(clear -Hk; lia))).
      unfold ens_mem. rewrite u64_lit by (unfold SEC_INST; lia).
      replace ((SEC_INST + 48 <=? SEC_INST + 48 + Z.of_nat k) && (SEC_INST + 48 + Z.of_nat k <? SEC_INST + 56)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (SEC_INST + 48 + Z.of_nat k - (SEC_INST + 48)) with (Z.of_nat k) by lia. rewrite Nat2Z.id. reflexivity.
    - intros z Hz. rewrite view_in by (unfold PB, IMG_HI, kPtrArrayCommit, kPtrArrayReserve in *; clear -Hz P1 P2 TG C0 HcR; lia). unfold rd_of.
      rewrite (RMin _ (INblk _ Hz)). unfold ens_mem. destruct (_ && _); eexists; reflexivity. }
  split; [unfold pendS in HP |- *; rewrite EM; exact HP|].
  split; [exact HK'|].
  split; [exact Htp|].
  split; [apply (stopJ_rwrl nW st tmax nx Hnx r r2); [intros i; reflexivity | intros l; reflexivity | exact HU]|].
  split; [exact HN|]. split; [exact Htop | exact HBud].
Qed.

Lemma site_b : ltac2:(tb__ "0|5|
S7S7Fx;S7S5bS22S58Q40M0A1M1S22S11G1A1S11S61A1S60S7S0SdS8RaR1A1A1S8R1A1A3FX;S7S0S11SbA1S9RbR1A1A1S9R1A1A3FX;S7S0S5SaRcR1A1A1SaR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S2aR8S36S30Sa8S28SacA1S28SadA1A3A1A2S8RdA1SdSaReA1S5S48ScR2A1S4fZ8M2S4aS1aSbS9RfA1A2A1A2A2S5S1S0S5S59G0S2cRcS83A2A2R1A3S1S47ScR3A1M3R1A2S1S47S48R1G2A2S48G3R2A2A2S1S47R2S7bA2S1S47S80G3A2S1S4S47S48G3S7bA2S7dA2S47S7cG3A2A2S5S1S47R2R1A2S49R1S48R2G2A2A2A2S2S58Q8A1M4G4S0S19G4A1Sc3S92S2dRfA1R3A3S1bG4R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2Tlo;Tc;TG;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HBR.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  pose proof (JG_sec_nums BX A Kc rho a r tp tr md BXg BXs BXp HJ) as (P1 & P2 & P3 & P4 & P5 & P6 & GT & TOP & TL).
  cbn zeta in P1, P2, P3, P4, P5, P6, GT, TOP, TL |- *.
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  cbn [holds eval] in HBR. rewrite E147, E146 in HBR. fold c in HBR.
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(lia) ltac:(lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HBR by lia. rewrite Z.eqb_eq in HBR.
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite P6, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  assert (LT : 8 * Z.of_nat (length (aa_sec A)) + 8 <= c) by (clear -HBR X8 P5; lia).
  assert (EBw : bv_unsigned (eval r Bw) = ag_pab G + 8 * Z.of_nat (length (aa_sec A))).
  { unfold Bw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G. rewrite !u64_lit by lia.
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by lia. rewrite Z.mod_small by lia. lia. }
  split; [exact EBw|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact P4|].
  intros z Hz. apply TL. lia.
Qed.

Lemma carve_w : ltac2:(tb__ "0|1|
S7S5bS22S58Q40A1M0S22S11G0A1S78S91VW;Vst;A2S6eVsegs;VJG;VAX;R8R7R6R5A5VL3b;R4R3R2A6S6eVsegs;VJG;VAX;R9R8R7R6A5VCO3b;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp w HW Hsp. destruct w as [tr [ms md]]. pose proof WCOb as WCO'. rewrite <- HCOb in WCO' |- *. unfold carveS, O_w in WCO' |- *.
  destruct (SPA_parts _ _ _ _ _ _ _ Hsp) as (HFall & HallX & HJ).
  pose proof (proj1 (Forall_forall _ _) HFall _ (FXb _ (or_introl eq_refl))) as HBR.
  destruct (site_b AX A Kc rho a r tp tr md AXg AXs AXp HJ HBR) as (EBw & B1 & B2 & B3 & B4 & B5 & TL). cbn zeta in EBw, B1, B2, B3, B4, B5, TL.
  set (lo := ag_pab (aa_geom A) + 8 * Z.of_nat (length (aa_sec A))) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  pose proof (JG_sec_nums AX A Kc rho a r tp tr md AXg AXs AXp HJ) as (_ & P2 & _). cbn zeta in P2.
  assert (SO0 : soff r (SLit 0) = 0) by (apply soff_lit_small; lia).
  assert (SO8 : soff r (SLit 8) = 8) by (apply soff_lit_small; lia).
  assert (NUM : 0 <= lo /\ lo + 8 <= 2 ^ 64 /\ lo + 8 <= ag_pab (aa_geom A) + kPtrArrayReserve /\ (lo + 8 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= lo)).
  { unfold IMG_HI, kPtrArrayReserve in *. clear -B1 B2 B3 B4 B5 P2 TG. lia. }
  destruct NUM as (N1 & N2 & N3 & N4).
  eapply (SPA_carve_unk segs (JG AX A Kc rho a) r L3b tp _ Bw (SLit 0) (SLit 8) (ss_next (ax_S L3b)) Hsp WCO' (Pos.le_refl _));
    rewrite ?SO0, ?SO8, ?EBw.
  - lia.
  - lia.
  - clear -N1. lia.
  - clear -N2. lia.
  - rewrite Z.add_0_r. apply (pab_piece_disjoint L3b [O_2 nx; O_1 nx] [] A Kc rho a r tp tr md _ lo (lo + 8) HW HJ HFall HallX SKb FCb);
      [exact B1 | exact N3 | | intros [|? ?] EE; [constructor | discriminate EE]].
    apply (pieces12_off AX A Kc rho a r tp tr md); [exact HJ | exact N4].
  - intros z Hz. rewrite Z.add_0_r in Hz. destruct (TL z Hz) as [b Hb].
    assert (Uz : 0 <= z < 2 ^ 64) by (clear -Hz N1 N2; lia).
    rewrite view_in in Hb by exact Uz. unfold wok_of. unfold rd_of in Hb |- *.
    destruct (rm r (Z_to_bv 64 z)) as [x|] eqn:E; [split; [reflexivity | exists x; reflexivity]|].
    exfalso. rewrite image_byte_none_A in Hb by (rewrite u64_lit by exact Uz; unfold IMG_HI in *; clear -Hz B1 B4; lia). discriminate Hb.
  - intros rr y j Hin. rewrite XCb in Hin. destruct Hin.
Qed.

Lemma path_b : ltac2:(tb__ "0|2|
S78OF_;S7S5bS22S58Q40A1M0S7aS91VW;Vst;A2Sb1VW;Vst;A2S5cR6A1S70Vsegs;R9S6fR7A1A3S22S11G0A1M1S79Vsegs;RcS6eVsegs;VJG;VAX;RbRaR9R8A5VT4b;R2R1A5R7A4FtY;FrY;S22G1S79Vsegs;RdS6eVsegs;VJG;VAX;RcRbRaR9A5VX3b;R2R1A5R8A4Ftp;Fr;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl HCb r tp.
  pose proof (JG_okf AX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable AX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (carve_w A Kc rho a _ tp w HW (gen_x11 AX A Kc rho a X3b L3b sLb r tp w HUS HKc ELb IDb GLb FBLb HL3b Hw)) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x3c614] GS [CO3b] [Y4b0; Y4b1] (JG AX A Kc rho a) ok Q tp Hokf HST Cert4b); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact (join4 AX A Kc rho a Y4b0 T4b s4b0 rE tp w HUS HKc E4b0 I4b0 Hw) | intros w Hw; right; exact Hw | apply HCb].
  - eapply triple_conseq; [intros w Hw; exact (join4 AX A Kc rho a Y4b1 T4b s4b1 rE tp w HUS HKc E4b1 I4b1 Hw) | intros w Hw; right; exact Hw | apply HCb].
Qed.

Lemma path_a : ltac2:(tb__ "0|5|
S78OF_;S7S5bS22S58Q40M0A1M1S7aS91VW;Vst;A2Sb1VW;Vst;A2S5cR6A1S70Vsegs;R9S6fR7A1A3Sb7Vsegs;RaS6fR8A1A3S49S48S4aS1aSbS9RaA1A2A1Z1A2S4bZ2Z14A2A2S59G0S2fR9PcA2A2S5S59G0R9A2S5Sb2R2A1S5S5S1S47S7eR3A1M2R1A2S49R1S48G2S4eR2Z8A2A2A2A2S3S0S19S58Q8A1M3A1S2dReS5aG0R2A2A2S1cG3A1A3A1F_;Fz;S22S22S11G1A1M4S97S8R12A1R6R5R10R3A5S79Vsegs;R14S6eVsegs;VJG;S98R13R12R4R10A5VT4a;R3R2A5RfA4F_;FtY;FrY;Frho'';S22G4S79Vsegs;R13S6eVsegs;VJG;VAX;R12R11R10RfA5VX3a;R2R1A5ReA4Ftp;Fr;F_;F_;TL;Tua;Tnv;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hok nv ua L RUNDEF HCa r tp.
  pose proof (JG_okf AX ok A Kc rho a Hokl) as Hokf. pose proof (JG_okp AX ok A Kc rho a Hokpl) as Hokp. pose proof (JG_stable AX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RS3 A Kc rho a r tp w Hw) | intros w Hw; exact Hw |].
  assert (HST' : stableA segs (ss_next (ax_S CS3)) (JG AX A Kc rho a)).
  { eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NXS3. }
  apply triple1_triple. eapply triple1_seq_l.
  { apply (triple1_fixed_commitA segs ok (JG AX A Kc rho a) (JGo A Kc rho a) CS3 r tp Bw 131072 Hokf Hokp HST' IC3 R17 R10 BBw R11 R12 R13 R14 R15 eq_refl ltac:(lia)).
    exact (ens_oblig A Kc rho a r tp HW HKc Hok). }
  fold O_blk. rewrite HG3.
  apply (triple_conseq (P:=fun w => exists r2 rho'', slink4 (aa_geom A) ua L rho rho'' /\ SPA segs (JG AXP A Kc rho'' a) G3 r2 tp w) (SPA segs (JGo A Kc rho a) G3 r tp) (Q:=Q));
    [intros w Hw; destruct w as [tr [ms md]]; exact (ensure_post A Kc rho a r tp tr ms md HW RUNDEF Hw) | intros w Hw; exact Hw |].
  apply triple_ex; intros r2. apply triple_ex; intros rho''.
  apply (triple_pre_pure segs ok _ _ (slink4 (aa_geom A) ua L rho rho'')); [intros w [SL _]; exact SL|]. intros SL.
  eapply triple_conseq; [intros w [_ Hw]; exact Hw | intros w Hw; exact Hw |].
  pose proof (JG_okf AXP ok A Kc rho'' a Hokl) as Hokf2. pose proof (JG_stable AXP A Kc rho'' a HUS HKc) as HST2.
  apply (cfg_soundA segs 4000%nat [0x410f0] GS [G3] [X3a3] (JG AXP A Kc rho'' a) ok Q tp Hokf2 HST2 Cert3a); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (gen_x11 AXP A Kc rho'' a X3a3 L3a sLa rE tp w HUS HKc ELa IDa GLa FBLa HL3a Hw) | intros w Hw; right; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x3c614] GS [L3a] [Y4a0; Y4a1] (JG AXP A Kc rho'' a) ok Q tp Hokf2 HST2 Cert4a); [|left; reflexivity].
  intros E' rE' HinE'. destruct HinE' as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact (join4 AXP A Kc rho'' a Y4a0 T4a s4a0 rE' tp w HUS HKc E4a0 I4a0 Hw) | intros w Hw; right; exact Hw | apply HCa; exact SL].
  - eapply triple_conseq; [intros w Hw; exact (join4 AXP A Kc rho'' a Y4a1 T4a s4a1 rE' tp w HUS HKc E4a1 I4a1 Hw) | intros w Hw; right; exact Hw | apply HCa; exact SL].
Qed.

Theorem sec_g3 : ltac2:(tb__ "0|5|
S78OF_;S7S5bS22S58Q40M0A1M1S7aS91VW;Vst;A2Sb1VW;Vst;A2S5cR6A1S70Vsegs;R9S6fR7A1A3Sb7Vsegs;RaS6fR8A1A3S49S48S4aS1aSbS9RaA1A2A1Z1A2S4bZ2Z14A2A2S59G0S2fR9PcA2A2S5S59G0R9A2S5Sb2R2A1S5S5S1S47S7eR3A1M2R1A2S49R1S48G2S4eR2Z8A2A2A2A2S3S0S19S58Q8A1M3A1S2dReS5aG0R2A2A2S1cG3A1A3A1F_;Fz;S22S22S11G1A1M4S97S8R12A1R6R5R10R3A5S79Vsegs;R14S6eVsegs;VJG;S98R13R12R4R10A5VT4a;R3R2A5RfA4F_;FtY;FrY;Frho'';S22G4S79Vsegs;R13S6eVsegs;VJG;VAX;R12R11R10RfA5VT4b;R2R1A5ReA4FtY;FrY;S22G4S79Vsegs;R14S6eVsegs;VJG;VAX;R13R12R11R10A5VD2;R2R1A5RfA4FtX;FrX;F_;F_;F_;TL;Tua;Tnv;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hok nv ua L RUNDEF HCa HCb rX tX.
  pose proof (JG_okf AX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable AX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU A Kc rho a rX tX w Hok Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x706a0; 0x410f0] GS [U2] [X3a; X3b] (JG AX A Kc rho a) ok Q tX Hokf HST Cert3); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (path_a ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hok RUNDEF HCa rE tX).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (path_b ok A Kc rho a Q HW HUS HKc Hokl HCb rE tX).
Qed.
End G3.
End SEC4.

End SpineCallocSec4.

