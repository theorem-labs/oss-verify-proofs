(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2 bw.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall c1.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module SpineMallocSec4IEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S29A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S28A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ7050cS0SbZ40f5cS2SbA1A3A3VGS0;S0S8S9S29Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x7050c; 0x40f5c] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineMallocSec4IW2.run3]); [exact SpineMallocSec4IW2.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ40f5cS2SbA1A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2cG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x40f5c] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineMallocSec4IW2.run3a]); [exact SpineMallocSec4IW2.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S28Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineMallocSec4IW2.run4a]); [exact SpineMallocSec4IW2.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c480S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S31G0G1A3S0S8S9S32G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c480] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineMallocSec4IW2.run4b]); [exact SpineMallocSec4IW2.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

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
Module CDepotCallS.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "pow"; "ltb"; "mul"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "rw"; "SVar"; "SLit"; "sprop"; "ss_next"; "sstate"; "ss_facts"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "cell"; "obj_range"; "ss_objs"; "soff"; "holds"; "sprop_below"; "SAlu"; "SPUle"; "mkObj"; "rl"; "rm"; "DZero"; "SExt"; "c_off"; "eval"; "mkSS"; "ob_cells"; "ob_dflt"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "cons"; "pair"; "true"; "list"; "false"; "prod"; "S"; "nil"; "option"; "andb"; "fst"; "snd"; "orb"; "Some"; "app"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_depot"; "aa_geom"; "DG"; "ag_pab"; "ageom"; "aa_Km"; "ag_ctx"; "ag_thread"; "budget_ok_alloc"; "topG"; "aa_Kf"; "aa_V"; "aa_live"; "depot_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "WI"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "coveredbL"; "hi_lebL"; "lo_gebL"; "T5d"; "call_cellS"; "cov_exact"; "cov_itv"; "havS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"; "nocells"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "lt"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "isSome"; "rstS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS.DCS"; "site_factsS"; "AXK"; "dlink"; "zoneS"; "MAPO"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "JLD"; "DFP"; "JD"; "MAP1"; "MAP1N"; "STORE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP"; "KDP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Lists.ListDef"; "Forall";
"seq"; "firstn"; "skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "omrg"; "osplit"; "lit63"; "oreb"; "F_call"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sitv"; "set_objs"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "bumpK"; "with_depot"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "LIVE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPRET"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition WI : nat := 2.
Definition X5f (X : axst) : axst := ax_add_facts F_call X.
Definition X5r (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|1|
S94S6eVX;A1S38S3dS37S10A2M0S39S37S10UbS15Vsz;A1A4S3fG0A1A3S3fS16A1A3").
Definition X5a (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S62VX;Vsz;A2S61S15Nf10A1A3").
Definition X5b (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6bVX;Vsz;A2S3eS61A1S15N910A1A3").
Definition X5c (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6cVX;Vsz;A2S3eS3eS61A1A1S15N848A1A3").
Definition X5s (X : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sc6S6dVX;Vsz;A2S3eS3eS3eS61A1A1A1S15N50A1A3").

Definition T50 (T X : axst) : axst := ltac2:(tb__ "0|0|
SdeVT;S19S49VX;A1A1A2").
Definition T5a (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S64VT;VX;A2U0A2").
Definition T5b (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc8S65VT;VX;A2U1A2").
Definition permS (n : nat) : list nat := ltac2:(tb__ "0|1|
S46S37S38S37U9S38S37UaS38S37UbS38S37U0S38S37UcS38S37U1S38S37UdS38S37U2S38S37U3S38S37U4S38S37U5S38S37U6S38S37U7S38S37U8S3fS37A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb3UeM0Sd9Vn;G0A2A2A3").
Definition T5c (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|2|
S4cS66VT;VX;A2M0Sd1S49G0A1M1SddS20G1A1S63Vn;A1A2A2A2").
Definition T5m1 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S67Vn;VT;VX;A3S61A2").
Definition T5m2 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S68Vn;VT;VX;A3S61A2").
Definition T5m3 (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S69Vn;VT;VX;A3S61A2").
Definition T5d (n : nat) (T X : axst) : axst := ltac2:(tb__ "0|0|
Sc5S6aVn;VT;VX;A3S61A2").

Definition havS (n : positive) : list (nat * sv) := ltac2:(tb__ "0|1|
S38S3dS37S10A2M0S39S37S10UaS14Vn;A1A4S38G0S39S37S10U1S15Se1A1A4S38G0S39S37S10U5S14S7aVn;P1A2A1A4S38G0S39S37S10U6S14S7aVn;P2A2A1A4S38G0S39S37S10U7S14S7aVn;P3A2A1A4S38G0S39S37S10UbS14S7aVn;P4A2A1A4S38G0S39S37S10UcS14S7aVn;P5A2A1A4S38G0S39S37S10UdS14S7aVn;P6A2A1A4S38G0S39S37S10UeS14S7aVn;P7A2A1A4S38G0S39S37S10UfS14S7aVn;P8A2A1A4S38G0S39S37S10U10S14S7aVn;P9A2A1A4S38G0S39S37S10U11S14S7aVn;PaA2A1A4S38G0S39S37S10U1cS14S7aVn;PbA2A1A4S38G0S39S37S10U1dS14S7aVn;PcA2A1A4S38G0S39S37S10U1eS14S7aVn;PdA2A1A4S38G0S39S37S10U1fS14S7aVn;PeA2A1A4S3fG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition call_cellS (c : cell) : bool := ltac2:(tb__ "0|4|
S10S36Lx;S2bVc;A1S0S41S6Se0Sd2R1A1M0A2S48S41S6N848G0A2S8G0N50A2A2A1A2Lz;S1S3aLi;Sb6S10S10S3aLb;La;M1Lop;M2G2Sb7G1Lop;M3G3S36S2S10S3aLa;Lw;Lsgn;S1S10S0S3aLk;Li;Ll;X10x8").
Definition C5S (X : axst) : axst := ltac2:(tb__ "0|3|
S49VX;A1S18S40S12A1S4aLx;S8aS12S20R1A1S61A3S12S4cVX;S2dZ7eac4SdaS33R2A1S76S17R2A1M0A1A2S31R2A1S30R2A1S34R2A1S46S12Sb4S12S61S20R2A1M1A3S38S12S26S1bR1A1S1dR1A1S1cR1A1SeaS1eS3bS1eA1SecS1eA1S1eSe9S73R1A1M2A1Lc;S1eSebG2A1Lx;S2eR1A1A6S2fR1A1A5Sb5S12S3eS61A1G1A3A3A3S19R2A1S7aG0PfA2S32R2A1A9A2Lo;VX;X40x2TS0;").

Definition lo_gebL (facts : list sprop) (l l' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVl;Vl';A2S3aS10S36Ll;Vl;S0G0Sc7R1A1S40S3dS0S0A2M1A1S36Lx;Sd0Vfacts;Vl';A2G1G1S36Lp;R1S0S0S6R1R4A2Lh';Lz;X3dx1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb6S10S10S3cLb;La;M2Lop;M3G3Sb7G2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll0;X10x8X36x2").
Definition hi_lebL (facts : list sprop) (h h' : sv) : bool := ltac2:(tb__ "0|5|
S36S36L_;M0S1aVh;Vh';A2S3aS10S36Lh;Vh;S0G0Sc7R1A1S40S3dS0S0A2M1A1S36Lx;Sd0Vfacts;Vh';A2G1G1S36Lp;R1S0S0S6R4R2A2Lz;Ll';X3dx1Lp;S3cX40x2S3cX36x2La;S1S3cLi;Sb6S10S10S3cLb;La;M2Lop;M3G3Sb7G2Lop;M4G4S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8X36x2").
Lemma lo_gebL_sound : ltac2:(tb__ "0|0|
S11S3bS16A1S10S10Sb2S16S22R4A1R3A3ScS36S71R4R3R2A3S3aA3S3S21R6R3A2S21R6R4A2A2F_;F_;Fl';Fl;Ffacts;Frho;").
Proof.
  intros rho facts l l' HF H. apply (lo_geb_sound rho facts l l' HF). unfold lo_gebL in H. unfold lo_geb.
  destruct (sv_eqb l l'); [reflexivity|]. cbn [orb]. destruct l; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Lemma hi_lebL_sound : ltac2:(tb__ "0|0|
S11S3bS16A1S10S10Sb2S16S22R4A1R3A3ScS36S70R4R3R2A3S3aA3S3S21R6R4A2S21R6R3A2A2F_;F_;Fh';Fh;Ffacts;Frho;").
Proof.
  intros rho facts h h' HF H. apply (hi_leb_sound rho facts h h' HF). unfold hi_lebL in H. unfold hi_leb.
  destruct (sv_eqb h h'); [reflexivity|]. cbn [orb]. destruct h; try discriminate H. destruct (lit63 z); [exact H | discriminate H].
Qed.
Definition cov_exact (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S1aS1dVo;A1S1dVo';A1A2S1aS1cVo;A1S1cVo';A1A2S3cX36x2S3cX36x2").
Definition cov_itv (facts : list sprop) (o o' : sobj) : bool := ltac2:(tb__ "0|1|
S36S36L_;M0S1aS1bVo;A1S1bVo';A1A2G0S71Vfacts;S1dVo;A1S1dVo';A1A3S70Vfacts;S1cVo;A1S1cVo';A1A3S3cX36x2S3cX36x2").
Definition coveredbL (facts : list sprop) (R objs : list sobj) : bool := ltac2:(tb__ "0|0|
S87S12S12S36S36L_;S88S12S74R1A1Vobjs;A3S3aS88S12S75Vfacts;R1A2Vobjs;A3X36x2Lo;VR;A3").
Lemma coveredbL_sound : ltac2:(tb__ "0|6|
S3bS16A1S3bS12A1M0G0S11S12S4fQ40M1A1Sb2S16S22R3A1R6A3ScS36S6fR7R6R5A3S3aA3S86S12R4R7A3SbS3S42S0S0S1fR6R5A2M2A3S4eG1R4A2M3A2S4G3S43S0S0G2A3A2A2SeS12S12SbS86S12R1R9A3SbS3S42S0S0S1fR8R1A2M4A3S4eG1R6A2M5A2S4G5S43S0S0G4A3A2A2A2Lo';A2F_;F_;F_;F_;Fa;Fo;Frho;Fobjs;FR;Ffacts;").
Proof.
  intros facts R objs rho o a HF H Ho Ha. pose proof (proj1 (forallb_forall _ _) H o Ho) as X. cbn beta in X.
  destruct (existsb (cov_exact o) objs) eqn:EX.
  - apply existsb_exists in EX as (o' & Ho' & E). unfold cov_exact in E.
    destruct (sv_eqb (ob_base o) (ob_base o')) eqn:Eb; [|discriminate E]. destruct (sv_eqb (ob_lo o) (ob_lo o')) eqn:El; [|discriminate E].
    apply sv_eqb_sound in Eb. apply sv_eqb_sound in El. apply sv_eqb_sound in E. exists o'. split; [exact Ho'|].
    unfold obj_range, obj_lo_of, obj_hi_of in Ha |- *. cbn [fst snd] in Ha |- *. rewrite <- Eb, <- El, <- E. exact Ha.
  - apply existsb_exists in X as (o' & Ho' & E). unfold cov_itv in E.
    destruct (sv_eqb (ob_base o) (ob_base o')) eqn:Eb; [|discriminate E]. destruct (lo_gebL facts (ob_lo o) (ob_lo o')) eqn:Hl; [|discriminate E].
    apply sv_eqb_sound in Eb. exists o'. split; [exact Ho'|].
    pose proof (lo_gebL_sound rho facts _ _ HF Hl) as L. pose proof (hi_lebL_sound rho facts _ _ HF E) as Hi.
    unfold obj_range, obj_lo_of, obj_hi_of in Ha |- *. cbn [fst snd] in Ha |- *. rewrite <- Eb. lia.
Qed.

Section DCS.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
ScS1Sd5VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
ScS36S7bSe2Vnx;A2S3aA3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S52ScS57S54VAX;R1A1A1S54R1A1A3FX;").
Hypothesis AXd : ltac2:(tb__ "0|0|
S52ScS60S53VAX;R1A1A1S53R1A1A3FX;").
Hypothesis AXV : ltac2:(tb__ "0|0|
S52ScS0S5eVAX;R1A1A1S5eR1A1A3FX;").
Hypothesis AXKm : ltac2:(tb__ "0|0|
S52ScS0S58VAX;R1A1A1S58R1A1A3FX;").
Hypothesis AXKf : ltac2:(tb__ "0|0|
S52ScS0S5dVAX;R1A1A1S5dR1A1A3FX;").
Hypothesis AXlive : ltac2:(tb__ "0|0|
S52ScS3bS3dS0S0A2A1S5fVAX;R1A1A1S5fR1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Se6VnW;Vst;Vnx;VBX;A4").

Definition AXK (G2 : DG) : AA -> AA := ltac2:(tb__ "0|0|
S52Sd7Sd8VAX;R1A1VG2;A2A1LX;").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Definition dlink (G2 : DG) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|3|
SbS1ScS4fQ40M0A1M1S13Vrho';R1A2S13Vrho;R1A2A3Fi;SbS1ScS3bS4fQ8A1M2A1S27Vrho';R1A2S27Vrho;R1A2A3Fl;G1SfSa5VG2;S4eG0R1A2A2A1ScS40G2A1S28Vrho';R2A2S28Vrho;R2A2A3F_;Fa;A2A2").

Variables (X5 C5 : axst).
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS36S7bVGS;S17S49VX5;A1A1A2S3aA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS36S87S16S23S17S49VX5;A1A1A1Sc9A3S3aA3").
Hypothesis XE5 : ax_X X5 = [].
Hypothesis F192 : ltac2:(tb__ "0|1|
S89S16S38S16S25S15Z1A1S14Pc0A1M0A2S38S16S25G0S15Vtmax;A1A2S3fS16A1A3A3S19S49VX5;A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S89S16S91S8fA1S19S49VX5;A1A1A3").

Hypothesis FUNW : ltac2:(tb__ "0|0|
S89S16S92VW;Vst;A2S19S49VX5;A1A1A3").
Hypothesis WX5r : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S35S49S62VX5;R2A2A1A1S3aA3F_;Fsz;").
Hypothesis DX5r : ltac2:(tb__ "0|4|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S3dS3bS3dS10S10A2M0A1M1S3bS16A1M2A2M3A1SdbS49S6eVX5;A1A1S49S62VX5;R2A2A1A2S45G3S39G1G2S38G0S39S10S10S2aS3cQ20S14Pc0A1A3S15R2A1A4S3fG0A1A3S3fS16A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S62VX5;R2A2A1S61S15Nf10A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6bVX5;R2A2A1S3eS61A1S15N910A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6cVX5;R2A2A1S3eS3eS61A1A1S15N848A1A3A2S3aA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbaS49S6dVX5;R2A2A1S3eS3eS3eS61A1A1A1S15N50A1A3A2S3aA3F_;Fsz;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Let X4 (sz : Z) : axst := X5s X5 sz.
Hypothesis HER : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS40S3bS12A1M0A1Sc4VX4;R2A1S78R2A1Vs4;R2A1A3S45G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS4aSbfVs4;R2A1S78R2A1S77R2A1VX4;R2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS3dS10S10A2M0A1S4bVX4;R2A1A1S3fG0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S16S23S17S49VX4;R2A1A1M0A1A1S19G0A1A3S3aA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36Sc3VX4;R2A1S78R2A1Vs4;R2A1VR4;R2A1S38S4aS77R2A1S3fS4aA1A3A5S3aA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS1S17S49VX4;R2A1A1A1S17S49VX5;A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PaM0A2S24Sb8S14G0A1S15N910A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PfA2S15N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS10SacVs4;R2A1PcA2S24Sb8S14PaA1S15N848A1A3A3F_;Fsz;").

Variable EXo : list sobj.
Definition MAPO : sobj := ltac2:(tb__ "0|0|
S26S14Vnx;A1S15Z0A1S14Sd4A1S3fS1eA1S29A5").
Definition in_fambS (o : sobj) : bool := ltac2:(tb__ "0|4|
S44S44S44ScaVo;A1S88S12S12Se5S79Vo;A1S79R1A1A2Lo';M0S38S12Sa0VEXo;A3A3A2S41S1aS1bVo;A1S14PaA1A2S10S36Lx;S1dVo;A1S0S41S6N910R1A2S6R1Z0A2A2Llo;S1S41S7dR1S8eA2S1aS1cVo;A1S15Nf10A1A2A2Li;Sb6S10S10S3cLb;La;M1Lop;M2G2Sb7G1Lop;M3G3S36S2S10S3cLa;Lw;Lsgn;S1S10S0S3cLk;Li;Ll;X10x8A2A2S88S12G0S90VW;A1A3A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S12Sa1VR4;R2A1A3S3aA3F_;Fsz;").

Hypothesis EX_zone : ltac2:(tb__ "0|3|
S52S8cS11S4fQ40A1M0S11S3bG0A1S98S12S0S7eVsegs;VJG;VAX;R9R8R7R6A5VX5;R5R4R3A6S86S12R3VEXo;A3SbS3S42S0S0S1fR7R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2SdSbS3ScdR4A2S4R4SccA2A2SbS3S56S54RcA1A1M2R4A2S4R4S5G2SceA2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS12A1SbeS49S78R2A1A1S49S77R2A1A1A2S3fS12A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S0ScS3bS3dS10S10A2M0A1S4bS77R1A1A1S3fG0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S87S16S23S17S49VT4;R2A1A1A1A1S19S49VX4;R2A1A1A1A3S3aA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS3bS3dS10S10A2M0A1S4bVT4;R2A1A1S3fG0A1A3F_;Fsz;").
Hypothesis RB1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbbS49S64VT4;R2A1VX4;R2A1A2A1U0A2A2S3aA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18SbbS49S65VT4;R2A1VX4;R2A1A2A1U1A2A2S3aA3F_;Fsz;").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS36SdcS63Vnobj;A1A1S3aA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS36S87S37S37Se8R1Vnobj;A2Li;S63Vnobj;A1A3S3aA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS36S87S37S37S88S37Se7R1A1S63Vnobj;A1A3Li;Sb3U0Vnobj;A2A3S3aA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS37S47S12S20S49S66VT4;R2A1VX4;R2A1A2A1A1A2Vnobj;A3F_;Fsz;").
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S67Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S68Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S69Vnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S93S18Sb9S49S6aVnobj;VT4;R2A1VX4;R2A1A3A1S61A2A2S3aA3F_;Fsz;").
Let T4d (sz : Z) : axst := ltac2:(tb__ "0|0|
S72Vnobj;VT4;Vsz;A1VX4;Vsz;A1A3").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S4dVT4d;R2A1VC5;Vsd;R2A1A3S3aA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36SaeVsd;R2A1VGS;A2S3aA3F_;Fsz;").
Hypothesis R4cov : ltac2:(tb__ "0|1|
S0SbS3Z1R1A2S3R1Vtmax;A2A2ScS36S6fS19S49VT4d;R2A1A1M0A1VR4;R2A1S20G0A1A3S3aA3F_;Fsz;").

Definition zoneS (T C pab ua L top a : Z) : Prop := ltac2:(tb__ "0|1|
SdSbSbS3ScfVa;A2S4Va;ScbA2A2SdS4Va;Sa9A2S3S5Sa7S9Z8Sa8A2A2Va;A2A2A2SdSbS3VT;Va;A2S4Va;S5VT;Z1000M0A2A2A2SdSbS3VC;Va;A2S4Va;S5VC;G0A2A2A2SdSbS3ScdVa;A2S4Va;SccA2A2SdSbS3Vpab;Va;A2S4Va;S5Vpab;SceA2A2A2SdSbS3Vua;Va;A2S4Va;S5Vua;VL;A2A2A2S3Vtop;Va;A2A2A2A2A2A2A2").

Definition site_factsS (A : AA) (rho : valuation) (a : word) (rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|9|
S4eQ40M0S13Vrho;PcA2A2S0S4eG0Va;A2S0S82R2A1S0SbSbS3Z1Vsz;A2S3Vsz;Vtmax;A2A2SbS3S51G0S13VrhoE;S8eA2A2M1SaS8fA1A2SbSe4S54VA;A1M2A1SbScS4fG0A1M3S13VrhoE;Vnx;A2Va;A3SbScG3S13VrhoE;Sd4A2S50G0R1A2A3SbScG3S13VrhoE;P97A2S50G0S5aG2A1A2A3SbScG3S13VrhoE;P98A2S50G0S59G2A1A2A3SbS3S5cG2A1M4S5S4eG0S13VrhoE;PaA2A2G1A2A2SbSbS3Zfc01R3A2S4R3S7Z2M5Z27A2A2A2SbSbS3Z12000R1A2S3R1S5R3Z3007A2A2A2SbS3ScbR2A2SbS3S5R2R1A2Z7fffff800000A2SbS12S0S86S12R2VEXo;A3SbS3S42S0S0S1fVrhoE;R3A2M6A3R2A2S4R2S43S0S0G6A3A2A2SdSbS3ScdR3A2S4R3SccA2A2SbS3S56G2A1M7R3A2S4R3S5G7SceA2A2A2A2F_;F_;Fz;Fo;Sb2S12S12SbSbS3S5G4Z10A2S4eG0S2cVrhoE;S1bR1A1A2A2M8A2S3G8S7G5Z2fA2A2A2SbScS10S1dR1A1S15N10A1A3ScS10S1cR1A1S15Z0A1A3A2A2Lo;S90VW;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2TL;Tua;Tnv;").

Lemma R4_zoneS : ltac2:(tb__ "0|3|
S0S52S11S4fQ40M0A1S11S12S0S9cR6R5R4R3R7A5S86S12R3VR4;R8A1A3SbS3S42S0S0S1fR5R4A2M1A3R3A2S4R3S43S0S0G1A3A2A2S9fS5aS54R9A1M2A1S59G2A1S56G2A1S4eG0R7A2S82S4eG0S13R8PcA2A2A1S5cG2A1R4A7F_;F_;F_;Fz;Fo;FrhoE;Fa;Frho;FA;Fsz;").
Proof.
  intros sz A rho a rhoE o z (Hsz & DEP & HG & Enx & EMS & E151 & E152 & TOP & HN & SMB & IMG & HTOP & HEX & LNK) Ho Ha.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG).
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (L := secmapsize nv) in *.
  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_fambS in Fo. apply orb_prop in Fo as [Fo|FL].
  2: {
    apply existsb_exists in FL as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoE o), Eo, (obj_range_nocells rhoE o') in Ha.
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (B & Elo & Ehi). destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in B, Elo, Ehi. subst olo ohi.
    pose proof (topG_range (aa_geom A)) as TGr.
    rewrite obj_range_mk in Ha by (clear -B TGr; lia). cbn [fst snd] in Ha. do 6 right. clear -Ha B. lia. }
  apply orb_prop in Fo as [Fo|Fo]; [apply orb_prop in Fo as [OK|Fo]|].
  -
    unfold rt_okD in OK. destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
    destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
    destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
    apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
      apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
      apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
      unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
    + apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
      rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
  -
    apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoE o), Eo, (obj_range_nocells rhoE o') in Ha.
    destruct Ho' as [<-|Ho'].
    + do 5 right. left.
      assert (SO : soff rhoE (SVar V_MS) = L).
      { unfold soff. cbn [eval]. rewrite EMS, signed_lit. unfold snorm. rewrite Z.mod_small by (clear -SMB HN; lia).
        destruct (Z.ltb_spec L (2 ^ 63)); clear -SMB HN H; lia. }
      unfold MAPO, obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi fst snd] in Ha.
      rewrite SO, soff_lit_small in Ha by lia. cbn [eval] in Ha. rewrite Enx in Ha. clear -Ha. lia.
    + destruct (HEX o' z Ho' Ha) as [B|P]; [do 3 right; left; exact B | do 4 right; left; exact P].
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (srange (rw rhoE V_DEPTH)) as R15.
    do 6 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    + apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Lemma zoneS_not_DFP : ltac2:(tb__ "0|1|
S52S11S3bS4fQ40A1A1S84S0S0S0Sd6R7R6R5R4A4S3ScbR4A2S3dS0S0A2M0S86G0R1Sa3S53RaA1A1A3Sa2R2S39S0S0R7R6A4A2F_;Fbn;S54RaA1S57S9fS5aR1A1S59R1A1S56R1A1R7R6S5cR1A1R5A7SfSa5S53RcA1R6A2A1F_;TG;F_;F_;F_;Fz;FL;Fua;Fmd;Ftp;Frho;FAx;").
Proof.
  intros Ax rho tp md ua L z HX IMG HSEP G HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4' & _); exact X4').
  pose proof (zones_not_DFPw Ax z HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  pose proof (dyn_ok_big _ _ _ HPAB ltac:(unfold kPtrArrayReserve; lia)) as PB.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot Ax) z) -> P -> ~ dfp_static z -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= z < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static z).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range z Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZB|[ZP|[ZM|ZK]]]]]].
  - apply (GOAL (IMG_LO <= z < IMG_HI /\ ~ dstatw z)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range z Hs). lia.
    + intros Hs. pose proof (dstat_range z Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (SHADOW_BAND_LO <= z < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | exact ZB |].
    apply (NS SHADOW_BAND_LO (z + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl H)))))))) ZP).
    apply (NS (ag_pab (aa_geom Ax)) (z + 1)); [lia | unfold IMG_HI in PB; unfold MAP1, MAP1N; lia].
  -
    destruct HD as [Hs|[(b & Hb & Hbz)|(b & Hb & Hbz)]].
    + pose proof (dstat_range z Hs) as DR. unfold IMG_HI in IMG. unfold MAP1, MAP1N, STORE in DR. clear -DR IMG ZM. lia.
    + pose proof (HSEP (b, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as SP.
      unfold sepZ in SP. cbn [fst snd] in SP. clear -SP Hbz ZM. lia.
    + pose proof (HSEP (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as SP.
      unfold sepZ in SP. cbn [fst snd] in SP. clear -SP Hbz ZM. lia.
  - apply (GOAL (topG (aa_geom Ax) <= z)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom Ax)) (z + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma GS_lt_next : ltac2:(tb__ "0|0|
S1S7cR1VGS;A2S7cR2S17S49VX5;A1A1A2F_;Fi;").
Proof. intros i Hi. eapply Pos.lt_le_trans; [exact Hi | apply Pos.leb_le; exact NXE]. Qed.

Lemma budget_A0 : ltac2:(tb__ "0|0|
S52S0S5bR2R1A2S5bVAX;Sd3R3R2A2A1Z0A2F_;Fnv;FA;").
Proof.
  intros A nv (HL & HR & HP). split; [|split].
  - rewrite AXV, AXKm, AXKf. cbn [aa_V aa_Km aa_Kf bumpV]. unfold limit_ok_alloc in *. rewrite Z.add_0_r. exact HL.
  - unfold sec_room, large_live in *. rewrite AXlive. cbn [aa_live bumpV]. exact HR.
  - apply (prim_room_same A (AX (bumpV A nv))); [rewrite AXlive; reflexivity | exact HP].
Qed.

Lemma dcS_facts : ltac2:(tb__ "0|2|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S98S7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6S9cR8R6R5R4S4eG0S13R4Pc0A2A2A5F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w Hw. pose proof (SPA_facts_hold segs _ rhoE X5 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (E12 & Enx & _ & E142 & E151 & E152 & _).
  pose proof (JGs_nums nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _).
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & Htop & _). unfold top_high in Htop.
  assert (FACT : forall p, In p (ss_facts (ax_S X5)) -> holds rhoE p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HF p Hp)).
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG. rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  unfold site_factsS. cbn zeta.
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact Enx|]. split; [exact E142|]. split; [exact E151|]. split; [exact E152|].
  split; [exact Htop|]. split; [exact HN|]. split; [exact SMB|]. split; [exact IMG|]. split; [exact HTOP|].
  split; [intros o z Ho Hz; exact (EX_zone A Kc rho a rhoE tp _ o z Hw Ho Hz)|].

  pose proof (topG_range (aa_geom A)) as TGr. pose proof (srange (rw rhoE V_DEPTH)) as R15. unfold malloc_depth in Fd1.
  apply (unwind_objs_above W rhoE (topG (aa_geom A))); [|clear -Htop Fd1; lia | clear -TGr; lia].
  apply Forall_forall. intros p Hp. apply FACT. apply FUNW.
  unfold unwind_factsS. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l0 W0']; [destruct Hp | exact Hp].
Qed.

Lemma dcS_site : ltac2:(tb__ "0|2|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S98S7eVsegs;VJG;VAX;R7R6R5R4A5VX5;R3R2R1A6S7eVsegs;VJG;VAX;R8R7R6R5A5VX4;S4eG0S13R4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w Hw. pose proof (dcS_facts A Kc rho a rhoE tp w Hw) as (Hsz & Fd1 & HG & _ & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.
  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3856)))) = bv_unsigned (rw rhoE 10%positive) - 3856).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3856))) with (2 ^ 64 - 3856) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG AX A Kc rho a) (X5f X5) rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X5f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }
  assert (HwR : SPA segs (JG AX A Kc rho a) (X5r X5 sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X5r, rstS. eapply SPA_restate; [exact (WX5r sz Hsz) | exact (DX5r sz Hsz) | reflexivity | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }
  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4, X5s. apply OS; [exact (SPL4 sz Hsz)|]. unfold X5c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X5b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X5a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dcS_R4 : ltac2:(tb__ "0|3|
S52S11S4fQ40M0A1M1S11S0S9cR5R4R3R2R1A5S52S11S3bG1A1S84G1Sd6R5R4R3R2A4ScS57S54R6A1S54RcA1A3S3dS0S0A2M2S86G2R1Sa3S53R8A1A1A3Sa2R2S39S0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;SadRbVR4;RaA1R4A3SfSa5S53R9A1S4eG0R5A2A2A1F_;F_;F_;F_;Fx;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Fa;Frho;FA;").
Proof.
  intros A rho a rhoE sz SF Ax rx tpx mdx x HX EG HSEP (o & Ho & Hox).
  pose proof (R4_zoneS sz A rho a rhoE o (bv_unsigned x) SF Ho Hox) as HZ. rewrite <- EG in HZ.
  pose proof SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG & _).
  exact (zoneS_not_DFP Ax rx tpx mdx _ _ (bv_unsigned x) HX IMG HSEP HZ).
Qed.

Let A0 (A : AA) (rho : valuation) : AA := ltac2:(tb__ "0|0|
VAX;Sd3VA;S4eQ40S13Vrho;PcA2A2A2A1").
Lemma A0_geom : ltac2:(tb__ "0|0|
S52S11ScS57S54VA0;R2R1A2A1S54R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXg. reflexivity. Qed.
Lemma A0_depot : ltac2:(tb__ "0|0|
S52S11ScS60S53VA0;R2R1A2A1S53R2A1A3Frho;FA;").
Proof. intros A rho. unfold A0. rewrite AXd. reflexivity. Qed.

Lemma dcS_entry : ltac2:(tb__ "0|4|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S0S3bS85A1M2S95S84S9cRaR8R7R6R4A5S8dRaA1S7fVsegs;R8R7VX4;R6A1S39G2S96R5S97R4R3A2A4A5VJG;VAX;RdRcRbRaR9R8R6R4A9Sa6Sb1Sb0VA0;ReRcA2M3RdRaS4eG0RbA2S82S4eG0S13RcPcA2A2A1A5S53G3A1SabSaaRaVR4;R8A1S8bR5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0.
  pose proof SF as (Hsz & Fd1 & HG & Enx & EMS & E151 & E152 & Htop & HN & SMB & IMG & HTOP & HEX). unfold malloc_depth in Fd1.
  pose proof HJ0 as (_ & _ & HA0 & HP0 & HK0 & _ & _ & _ & _ & HB0). cbn zeta in HA0, HP0, HB0. fold (A0 A rho) in HA0.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2320)))) = bv_unsigned (rw rhoE 10%positive) - 2320).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2320))) with (2 ^ 64 - 2320) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  pose proof HP0 as (PIn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSep).
  split.
  - apply (KDP_intro (A0 A rho) Kc rhoE 0 (budget_A0 A _ HB0) HKm0 _ _ tp tr0 md0 HA0 HK0 PIn).
    + rewrite A0_depot. exact PSep.
    + unfold TOPr, V_DEPTH. rewrite A0_geom. cbn [rw rho_sub rho_absorb].
      rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
      change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X (A0 A rho) rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot (A0 A rho)) rhoE _ md0 tp); [|exact HD0]. intros z Hz. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin.
    apply (dcS_R4 A rho a rhoE sz SF (A0 A rho) rhoE tp md0 _ HX0 (A0_geom A rho) ltac:(rewrite A0_depot; exact PSep) Hin). rewrite u64_lit by exact Hr. exact Hz.
Qed.

Lemma dcS_exit_ok : ltac2:(tb__ "0|5|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S0S3bS85A1M3S95S84S11G2G3S95S84S9cRfRdRcRbR9A5S8dRfA1Sa4Sb1Sb0VA0;R11RfA2M4R10RdS4eG0ReA2S82S4eG0S13RfPcA2A2A1A5S53G4A1A3Sc0SabSaaReVR4;RcA1S8bR9RdRaA3A3Vs4;RcA1A2S11S7fVsegs;RfReVX4;RdA1S39G3S96RcS97RbRaA2A4A5VJG;VAX;R14R13R12R11R10RfRdRbA9SbcS17S49S78RfA1A1A1R3RbA3S7fVsegs;RcRbS77R10A1S39G3S96RaS97R9R8A2A4A5R6R5R12RdRcRbR9A6Sc2R14S8bRfR13R10A3VR4;R12A1Vs4;R12A1S78R12A1S77R12A1VX4;R12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros x Hin. apply HRM. pose proof HKD' as ((HXK & _) & (_ & HSEP')).
    exact (dcS_R4 A rho a rhoE sz SF _ rhoE tpL md' x HXK (A0_geom A rho) HSEP' Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r x j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r x j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dcS_exit_core : ltac2:(tb__ "0|7|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S9cR11RfReRdRbA5S8dR11A1Sa4Sb1Sb0VA0;R13R11A2M4R12RfS4eG0R10A2S82S4eG0S13R11PcM5A2A2A1A5S53G4A1A3Sc0SabSaaR10VR4;ReA1S8bRbRfRcA3A3Vs4;ReA1A2S11S7fVsegs;R11R10VX4;RfA1S39G3S96ReS97RdRcA2A4A5VJG;VAX;R16R15R14R13R12R11RfRdA9SbcS17S49S78R11A1A1A1R3RdA3S7fVsegs;ReRdS77R12A1S39G3S96RcS97RbRaA2A4A5R6R5R14RfReRdRbA6S11S98SbdR18S8bR13R17R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R2R12A9S7eVsegs;Sc1RaR9R18R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R3R12R2A6SeS55S55SeS11S11SeS11S11SbS3dS0S0A2M6S86G6R1Sa3R4A1A3Sa2R2S39S0S0S4eG0R20A2S82S4eG0S13R21G5A2A2A1A4A2F_;Fbn;SbS9eR3R1fR2A3S7eVsegs;VJG;S9dR3A1R21R20R2R1eA5VC5;R1R16R6A6A2A2LrhoX;A2Lrho'';A2LG2;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & Enx & EMS & E151 & E152 & Htop & HN & SMB & IMG & HTOP & HEX).
  pose proof HJ0 as (Hag0 & Ha0 & HA0 & HP0 & HK0 & Htp0 & HU0 & HN0 & Htop0 & HB0). cbn zeta in HA0, HP0, HB0, HN0. fold (A0 A rho) in HA0. unfold top_high in Htop0.
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as ((HX2 & HK2 & HL2 & HT2) & (PIn2 & HSEP2)).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GS)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. rewrite (NX4 sz Hsz). exact (GS_lt_next i Hi). }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  match type of HJc with ?Jx _ _ _ _ => set (JP := Jx) in * end.
  assert (HT40 : SPA segs JP (T50 (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T50. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }
  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T50 (T4 sz) (X4 sz)) = []) by (unfold T50, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  assert (HT4b : SPA segs JP (T5b (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T5b. apply OR; [exact (RB2 sz Hsz) | unfold T5a; rewrite AXr; exact AX40 |]. unfold T5a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }
  assert (HT4c : SPA segs JP (T5c nobj (T4 sz) (X4 sz)) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T5c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }
  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d, T5d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T5m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T5m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T5m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T5d, T5m3, T5m2, T5m1. rewrite !AXm. unfold T5c. cbn [ax_X ax_setS]. unfold T5b, T5a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := AXK G2 (bumpV A (bv_unsigned (rw rho 12%positive)))).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall x, rm rho5 x = if in_ranges_dec rho' (R4 sz) x then rm rhoE x else rm rhoL x).
  { intros x. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall x, in_ranges rho' (R4 sz) x <-> in_ranges rhoE (R4 sz) x).
  { intros x. split; intros (o & Ho & Hox); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hox). }
  assert (R4DFP : forall x, in_ranges rhoE (R4 sz) x -> ~ DFP G2 (bv_unsigned x)).
  { intros x Hin. exact (dcS_R4 A rho a rhoE sz SF _ rhoE tpL md2 x HX2 (A0_geom A rho) HSEP2 Hin). }
  assert (KEY : forall x, ~ DFP G2 (bv_unsigned x) -> rm rho5 x = rm rhoE x).
  { intros x Hx. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) x) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 x Hx). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE x) Hi)). }
  assert (KEYin : forall x, in_ranges rhoE (R4 sz) x -> rm rho5 x = rm rhoE x).
  { intros x Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) x) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE x) Hi)). }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros z Hz. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 z) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Hz. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X (A0 A rho) rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A', AXK. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. fold (A0 A rho). lia. }
  assert (RW5 : forall i, (i < GS)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (GWS : forall i, (i < GW)%positive -> (i < GS)%positive) by (intros i Hi; exact (lt_GW_GS nx NXG i Hi)).
  assert (HJG5 : JG (AXK G2) A Kc rho'' a rho5 tpL tr2 md2).
  { unfold JG, JGs. cbn zeta. change (rw rho'' 12%positive) with (rw rho 12%positive).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - split; [|split].
      + intros i Hi. refine (eq_trans _ (eq_trans (Hagw i Hi) (eq_sym (RW5 i (GWS i Hi))))).
        unfold rhoM_of, cnt_of, chk_of, cst_of. change (rw rho'' 12%positive) with (rw rho 12%positive). apply rw_rho_sets_ext. intros j. reflexivity.
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros x. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - rewrite (RW5 nx (nx_lt_GS nx)). exact Ha0.
    - exact HA5.
    - destruct HP0 as (_ & PR). exact (conj PIn2 PR).
    - exact HK2.
    - unfold tp_ok in Htp0 |- *. rewrite (RW5 24%positive) by (apply GWS; unfold GW; lia). exact Htp0.
    - apply (HW rhoE rho5); [|exact HU0]. intros i Hi. apply RW5. apply GWS. unfold NF in Hi; unfold GW; lia.
    - exact HN0.
    - unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (apply GWS; unfold GW, V_DEPTH; lia). exact Htop0.
    - exact HB0. }

  assert (HT5 : SPA segs (JG (AXK G2) A Kc rho'' a) (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJG5].
    intros o x Ho Hx. exact (coveredbL_sound _ _ _ rho' o x HfT (R4cov sz Hsz) Ho Hx). }
  pose proof (SPA_entails segs (JG (AXK G2) A Kc rho'' a) GS (T4d sz) C5 _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGs_stable nW st tmax nx Hnx NXG (AXK G2) A Kc rho'' a HUS HKc) HT5) as HC5.
  exists G2, rho'', (rho_sub rho5 (sd sz)). split; [exact HSEP2|]. split; [|exact HC5].
  split; [intros i; reflexivity|]. split; [intros l; reflexivity|].
  intros x Hx. unfold rho''. cbn [rm]. rewrite (KEY x Hx). rewrite <- (Hagm x). unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
Qed.

Lemma dcS_exit : ltac2:(tb__ "0|7|
S98OF_;S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S9bS0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S55S11S11G2S3dS0S0A2M4S86G4R1Sa3R5A1A3Sa2R2S39S0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;S9eR5R15R4A3S9aVsegs;R19S7eVsegs;VJG;S9dR6A1R18R17R5R15A5VC5;R4R3A5R12A4F_;F_;Ftp';FrhoX;Frho';FG2;S9cR13R11R10RfRcA5S8dR13A1Sa4Sb1Sb0VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc0SabSaaR12VR4;RfA1S8bRcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S39G3S96RfS97ReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbcS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S39G3S96RdS97RcRbA2A4A5R6R5R16R10RfReRcA6SbSc2R18S8bR12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11SbdR19S8bR13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S9aVsegs;R1fS7eVsegs;Sc1R9R8R19R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl n' Hg' w' HC5).
Qed.

Lemma dcS_exitE : ltac2:(tb__ "0|7|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1M2S98OF_;S0S3bS85A1M3S95S84S11G2G3S95S84SafVW;Vst;A2S83VW;Vst;A2S55S11S11G2S3dS0S0A2M4S86G4R1Sa3R5A1A3Sa2R2S39S0S0S4eG0R15A2S82S4eG0S13R16PcM5A2A2A1A4A2F_;Fbn;S9eR5R15R4A3S99Vsegs;S7eVsegs;VJG;S9dR6A1R18R17R5R15A5VC5;R4R3A5R12A3F_;F_;Ftp';FrhoX;Frho';FG2;S9cR13R11R10RfRcA5S8dR13A1Sa4Sb1Sb0VA0;R15R13A2M6R14R11S4eG0R12A2S82S4eG0S13R13G5A2A2A1A5S53G6A1A3Sc0SabSaaR12VR4;RfA1S8bRcR11RdA3A3Vs4;RfA1A2S11S7fVsegs;R13R12VX4;R10A1S39G3S96RfS97ReRdA2A4A5VJG;VAX;R18R17R16R15R14R13R10ReA9SbcS17S49S78R12A1A1A1R3ReA3S7fVsegs;RfReS77R13A1S39G3S96RdS97RcRbA2A4A5R6R5R16R10RfReRcA6SbSc2R18S8bR12R17R13A3VR4;R15A1Vs4;R15A1S78R15A1S77R15A1VX4;R15A1R11A8S11SbdR19S8bR13R18R14A3VR4;R16A1Vs4;R16A1S49S78R16A1A1S49VX4;R16A1A1S49S77R16A1A1R1R12A9S99Vsegs;S7eVsegs;Sc1R9R8R19R13R12A5SbfVs4;R17A1S78R17A1S77R17A1VX4;R17A1VR4;R17A1A5R2R12A5R18A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dcS_exit_ok A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dcS_exit_core A Kc rho a rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (G2 & rho'' & rhoX & Hsep & Hl & HC5).
  exact (Hcont G2 rho'' rhoX tpL Hsep Hl w' HC5).
Qed.

Lemma dcS_nums : ltac2:(tb__ "0|4|
S52S8cS11S4fQ40M0A1M1S11S3bG1A1S3bS85A1S84VJG;VAX;R8R7R6R5R4R3R2R1A9S4eG0R6A2S0S82S4eG0S13R8PcA2A2A1S0SbS5bVA0;RbR9A2M2Z0M3A2SbS3G3S58G2A1A2SbS3G3R2A2SbS3G3R1A2SbS4S5R2R1A2S7Z2Z40A2A2Se3Vsegs;G2R7R6R4A5A2A2A2A2A2TL;Tua;F_;Fmd;Ftr;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp tr md HJ. cbn zeta.
  pose proof (JGs_nums nW st tmax nx Hnx AX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _).
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HB). cbn zeta in HA, HB. fold (A0 A rho) in HA.
  pose proof (AInvA_budget (A0 A rho) rhoE tp md HA) as (_ & _ & _ & HKm0 & _). pose proof (urange a) as Ra.
  split; [exact (budget_A0 A _ HB)|]. split; [exact HKm0|]. split; [lia|]. split; [lia|]. split; [lia | exact HA].
Qed.

Theorem depot_call_S : ltac2:(tb__ "0|4|
S98OF_;S52S8cS11S4fQ40M0A1M1S9bSafVW;Vst;A2S83VW;Vst;A2S8dR6A1S81Vsegs;R9S80R7A1A3SdfVsegs;RaS80R8A1A3S55S11S11S3bG1A1M2S3dS0S0A2M3S86G3R1Sa3R5A1A3Sa2R2S39S0S0S4eG0RdA2S82S4eG0S13RePcA2A2A1A4A2F_;Fbn;S9eR5RdR4A3S9aVsegs;R11S7eVsegs;VJG;S9dR6A1R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S9aVsegs;ReS7eVsegs;VJG;VAX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rhoE tp n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dcS_facts A Kc rho a rhoE tp _ Hw) as SF. pose proof (dcS_site A Kc rho a rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (dcS_nums A Kc rho a rhoE tp tr md HJ) as (HB & HKm0 & Hua & HL & HuaL & HA). cbn zeta in Hua, HL, HuaL.
  pose proof (topG_range (aa_geom A)) as TG.
  set (K := KDP (A0 A rho) Kc rhoE (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))).
  assert (HKT : forall G r t tr0 md0, K G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. pose proof (KD_top _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) as X. rewrite A0_geom in X.
    pose proof SF as (_ & _ & HG & _). rewrite (geom_top _ HG). exact X. }
  apply (call_soundPA segs ok (JG AX A Kc rho a) (JD segsA K (aa_depot (A0 A rho))) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as ((_ & _ & _ & HT1) & _). unfold TOPr in HT1. rewrite A0_geom in HT1.
    refine (seg_D_sound2 K (hcD (A0 A rho)) (KDP_laws (A0 A rho) Kc rhoE 0 HKc HB ltac:(lia) HKm0 _ _ Hua HL HuaL NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot (A0 A rho)) (dN_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) (hcD_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) Hp Hok).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dcS_entry A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L0 JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L0 JL. clear EL.
    exact (dcS_exit ok A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_SE : ltac2:(tb__ "0|4|
S52S8cS11S4fQ40M0A1M1S98OF_;SafVW;Vst;A2S83VW;Vst;A2S8dR6A1S55S11S11S3bG1A1M2S3dS0S0A2M3S86G3R1Sa3R5A1A3Sa2R2S39S0S0S4eG0RbA2S82S4eG0S13RcPcA2A2A1A4A2F_;Fbn;S9eR5RbR4A3S99Vsegs;S7eVsegs;VJG;S9dR6A1ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S11G2S99Vsegs;S7eVsegs;VJG;VAX;RbRaR9R8A5VX5;R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc Hcont rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (dcS_facts A Kc rho a rhoE tp _ Hw) as SF. pose proof (dcS_site A Kc rho a rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (dcS_nums A Kc rho a rhoE tp tr md HJ) as (HB & HKm0 & Hua & HL & HuaL & HA). cbn zeta in Hua, HL, HuaL.
  pose proof (topG_range (aa_geom A)) as TG.
  set (K := KDP (A0 A rho) Kc rhoE (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))).
  assert (HKT : forall G r t tr0 md0, K G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. pose proof (KD_top _ _ _ G r t tr0 md0 (KDP_KD _ _ _ _ _ G r t tr0 md0 HKG)) as X. rewrite A0_geom in X.
    pose proof SF as (_ & _ & HG & _). rewrite (geom_top _ HG). exact X. }
  apply (call_completePA segs (JG AX A Kc rho a) (JD segsA K (aa_depot (A0 A rho))) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA K (aa_depot (A0 A rho)))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as ((_ & _ & _ & HT1) & _). unfold TOPr in HT1. rewrite A0_geom in HT1.
    exact (seg_D_complete2 K (hcD (A0 A rho)) (KDP_laws (A0 A rho) Kc rhoE 0 HKc HB ltac:(lia) HKm0 _ _ Hua HL HuaL NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot (A0 A rho)) (dN_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) (hcD_entry (A0 A rho) rhoE 0 HB ltac:(lia) tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dcS_entry A Kc rho a rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L0 JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L0 JL. clear EL.
    exact (dcS_exitE A Kc rho a rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' HW HUS Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DCS.
End CDepotCallS.

(* [comment removed for export] *)
Module SpineCallocSec3IELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1.
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

Lemma NXT0_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S1bA1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
SaS1S23VGS0;S10S11S16S1cSfS11S1aA1A1A2A1A1A2S3A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S1bZ1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S1fG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
SaS1S8S9Ufa0S0SbS18S2SbA1A3VGS0;S0S6S7S16S1cSfS11S1aA1A1A2Z1SdZ0M0A1M1A3S2S6A1M2A3S0S6S7S20G0G1A3G2A3A6S3A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_1l : ltac2:(tb__ "0|6|
S19S25ScS13Q40M0A1M1S5G1A1M2S15OF_;S22VW;Vst;A2S26R6A1S29S4S12G0R5A2S21S12G0SeR6PcM3A2A2A1A3ScScG2S2aS12G0R9A2S21S12G0SeRaG3A2A2A1RaR3A4S14S9S17S9S27U1M4Vst;S1dS19R1LX;M5RdRcR4RaA8S1eR3R2A5R8A3F_;FtpY;FrhoY;Frho';ScS14S9S17S9S28G4Vst;S1dG5RbRaR9R8A8S24VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 1%nat) (st := st) (tmax := tmax) (hi := false) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
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
End SpineCallocSec3IELW1.

(* [comment removed for export] *)
Module SpineCallocSec3IEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1.
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

Lemma NXT0_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S1aA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1bSeS10S19A1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1aZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1eG0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1bSeS10S19A1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1fG0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_1h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S21VW;Vst;A2S25R6A1S28S1S11G0R5A2S20S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S20S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U1M4Vst;S1cS18R1LX;M5RdRcR4RaA8S1dR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1cG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 1%nat) (st := st) (tmax := tmax) (hi := true) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
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
End SpineCallocSec3IEW1.

(* [comment removed for export] *)
Module SpineCallocSec4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "aa_ptr_committed"; "sec_chunk"; "ag_pab"; "ageom"; "budget_bound"; "ag_top"; "topG"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "prod"; "app"; "nil"; "pair"; "option"; "length"; "Some"; "None"; "fst"; "snd"; "andb"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_objs"; "SVar"; "ss_facts"; "holds"; "SLit"; "eval"; "rm"; "reg_sv"; "rw"; "SPBranch"; "obj_range"; "obj_holds"; "ranges_disjoint"; "sprop_below"; "swf"; "SPNot"; "rl"; "DUnknown"; "cell"; "enc_bytes"; "image_byte"; "mkObj"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "sub"; "div"; "mul"; "lxor"; "land"; "eqb"; "ge"; "leb"; "log2"; "ltb"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "alloc_top"; "vm_maps"; "vm_reserved"; "region_free"; "m_vm_lazy"; "map_contains"; "maps_subtract"; "vm_limit"; "vm_noaccess"; "vm_forget_range"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "kPtrArrayCommit"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "genL"; "Bw"; "F_g3"; "F_l2"; "x11e3"; "O_1"; "O_2"; "O_blk"; "a0e3"; "O_w"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4.SEC4"; "slink4"; "AXP"; "JGo"; "nopab"; "O_nres"; "range_nopab"; "rtint"; "xor63_okb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "Build_machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "ALU_XOR"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NCH"; "V_NRES"; "O_seci"; "msx"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI";
"stopJ_stable"; "secmapsize"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "vms"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "rt_zoneG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
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

Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.

Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SbcVnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.slink.

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
S0S12Sb5S92Ufa0S14S5Z7050cS14S5Z40f5cS17S5A1A3A3VGS;S14S41VU2;S17S41A1M0A3S14S41VX3a;S14S41VX3b;G0A3A3A6S13A3").

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
S0S12Sb5S92Ufa0S14S5Z40f5cS17S5A1A3VGS;S14S41VG3;S17S41A1M0A3S14S41VX3a3;G0A3A6S13A3").

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
S0S12Sb5S92Ufa0S14S5Z3c480S17S5A1A3VGS;S14S41VL3a;S17S41A1M0A3S14S41VY4a0;S14S41VY4a1;G0A3A3A6S13A3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0S12S42VY4a0;VT4a;Vs4a0;A3S13A3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0S12S8dVs4a0;VGS;A2S13A3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0S12S42VY4a1;VT4a;Vs4a1;A3S13A3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0S12S8dVs4a1;VGS;A2S13A3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0S12Sb5S92Ufa0S14S5Z3c480S17S5A1A3VGS;S14S41VCO3b;S17S41A1M0A3S14S41VY4b0;S14S41VY4b1;G0A3A3A6S13A3").
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
  unfold JG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.JGs. cbn [rw rho'']. fold nv.
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
  apply (cfg_soundA segs 4000%nat [0x3c480] GS [CO3b] [Y4b0; Y4b1] (JG AX A Kc rho a) ok Q tp Hokf HST Cert4b); [|left; reflexivity].
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
  apply (cfg_soundA segs 4000%nat [0x40f5c] GS [G3] [X3a3] (JG AXP A Kc rho'' a) ok Q tp Hokf2 HST2 Cert3a); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (gen_x11 AXP A Kc rho'' a X3a3 L3a sLa rE tp w HUS HKc ELa IDa GLa FBLa HL3a Hw) | intros w Hw; right; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x3c480] GS [L3a] [Y4a0; Y4a1] (JG AXP A Kc rho'' a) ok Q tp Hokf2 HST2 Cert4a); [|left; reflexivity].
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
  apply (cfg_soundA segs 4000%nat [0x7050c; 0x40f5c] GS [U2] [X3a; X3b] (JG AX A Kc rho a) ok Q tX Hokf HST Cert3); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (path_a ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hok RUNDEF HCa rE tX).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (path_b ok A Kc rho a Q HW HUS HKc Hokl HCb rE tX).
Qed.
End G3.
End SEC4.

End SpineCallocSec4.

(* [comment removed for export] *)
Module SpineCallocSec3IE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1.
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
S9S2S22VGS0;SfS10S1aA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1bSeS10S19A1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1aZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1eG0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1bSeS10S19A1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S1fG0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_0h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S21VW;Vst;A2S25R6A1S28S1S11G0R5A2S20S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S20S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U0M4Vst;S1cS18R1LX;M5RdRcR4RaA8S1dR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1cG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 0%nat) (st := st) (tmax := tmax) (hi := true) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
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
End SpineCallocSec3IE.

