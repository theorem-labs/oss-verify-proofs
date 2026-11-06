(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall bx CertCallocST.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.

(* [comment removed for export] *)
Module SpineMallocSec3IEW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "rw"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "CO1c"; "T0c"; "T1c"; "nx0"; "D2c"; "ET1c"; "ET2c"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "JGsC"; "clsP"; "slink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXT0_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S1cA1A1A2S1A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXD1_0 : ltac2:(tb__ "0|0|
S9S2S22VGS0;SfS10S15S1dSeS10S1bA1A1A2A1A1A2S1A3"). Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S1cZ1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S20G0G1A3G2A3A6S1A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA T0c 1 (SLit 0)] [mkVNA ET1c 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.run1]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2.run1__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert2_0 : ltac2:(tb__ "0|3|
S9S2S7S8Ufa0S0SaS17S3SaA1A3VGS0;S0S5S6S15S1dSeS10S1bA1A1A2Z1ScZ0M0A1M1A3S3S5A1M2A3S0S5S6S21G0G1A3G2A3A6S1A3").
Proof. rewrite HD1_0. vm_cast_no_check (eq_refl true). Qed.

Theorem esec_g12_2h : ltac2:(tb__ "0|6|
S18S24SbS12Q40M0A1M1S4G1A1M2S14OF_;S1aVW;Vst;A2S25R6A1S28S1S11G0R5A2S19S11G0SdR6PcM3A2A2A1A3SbSbG2S29S11G0R9A2S19S11G0SdRaG3A2A2A1RaR3A4S13S8S16S8S26U2M4Vst;S1eS18R1LX;M5RdRcR4RaA8S1fR3R2A5R8A3F_;FtpY;FrhoY;Frho';SbS13S8S16S8S27G4Vst;S1eG5RbRaR9R8A8S23VW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp Q HUS HKc HC HCONT rhoX. unfold W, st, tmax in *. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  eapply esec_g12 with (nW := 2%nat) (st := st) (tmax := tmax) (hi := true) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0)
    (AX := fun X : AA => X) (AXg := fun X => eq_refl) (AXb := fun X => eq_refl)
    (E0 := E0c) (T0 := T0c) (SKT := SKT_0) (FCT := FCT_0) (AF0 := AF0_0)
    (ET1 := ET1c) (CT1 := CT1c) (CO1 := CO1c) (T1 := T1c) (ET2 := ET2c) (CT2 := CT2c) (CO2 := CO2c) (T2 := T2c) (s1 := s1c) (s2 := s2c) (R1 := R1c) (R2 := R2c)
    (NXT0 := NXT0_0) (NXD1 := NXD1_0) (ECert1 := ECert1_0) (ECert2 := ECert2_0)
    (WC1 := WC1_0) (DF1 := DF1_0) (NX1 := NX1_0) (HC1 := HC1_0) (SK1 := SK1_0) (FC1 := FC1_0) (XC1 := XC1_0) (HCO1 := HCO1_0) (WCO1 := WCO1_0)
    (He1 := He1_0) (Hchk1 := Hchk1_0) (HT1 := HT1_0) (FBC1 := FBC1_0) (FBT1 := FBT1_0) (NXC1 := NXC1_0)
    (WC2 := WC2_0) (DF2 := DF2_0) (NX2 := NX2_0) (HC2 := HC2_0) (SK2 := SK2_0) (FC2 := FC2_0) (XC2 := XC2_0) (HCO2 := HCO2_0) (WCO2 := WCO2_0)
    (He2 := He2_0) (Hchk2 := Hchk2_0) (HT2 := HT2_0) (FBC2 := FBC2_0) (FBT2 := FBT2_0) (NXC2 := NXC2_0);
    [intros E; discriminate E | exact HUS | exact HKc | exact HC | exact HCONT].
Qed.
End INST.
End SpineMallocSec3IEW2.

(* [comment removed for export] *)
Module SpineMallocSec4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "app"; "pair"; "option"; "length"; "Some"; "None"; "fst"; "snd"; "andb"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_sec"; "aa_ptr_committed"; "sec_chunk"; "ag_pab"; "ageom"; "budget_bound"; "ag_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_objs"; "SVar"; "ss_facts"; "holds"; "SLit"; "eval"; "rm"; "reg_sv"; "rw"; "SPBranch"; "obj_range"; "obj_holds"; "ranges_disjoint"; "sprop_below"; "swf"; "SPNot"; "rl"; "DUnknown"; "cell"; "enc_bytes"; "image_byte"; "mkObj"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "sub"; "div"; "mul"; "lxor"; "land"; "eqb"; "ge"; "leb"; "log2"; "ltb"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "alloc_top"; "vm_maps"; "vm_reserved"; "region_free"; "m_vm_lazy"; "map_contains"; "maps_subtract"; "vm_limit"; "vm_noaccess"; "vm_forget_range"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "kPtrArrayCommit"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "genL"; "Bw"; "F_g3"; "F_l2"; "x11e3"; "O_1"; "O_2"; "O_blk"; "a0e3"; "O_w"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4.SEC4"; "slink4"; "AXP"; "JGo"; "nopab"; "O_nres"; "range_nopab"; "rtint"; "xor63_okb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "Build_machine_state"; "ms_fcsr"; "ms_fregs"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "ms_svc_pending"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "ALU_XOR"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NCH"; "V_NRES"; "O_seci"; "msx"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "secmapsize";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "vms"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "rt_zoneG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
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
S0S6Sb2VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S8Sc6ScbVnx;A2S9A3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S18S0S1eS19VAX;R1A1A1S19R1A1A3FX;").
Hypothesis AXs : ltac2:(tb__ "0|0|
S18S0S7S1cA1S1aVAX;R1A1A1S1aR1A1A3FX;").
Hypothesis AXp : ltac2:(tb__ "0|0|
S18S0S5S1bVAX;R1A1A1S1bR1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S18S0S5S1fVAX;R1A1A1S1fR1A1A3FX;").

Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx.

Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SbeVnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.slink.

Definition AXP : AA -> AA := fun X => bumpP (AX X).
Lemma AXPg : ltac2:(tb__ "0|0|
S18S0S1eS19S9aR1A1A1S19R1A1A3FX;").
Proof. intros X. unfold AXP. cbn [aa_geom bumpP]. apply AXg. Qed.

Definition rtint (G : ageom) (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S1S47S98Vx;A2S49Vx;S48S98Z40A2A2A2S1S47S1dVG;A1M0Vx;A2S49Vx;S48G0S7eA2A2A2A2").

Definition slink4 (G : ageom) (ua L : Z) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|a|
S1S6S0S58Q40M0A1M1S2fVrho';R1A2S2fVrho;R1A2A3Fi;S1S6S0S7S58Q8A1M2A1S37Vrho';R1A2S37Vrho;R1A2A3Fl;S1G1S4S0SfG2A1M3S2dVrho';R1A2M4S2dVrho;R1A2M5A3S4S1S0G3G5S12G2A1M6A3S1S0G3S3bS94R1A2G6A3S1S47S80S59G0R1A2M7A2S49G7S7fA2A2A2A2S4S1S1S47S81Vua;A1M8G7A2S49G7S48G8S4eVL;Z8A2A2M9A2A2S3S0G3G4G6A3A1A2S9fVG;G7A2A2A2A2Fa;S5S1S47G8R1A2S49R1G9A2A2S3S0G3S2dVrho';S5aG0R2A2A2G6A3A1F_;Fz;A2A2A2").

Lemma slink_slink4 : ltac2:(tb__ "0|0|
S1eS5S5S22S22Vslink;R4R3R2R1A4S99R6R5R4R3R2A5F_;Fr2;Fr1;FL;Fua;FG;").
Proof.
  intros G ua L r1 r2 (W1 & L1 & M1 & D1). split; [exact W1|]. split; [exact L1|]. split; [|exact D1].
  intros a. destruct (M1 a) as [E|[X|X]]; [left; exact E | right; left; exact X | right; right; left; exact X].
Qed.
Lemma slink4_trans : ltac2:(tb__ "0|0|
S1eS5S5S22S22S22S99R6R5R4R3R2A5S99R7R6R5R3R2A5S99R8R7R6R5R3A5F_;F_;Fr3;Fr2;Fr1;FL;Fua;FG;").
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
Sa2Sa6Vms;A1Sa4Vms;A1Sa5Vms;A1Sa9Vms;A1Sa7Vms;A1Sa3Vms;A1Vf;Sa8Vms;A1A8").

Definition ens_mem (v : Z) : word -> option byte := ltac2:(tb__ "0|6|
S58Q40M0A1S8SfS58Q8M1A1M2A1L_;S15S54S48S98Z30A2M3S59G0R1A2M4A2S56G4S48S98Z38A2A2A2S11G2S79G2S57S4dG4G3A2A1S3aU8S5aG0Vv;A2A2S5aG1Z0A2M5A4A2S11G2G5A2X8x2La;").

Definition O_nres : sobj := ltac2:(tb__ "0|0|
S3cS2bS48S98Z30A2A1S2bZ0A1S2bZ8A1SbS39A1S38A5").
Definition R_ens : list sobj := ltac2:(tb__ "0|0|
SaS23S9dSaS23S8cSbS23A1A3A3").

Lemma JG_sec_nums : ltac2:(tb__ "0|9|
S18S18Fx;S18S5bS22S58Q40A1M0S22S7G0A1S7S64A1S63S18S0S1eS19RaR1A1A1S19R1A1A3FX;S18S0S7S1cA1S1aRbR1A1A1S1aR1A1A3FX;S18S0S5S1bRcR1A1A1S1bR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S19RcA1S1eS1bRdA1S5S1S47S83S1dR2A1M1A2S1S47S48G1S7eA2M2S21R2A1M3A2S1S0S5S4cG1S84A2Z0M4A3S1S4S47G2S80A2S47S7fG1A2A2S1S1S47S4fZ8M5S4aS10S1cS1aReA1A2A1A2R1A2S47R1S7eA2A2S1S0S5S4cR1S82A2G4A3S1S0S5G3S20R2A1M6A3S1S0S5S66S65R7A1A1G6A3S5S1S47S48S1dR3A1M7S4fG5S4aS10S1cS1aRfA1A2A1A2A2R1A2S49R1S48G7R2A2A2A2S2S58Q8A1M8G8S0SfG8A1Sc5S94S2dRdA1R3A3S11G8R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ.
  destruct HJ as (Hagr & Ha & HA & _).
  pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. exact X.
Qed.

Lemma F_g3_hold : ltac2:(tb__ "0|1|
S18S18F_;S18S5bS22S58Q40A1M0S22S7G0A1S7S64A1S63VJG;R9R8R7R6R5R4R3R2R1A9S49S48S4aS10S1cS1aR9A1A2A1Z1A2S4bZ2Z14A2A2S77S25S2aR6A1S87A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ Hok.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E147 & _).
  unfold F_g3. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite E147, !u64_lit by lia. lia.
Qed.

Definition xor63_okb (c : Z) : bool := ltac2:(tb__ "0|1|
S52S50Vc;Z3fM0A2S4dG0Vc;A2A2").
Lemma xor63_all : ltac2:(tb__ "0|0|
S0S8S97S5Sa0S78S17S5S4aS7aU0U40A2A4A3S9A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma xor63 : ltac2:(tb__ "0|1|
S5S1S47Z0R1A2S47R1Z3fM0A2A2S0S5S50R2G0A2S4dG0R2A2A3F_;Fc;").
Proof.
  intros c Hc. pose proof (proj1 (forallb_forall _ _) xor63_all c) as X. apply Z.eqb_eq. apply X.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma xor_valE : ltac2:(tb__ "0|2|
S58Q40M0A1M1G1S0S5S59G0Sc8SacR2R1A3A2S50S59G0R2A2S59G0R1A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.
Lemma land_m4096E : ltac2:(tb__ "0|0|
S5S1S47Z0R1A2S49R1S4bZ2Z40A2A2A2S0S5S51R2Zfffffffffffff000A2S4dR2S4cR2Z1000A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask by lia. reflexivity. Qed.
Lemma land_m8E : ltac2:(tb__ "0|0|
S5S1S47Z0R1A2S49R1S4bZ2Z40A2A2A2S0S5S51R2Zfffffffffffffff8A2S4dR2S4cR2Z8A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. reflexivity. Qed.

Lemma msx_val : ltac2:(tb__ "0|2|
S18S18F_;S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1S63VJG;R9R8R7R6R5R4R3R2R1A9S0S5S59G0S2cR5Sb1A2A2Sb4S59G0S2fR7PcA2A2A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
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
S18S18F_;S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1S63VJG;R9R8R7R6R5R4R3R2R1A9S1S0S5S59G0S2cR5S89A2A2M2S55Sb4S59G0S2fR7PcA2A2A1A1A3S1S47Z10G2A2S47G2Z28A2A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
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
S18S18Fx;S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1S63S18S0S1eS19RaR1A1A1S19R1A1A3FX;S18S0S7S1cA1S1aRbR1A1A1S1aR1A1A3FX;S18S0S5S1bRcR1A1A1S1bR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S2aR8S30SaaS28SaeA1S28SafA1A3A2S77S25S2aR9A1S87A3S19ReA1S1eS1bRfA1S5S48S1dR2A1R1A2S5S1S0S5S4fZ8S4aS10S1cS1aR11A1A2A1A2R2A3S1S47S48R2S82A2S7eA2S1S0S5S59G0S2cRdS8dA2A2R1A3S1S0S5S59G0S2cRdS86A2A2R1A3S1S0S5S4cR1Z1000A2Z0M2A3S1S47S83S1dR3A1M3A2S1S47S48G3S7eA2S66S65RaA1A1A2S47G2R2A2A2A2A2A2A2A2A2TPB;Tc;TG;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
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
S3S1S47S1dVG;A1M0Vx;A2S49Vx;S48G0S7eA2A2A2A1").
Definition range_nopab (G : ageom) (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S5S1S47S13S5S5Vr;A3R1A2S49R1S14S5S5Vr;A3A2A2S9cVG;R2A2F_;Fx;").

Lemma rt_zoneG_nopab : ltac2:(tb__ "0|1|
S18S18Fx;S18S5bS22S58Q40A1M0S22S7G0A1S7S64A1S63S5S18S0S1eS19RbR1A1A1S19R1A1A3FX;S18S0S7S1cA1S1aRcR1A1A1S1aR1A1A3FX;S18S0S5S1bRdR1A1A1S1bR1A1A3FX;VJG;RdRcRbRaR9R8R7R6R5A9SccS19RdA1R5A2S9cS19ReA1R6A2F_;F_;F_;F_;F_;Fx;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md x BXg BXs BXp HJ Hz.
  pose proof (JG_sec_nums BX A Kc rho a r tp tr md BXg BXs BXp HJ) as (P1 & _). cbn zeta in P1.
  destruct HJ as (Hagr & Ha & HA & _). pose proof (AInvA_pabsep _ _ _ _ HA) as (_ & PT & PF & PC & PD).
  rewrite BXg in PT, PF, PC, PD. cbn [aa_geom bumpV] in PT, PF, PC, PD.
  unfold nopab. unfold rt_zoneG in Hz. rewrite FS_total_val in *. unfold IMG_HI, kPtrArrayReserve in *.
  destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]]; [clear -Z1 P1; lia | clear -Z2 PT; lia | clear -Z3 PC; lia | clear -Z4 PD; lia | clear -Z5 PF; lia].
Qed.

Lemma objs_nopab : ltac2:(tb__ "0|4|
S41S7S23A1M0G0S18S5bS22S58Q40A1M1S22S7G1A1S7S64A1S63Sa1S0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;VJG;VAX;RaR9R8R7R6R5R4R3A9S77S25S2aR7A1S29S40ReA1A1A3S77S23S32Vsegs;R8R4A3S27S40RfA1A1A3S0S7ScScS24S24A2S24A2M2A1M3S78S23G2S76S27S40R10A1A1A4S78S23G2S76SdS23RfSdS23SbdVnW;Vnx;A2ReA3A3A4A3S95S25SdS25S62VW;Vst;A2S61S60A1A3S29S40R11A1A1A3S2G0G0S2G0G0S2G0G0S1S0G0S27S40R15A1A1SdS23R3SdS23R2R1A3A3A3S1S0G3S78S23G2S76R3A4S78S23G2S76R14A4A3S1S0G3S78S23G2S76R1A4S78S23G2S76R13A4A3S77S23S23S9eS19R13A1S31RfR1A2A2Lo;R2A3A2A2A2Ll2;A2Ll1;A2Ll0;A2F_;F_;F_;F_;F_;F_;FmsX;Fmd;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
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
    { destruct st; [apply chain_pre_in; exact Hp|]. exfalso. clear -Hp HW. unfold W in *. rewrite (HW eq_refl) in Hp. destruct Hp. }
    apply HFX. apply in_or_app; left. exact Hp'. }
  eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
  intros x Hx. rewrite obj_range_mk in Hx by (clear -B; lia). cbn [fst snd] in Hx. unfold nopab. clear -B Hx P2. lia.
Qed.

Lemma pab_piece_disjoint : ltac2:(tb__ "0|6|
S41S7S23A1M0G0S18S5bS22S58Q40A1M1S22S7G1A1S7S64A1S63Sa1S5S5S0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;VJG;VAX;RcRbRaR9R8R7R6R5A9S77S25S2aR9A1S29S40R10A1A1A3S77S23S32Vsegs;RaR6A3S27S40R11A1A1A3S0S7ScScS24S24A2S24A2M2A1M3S78S23G2S76S27S40R12A1A1A4S78S23G2S76SdS23R11SdS23SbdVnW;Vnx;A2R10A3A3A4A3S95S25SdS25S62VW;Vst;A2S61S60A1A3S29S40R13A1A1A3S47S1dS19R11A1A1R8A2S47R8S48S1dS19R12A1A1S7eA2A2G0S0G3S78S23G2S76R1A4S78S23G2S76R16A4A3M4S77S23S23S33S31R12R1A2SeS5S5RdRcA4A2Lo;M5R2A3F_;Fl;G0G4S77S23S23S33S31R13R1A2SeS5S5ReRdA4A2Lo;R2A3F_;Fl;S77S23G5S27S40R18A1A1A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fh2;Flo;FmsX;Fmd;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
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
S74S41S22S7S58Q40A1A1S7S64A1M0Sa1S63S71Vsegs;R7R6R5R4SeG0Sb5R3Sb6R2R1A2A4A6S1S77S25S2aR6A1S29S40R7A1M1A1A3S1S77S23S32Vsegs;R6Sc3R2R5R3A3A3S27G1A1A3R8R6R5R4R2A4A2A2F_;Fmd;Fms;Ftr;Ftp;Fr;FX;FJ;").
Proof.
  intros J X r tp tr ms md Hsp. pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  split; [exact (smatch_facts_hold _ _ _ _ Hsm)|]. split; [|exact (proj2 Hsp)].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall.
Qed.
Lemma pending_parts : ltac2:(tb__ "0|2|
S41S22S7S58Q40A1A1S7S64A1M0Sa1S63SbaVsegs;R5R4R6SeG0Sb5R3Sb6R2R1A2A4A5S1S77S25S2aR6A1S29S40R7A1M1A1A3S77S23S32Vsegs;R6Sc3R2R5R3A3A3S27G1A1A3A2F_;Fmd;Fms;Ftr;Ftp;Fr;FX;").
Proof.
  intros X r tp tr ms md Hsp. pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm.
  split; [exact (smatch_pending_facts _ _ _ _ _ _ Hsm)|].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall.
Qed.

Lemma JG_K : ltac2:(tb__ "0|1|
S18S18F_;S18S5bS22S58Q40A1M0S22S7G0A1S7S64A1S63VJG;R9R8R7R6R5R4R3R2R1A9R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof. intros BX A Kc rho a r tp tr md HJ. exact (JGs_K nW st nx BX A Kc rho a r tp tr md HJ). Qed.
Lemma JG_okf : ltac2:(tb__ "0|0|
S18S18F_;S7bOF_;S18S7S64A1S63OF_;F_;S22S58Q40A1S73Vsegs;R5S72R3A1A3S73Vsegs;R6VJG;R7R5R4R3R2A5A3F_;Fa;Frho;FKc;FA;Fok;FBX;").
Proof. intros BX ok A Kc rho a Hokl r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). exact (JG_K _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma JG_okp : ltac2:(tb__ "0|0|
S18S18F_;S7bOF_;S18S7S64A1S63OF_;F_;S22S58Q40A1Sb9Vsegs;R5S72R3A1A3Sb9Vsegs;R6VJG;R7R5R4R3R2A5A3F_;Fa;Frho;FKc;FA;Fok;FBX;").
Proof. intros BX ok A Kc rho a Hokp. apply (ok_pframeA_liftKA segs ok Kc). exact Hokp. intros r t tr md HJ. exact (JG_K _ _ _ _ _ _ _ _ _ HJ). Qed.
Lemma JG_stable : ltac2:(tb__ "0|0|
S18S18F_;S18S5bS22S58Q40A1Sb3VW;Vst;A2S5fR4A1S75Vsegs;VGS;VJG;R7R6R5R4R3A5A3F_;F_;Fa;Frho;FKc;FA;FBX;").
Proof. intros BX A Kc rho a HUS HKc. exact (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc). Qed.

Lemma gen_x11 : ltac2:(tb__ "0|1|
S18S18F_;S18S5bS22S58Q40A1M0S41S41S93S22S7G0A1S7bSb3VW;Vst;A2S5fRaA1S0S8S42R8S85R8A1R6A3S9A3S0S8S90R7VGS;A2S9A3S0S24S91R8S26S40RaA1A1A2S89A3S0S8S97S25S34S26S40S85RbA1A1A1A1S88S26S40RbA1A1A1A3S9A3S0S41Sb8S88S26S40RcA1A1A1S85RcA1A2RbA3S71Vsegs;VJG;R12R11R10RfReA5RdRaR9R8A6S71Vsegs;VJG;R13R12R11R10RfA5RdS92RbRcA2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fr;Fs;FL;FX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a X L s r tp w HUS HKc HE HID HG HFB HL Hsp. rewrite <- HL.
  apply (SPA_entails_sem segs (JG BX A Kc rho a) GS X (genL X) (F_l2 (ss_next (ax_S X))) s r tp w HE HID (JG_stable BX A Kc rho a HUS HKc) HFB); [|exact Hsp].
  intros rr t' tr' md' HJ _. destruct (x11e3_val BX A Kc rho a rr t' tr' md' HJ) as [_ B].
  unfold F_l2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds eval rho_sub rw]; rewrite HG, u64_lit by lia; clear -B; lia.
Qed.

Lemma join4 : ltac2:(tb__ "0|1|
S18S18F_;S18S5bS22S58Q40A1M0S41S41S93S22S7G0A1S7bSb3VW;Vst;A2S5fRaA1S0S8S42R8R7R6A3S9A3S0S8S90R7VGS;A2S9A3S71Vsegs;VJG;RfReRdRcRbA5RaR7R6R5A6S71Vsegs;VJG;R10RfReRdRcA5RaS92R8R9A2R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fr;Fs;FT;FY;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a Y T s r tp w HUS HKc HE HID Hsp.
  exact (SPA_entails0 segs (JG BX A Kc rho a) GS Y T s r tp w HE HID (JG_stable BX A Kc rho a HUS HKc) Hsp).
Qed.

Definition JGo (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|7|
S22S7S58Q40A1M0A1S7S64A1S63S19VA;A1S1eS48S1dR1A1S1bVA;A1A2S5S2S63S63S1VJG;VAX;VA;VKc;Vrho;Va;R7R6R5R1A9S1S2aR7S30SaaS28SaeA1S28SafA1A3A2S1S77S25S2aR7A1S87A3S1S0S7ScG0G0A2A1M1S67S65R4A1M2A1S67S65R1A1M3A1A3S1S0G1S68G2A1S68G3A1A3S1S0G1S6eG2A1S6cS6eG3A1M4R2S48R2S82A2M5A3A3S1S0G1S6aR4A1S6cS6aR1A1M6R2G5A3A3S1S0S5S6dG2A1S6dG3A1A3S1S0S5S66G2A1S66G3A1A3S1Sc0G4A1S1Sc0G6A1S1S47Sc2R4R6A2S48Sc2R1R6A2S82A2A2VKc;R5R4A2A2A2A2A2A2A2A2A2A2A2A2A2Lmd0;A2TPB;TG;Lmd';Ltr;Ltp;Lr;").

Section G3.

Variables (D2 U2 X3a X3b CS3 G3 X3a3 L3a L3b CO3b T4a T4b Y4a0 Y4a1 Y4b0 Y4b1 : axst).
Variables (sLa sLb s4a0 s4a1 s4b0 s4b1 : wsub).

Hypothesis WU2 : ltac2:(tb__ "0|0|
S0S8S35S40VU2;A1A1S9A3").
Hypothesis DU2 : ltac2:(tb__ "0|4|
S0SfScS7ScS24S24A2M0A1M1S7S25A1M2A2M3A1SbfS40VD2;A1S40VU2;A1A2S11G3SeG1G2SbG0A1S87A4A2A3").
Hypothesis NXU2 : ltac2:(tb__ "0|0|
S0S6S26S40VU2;A1A1S26S40VD2;A1A1A3").
Hypothesis HU2 : ltac2:(tb__ "0|0|
S0S41S43VD2;S40VU2;A1A2VU2;A3").

Hypothesis Cert3 : ltac2:(tb__ "0|1|
S0S8Sb7S94Ufa0SaS5Z7050cSaS5Z40f5cSbS5A1A3A3VGS;SaS41VU2;SbS41A1M0A3SaS41VX3a;SaS41VX3b;G0A3A3A6S9A3").

Hypothesis WC3 : ltac2:(tb__ "0|0|
S0S8S35S40VCS3;A1A1S9A3").
Hypothesis DC3 : ltac2:(tb__ "0|4|
S0SfScS7ScS24S24A2M0A1M1S7S25A1M2A2M3A1SbfS40VX3a;A1S40VCS3;A1A2S11G3SeG1G2SaG0SeS24S24S8dS86A4SbG0A1A3SbS25A1A4A2A3").
Hypothesis NXC3 : ltac2:(tb__ "0|0|
S0S6S26S40VCS3;A1A1S26S40VX3a;A1A1A3").
Hypothesis HC3 : ltac2:(tb__ "0|0|
S0S41S43VX3a;S40VCS3;A1A2VCS3;A3").
Hypothesis FX3a : ltac2:(tb__ "0|0|
S95S25SdS25SaS25S30SaaS28SaeA1S28SafA1A3SbS25A1A3S87A3S29S40VX3a;A1A1A3").
Hypothesis IC3 : ltac2:(tb__ "0|0|
S0SfSabA1ScaS94S3eS40VCS3;A1A1A2S11SabSadA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1Z11A2S2bZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S24S2eS40VCS3;A1ZaA2S86A3").
Hypothesis BBw : ltac2:(tb__ "0|0|
S0S8S3fS26S40VCS3;A1A1S86A2S9A3").
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
S0S7ScScS24S24A2S24A2M0A1S78S23G0S76S27S40VCS3;A1A1A4S78S23G0S76SdS23SaS23S8bVnx;A1SaS23S8aVnx;A1SbS23A1M1A3A3SdS23SbdVnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC3 : ltac2:(tb__ "0|0|
S95S25SdS25S62VW;Vst;A2S61S60A1A3S29S40VCS3;A1A1A3").
Hypothesis FCS3 : ltac2:(tb__ "0|0|
S95S25SdS25SaS25S30SaaS28SaeA1S28SafA1A3SbS25A1A3S87A3S29S40VCS3;A1A1A3").
Hypothesis NXS3 : ltac2:(tb__ "0|0|
S0S8Sc6VGS;S26S40VCS3;A1A1A2S9A3").

Hypothesis HG3 : ltac2:(tb__ "0|1|
S0S41S43VCS3;Sc9S40VCS3;A1M0S86SdS23S27G0A1SaS23S8cSbS23A1A3A3S26G0A1A4A2VG3;A3").

Hypothesis Cert3a : ltac2:(tb__ "0|1|
S0S8Sb7S94Ufa0SaS5Z40f5cSbS5A1A3VGS;SaS41VG3;SbS41A1M0A3SaS41VX3a3;G0A3A6S9A3").

Hypothesis ELa : ltac2:(tb__ "0|0|
S0S8S42VX3a3;S85VX3a3;A1VsLa;A3S9A3").
Hypothesis IDa : ltac2:(tb__ "0|0|
S0S8S90VsLa;VGS;A2S9A3").
Hypothesis GLa : ltac2:(tb__ "0|0|
S0S24S91VsLa;S26S40VX3a3;A1A1A2S89A3").
Hypothesis FBLa : ltac2:(tb__ "0|0|
S0S8S97S25S34S26S40S85VX3a3;A1A1A1A1S88S26S40VX3a3;A1A1A1A3S9A3").
Hypothesis HL3a : ltac2:(tb__ "0|0|
S0S41Sb8S88S26S40VX3a3;A1A1A1S85VX3a3;A1A2VL3a;A3").
Hypothesis ELb : ltac2:(tb__ "0|0|
S0S8S42VX3b;S85VX3b;A1VsLb;A3S9A3").
Hypothesis IDb : ltac2:(tb__ "0|0|
S0S8S90VsLb;VGS;A2S9A3").
Hypothesis GLb : ltac2:(tb__ "0|0|
S0S24S91VsLb;S26S40VX3b;A1A1A2S89A3").
Hypothesis FBLb : ltac2:(tb__ "0|0|
S0S8S97S25S34S26S40S85VX3b;A1A1A1A1S88S26S40VX3b;A1A1A1A3S9A3").
Hypothesis HL3b : ltac2:(tb__ "0|0|
S0S41Sb8S88S26S40VX3b;A1A1A1S85VX3b;A1A2VL3b;A3").

Hypothesis HCOb : ltac2:(tb__ "0|0|
S0S41S8fVL3b;S8eA2VCO3b;A3").
Hypothesis WCOb : ltac2:(tb__ "0|0|
S0S8S35S40VCO3b;A1A1S9A3").
Hypothesis XCb : ax_X L3b = [].
Hypothesis SKb : ltac2:(tb__ "0|2|
S0S7ScScS24S24A2S24A2M0A1S78S23G0S76S27S40VL3b;A1A1A4S78S23G0S76SdS23SaS23S8bVnx;A1SaS23S8aVnx;A1SbS23A1M1A3A3SdS23SbdVnW;Vnx;A2G1A3A3A4A3").
Hypothesis FCb : ltac2:(tb__ "0|0|
S95S25SdS25S62VW;Vst;A2S61S60A1A3S29S40VL3b;A1A1A3").
Hypothesis FXb : ltac2:(tb__ "0|0|
S95S25SaS25S36S30SaaS28SaeA1S28SafA1A3A1SbS25A1A3S29S40VL3b;A1A1A3").

Hypothesis Cert4a : ltac2:(tb__ "0|1|
S0S8Sb7S94Ufa0SaS5Z3c480SbS5A1A3VGS;SaS41VL3a;SbS41A1M0A3SaS41VY4a0;SaS41VY4a1;G0A3A3A6S9A3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0S8S42VY4a0;VT4a;Vs4a0;A3S9A3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0S8S90Vs4a0;VGS;A2S9A3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0S8S42VY4a1;VT4a;Vs4a1;A3S9A3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0S8S90Vs4a1;VGS;A2S9A3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0S8Sb7S94Ufa0SaS5Z3c480SbS5A1A3VGS;SaS41VCO3b;SbS41A1M0A3SaS41VY4b0;SaS41VY4b1;G0A3A3A6S9A3").
Hypothesis E4b0 : ltac2:(tb__ "0|0|
S0S8S42VY4b0;VT4b;Vs4b0;A3S9A3").
Hypothesis I4b0 : ltac2:(tb__ "0|0|
S0S8S90Vs4b0;VGS;A2S9A3").
Hypothesis E4b1 : ltac2:(tb__ "0|0|
S0S8S42VY4b1;VT4b;Vs4b1;A3S9A3").
Hypothesis I4b1 : ltac2:(tb__ "0|0|
S0S8S90Vs4b1;VGS;A2S9A3").

Lemma RSU : ltac2:(tb__ "0|1|
S18S5bS22S58Q40A1M0S22S7G0A1S7bS49S48S4aS10S1cS1aR7A1A2A1Z1A2S4bZ2Z14A2A2S71Vsegs;VJG;VAX;R8R7R6R5A5VD2;R4R3R2A6S71Vsegs;VJG;VAX;R9R8R7R6A5VU2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hok Hw. destruct w as [tr [ms md]]. rewrite <- HU2.
  eapply SPA_restate; [exact WU2 | exact DU2 | exact NXU2 | constructor | | exact Hw].
  exact (F_g3_hold AX A Kc rho a rhoX tp tr md (proj2 Hw) Hok).
Qed.

Lemma SPA_facts : ltac2:(tb__ "0|0|
S74S41S22S7S58Q40A1A1S7bS7S25A1S71Vsegs;R6R5R4R3R2A6S95S25R2S29S40R6A1A1A3S77S25S2aR6A1R3A3F_;F_;FF;Fw;Ftp;Fr;FX;FJ;").
Proof.
  intros J X r tp w F Hsp HF.
  pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFall.
  apply Forall_forall. intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (HF p Hp)).
Qed.

Lemma RS3 : ltac2:(tb__ "0|1|
S18S5bS22S58Q40A1M0S22S7G0A1S7bS71Vsegs;VJG;VAX;R7R6R5R4A5VX3a;R3R2R1A6S71Vsegs;VJG;VAX;R8R7R6R5A5VCS3;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HC3.
  pose proof (SPA_facts _ _ _ _ _ _ Hw FX3a) as HF. apply Forall_app in HF as [HB HF]. apply Forall_inv in HB.
  destruct (ens_site AX A Kc rho a rhoX tp tr md AXg AXs AXp (proj2 Hw) HB HF) as (_ & _ & EA0 & EBw & _).
  eapply SPA_restate; [exact WC3 | exact DC3 | exact NXC3 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq. rewrite EA0, EBw. reflexivity.
Qed.

Lemma region_free_of_apart : ltac2:(tb__ "0|2|
S7ScS58Q40A1M0G0A2M1A1G0G0G1S96G1R1R4A3SbbSeG0G0R4R3A4R2A2F_;Fe;S0S8S69R4R3R2A3S9A3F_;Fn;Fa;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite (IH a n) by (intros e He; apply H; right; exact He). rewrite andb_true_r.
  pose proof (H (b, s) (or_introl eq_refl)) as X. unfold apartW in X. cbn [fst snd] in X.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct X as [X|X]; [right|left]; apply Z.ltb_ge; lia.
Qed.
Lemma apartW_sub : ltac2:(tb__ "0|4|
S58Q40M0A1M1G1ScG1G1A2M2G2S47S59G0S13G1G1R2A3A2S59G0R4A2M3A2S47S48S59G0R5A2G3A2S48S59G0S13G1G1R3A3A2S59G0S14G1G1R3A3A2A2A2SbbR4R3A2SbbSeG1G1R7R6A4R4A2F_;F_;F_;Fe';Fe;Fn;Fa;").
Proof. intros a n e e' H1 H2 [X|X]; unfold apartW in *; cbn [fst snd] in *; [left|right]; lia. Qed.

Lemma maps_disjoint_pick : ltac2:(tb__ "0|4|
S7ScS58Q40A1M0G0A2M1A1M2G2G1G2SbcSdG1R4SdG1R3SaG1R2R1A3A3A3A1S1G1S96G1R1R6A3SbbR5R2A2M3F_;Fe';G1S96G1R1SdG1R5R3A3A3G3F_;Fe';A2F_;Fl2;Fe;Fl1;FR;").
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
S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1S63G1G1VJG;VAX;RaR9R8R7R6R5R4R3A9S19RbA1S1eS47S1dR1A1S59G0R4A2M2A2S47S48S59G0R5A2M3G2A2S48S1dR2A1S7eA2A2S1S0S8S69S68S65R7A1M4A1R6R5A3S9A3S1S0S8S6bS67G4A1M5R6R5A3S9A3S47Sc1G5S59G0R6A2M6S48G6G3A2A3G3A2A2A2F_;F_;TG;F_;Fn0;Fa0;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
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
S18S18F_;S18S5bS22S58Q40A1M0S22S7G0A1S7S64A1S63S5S5VJG;RbRaR9R8R7R6R5R4R3A9S4S47R2S80A2S47S7fR3A2A2S7S23A1S0S7ScScS24S24A2S24A2M1A1S78S23G1S76R1A4S78S23G1S76SaS23S8bVnx;A1SaS23S8aVnx;A1SbS23A1A3A3A4A3S77S23S23S33S31RbR1A2SeS5S5R7R6A4A2Lo;R2A3F_;Fl;F_;F_;Fh2;Flo;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
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
S18S5bS22S58Q40M0A1M1S22S7G1A1S0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;S5fR6A1S49S48S4aS10S1cS1aR8A1A2A1Z1A2S4bZ2Z14A2A2S7S64A1M2Sa1S63SbaVsegs;R8R7VCS3;SeG2Sb5R3Sb6R2R1A2A4A5VJG;VAX;RdRcRbRaR9R8R4R2A9S2cRaS86A2G1S59G0R1A2M3S5Z20000S5S1S0S5S4cR2Z1000A2Z0M4A3S1S49G4R2A2S1S47S48R2R1A2M5S66S65R6A1M6A1A2S1S0S8S69S68G6A1R3S5aG0R1A2M7A3S9A3S1S0S8S6bS67G6A1M8R3G7A3S9A3S1S47Sc1G8R2G5A3R1A2S1S53Sc4R6RcA2R1A2S1S23S96S23R1S27S40VCS3;A1A1A3S33S31RfR2A2SeS5S5R4S48R4R3A2A4A2F_;Fo;S1G1S1S47R3G3A2S49G3S48R3R2A2A2A2S0S8S3dVsegs;R2A2S16A3F_;Fx;S1ScS24S24A2M9S5S96G9R2S44VCS3;A1A3S1S47S59G0S2cR10S13S24S24R3A3A2A2MaR2A2S49R2S48GaS59G0S2cR10S14S24S24R3A3A2A2A2A2A2S3S1S47R6S59G0S46S59G0S2cR11S45VCS3;A1A2A2R3A2A2MbA2S49GbS48R6R5A2A2A2A1F_;F_;Fy;Frr;S9bR11R10RfReRdRcR8S6fR2G5S70Sc7G6R3G7A3R6A2A3A8A2A2A2A2A2A2A2A2A2A2Tnlit;Tua;Ta0;F_;F_;Fmd;Fms;Ftr;F_;F_;F_;Ftp;FrhoX;Fa;Frho;FKc;FA;").
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
S0S7S23A1S27S40VG3;A1A1SdS23S27S40VCS3;A1A1SaS23S8cSbS23A1A3A3A3").
Proof. rewrite <- HG3. reflexivity. Qed.
Lemma XG3 : ax_X G3 = [].
Proof. rewrite <- HG3. cbn. exact XC3. Qed.
Lemma OSECI : ltac2:(tb__ "0|0|
S2S23S23S1S96S23R1S27S40VCS3;A1A1A3S0ScScS24S24A2S24A2S76R1A1S76Sb0A1A3A2Lo;A2").
Proof.
  assert (IN : In (skel O_seci) (map skel (ss_objs (ax_S CS3)))).
  { rewrite SK3. rewrite !map_app. apply in_or_app. right. apply in_or_app. left. unfold SKEL0. rewrite !map_app.
    apply in_or_app. left. apply in_or_app. right. unfold RT_sec, N_sec, O_seci. cbn. left. reflexivity. }
  apply in_map_iff in IN as (o & Ho & Hin). exists o. split; [exact Hin | exact Ho].
Qed.

Lemma range_seci : ltac2:(tb__ "0|0|
S22S0ScS5S5A2S31R1Sb0A2SeS5S5S98S48S98Z40A2A4A3Fr;").
Proof.
  intros r. unfold O_seci, RT_sec, N_sec. cbn -[carve_obj SEC_INST Z.add].
  rewrite (carve_range r _ (proj1 (Forall_forall _ _) N_sec_small _ ltac:(unfold N_sec; left; reflexivity))).
  unfold spec_range. cbn [fst snd eval]. rewrite u64_lit by lia. f_equal; lia.
Qed.

Lemma ensure_post : ltac2:(tb__ "0|5|
S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1M2Sa1S63S0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;S59G0S2fR8PcA2A2S5S59G0R8A2S5Sb4R2A1S5S5S1S47S81R3A1M3R1A2S49R1S48G3S4eR2Z8A2A2A2A2S3S0SfS58Q8A1M4A1S2dRdS5aG0R2A2A2S12G4A1A3A1F_;Fz;S71Vsegs;S9bReRdRcRbA4VG3;RaR9SeG2Sb5R8Sb6R7R6A2A4A6S2S22S22S2S22S22S1S99S19R11A1R6R5RfR1A5S71Vsegs;VJG;S9aR11R10R1ReA5VG3;R2RcSeG2Sb5RbSb6RaR9A2A4A6A2Lrho'';A2Lr2;A2F_;F_;TL;Tua;Tnv;F_;Fmd';Fms;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
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
  unfold JG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs. cbn [rw rho'']. fold nv.
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
S18S18Fx;S18S5bS22S58Q40M0A1M1S22S7G1A1S7S64A1S63S18S0S1eS19RaR1A1A1S19R1A1A3FX;S18S0S7S1cA1S1aRbR1A1A1S1aR1A1A3FX;S18S0S5S1bRcR1A1A1S1bR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S2aR8S36S30SaaS28SaeA1S28SafA1A3A1A2S19RdA1S1eS1bReA1S5S48S1dR2A1S4fZ8M2S4aS10S1cS1aRfA1A2A1A2A2S5S1S0S5S59G0S2cRcS86A2A2R1A3S1S47S1dR3A1M3R1A2S1S47S48R1G2A2S48G3R2A2A2S1S47R2S7eA2S1S47S83G3A2S1S4S47S48G3S7eA2S80A2S47S7fG3A2A2S5S1S47R2R1A2S49R1S48R2G2A2A2A2S2S58Q8A1M4G4S0SfG4A1Sc5S94S2dRfA1R3A3S11G4R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2Tlo;Tc;TG;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
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
S18S5bS22S58Q40A1M0S22S7G0A1S7bS0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;S71Vsegs;VJG;VAX;R8R7R6R5A5VL3b;R4R3R2A6S71Vsegs;VJG;VAX;R9R8R7R6A5VCO3b;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fa;Frho;FKc;FA;").
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
S7bOF_;S18S5bS22S58Q40A1M0S7dS0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;Sb3VW;Vst;A2S5fR6A1S73Vsegs;R9S72R7A1A3S22S7G0A1M1S7cVsegs;RcS71Vsegs;VJG;VAX;RbRaR9R8A5VT4b;R2R1A5R7A4FtY;FrY;S22G1S7cVsegs;RdS71Vsegs;VJG;VAX;RcRbRaR9A5VX3b;R2R1A5R8A4Ftp;Fr;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
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
S7bOF_;S18S5bS22S58Q40M0A1M1S7dS0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;Sb3VW;Vst;A2S5fR6A1S73Vsegs;R9S72R7A1A3Sb9Vsegs;RaS72R8A1A3S49S48S4aS10S1cS1aRaA1A2A1Z1A2S4bZ2Z14A2A2S59G0S2fR9PcA2A2S5S59G0R9A2S5Sb4R2A1S5S5S1S47S81R3A1M2R1A2S49R1S48G2S4eR2Z8A2A2A2A2S3S0SfS58Q8A1M3A1S2dReS5aG0R2A2A2S12G3A1A3A1F_;Fz;S22S22S7G1A1M4S99S19R12A1R6R5R10R3A5S7cVsegs;R14S71Vsegs;VJG;S9aR13R12R4R10A5VT4a;R3R2A5RfA4F_;FtY;FrY;Frho'';S22G4S7cVsegs;R13S71Vsegs;VJG;VAX;R12R11R10RfA5VX3a;R2R1A5ReA4Ftp;Fr;F_;F_;TL;Tua;Tnv;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
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
S7bOF_;S18S5bS22S58Q40M0A1M1S7dS0S5eVst;S5dA3S0S7S5cA1VW;SbS5cA1A3F_;Sb3VW;Vst;A2S5fR6A1S73Vsegs;R9S72R7A1A3Sb9Vsegs;RaS72R8A1A3S49S48S4aS10S1cS1aRaA1A2A1Z1A2S4bZ2Z14A2A2S59G0S2fR9PcA2A2S5S59G0R9A2S5Sb4R2A1S5S5S1S47S81R3A1M2R1A2S49R1S48G2S4eR2Z8A2A2A2A2S3S0SfS58Q8A1M3A1S2dReS5aG0R2A2A2S12G3A1A3A1F_;Fz;S22S22S7G1A1M4S99S19R12A1R6R5R10R3A5S7cVsegs;R14S71Vsegs;VJG;S9aR13R12R4R10A5VT4a;R3R2A5RfA4F_;FtY;FrY;Frho'';S22G4S7cVsegs;R13S71Vsegs;VJG;VAX;R12R11R10RfA5VT4b;R2R1A5ReA4FtY;FrY;S22G4S7cVsegs;R14S71Vsegs;VJG;VAX;R13R12R11R10A5VD2;R2R1A5RfA4FtX;FrX;F_;F_;F_;TL;Tua;Tnv;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
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

End SpineMallocSec4.

(* [comment removed for export] *)
Module DepotCallW.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "mul"; "opp"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "sobj"; "sprop"; "rw"; "sstate"; "SVar"; "ss_next"; "ss_facts"; "SPUle"; "sv_eqb"; "SAlu"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_below"; "ss_objs"; "eval"; "swf"; "SExt"; "holds"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nat"; "nil"; "pair"; "prod"; "false"; "option"; "andb"; "orb"; "Some"; "app"; "None"; "fst"; "length"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.DepotCallW.DCW"; "X4"; "isSome"; "site_facts"; "X4r"; "osplit"; "permW"; "F_call"; "T4b"; "T4d"; "X4a"; "X4b"; "X4c"; "X4f"; "zoneR"; "R4_families"; "T40"; "T4a"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "in_famb"; "prim_fitb"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_depot"; "ag_spacebeg"; "topG"; "ag_ctx"; "ag_thread"; "sec_chunk"; "ageom"; "DG"; "aa_live"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"; "nocells"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E4d"; "C5"; "upd"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "PIECES"; "V_CNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "J_alloc_preT"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "rz"; "ClassID"; "IMG_HI"; "IMG_LO"; "Sh"; "is_primary"; "kSpaceSize"; "needed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.Riscv.Instr";
"ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DFP"; "JLD"; "MAP1"; "MAP1N"; "STORE"; "dfp_static"; "DFPw"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "chk_of"; "cnt_of"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "inv3"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "HD_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "pvals_ok"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE"; "HDE_stmt"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "lt"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DCW.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Hypothesis HUS : stopJ_stable W st.

Hypothesis HUSr : ltac2:(tb__ "0|1|
S15S15S9Se0R1Sc2A2ScS68Q40A1S1aR3R2A2S1aR4R2A2A3F_;Fi;S89VW;Vst;R3A3M0G0F_;F_;Fr';Fr;").
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S8Sd9VCST;R1A2SfSbaR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S86VAInv;VW;Vst;VA;VKc;S1cPcA1A6").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Local Notation KEEPD := (DepotCall.KEEPD CST XGL).

Definition F_call : list sprop := ltac2:(tb__ "0|3|
S2fS19S1fS17Z7fff7f800000A1M0S1cPaA1M1A2S2fS19S1fG0S21SafG1S17Nee0A1A3A2S2fS19S1fG0S21SafG1S17N840A1A3M2A2S2fS19S1fG2S17S7S4Z2Z40A2Z840A2A1A2S31S19A1A3A3A3A3").
Definition X4f : axst := ltac2:(tb__ "0|0|
Sd5S45S6eVW;Vst;Vtmax;A3A2").
Definition X4r (sz : Z) : axst := ltac2:(tb__ "0|1|
S70VW;Vst;Vtmax;S4bZ7e850S2fS33S30S16A2M0S32S30S16UbS17Vsz;A1A4S31G0A1A3S31S18A1S34S31S19A1A9").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9cS10VA;A1Vi;Vmid;A3S1bS13VA;R1A2LS';VA;X35x2").
Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
Definition X4a (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S42Vsz;A1U0S17Nee0A1A3").
Definition X4b (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S48Vsz;A1U1S17N8e0A1A3").
Definition X4c (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S49Vsz;A1U2S17N840A1A3").
Definition X4 (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S4aVsz;A1U3S17N48A1A3").
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS2cSdfSc2S1dS10S6eVW;Vst;Vtmax;A3A1A1A2S2eA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS2cS8fS19S26S1dS10S6eVW;Vst;Vtmax;A3A1A1A1S45A3S2eA3").
Hypothesis XE4 : ltac2:(tb__ "0|1|
ScS2dS33S16S16A2M0A1S12S6eVW;Vst;Vtmax;A3A1S31G0A1A3").
Hypothesis F192 : ltac2:(tb__ "0|1|
S91S19S2fS19S1fS17Z1A1S1cPc0A1M0A2S2fS19S1fG0S17Vtmax;A1A2S31S19A1A3A3S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S91S19S87S84A1S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FUNW : ltac2:(tb__ "0|0|
S91S19S88VW;Vst;A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FGEN4 : ltac2:(tb__ "0|0|
S91S19S71S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP4 : ltac2:(tb__ "0|0|
S90S19S1fS17Z1A1S1cS77A1A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis WX4r : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS29S10S42R2A1A1A1S2eA3F_;Fsz;").
Hypothesis DX4r : ltac2:(tb__ "0|4|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S33S2dS33S16S16A2M0A1M1S2dS19A1M2A2M3A1SccS10S4bA1S10S42R2A1A1A2S38G3S32G1G2S2fG0S32S16S16S2aS34Q20S1cPc0A1A3S17R2A1A4S31G0A1A3S31S19A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S42R2A1A1U0S17Nee0A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S48R2A1A1U1S17N8e0A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S49R2A1A1U2S17N840A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S4aR2A1A1U3S17N48A1A3A2S2eA3F_;Fsz;").

Definition call_pack (X : axst) (sz : Z) : option (wsub * list sobj * axst) := ltac2:(tb__ "0|6|
S2fS33S9S16A2M0S32S9S16PfS17N600A1A4Sd1P1S10VX;A1S10S66Vsz;A1M1A1A3A3S2dG0A1M2S35S2dS18A1M3A1S35S33S33S99G3A2S11A2M4A1Lx;Sa2VX;G1R1A3G3S38S33S33G2G3A2M5S11A2S32G5S11S32G2G3R2R1A4S9eR2G1S65Vsz;A1VX;R1A5A4A2LR;S3aG4A1X35x2Ts;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Hypothesis HER : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S2dS18A1M0A1Sa2S3fR2A1S66R2A1Vs4;R2A1A3S38G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS11S9eVs4;R2A1S66R2A1S65R2A1S3fR2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12S3fR2A1A1S31G0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10S3fR2A1A1M0A1A1S1eG0A1A3S2eA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cSa3S3fR2A1S66R2A1Vs4;R2A1VR4;R2A1S2fS11S65R2A1S31S11A1A3A5S2eA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS9S1dS10S3fR2A1A1A1S1dS10S6eVW;Vst;Vtmax;A3A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PaM0A2S21SafS1cG0A1S17N8e0A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PfA2S17N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PcA2S21SafS1cPaA1S17N840A1A3A3F_;Fsz;").

Definition R4_families : list sobj := ltac2:(tb__ "0|0|
S39S18SceS39S18S2fS18S72S2fS18S74S2fS18S73S2fS18S75S31S18A1A3A3A3A3S76A3A3").
Definition in_famb (o : sobj) : bool := ltac2:(tb__ "0|3|
S37S92S18S18SdaS67Vo;A1S67R1A1A2Lo';S39S18S4dS85VW;A1A3A3S36S20S22Vo;A1S1cPaA1A2S16S2cLx;S24Vo;A1S8S36S3N8e0R1A2S3R1Z0A2A2Llo;S9S36SdeR1S83A2S20S23Vo;A1S17Nee0A1A2A2Li;Sb0S16S16S34Lb;La;M0Lop;M1G1Sb1G0Lop;M2G2S2cSaS16S34La;Lw;Lsgn;S9S16S8S34Lk;Li;Ll;X16x8A2A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS18S54VR4;R2A1A3S2eA3F_;Fsz;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS18A1Sb4S10S66R2A1A1S10S65R2A1A1A2S31S18A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S8ScS2dS33S16S16A2M0A1S12S65R1A1A1S31G0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10VT4;R2A1A1A1A1S1eS10S3fR2A1A1A1A3S2eA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12VT4;R2A1A1S31G0A1A3F_;Fsz;").
Definition T40 (sz : Z) : axst := ltac2:(tb__ "0|0|
Sd6VT4;Vsz;A1S1eS10S3fVsz;A1A1A1A2").
Definition oreb (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9dS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition omrg (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9bS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition T4a (sz : Z) : axst := oreb (T40 sz) 0.
Definition T4b (sz : Z) : axst := oreb (T4a sz) 1.
Hypothesis RB1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4eR2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4fR2A1A1U1A2A2S2eA3F_;Fsz;").
Definition permW (n : nat) : list nat := ltac2:(tb__ "0|1|
S39S30S2fS30U9S2fS30U0S2fS30UaS2fS30U1S2fS30UbS2fS30U2S2fS30U3S2fS30U4S2fS30U5S2fS30U6S2fS30U7S2fS30U8S31S30A1A3A3A3A3A3A3A3A3A3A3A3A3Sc1UcM0Sd0Vn;G0A2A2A3").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS2cSd2S44Vnobj;A1A1S2eA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS2cS8fS30S30SddR1Vnobj;A2Li;S44Vnobj;A1A3S2eA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS2cS8fS30S30S92S30SdcR1A1S44Vnobj;A1A3Li;Sc1U0Vnobj;A2A3S2eA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS30S3cS18S27S10S46R2A1A1A1A2Vnobj;A3F_;Fsz;").
Definition T4c (sz : Z) : axst := ltac2:(tb__ "0|2|
S13S46Vsz;A1M0Sd4S10G0A1M1Sd3S27G1A1S44Vnobj;A1A2A2A2").
Definition T4m1 (sz : Z) : axst := omrg (T4c sz) 0.
Definition T4m2 (sz : Z) : axst := omrg (T4m1 sz) 0.
Definition T4m3 (sz : Z) : axst := omrg (T4m2 sz) 0.
Definition T4d (sz : Z) : axst := omrg (T4m3 sz) 0.
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S50R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S51R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S52R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S53R2A1A1U0A2A2S2eA3F_;Fsz;").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS14S47R2A1S6fVW;Vst;Vtmax;A3Vsd;R2A1A3S2eA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS9aVsd;R2A1Sc2A2S2eA3F_;Fsz;").

Hypothesis R4cov : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS94S1eS10S47R2A1A1M0A1VR4;R2A1S27G0A1A3S2eA3F_;Fsz;").

Definition rt_okD (o : sobj) : bool := ltac2:(tb__ "0|b|
S16S2cLx;M0S24Vo;A1S8G0S23Vo;A1S8S37S37S36S20S22Vo;A1M1S17Z0M2A1A2S36S36S36S3Sa9R2A2S3R2R1A2M3A2S3R1Sa8A2A2S37S3R1Sb9A2S3S1Sb7S5Z8Sb8A2A2R2A2A2A2A2S36S20G1S1cP97A1A2S36S36S3G2R2A2G3A2S3R1Z1000A2A2M4A2A2S36S20G1S1cP98A1A2G4A2A2Lhi;S9S34Li;M5Sb0S16S16S34Lb;La;M6Lop;M7G7Sb1G6Lop;M8G8S2cSaS16S34La;Lw;Lsgn;M9S9S16S8S34Lk;Li;Ll;MaX16x8Llo;G5G7G7G8G8G9GaX16x8").
Lemma RT_m1_okD : ltac2:(tb__ "0|0|
ScS2cS8fS18S56SceA3S2eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma obj_range_nocells : ltac2:(tb__ "0|0|
S15S18ScS33S8S8A2S25R2S67R1A1A2S25R2R1A2A3Fo;Frho;").
Proof. intros rho [b lo hi cs d]. reflexivity. Qed.

Definition zoneR (T C SB ab szc top a : Z) : Prop := ltac2:(tb__ "0|2|
SdSbSbS0Sa9Va;A2S2Va;Sa8A2A2SdS2Va;Sb9A2S0S1Sb7S5Z8Sb8A2A2Va;A2A2A2SdSbS0VT;Va;A2S2Va;S1VT;Z1000M0A2A2A2SdSbS0VC;Va;A2S2Va;S1VC;G0A2A2A2SdSbS0Vab;Va;A2S2Va;S1Vab;Vszc;A2M1A2A2SdSbS0SaaVab;A1Va;A2S2Va;SaaG1A1A2A2S0Vtop;Va;A2A2A2A2A2A2").

Lemma R4_zone : ltac2:(tb__ "0|a|
S8S15S57S18S8SbS0Z1M0R5A2S0R5Vtmax;A2A2S69Q40M1S1aR5PcA2A2S8ScfR6S5aS58R5A1A1SbdR1A1M2SbeR5R1A2Sa6R1A1Sa5G2A1R1A7SbS0G0SbfR6R2A2M3A2S0G3Z10M4A2A2ScS68G1A1M5S1aR8P97A2S6aG1S5dS58R7A1A1A2A3ScG5S1aR9P98A2S6aG1S5cS58R8A1A1A2A3ScG5S1aRaP95A2S6aG1SbfR9R5A2A2A3Sc3S58RaA1A1S0S5bS58RbA1A1S1S69G1S1aRcPaA2A2S6bG1S1aRcS83A2A2A2A2S0S6bG1S1aRdS83A2A2S6S84A1A2Sc0S18S18SbSbS0S1S5bS58ReA1A1G4A2S69G1S28RfS22R1A1A2A2M6A2S0G6S4Z2M7Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3S90S18RdVR4;R10A1A3SbS0S3bS8S8S25R10ReA2M8A3RdA2S2RdS3eS8S8G8A3A2A2S1S1S5aS58R10A1A1S5SbdRcA1S4G7Z20A2A2A2S5G4SbeR10RcA2A2A2S8S4cS5dS58R11A1M9A1S5cG9A1S5aG9A1R1Sa5SbdRdA1A1S5bG9A1RfA7Tab;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tnv;F_;Fa;Fo;FA;FrhoX;Fsz;").
Proof.
  intros sz rhoX A o a Hsz nv PV Hcnt E151 E152 E149 HG TOP DEP LNK Ho Ha ab.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (pv_ab rhoX _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoX _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoX _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoX _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoX _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoX _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoX _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoX _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoX _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoX _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoX _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoX _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr.
  set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  set (szc := Size (cls_of nv)) in *. set (rzv := rz nv) in *. set (x := chk_of A nv) in *. set (c := cls_of nv) in *.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_le_mono nv (nv + 7) 8 ltac:(lia) ltac:(lia)) as Q1.
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(lia)) ltac:(tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. fold SB c x. lia. }
  assert (SHR : forall k, 0 <= k <= szc -> Sh ab <= Sh (ab + k) <= Sh (ab + szc)).
  { intros k Hk. unfold Sh. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  assert (SHK : forall k, 0 <= k -> Sh (ab + k) = Sh ab + k / 8).
  { intros k Hk. unfold Sh. destruct (proj1 (Z.mod_divide ab 8 ltac:(lia)) AB8) as [q Hq]. rewrite Hq.
    replace (q * 8 + k) with (q * 8 + k) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia. lia. }

  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_famb in Fo. apply orb_prop in Fo as [Fo|Fo].
  - apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoX o), Eo, (obj_range_nocells rhoX o') in Ha. clear Eo Ho o. rename o' into o.
    apply in_app_or in Ho' as [Ho'|HLK].
    2: {
      pose proof (proj1 (Forall_forall _ _) LNK o HLK) as (B & Elo & Ehi). destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in B, Elo, Ehi. subst olo ohi.
      rewrite obj_range_mk in Ha by (clear -B TG; lia). cbn [fst snd] in Ha. do 5 right. clear -Ha B. lia. }
    unfold R4_families in Ho'. apply in_app_or in Ho' as [HRT|Ho']; [|apply in_app_or in Ho' as [HPC|HPI]].
    +
      pose proof (proj1 (forallb_forall _ _) RT_m1_okD o HRT) as OK. unfold rt_okD in OK.
      destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
      destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
      destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
      apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
        apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
        apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
        unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
    +
      assert (EB : bv_unsigned (eval rhoX pc_base) = T + 0xd0 + 80 * c).
      { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
        rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia. }
      assert (ECH : soff rhoX choff = 16 + 4 * (cnt_of A nv - 1)).
      { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear - Hcnt; lia).
        replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
        replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
        change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
        unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
      assert (ET : bv_unsigned (eval rhoX vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
      right. left. destruct HPC as [<-|[<-|[<-|[<-|[]]]]].
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcc] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcs] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pck] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB, ECH in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_st] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite ET in Ha. cbn [fst snd] in Ha. lia.
    +
      assert (ELL : soff rhoX LLe = 2 * (rzv / 16 * 2) / 2).
      { destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr].
        apply soff_of_val; [|first [clear - Brz Hqr; lia | lia]]. unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by lia. change (3 mod 64) with 3.
        rewrite Z.shiftr_div_pow2 by lia. rewrite Hqr. replace (qr * 16 / 2 ^ 3) with (2 * qr) by (apply Z.div_unique with 0; lia).
        replace (qr * 16 / 16) with qr by (apply Z.div_unique with 0; lia). first [clear - Hqr Brz; lia | lia]. }
      destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr]. rewrite Hqr in ELL.
      replace (qr * 16 / 16) with qr in ELL by (apply Z.div_unique with 0; lia). replace (2 * (qr * 2) / 2) with (2 * qr) in ELL by (apply Z.div_unique with 0; lia).
      assert (SHab : Sh (ab + rzv) = Sh ab + 2 * qr). { rewrite (SHK rzv) by lia. rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (apply Z.div_unique with 0; lia). lia. }
      destruct HPI as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold obj_range, obj_lo_of, obj_hi_of in Ha;
        cbn [ob_base ob_lo ob_hi O_H O_UB O_T O_L O_U O_P O_R] in Ha; rewrite ?soff_lit_small in Ha by lia.
      * rewrite Eab in Ha. rewrite (soff_of_val rhoX (SVar V_RZ) rzv) in Ha by (cbn [eval]; unfold V_RZ; rewrite ?E150; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eub in Ha. rewrite (soff_of_val rhoX (SVar 12) nv) in Ha by (cbn [eval]; rewrite ?E12; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eue in Ha. rewrite (soff_of_val rhoX LTe _ Elt) in Ha by lia. cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Ebsh, ELL in Ha. cbn [fst snd] in Ha. do 4 right. left. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono rzv szc 8 ltac:(lia) ltac:(lia)). assert (rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia). lia.
      * rewrite Ebu in Ha. rewrite (soff_of_val rhoX LUe (nv / 8) Elu) in Ha by (first [clear - Bn Q0; lia | lia]). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono (rzv + nv) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr in M at 1. replace ((qr * 16 + nv) / 8) with (2 * qr + nv / 8) in M by (rewrite <- (Z.div_add_l (2 * qr)) by lia; f_equal; lia).
        lia.
      * rewrite Ebp in Ha. rewrite (soff_of_val rhoX LPe lp Elp) in Ha by (unfold lp; destruct (Z.eq_dec _ _); lia). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        pose proof (Z.div_le_mono (rzv + r8) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr, Q84 in M. fold lp in M.
        replace ((qr * 16 + (8 * (nv / 8) + (if Z.eq_dec (nv mod 8) 0 then 0 else 8))) / 8) with (2 * qr + nv / 8 + lp) in M.
        2:{ unfold lp. destruct (Z.eq_dec _ _); apply Z.div_unique with 0; lia. }
        unfold lp in *. destruct (Z.eq_dec _ _); lia.
      * rewrite Ebr in Ha. rewrite (soff_of_val rhoX LRe _ Elr) in Ha by (destruct R8F as (Q81 & Q82 & Q83 & Q84); pose proof (Z.div_le_upper_bound (szc - rzv - r8) 8) as DUB8; first [clear - Blr Bsz Brz Bn Q82 Q83 DUB8; lia | lia]).
        cbn [fst snd] in Ha. do 4 right. left. rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        assert (Y1 : r8 / 8 + (szc - rzv - r8) / 8 <= (szc - rzv) / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le r8 8 ltac:(lia)). pose proof (Z.mul_div_le (szc - rzv - r8) 8 ltac:(lia)). lia. }
        pose proof (Z.div_le_mono (szc - rzv) szc 8 ltac:(lia) ltac:(lia)) as Y2. pose proof (Z.div_pos r8 8 ltac:(lia) ltac:(lia)) as Y3.
        assert (Y4 : rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia).
        assert (Y5 : (szc - rzv) / 8 + 2 * qr <= szc / 8).
        { rewrite <- Y4. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (szc - rzv) 8 ltac:(lia)). pose proof (Z.mul_div_le rzv 8 ltac:(lia)). lia. }
        lia.
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoX 10%positive)) as R10. pose proof (srange (rw rhoX V_DEPTH)) as R15.
    do 5 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    +
      apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Definition prim_fitb (n : Z) : bool := ltac2:(tb__ "0|0|
S37S3dSabVn;A1A1S3S1Vn;Sa6Vn;A1A2Sa5Sa7SadVn;A1A1A1A2A2").
Lemma prim_fitb_all : ltac2:(tb__ "0|1|
S8SbS0Z1M0R1A2S2R1S1G0Z10000A2A2A2ScS2cS55R2A1S2eA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_fitb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prim_fit : ltac2:(tb__ "0|0|
S8S0Z1R1A2ScS2cSabR2A1S2eA3S0S1R3Sa6R3A1A2Sa5Sa7SadR3A1A1A1A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_fitb_all n ltac:(lia)) as H. unfold prim_fitb in H. rewrite HP in H. cbn [negb orb] in H. apply Z.leb_le in H. exact H.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma live_user_zone : ltac2:(tb__ "0|2|
Sd8S57S8S8S8Sc3S58R4A1A1Sc4R5A1Sc5R7R6A2Sc6R8R7A2S90S33S8S8A2S32S8S8R7R6A4S61R8A1A3S0Z1R7A2SbS0R9R7A2S2R7S1R9R8A2A2A2SdSbS0S5aS58RbA1A1M0R8A2S2R8S1S1G0SacA2Z1000A2A2A2SeS5eS5eSbS90S5eR1S62RcA1A3SbS0S63R1A1M1R9A2S2R9S1G1S64R1A1A2A2A2A2Lch;A2A2F_;F_;F_;F_;F_;F_;F_;Fz;Fn;Fb;FA;Fm;").
Proof.
  intros m A b n z HG HI3 HP HS Hin Hn Hz. destruct HI3 as (_ & LIV3 & _).
  destruct (LIV3 b n Hin) as [EP|(ch & Hch & Eb & Esz)].
  - left. pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (prim_fit n ltac:(lia) EP) as FIT. pose proof (rz_bound n) as RZ.
    destruct HP as (_ & _ & _ & P4).
    destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
    destruct (LV b n Hin EP eq_refl) as (R1 & R2 & R3).
    pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
    pose proof (Size_pos _ Hc) as SP.
    set (c := ClassID (needed n)) in *. clearbody c.
    unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3. rewrite kSpaceSize_val.
    nia.
  - right. exists ch. split; [exact Hch|]. destruct HS as (HS1 & _). destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    assert (RU : forall x, x <= round_up x PG) by (intros x; unfold round_up, PG; pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)); lia).
    pose proof (RU (sc_size ch)). pose proof (round_up_ge8 n). unfold PG in *. lia.
Qed.

Lemma DFP_split : ltac2:(tb__ "0|0|
S60S8Sb5R2R1A2SdSbaR2A1SbbR3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma keep_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8Sc7R5R4R3R2A4S93VCST;VXGL;R6R2A4SfSb5S59R7A1R3A2A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HX HK HD.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HK as [HC|HSH].
  - destruct (client_addr_cases CST A a _ HF HC) as [ST|[(b & n & Hbn & Hab)|[FR|[HCa|FL]]]].
    + apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | lia | apply (NS (topG (aa_geom A)) (2 ^ 47)); [lia | unfold MAP1, MAP1N; lia]].
    + destruct (Hsep b n Hbn) as (N1 & _).
      destruct (live_user_zone _ A b n a HG HI3 HP HS Hbn N1 Hab) as [SP|(ch & Hch & Hz)].
      * apply (GOAL _ (fun H => ZN (or_intror (or_introl H))) SP). eapply NS; [exact SP | unfold MAP1, MAP1N; lia].
      * apply (GOAL (exists ch, In ch (aa_sec A) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
        -- intros H. apply ZN. do 7 right. left. exact H.
        -- exists ch. exact (conj Hch Hz).
        -- destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
           pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      eapply NS; [exact Hx | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
    + destruct (HCST _ HCa) as [X _]. apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | | exact (HCSTD a HCa)].
      split; [exact X|]. intros [Hs _]. exact (HCSTD a HCa Hs).
    + destruct FL as (c & p & Hc & Hp & _ & Ex). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M. rewrite <- Ex in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      apply (NS a (a + 1)); [lia | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
  - pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep HSH) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | |];
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; [lia|].
    eapply NS; [split; [apply Z.le_refl | apply Z.lt_succ_diag_r] | unfold MAP1, MAP1N; lia].
Qed.

Lemma zoneR_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8S8S8Sc7R7R6R5R4A4S58R8A1S5fS0S5aR1A1R5A2S0S1R6R5A2S1S5aR2A1SacA2A2S0Z0R6A2S2S1R8R7A2S4Z2Z2fA2A2S4cS5dR5A1S5cR5A1S5aR5A1R9R8S5bR5A1R7A7SfSb5S59ReA1R8A2A1F_;F_;F_;F_;F_;TG;F_;Fa;Fszc;Fab;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md ab szc a HX G Hab1 Hab2 Hsz Hab3 HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, Hab2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZS|ZK]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom A) <= a < ag_spacebeg (aa_geom A) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - pose proof (Sh_in_band ab ltac:(lia)) as B1. pose proof (Sh_in_band (ab + szc) ltac:(lia)) as B2.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | lia |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma SPA_updR : ltac2:(tb__ "0|5|
S7bS15S11S8S2dS33S30S16A2A1S2dS68Q40A1A1S8aS2dS33S16S16A2A1M0S2dS19A1M1ScS2cS29S10S70VW;Vst;Vtmax;R7R6R5S31S18A1M2S34S31S19A1M3A9A1A1S2eA3ScS35S33G0G1A2M4A1SccS10R8A1S10S70VW;Vst;Vtmax;R8R7R6G2S34G3A9A1A2S38G4S32G0G1R3R2A4A2A3ScdRaR4A2Sc0S19S2bRbA1R4A3S78Vsegs;RdRbRcR8R7A6S78Vsegs;ReS70VW;Vst;Vtmax;RcRbRaG2S34G3A9RdR9R8A6F_;F_;F_;F_;F_;Fnf;Fd;Fw;FtpY;Fru;Fpc;FE;FrhoY;FJx;").
Proof. intros Jx rhoY E pc ru tpY w d nf Hw Hd Hok Hnf HE. unfold CertMallocSP.upd. eapply SPA_restate; [exact Hw | exact Hd | reflexivity | exact Hok | exact Hnf | exact HE]. Qed.

Definition site_facts (A : AA) (rho rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|c|
SbSbS0Z1M0Vsz;A2S0Vsz;Vtmax;A2A2SbS0S6bQ40M1S1aVrhoE;S83A2A2M2S6S84A1A2SbSc3S58VA;A1M3A1SbScS68G1A1M4S1aVrhoE;PcM5A2M6S1aVrho;G5A2A3SbS69G1G6A2S8SbScfVrhoE;S5aG3A1SbdR1A1M7SbeVA;R1A2Sa6R1A1Sa5G7A1R1A7SbSbS0G0SbfVA;R1A2M8A2S0G8Z10M9A2A2ScG4S1aVrhoE;P95A2S6aG1G8A2A3A2A2Tnv;SbScG4S1aVrhoE;P97A2S6aG1S5dG3A1A2A3SbScG4S1aVrhoE;P98A2S6aG1S5cG3A1A2A3SbS0S5bG3A1MaS1S69G1S1aVrhoE;PaA2A2G2A2A2Sc0S18S18SbSbS0S1GaG9A2S69G1S28VrhoE;S22R1A1A2A2MbA2S0GbS4Z2Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3A2A2A2A2A2A2A2A2").

Lemma dc_facts : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S41R7R5R4S69G0S1aR4Pc0A2A2A4F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB. unfold top_high in Htop.
  pose proof (JG_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
  assert (FACT : forall p, In p (ss_facts (ax_S (E4d W st tmax))) -> holds rhoE p).
  { intros p Hp. exact (fact_of_state nW st A Kc rho rhoE tp _ _ p Hw Hp). }
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  pose proof (cnt_pos_of_fact nW st A Kc rho rhoE tp _ _ Hw YP4) as Hcnt.
  pose proof (JGb_pvals nW st A Kc rho rhoE tp _ _ (conj (proj1 Hw) (JG_JGb nW st A Kc rho rhoE tp tr md (proj2 Hw))) FGEN4 Hcnt) as PV.
  cbn zeta in PV. rewrite <- E12 in PV, Hcnt, E149.
  pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & _).
  assert (Hcnt16 : 1 <= cnt_of A (bv_unsigned (rw rhoE 12%positive)) <= 16).
  { split; [exact Hcnt|]. pose proof (pc_entry_facts segs A rhoE tp md _ HA Bn Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & X & _). exact X. }
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact E12|]. split; [exact (conj PV (conj Hcnt16 E149))|].
  split; [exact E151|]. split; [exact E152|]. split; [exact Htop|].
  pose proof (topG_range (aa_geom A)) as TGr. pose proof (srange (rw rhoE V_DEPTH)) as R15. unfold malloc_depth in Fd1.
  apply (unwind_objs_above W rhoE (topG (aa_geom A))); [|clear -Htop Fd1; lia | clear -TGr; lia].
  apply Forall_forall. intros p Hp. apply FACT. apply FUNW.
  unfold unwind_factsS. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l0 W0']; [destruct Hp | exact Hp].
Qed.

Lemma dc_site : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S78Vsegs;S8eVW;Vst;R7R6R5A5S3fS69G0S1aR4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. pose proof (dc_facts A Kc rho rhoE tp w Hw) as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.

  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3808)))) = bv_unsigned (rw rhoE 10%positive) - 3808).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3808))) with (2 ^ 64 - 3808) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG W st A Kc rho) X4f rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X4f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }

  assert (HwR : SPA segs (JG W st A Kc rho) (X4r sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X4r. eapply SPA_updR; [exact (WX4r sz Hsz) | exact (DX4r sz Hsz) | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }

  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4. apply OS; [exact (SPL4 sz Hsz)|]. unfold X4c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X4b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X4a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dc_R4 : ltac2:(tb__ "0|2|
S57S15S15S8S41R4R3R2R1A4S57S15S2dS68Q40M0A1M1A1S6cG1Sc7R5R4R3R2A4ScS5fS58R6A1S58RbA1A3S98RaVR4;R9A1R3A3SfSb5S59R8A1S69G0R4A2A2A1F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Frho;FA;").
Proof.
  intros A rho rhoE sz (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK) Ax rx tpx mdx a HX EG (o & Ho & Hoa) HD.
  cbn zeta in PV. pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (R4_zone sz rhoE A o (bv_unsigned a) Hsz PV Hcnt16 E151 E152 E149 HG Htop Fd1 LNK Ho Hoa) as HZ. cbn zeta in HZ. rewrite <- EG in HZ.
  refine (zoneR_not_DFP Ax rx tpx mdx _ _ (bv_unsigned a) HX _ _ _ _ HZ HD); rewrite ?EG; rewrite ?kSpaceSize_val; lia.
Qed.

Lemma dc_entry : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40A1A1S8S2dS6dA1M0S7eS6cS41R9R7R6R4A4S82R9A1S79Vsegs;R8R7S3fR6A1S32G0S7fR5S80R4R3A2A4A5S8eVW;Vst;RcRbRaR9R8R6R4A9SbcSaeSa4RdRcRaA3S59RdA1S96S95RaVR4;R8A1S7dR5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 [Hag0 HJ0].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK). unfold malloc_depth in Fd1.
  pose proof HJ0 as (HA0 & HK0 & _ & _ & HB0 & HN0 & _). cbn [eval] in HB0, HN0.
  pose proof (AInvA_budget A rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2272)))) = bv_unsigned (rw rhoE 10%positive) - 2272).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2272))) with (2 ^ 64 - 2272) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE _ HB0 HKm0 tp tr0 md0 HA0 HK0). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
    change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X A rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md0 tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (dc_R4 A rho rhoE sz SF A rhoE tp md0 _ HX0 eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma dc_exit_ok : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6Sa1R14S7dRfR13R10A3VR4;R12A1Vs4;R12A1S66R12A1S65R12A1S3fR12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (dc_R4 A rho rhoE sz SF _ rhoE tpL md' a HXK eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r a j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dc_exit_core : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6S15S8aSb3R16S7dR11R15R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R2R10A9S78Vsegs;Sa0RaR9R16R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R3R10R2A6SeS57S57SeS15S15SeS15S15SbSc9R1eR3A2SbScaS93VCST;VXGL;R1eA3R1cR2A3S78Vsegs;Sc8VW;Vst;R3R1dR2A5S6fVW;Vst;Vtmax;A3R1R14R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK).
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0 & HK0 & Htp0 & HU0 & _ & HN0 & Htop0). cbn [eval] in HN0. unfold top_high in Htop0.
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. rewrite (NX4 sz Hsz). apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE (R4 sz) (vms md0 tp ms0)) (s4 sz)) tp rhoL tpL) (T40 sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T40. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }

  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T40 sz) = []) by (unfold T40, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.
  assert (HT4b : SPA segs JP (T4b sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4b. apply OR; [exact (RB2 sz Hsz) | unfold T4a; rewrite AXr; exact AX40 |]. unfold T4a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }

  assert (HT4c : SPA segs JP (T4c sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }

  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T4m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T4m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T4m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T4m3, T4m2, T4m1. rewrite !AXm. unfold T4c. cbn [ax_X ax_setS]. unfold T4b, T4a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpK (with_depot A G2)).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' (R4 sz) a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' (R4 sz) a <-> in_ranges rhoE (R4 sz) a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE (R4 sz) a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (dc_R4 A rho rhoE sz SF A' rhoE tpL md2 a HX2 eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE (R4 sz) a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall Ax rx tpx mdx a, AInvX Ax rx tpx mdx -> SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP (aa_depot Ax) a).
  { intros Ax rx tpx mdx a HX HB' HD. pose proof HX as (HGx & _ & _ & HRest & _ & HI3x & _). destruct HRest as (_ & _ & _ & HSx & _).
    assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSx as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HSx as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw Ax a HGx HI3x HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB'; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; exact HB' | exact Hws]. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJGb5 : JGb W st A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold A'. refine (eq_trans (rhoM_of_AK A G2 rho rho'' (fun j => eq_refl _) i) _). rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - split; [exact HA5|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact (HUSr rhoE rho5 RW5 HU0)|]. split; [exact I|].
      split; [cbn [eval]; rewrite (RW5 12%positive) by (unfold GW; lia); exact HN0|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JGb W st A' Kc rho'') (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJGb5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT (R4cov sz Hsz) Ho Ha). }
  pose proof (SPA_entails segs (JGb W st A' Kc rho'') GW (T4d sz) (C5 W st tmax) _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGb_stable nW st A' Kc rho'' HUS HKc) HT5) as HC5.
  exists A', rho'', (rho_sub rho5 (sd sz)). split; [|split; [|exact HC5]].
  - unfold depot_onlyK, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpK with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; reflexivity|].
      exact (keep_not_DFP A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; exact Hdef|].
      exact (BAND A' rhoE tpL md2 (bv_unsigned a) HX2 HBa).
Qed.

Lemma dc_exit : ltac2:(tb__ "0|2|
S8aOF_;S57S81S15S15S2dS68Q40A1A1M0S8bS8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8dVsegs;R16S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A4F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8dVsegs;R1cS78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
Qed.

Lemma dc_exitE : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8aOF_;S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8cVsegs;S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A3F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8cVsegs;S78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
Qed.

Theorem depot_call_HD : ltac2:(tb__ "0|0|
S8aOF_;S57S81S15S8bS82R3A1S7cVsegs;R6S7aR4A1A3Sd7Vsegs;R7S7aR5A1A3ScbVnW;Vst;Vtmax;S93VCST;VXGL;R7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho Q HKc Hokl Hokpl rhoE tp Hcont n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_soundPA segs ok (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  -
    intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc A Kc rhoE G r t tr0 md0 HKG) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc A Kc rhoE G r t tr0 md0 HKG) Hp Hok).
  -
    intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  -
    intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exit ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_HDE : ltac2:(tb__ "0|0|
S57S81S15S8aOF_;S82R3A1SdbVnW;Vst;Vtmax;S93VCST;VXGL;R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;").
Proof.
  intros A Kc rho Q HKc rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_completePA segs (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exitE A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DCW.
End DepotCallW.

(* [comment removed for export] *)
Module SpineCallocSec3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "bool"; "app"; "true"; "prod"; "nil"; "cons"; "pair"; "option"; "Some"; "None"; "fst"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "sprop"; "eval"; "ss_facts"; "ss_next"; "ss_objs"; "rl"; "SLit"; "sprop_below"; "swf"; "cell"; "mkObj"; "obj_range"; "rm"; "DUnknown"; "ranges_disjoint"; "SVar"; "holds"; "DZero"; "agree_below"; "image_byte"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "mkLeafA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "modulo"; "sub"; "pow"; "mul"; "land"; "of_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "budget_bound"; "aa_ptr_committed"; "aa_sec"; "ag_ctx"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "budget_ok_alloc"; "sec_chunk"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.SEC3"; "JGs"; "GS"; "slink"; "SKEL0"; "JGsC"; "clsP"; "pgq"; "noband"; "npg"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "Kc_ok"; "unwind_stopJ"; "A_globals"; "top_high"; "tp_ok"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "liftKA"; "smatchA"; "LQA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "round_up"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "rhoM_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "carveS"; "B2"; "L1"; "L2"; "B1"; "F_map"; "Pret_ms"; "a0e2"; "a2e1"; "a2e2"; "O_1"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "JGsC"; "SHC"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_MS"; "RT_sec"; "V_NCH"; "V_NRES"; "V_NS"; "V_PAB"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "rt_zoneG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA LedgerA.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC3.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S6Sa7VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S8S90S99Vnx;A2SaA3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S41S0S43S42VAX;R1A1A1S42R1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S41S0S5S44VAX;R1A1A1S44R1A1A3FX;").
Definition GS : positive := Pos.succ nx.

Lemma GW_le_nx : (GW <= nx)%positive.
Proof. apply Pos.leb_le. exact NXG. Qed.
Lemma nx_lt_GS : (nx < GS)%positive.
Proof. unfold GS. apply Pos.lt_succ_diag_r. Qed.
Lemma GW_lt_GS : (GW < GS)%positive.
Proof. eapply Pos.le_lt_trans; [exact GW_le_nx | exact nx_lt_GS]. Qed.
Lemma lt_GW_GS : ltac2:(tb__ "0|0|
S6S91R1S99A2S91R2S50A2F_;Fi;").
Proof. intros i Hi. eapply Pos.lt_trans; [exact Hi | exact GW_lt_GS]. Qed.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S16S7S3fQ40M0A1M1A1S7S7aA1S79S3eG0S18Vrho;PcA2A2S5S1S2bS99S78VA;Vrho;A2R5A3S1S0G1S18R5Vnx;A2Va;A3S1Sa8Vsegs;VAX;S9cVA;R1A2A1R5R4R2A5S1S9fVA;S3eG0Va;A2S75R1A1R2A4S1VKc;R3R2A2S1S61VA;R5A2S1S5eVW;Vst;R5A3S1S1S34Zfc01R1A2S37R1S3aZ2Z27A2A2A2S1S60VA;R5A2S4bVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S16S7S3fQ40M0A1A1S7S7aA1S79S3eG0S18Vrho;PcA2A2S5S1S4fVA;VKc;Vrho;Va;R5R4R3R2A8S34S35S35SadR2R4A2Sb0VAX;S9cVA;R1A2A1M1A1A2S9eR1A1A2SaaG1A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma JGsC_of_Sec : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7S7aA1S79S41S0S41VAX;R1A1R1A3FX;S9dVW;Vst;Vtmax;R9R8R7R6R5R4R3R2AbS53RaR9R8R7R6R5R4R3A8F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md AXid H. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv.JGs in H. rewrite Hnx in H. unfold JGsC, JGs. rewrite !AXid. rewrite (PrimCredit.prim_credit_same A (bumpV A (bv_unsigned (rw rho 12%positive))) eq_refl). exact H. Qed.

Definition slink (ua L : Z) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|a|
S1S6S0S3fQ40M0A1M1S18Vrho';R1A2S18Vrho;R1A2A3Fi;S1S6S0S7S3fQ8A1M2A1S1eVrho';R1A2S1eVrho;R1A2A3Fl;S1G1S3S0SfG2A1M3S25Vrho';R1A2M4S25Vrho;R1A2M5A3S3S1S0G3G5S11G2A1M6A3S1S0G3S2cS8fR1A2G6A3S1S34S6eS3eG0R1A2M7A2S37G7S6dA2A2A2A2S1S1S34S6cVua;A1M8G7A2S37G7S35G8S36VL;Z8A2A2M9A2A2S4S0G3G4G6A3A1A2A2A2Fa;S5S1S34G8R1A2S37R1G9A2A2S4S0G3S25Vrho';S40G0R2A2A2G6A3A1F_;Fz;A2A2A2").

Lemma slink_trans : ltac2:(tb__ "0|0|
S5S5S16S16S16S51R5R4R3R2A4S51R6R5R3R2A4S51R7R6R5R3A4F_;F_;Fr3;Fr2;Fr1;FL;Fua;").
Proof.
  intros ua L r1 r2 r3 (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2).
  split; [intros i; rewrite W2; apply W1|]. split; [intros l; rewrite L2; apply L1|]. split; [|exact D2].
  intros a. destruct (M2 a) as [E2|[(N2 & I2 & B2)|(R2 & S2)]].
  - rewrite E2. destruct (M1 a) as [E1|[X|X]]; [left; exact E1 | right; left; exact X | right; right; exact X].
  - destruct (M1 a) as [E1|[(N1 & I1 & B1)|(R1 & S1)]].
    + right. left. rewrite <- E1. exact (conj N2 (conj I2 B2)).
    + right. left. exact (conj N1 (conj I2 B2)).
    + exfalso. exact (S1 N2).
  - right. right. exact (conj R2 S2).
Qed.

Lemma JGs_rigidS : ltac2:(tb__ "0|5|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcM2A2M3A2S5S42RaA1S43S1S0G1G3S18R9G2A2A3S1S0G1S18R7Vnx;A2R8A3S1S0G1S18R7Sa5A2S40G0S77R2A1A2A3S1S0G1S18R7Sa1A2S40G0S75R2A1A2A3S1S0G1S18R7P97A2S40G0S4aR1A1A2A3S1S0G1S18R7P98A2S40G0S47R1A1A2A3S1S0G1S18R7P9bA2S40G0S49R1A1A2A3S1S0G1S18R7Sa6A2S40G0S48R1A1A2A3S1S0G1S18R7Sa4A2S40G0S36S45RbA1Z8A2A2A3S1S0G1S18R7Sa3A2S40G0S3dS13S4cS46RbA1A2A1A2A3S1G1S0SfS3fQ8A1M4A1S25R8R1A2S25RaR1A2A3Fx;S6S0S7G4A1S1eR8R1A2S1eRaR1A2A3Fl;A2A2A2A2A2A2A2A2A2A2A2TG;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. destruct HJ as ((Hagw & Hagl & Hagm) & Ha & _).
  cbn zeta. unfold V_NS, V_MS, V_PAB, V_NRES, V_NCH.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - exact Ha.
  - intros x. rewrite <- (Hagm x). reflexivity.
  - intros l. rewrite <- (Hagl l). reflexivity.
Qed.

Lemma JGs_K : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md HJ. destruct HJ as (_ & _ & _ & _ & HK & _). exact HK. Qed.
Lemma JGsC_K : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7S7aA1S79S53R8R7R6R5R4R3R2R1A8R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md [HJ _]. exact (JGs_K _ _ _ _ _ _ _ _ HJ). Qed.

Lemma stopJ_rwrl : ltac2:(tb__ "0|1|
S16S16S6S0S3fQ40A1S18R3R1A2S18R2R1A2A3Fi;S6S0S7S3fQ8A1A1S1eR4R1A2S1eR3R1A2A3Fl;S5eVW;Vst;R4A3M0G0F_;F_;F_;Fr';Fr;").
Proof.
  intros r r' Hw Hl H. unfold unwind_stopJ in *. destruct W as [|u us]; [exact H|]. destruct st; [exact H|].
  destruct (last_link (SVar 28) (u :: us)) as [[bp nbp] pc]. rewrite !(eval_ext_rwrl r' r) in H by assumption. exact H.
Qed.

Lemma JGs_stable : ltac2:(tb__ "0|0|
S41S59S16S3fQ40A1S76VW;Vst;A2S5dR4A1S66Vsegs;S50S4fR6R5R4R3A4A3F_;F_;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a HUS HKc r r' tp tr md md' Hag Hme HJ.
  pose proof Hag as (Hw & Hl & Hm). pose proof GW_lt_GS as LT. pose proof nx_lt_GS as LT2.
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros x; symmetry; apply Hm).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact HN|split; [|exact HB]]]]]]]]].
  - destruct Hagr as (A1 & A2 & A3). split; [|split].
    + intros i Hi. rewrite (A1 i Hi). apply Hw. exact (lt_GW_GS i Hi).
    + intros l. rewrite (A2 l). apply Hl.
    + intros x. rewrite (A3 x). apply Hm.
  - rewrite <- (Hw nx LT2). exact Ha.
  - unfold AInvA in HA |- *. rewrite Erm. fold (AInvA segs (AX (bumpV A (bv_unsigned (rw rho 12%positive)))) r tp md') (AInvA segs (AX (bumpV A (bv_unsigned (rw rho 12%positive)))) r tp md) in *.
    eapply AInvA_mat; [exact HA | exact Hme].
  - destruct Hme as ((mat' & ->) & _). unfold pendS in HP |- *. rewrite m_vmmaps_with_vm_backing. exact HP.
  - destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold tp_ok in Htp |- *. rewrite <- (Hw 24%positive) by (apply lt_GW_GS; unfold GW; lia). exact Htp.
  - apply (HUS r r'); [|exact HU]. eapply agree_below_le; [|exact Hag]. pose proof GW_lt_GS. unfold GW, NF in *. lia.
  - unfold top_high in Htop |- *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (apply lt_GW_GS; unfold GW, V_DEPTH; lia). exact Htop.
Qed.
Lemma JGsC_stable : ltac2:(tb__ "0|0|
S41S59S16S3fQ40A1S76VW;Vst;A2S5dR4A1S66Vsegs;S50S53R6R5R4R3A4A3F_;F_;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a HUS HKc r r' tp tr md md' Hag Hme [HJ HC].
  split; [exact (JGs_stable A Kc rho a HUS HKc r r' tp tr md md' Hag Hme HJ)|].
  destruct Hme as (_ & Hpaid & _). rewrite Hpaid. exact HC.
Qed.

Lemma AInvA_boundD : ltac2:(tb__ "0|0|
S41S16S7S3fQ40A1A1S79Sa8S8fR4R3R2R1A5S34SaaR5A1S44R5A1A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Lemma Sh_add8 : ltac2:(tb__ "0|1|
S5S5S0S5S38R1Z8M0A2Z0A3S0S5S6cS35R3R2A2A1S35S6cR3A1S36R2G0A2A2A3F_;Fb;Fa;").
Proof. intros a b Hb. unfold Sh. rewrite (Z.div_mod b 8) at 1 by lia. rewrite Hb, Z.add_0_r. rewrite Z.mul_comm, Z.div_add by lia. lia. Qed.

Definition npg (lo h2 : Z) : Z := ltac2:(tb__ "0|1|
S35S39S36S39Vh2;Z1M0A2S6bA2S36Vlo;S6bA2A2G0A2").
Definition pgq (lo : Z) : Z := ltac2:(tb__ "0|0|
S3bS6bS36Vlo;S6bA2A2").
Lemma pg_run : ltac2:(tb__ "0|4|
S5S5S34Z0M0R2A2S37R3R2A2S1S34S55R4A1M1R4A2S1S34R3S35G1S3bS6bS57R4R3A2M2A2A2M3A2S1S0S5S38G1S6bA2G0A3S1S1S34G0G2A2S34G2S35S36S39R3R4A2S6bA2Z2A2A2A2S1S37R4S35G1S6bA2A2S37G3S35R3S6bA2A2A2A2A2A2A2F_;F_;Fh2;Flo;").
Proof.
  intros lo h2 H0 Hlt. unfold npg, pgq, PG.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (h2 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (h2 - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod (h2 - lo) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (h2 - lo) 4096 ltac:(lia)).
  assert (lo / 4096 <= (h2 - 1) / 4096) by (apply Z.div_le_mono; lia).
  repeat split; try lia.
Qed.

Definition clsP (h : bool) (ua L : Z) : Prop := ltac2:(tb__ "0|0|
S8OLh;Vh;S34S6dVua;A2S34S35Vua;VL;A2S6eA2X8x2").
Lemma shadow_run_band : ltac2:(tb__ "0|1|
S8S5S5S54R3R2R1A3S34S6fR3A2S37Z0R3A2S34S35R5R4A2Z7fffff800000A2S55S6cR6A1A1S5S35S55S6cR7A1M0A1S3bS6bS57G0S35G0S36R6Z8A2A2A2A2A2S5S1S8OLh;R9S1S34S71R2A2S34R1S72A2A2S1S34S73R2A2S34R1S74A2A2X8x2S1S34Z646000R2A2S1S34R1S3aZ2Z40A2A2S1S34S6eR2A2S34R1S6dA2A2A2A2A2Th2;Tlo;F_;F_;F_;F_;FL;Fua;Fh;").
Proof.
  intros h ua L HC Himg HL Htop lo h2.
  assert (R : Sh ua < Sh ua + L / 8 \/ L / 8 = 0) by (pose proof (Z.div_pos L 8); lia).
  pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  unfold clsP in HC. unfold Sh, SHADOW_OFF, IMG_HI, HIGH_SHADOW_BEG, HIGH_SHADOW_END, LOW_SHADOW_BEG, SHADOW_GAP_BEG, SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, LOW_SHADOW_BEG in *.
  subst lo h2. unfold npg, pgq, PG.
  pose proof (Z.div_mod ua 8 ltac:(lia)). pose proof (Z.mod_pos_bound ua 8 ltac:(lia)).
  set (s := ua / 8 + 2147450880) in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)). pose proof (Z.mod_pos_bound s 4096 ltac:(lia)).
  pose proof (Z.div_mod (s + L / 8 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (s + L / 8 - 1) 4096 ltac:(lia)).
  destruct h; lia.
Qed.

Definition SKEL0 : list sobj := ltac2:(tb__ "0|0|
S9S15S9S15S9S15SdS15SaeS9S15S62VW;A1S5fA3A3SafA3Sa2A3SdS15S23S28Vnx;A1S1fZ0A1S28Sa1A1ScS22A1S2aA5ScS15A1A3A3").
Definition noband (x : Z) : Prop := ltac2:(tb__ "0|0|
S3S37Vx;S6eA2S34S6dVx;A2A2").
Definition range_noband (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S5S1S34S12S5S5Vr;A3R1A2S37R1S14S5S5Vr;A3A2A2S56R2A1F_;Fx;").

Lemma rt_zoneG_noband : ltac2:(tb__ "0|0|
S43S5Sa9R2A1Sb1R3R2A2S56R3A1F_;F_;Fx;FG;").
Proof.
  intros G x HG Hz. pose proof (geom_bands G HG) as (FB & TB & CB & DB & _). rewrite FS_total_val in FB.
  unfold noband. unfold rt_zoneG in Hz. rewrite FS_total_val in Hz. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]]; [clear -Z1; lia | clear -Z2 TB; lia | clear -Z3 CB; lia | clear -Z4 DB; lia | clear -Z5 FB; lia].
Qed.

Lemma objs_noband : ltac2:(tb__ "0|4|
S2eS7S15A1M0G0S41S59S16S3fQ40A1M1S16S7G1A1S7bS7eVW;Vst;A2S64Vsegs;S4fR8R7R6R5A4RbR4R3R2A6S0S7SbSbS17S17A2S17A2M2A1M3S4dS15G2S63S1dS2dRcA1A1A4S4dS15G2S63S9S15RbS9S15S52RaA3A3A4A3S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dRdA1A1A3S2G0G0S2G0G0S2G0G0S1S0G0S1dS2dR11A1A1S9S15R3S9S15R2R1A3A3A3S1S0G3S4dS15G2S63R3A4S4dS15G2S63R10A4A3S1S0G3S4dS15G2S63R1A4S4dS15G2S63RfA4A3S4eS15S15S58S24RbR1A2A1Lo;R2A3A2A2A2Ll2;A2Ll1;A2Ll0;A2F_;F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp w HW Hsp SKP FC. destruct w as [tr [ms md]].
  rewrite map_app in SKP. destruct (map_eq_app _ _ _ _ SKP) as (l0 & l12 & EO0 & SK0' & SKP').
  rewrite map_app in SKP'. destruct (map_eq_app _ _ _ _ SKP') as (l1 & l2 & EO12 & SK & SK2).
  exists l0, l1, l2. split; [rewrite EO0, EO12; reflexivity|]. split; [exact SK0'|]. split; [exact SK2|].
  pose proof (proj2 Hsp) as HJ. pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & _).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  pose proof HA as (HG & _). rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & T1 & T2 & T0' & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFall.
  assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (FC p Hp)). }
  assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
  assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) l1).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). rewrite EO0, EO12 in Hall.
    apply Forall_app in Hall as [_ Hall]. apply Forall_app in Hall as [Hall _]. exact Hall. }
  unfold SKEL0 in SK. cbn [app] in SK.
  destruct (skel_head _ sw_s1 _ SK) as (o0 & rest & EO & SK0 & SKR).
  subst l1.
  pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
  constructor.
  { intros x Hx. unfold noband, SHADOW_BAND_HI, HIGH_SHADOW_END. right. clear -SW1 Hx. lia. }
  apply (Forall_ranges_skel rhoX range_noband _ _ SKR).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
  apply Forall_app. split.
  2:{
    apply Forall_cons; [|apply Forall_nil].
    pose proof HP as (_ & _ & HL & DI & _). destruct DI as (_ & _ & _ & _ & WB).
    pose proof (secmapsize_bounds (bv_unsigned (rw rho 12%positive)) ltac:(clear -HN; lia)) as [SMB _].
    assert (SO : soff rhoX (SVar V_MS) = secmapsize (bv_unsigned (rw rho 12%positive))).
    { unfold soff. cbn [eval]. rewrite E142, signed_lit. unfold snorm. rewrite Z.mod_small by (clear -SMB HN; lia).
      destruct (Z.ltb_spec (secmapsize (bv_unsigned (rw rho 12%positive))) (2 ^ 63)); clear -SMB HN H; lia. }
    intros x Hx. unfold obj_range, obj_lo_of, obj_hi_of in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx.
    rewrite SO, soff_lit_small in Hx by lia. cbn [eval] in Hx. rewrite Enx in Hx.
    unfold noband. clear -WB Hx. lia. }
  apply Forall_app. split.
  2:{
    unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
    intros x Hx. apply (rt_zoneG_noband (aa_geom A) x HG). apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(clear -T1 T2 TG; lia) Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
    intros x Hx. apply (rt_zoneG_noband (aa_geom A) x HG). apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
      intros x Hx; rewrite obj_range_mk in Hx by lia; cbn [fst snd eval] in Hx; rewrite u64_lit in Hx by lia;
      unfold noband, SHADOW_BAND_LO, LOW_SHADOW_BEG; left; lia. }

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -TG; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
    apply HFX. apply in_or_app; left. exact Hp'. }
  eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
  intros x Hx. rewrite obj_range_mk in Hx by (clear -B; lia). cbn [fst snd] in Hx. unfold noband, SHADOW_BAND_HI, HIGH_SHADOW_END. right. clear -B Hx TG. lia.
Qed.

Lemma carve_piece : ltac2:(tb__ "0|4|
S2eS17S17S41S59S16S16S3fQ40M0A1M1S16S7G1A1S7bS3eG0S18R5PcA2A2S5S83RcS23RbS1fZ0A1RaScS22A1S26A5A2S2eS51S3eG0R6A2S75R2A1R8R7A4S64Vsegs;S4fRbRaR8R7A4ReR6R5R4A6S0S8S21S2dR3A1A1SaA3S0S7SbS17S17A2M2A1S32R10A1ScG2A1A3S34S6cS3eG0RaA2A1S3eG0S1aR9R10A2A2A2S34S35S3eG0S1aRaR11A2A2S3eG0S1aRaR10A2A2A2S35S6cS3eG0RbA2A1S36S75R7A1Z8A2A2A2S4eS15S15S27S24RcR1A2SeS5S5S3eG0S1aRcR13A2A2M3S35G3S3eG0S1aRcR12A2A2A2A4A2Lo;S1dS2dR13A1A1A3S64Vsegs;S4fR11R10ReRdA4R8RcRbRaA6F_;F_;F_;F_;F_;F_;F_;TCO;Tnv;Fw;Ftp;FrhoX;Fa;Frho;Frho0;FKc;FA;FL;FB;FC;").
Proof.
  intros C B L A Kc rho0 rho a rhoX tp w nv CO SL Hsp WCO XC HB1 HB2 DJ. destruct w as [tr [ms md]].
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ.
  pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & _ & _ & _ & _ & _ & _ & Erm & Erl).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HBud). fold nv in HN.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB SMM].
  pose proof (urange a) as Ra. pose proof (urange (eval rhoX B)) as RB. pose proof (urange (eval rhoX L)) as RL.
  set (b := bv_unsigned (eval rhoX B)) in *. set (l := bv_unsigned (eval rhoX L)) in *.
  assert (L8 : secmapsize nv / 8 <= nv / 8 + 1537) by (clear -SMB; pose proof (Z.div_le_mono (secmapsize nv) (nv + 12295) 8 ltac:(lia) ltac:(lia)); rewrite <- Z.div_add by lia; lia).
  assert (SO0 : soff rhoX (SLit 0) = 0) by (apply soff_lit_small; lia).
  assert (SOL : soff rhoX L = l) by (unfold soff; rewrite signed_small; [reflexivity|]; clear -HB1 HB2 L8 HN RB; subst l; lia).
  destruct SL as (_ & _ & _ & DEF).
  unfold CO, carveS. eapply (SPA_carve_unk segs (JGs A Kc rho a) rhoX C tp _ B (SLit 0) L (ss_next (ax_S C)) Hsp WCO (Pos.le_refl _));
    rewrite ?SO0, ?SOL; fold b.
  - clear -RL; lia.
  - clear -HB1 HB2 L8 HN; lia.
  - clear -RB; lia.
  - clear -HB1 HB2 L8 HN Ra; unfold Sh, SHADOW_OFF in *. pose proof (Z.div_lt_upper_bound (bv_unsigned a) 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia.
  - rewrite Z.add_0_r. exact DJ.
  - intros z Hz. rewrite Z.add_0_r in Hz.
    pose proof (DEF z ltac:(clear -Hz HB1 HB2; lia)) as D. rewrite <- (Erm (Z_to_bv 64 z)) in D.
    unfold wok_of, rd_of. destruct (rm rhoX (Z_to_bv 64 z)) as [x|]; [|exfalso; exact (D eq_refl)]. split; [reflexivity | exists x; reflexivity].
  - intros rr y j Hin. rewrite XC in Hin. destruct Hin.
Qed.

Lemma pieces_disjoint : ltac2:(tb__ "0|6|
S2eS7S15A1M0G0S41S59S16S3fQ40A1M1S16S7G1A1S7bS5S5S7eVW;Vst;A2S64Vsegs;S4fRaR9R8R7A4RdR6R5R4A6S0S7SbSbS17S17A2S17A2M2A1M3S4dS15G2S63S1dS2dReA1A1A4S4dS15G2S63S9S15RdS9S15S52RcA3A3A4A3S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dRfA1A1A3S34S6eR6A2S34R6S6dA2G0S0G3S4dS15G2S63R1A4S4dS15G2S63R12A4A3M4S4eS15S15S27S24ReR1A2SeS5S5RbRaA4A2Lo;M5R2A3F_;Fl;G0G4S4eS15S15S27S24RfR1A2SeS5S5RcRbA4A2Lo;R2A3F_;Fl;S4eS15G5S1dS2dR14A1A1A3F_;F_;F_;F_;F_;F_;F_;F_;Fh2;Flo;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp w lo h2 HW Hsp SK FC HLO HHI HP0 HP.
  destruct (objs_noband X P0 P A Kc rho a rhoX tp w HW Hsp SK FC) as (l0 & l1 & l2 & EO & SK0' & SK2 & NB).
  rewrite EO. apply Forall_app. split; [exact (HP0 l0 SK0')|]. apply Forall_app. split; [|exact (HP l2 SK2)].
  eapply Forall_impl; [|exact NB]. intros o Ho. unfold ranges_disjoint, range_noband, noband in *. cbn [fst snd].
  destruct (obj_range rhoX o) as [olo ohi]. cbn [fst snd] in Ho |- *.
  destruct (Z_le_dec ohi olo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec ohi lo) as [E2|E2]; [right; right; left; exact E2|].
  destruct (Z_le_dec h2 olo) as [E3|E3]; [right; right; right; exact E3|].
  destruct (Z_le_dec h2 lo) as [E4|E4]; [right; left; exact E4|].
  exfalso. destruct (Ho (Z.max olo lo) ltac:(clear -E E2 E3 E4; lia)) as [Y|Y]; clear -Y E E2 E3 E4 HLO HHI; lia.
Qed.

Section MS.
Variables (E C CO T : axst) (B L : sv) (P0 P : list sobj).
Variables (Pre Pret : axst) (Posts : list leafA) (s : wsub) (R : list sobj).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S7S2fA1VPosts;SdS2fS33VPret;SacA2ScS2fA1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S7bOF_;S6aS16S7S3fQ40A1A1S65Vsegs;R4R3A3S66Vsegs;S94R4A3S7cVsegs;R6S64Vsegs;R5VPre;R4R3A5S69Vsegs;R5S94R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S6S1cS2dVPre;A1A1S94A3").

Hypothesis RS : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7bS7eVW;Vst;A2S64Vsegs;S4fR8R7R6R5A4VE;R4R3R2A6S64Vsegs;S4fR9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis HBL : ltac2:(tb__ "0|a|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7bS64Vsegs;S4fR7R6R5R4A4VC;R3R2R1A6S1S34S6cS3eG0R5A2A1M2S3eG0S1aR4VB;A2A2M3A2S1S34S35G3S3eG0S1aR4VL;A2A2A2S35G2S36S75S3eG0S18R6PcA2A2A1Z8A2A2A2S1S7S15A1M4S0S7SbSbS17S17A2S17A2M5A1M6S4dS15G5S63R1A4M7S4dS15G5S63VP0;A4A3S4eS15S15S27S24R7R1A2SeS5S5S3eG0S1aR7VB;A2A2M8S35G8S3eG0S1aR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S4dS15G5S63VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").

Hypothesis SKC : ltac2:(tb__ "0|1|
S0S7SbSbS17S17A2S17A2M0A1S4dS15G0S63S1dS2dVC;A1A1A4S4dS15G0S63S9S15VP0;S9S15S52VP;A3A3A4A3").
Hypothesis FCC : ltac2:(tb__ "0|0|
S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dVC;A1A1A3").
Hypothesis XC : ax_X C = [].
Hypothesis HCO : ltac2:(tb__ "0|0|
S0S2eS83VC;S23VB;S1fZ0A1VL;ScS22A1S26A5A2VCO;A3").
Hypothesis WCO : ltac2:(tb__ "0|0|
S0S8S21S2dVCO;A1A1SaA3").
Hypothesis He : ltac2:(tb__ "0|1|
S0SfS7S15A1M0A1S97VCO;VPre;Vs;A3S10G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S8S96VCO;VPre;Vs;VR;S4dS2fS2eS30VPosts;A4A5SaA3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S2eS98Vs;VPre;VPret;VCO;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S8S81S19S20S1cS2dVCO;A1M0A1A1S1bG0A1A3SaA3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S8S81S19S20S1cS2dVT;A1A1A1S1bS2dVCO;A1A1A3SaA3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S0S8S90S50S1cS2dVCO;A1A1A2SaA3").

Lemma ms_step : ltac2:(tb__ "0|4|
S7bOF_;S41S59S16S16S3fQ40M0A1M1S7G1A1M2S7dS7eVW;Vst;A2S76VW;Vst;A2S5dR8A1S65Vsegs;RbS67R9A1A3S51S3eG0R7A2S75S3eG0S18R8PcA2A2A1R9R8A4S16G2S7cVsegs;RfS64Vsegs;S4fReRdRbRaA4M3S95VT;S1bS2dVCO;A1A1A2R2R1A5R8A4FtpY;FrhoY;S16S7cVsegs;RfS64Vsegs;G3VE;R1R9A5R8A4FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp Q HW HUS HKc Hokf SL HD rhoX.
  pose proof (JGs_stable A Kc rho a HUS HKc) as HST.

  apply (triple_conseq (P:=SPA segs (JGs A Kc rho a) CO rhoX tp) (SPA segs (JGs A Kc rho a) E rhoX tp) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { pose proof (RS A Kc rho a rhoX tp w HW Hw) as HC.
    destruct (HBL A Kc rho a rhoX tp w HC) as (HB1 & HB2 & HDP0 & HDP).
    rewrite <- HCO. apply (carve_piece C B L A Kc rho0 rho a rhoX tp w SL HC); [rewrite HCO; exact WCO | exact XC | exact HB1 | exact HB2 |].
    destruct w as [trw [msw mdw]]. pose proof (proj2 HC) as HJc. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJc.
    destruct HJc as (_ & _ & _ & HPc & _ & _ & _ & HNc & _). pose proof HPc as (_ & _ & HLc & DIc & _). destruct DIc as (D0c & _ & DTc & _).
    pose proof (topG_range (aa_geom A)) as TG. pose proof (urange a) as Ra.
    pose proof (Sh_in_band (bv_unsigned a) ltac:(clear -Ra DTc TG HLc; lia)) as SB.
    apply (pieces_disjoint C P0 P A Kc rho a rhoX tp _ _ _ HW HC SKC FCC); [| |exact HDP0|exact HDP].
    - clear -SB HB1. lia.
    - eapply Z.le_trans; [exact HB2|]. clear -DTc TG Ra HLc. unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
      pose proof (Z.div_le_mono (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) 140737479966720 8 ltac:(lia) ltac:(lia)).
      assert (DS : bv_unsigned a / 8 + secmapsize (bv_unsigned (rw rho 12%positive)) / 8 <= (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) / 8).
      { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (bv_unsigned a) 8). pose proof (Z.mul_div_le (secmapsize (bv_unsigned (rw rho 12%positive))) 8). lia. }
      lia. }

  set (Jf := (fun (_ : valuation) t tr md => JGs A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokf rhoX t tr ms md msv' (JGs_K _ _ _ _ _ _ _ _ HJ) HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoX) (ss_facts (ax_S CO)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CO tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JGs A Kc rho a) Jf Jf (JGs A Kc rho a) CO Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.
End MS.

Lemma JGs_nums : ltac2:(tb__ "0|6|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcA2A2S5S3eG0R7A2S5S75R2A1S5S1S1S34Zfc01R3A2S37R3S3aZ2Z27A2A2A2S1S1S34Z12000R1A2S34R1S35R3Z3007A2A2A2S1S0S5S38R1S6bA2Z0M2A3S1S0S5S38R2S6bA2G2A3S1S34S6fR2A2S1S34S35R2R1A2Z7fffff800000A2S1S0S5S77R3A1M3S35S70R3Z8M4A2M5Z1000A2A3S1S0S5R1S35S70G3S6bA2S6bA2A3S1S0S5S38G5G4A2G2A3S1S34R3G5A2S34G5S35R3Z7A2A2A2A2A2A2A2A2A2A2A2A2TL;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB). cbn zeta.
  pose proof (secmapsize_bounds (bv_unsigned (rw rho 12%positive)) ltac:(clear -HN; lia)) as [SMB SMM].
  pose proof HP as (_ & AL & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG. destruct DI as (_ & _ & DT & _).
  pose proof (topG_range (aa_geom A)) as TG.
  pose proof (round_up_ge' (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as R1. pose proof (round_up_mod (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as R2.
  repeat split; try assumption; try reflexivity; try (clear -HN; lia); try (clear -DT TG; lia); try (clear -R1; lia); try (clear -SMB; lia).
Qed.

Lemma site1_a2 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S0G0S1aR5S8bVnx;A1A2S1aR5S1fZ200A1A2A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & _).
  pose proof (urange a) as Ra.
  unfold a2e1, vMAPn. cbn [eval]. rewrite Enx. apply bv_eq.
  rewrite sub_val, add_val, !srl_val, add_val, !u64_lit by lia. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold PG in AL. set (ua := bv_unsigned a) in *.
  rewrite (Z.mod_small (ua + 4088)) by (clear -Ra TOP SMB; lia).
  replace ((ua + 4088) / 8) with (ua / 8 + 511).
  2:{ replace (ua + 4088) with (ua + 511 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite (Z.mod_small (ua / 8 + 511 + 1)) by (clear -Ra TOP SMB; pose proof (Z.div_pos ua 8); pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61)); lia).
  rewrite Z.mod_small by (clear -Ra; pose proof (Z.div_pos ua 8); lia). lia.
Qed.

Lemma site1_bounds : ltac2:(tb__ "0|4|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S1S0S5S3eG0S1aR5S87Vnx;A1A2A2S6cS3eG0R6A2A1M2A3S1S0S5S3eG0S1aR5S85A2A2Z200M3A3S34S35G2G3A2S35G2S36S75S3eG0S18R7PcA2A2A1Z8A2A2A2A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & _).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  split; [|split].
  - unfold B1, shS, vMAPn. cbn [eval]. rewrite Enx, add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. fold ua. unfold Sh, SHADOW_OFF. apply Z.mod_small.
    clear -Ra TOP. pose proof (Z.div_pos ua 8). pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61)). lia.
  - unfold L1. cbn [eval]. apply u64_lit. lia.
  - pose proof (Z.div_le_mono 73728 (secmapsize (bv_unsigned (rw rho 12%positive))) 8 ltac:(lia) ltac:(clear -SMB; lia)). clear -H. cbn in H. lia.
Qed.

Lemma land_m8 : ltac2:(tb__ "0|0|
S5S1S34Z0R1A2S37R1S3aZ2Z40A2A2A2S0S5S3cR2Zfffffffffffffff8A2S39R2S38R2Z8A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. reflexivity. Qed.
Lemma land_m4096 : ltac2:(tb__ "0|0|
S5S1S34Z0R1A2S37R1S3aZ2Z40A2A2A2S0S5S3cR2Zfffffffffffff000A2S39R2S38R2Z1000A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask by lia. reflexivity. Qed.

Lemma site2_vals : ltac2:(tb__ "0|a|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcA2A2S5S3eG0R7A2S5S77R2A1S5S75R3A1S5S1S0S5S3eG0S1aR9S8aVnx;A1A2A2S35S35S6cR3A1M2S36R2Z8M3A2M4A2Z200M5A2M6A3S1S0S5S3eG0S1aR9S84Vnx;A1A2A2G6A3S1S0S5S3eG0S1aR9S8cVnx;A1A2A2S39S39S36R1G3A2M7G4A2G5A2M8A3S1S0S5S3eG0S1aR9S86A2A2G8A3S1S1S34Z0M9G8A2S34G8Z1ffA2A2S1S0S5S38R2G3A2G9A3S1S0S5S38R1G3A2G9A3S0S5S35G6G8A2S35G2G7A2A3A2A2A2A2A2A2A2TMS;TVNS;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  set (VNS := secneeded nv) in *. set (MS := secmapsize nv) in *.
  assert (V8 : VNS mod 8 = 0) by (rewrite ENS, Z.add_mod, R8M by lia; reflexivity).
  assert (M8 : MS mod 8 = 0).
  { pose proof (Z.div_mod MS 4096 ltac:(lia)) as X. unfold PG in SMM. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (MS / 4096)) with ((512 * (MS / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (VB : 68609 <= VNS <= nv + 4103) by (rewrite ENS; clear -R8B HN; lia).
  assert (MB : VNS + 4096 <= MS <= VNS + 8191).
  { rewrite EMS. unfold PG. pose proof (round_up_ge' VNS 4096 ltac:(lia)). fold VNS in H. clear -H. lia. }
  pose proof (Z.div_mod VNS 8 ltac:(lia)) as DV. pose proof (Z.div_mod MS 8 ltac:(lia)) as DM. pose proof (Z.div_mod ua 8 ltac:(lia)) as DA.
  rewrite V8 in DV. rewrite M8 in DM. rewrite A8 in DA.
  assert (SHB : Sh ua + MS / 8 < 2 ^ 45) by (unfold Sh, SHADOW_OFF; clear -TOP DM DA Ra MB VB; lia).
  assert (EA0 : bv_unsigned (eval r (a0e2 nx)) = Sh ua + VNS / 8 + 512).
  { unfold a0e2, vMAPn. cbn [eval]. rewrite Enx, E141. rewrite add_val, srl_val, and_val, !add_val, !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua VNS. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (ua + 4096)) by lia. rewrite (Z.mod_small (ua + 4096 + VNS)) by lia.
    rewrite land_m8 by lia. replace (ua + 4096 + VNS) with ((ua / 8 + 512 + VNS / 8) * 8) by (clear -DA DV; lia).
    rewrite Z_mod_mult, Z.sub_0_r, Z.div_mul by lia.
    unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EB : bv_unsigned (eval r (B2 nx)) = Sh ua + VNS / 8 + 512).
  { unfold B2, BR, shS, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !add_val. rewrite !srl_val. rewrite !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF in *. rewrite !Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EA2 : bv_unsigned (eval r (a2e2 nx)) = MS / 8 - VNS / 8 - 512).
  { unfold a2e2, msx, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !sub_val. rewrite !add_val. rewrite !srl_val. rewrite !and_val. rewrite ?add_val, ?and_val, ?add_val.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite !u64_lit by lia.
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite land_m4096 by lia.
    assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = MS).
    { rewrite EMS. unfold round_up, PG. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). replace (VNS + 4095) with (VNS + 4096 - 1) by lia. lia. }
    rewrite ERU. rewrite (Z.mod_small MS) by lia. rewrite (Z.mod_small (MS + ua)) by lia.
    replace ((MS + ua + (2 ^ 64 - 8)) mod 2 ^ 64) with (MS + ua - 8).
    2:{ replace (MS + ua + (2 ^ 64 - 8)) with (MS + ua - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
    rewrite (Z.mod_small (ua + 4096)) by lia. rewrite (Z.mod_small (ua + 4096 + VNS)) by lia. rewrite land_m8 by lia.
    replace (ua + 4096 + VNS) with ((ua / 8 + 512 + VNS / 8) * 8) by (clear -DA DV; lia).
    rewrite Z_mod_mult, Z.sub_0_r, Z.div_mul by lia.
    replace (MS + ua - 8) with ((MS / 8 + ua / 8 - 1) * 8) by (clear -DA DM; lia). rewrite Z.div_mul by lia.
    rewrite (Z.mod_small (MS / 8 + ua / 8 - 1 + 1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EL : bv_unsigned (eval r L2) = MS / 8 - VNS / 8 - 512).
  { unfold L2. cbn [eval]. rewrite E141, E142. rewrite ?sub_val, ?add_val, ?srl_val, ?add_val, ?srl_val. rewrite !u64_lit by lia.
    change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !Z.mod_small; lia. }
  repeat split; try assumption; lia.
Qed.

Section Reveal.
Variables E0 T0 : axst.
Hypothesis SKT : ltac2:(tb__ "0|1|
S0S7SbSbS17S17A2S17A2M0A1S4dS15G0S63S1dS2dVT0;A1A1A4S4dS15G0S63S52A4A3").
Hypothesis FCT : ltac2:(tb__ "0|0|
S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dVT0;A1A1A3").
Hypothesis AF0 : ltac2:(tb__ "0|0|
S16S7S3fQ40A1A1SbS7S7aA1S92A2S68Vsegs;R3R2VE0;R1A5S4eS19S29R4A1S88Vnx;Vhi;A2A3S68Vsegs;R5R4VT0;R3A5F_;F_;Fw;Ftp;Frho;").

Lemma F_map_hold : ltac2:(tb__ "0|2|
S41S59S16S3fQ40M0A1M1S16S7G1A1S7S7aA1S79S4fR8R7R6R5R4R3R2R1A8S54Vhi;S3eG0R6A2S75S3eG0S18R7PcA2A2A1A3S4eS19S29R6A1S88Vnx;Vhi;A2A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ HC.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  set (nv := bv_unsigned (rw rho 12%positive)) in *. pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB _].
  pose proof HP as (_ & _ & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG.
  destruct DI as (D0 & _ & DT & _ & WB). pose proof (topG_range (aa_geom A)) as TG.
  assert (EUM : bv_unsigned (alu64 ALU_ADD a (rw r V_MS)) = ua + secmapsize nv).
  { rewrite add_val, E142, u64_lit by (clear -SMB HN; lia). fold ua. apply Z.mod_small. clear -Ra DT TG SMB. lia. }
  unfold F_map, F_cls, clsP in *. apply Forall_app. split.
  - apply Forall_cons. { cbn [holds]. rewrite Enx. fold ua. split; [lia|]. change (2 ^ 12) with PG. exact (proj1 (proj2 HP)). }
    apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold IMG_HI; lia). exact IMG. }
    apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, EUM, u64_lit by lia. clear -DT TG. lia. }
    apply Forall_nil.
  - destruct hi.
    + apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia). exact HC. }
      apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by lia. fold ua. clear -DT TG SMB. lia. }
      apply Forall_nil.
    + apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia). fold ua. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in *. clear -HC SMB. lia. }
      apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, EUM, u64_lit by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia). exact HC. }
      apply Forall_nil.
Qed.

Lemma sec_reveal : ltac2:(tb__ "0|4|
S41S59S16S3fQ40M0A1M1S16S7G1A1M2S7S7aA1M3SabS79S7eVW;Vst;A2S76VW;Vst;A2S5dRaA1S3eG0S18RaPcA2A2S5S54Vhi;S3eG0RaA2S75R1A1A3S64Vsegs;S53ReRdRcRbA4VE0;RaR9SeG3S92R8S93R7R6A2A4A6S2G2G2S2S16S16S2S16S16S1S51S3eG0RfA2S75R6A1R10R1A4S1S6S0G1S18R3R1A2S18RfR1A2A3Fi;S1S6S0S7S3fQ8A1A1S1eR3R1A2S1eRfR1A2A3Fl;S64Vsegs;S4fR12R11R1RfA4VT0;R2S9G1R3RdA3SeG3S92RcS93RbRaA2A4A6A2A2A2Lrho';A2LrhoX';A2Ltp1;A2F_;F_;Tnv;F_;F_;F_;Fmd;Fms;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp tr ms md HW HUS HKc nv HC Hsp.
  pose proof (proj2 Hsp) as [HJ HCR]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ, HCR. fold nv in HCR.
  pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & E145 & E146 & E147 & Erm & Erl).
  pose proof HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB). fold nv in HA, HP, HN, HB.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB SMM]. set (L := secmapsize nv) in *.
  pose proof HP as (_ & _ & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG.
  destruct DI as (D0 & _ & DT & _ & WB). pose proof (topG_range (aa_geom A)) as TG.

  assert (HT0 : SPA segs (JGsC A Kc rho a) T0 rhoX tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hsp)]. apply AF0; [exact (proj1 Hsp) | exact (F_map_hold A Kc rho a rhoX tp tr md HJ HC)]. }

  destruct (SPA_J_out segs _ T0 rhoX tp _ HT0) as [HJT _].
  set (q := pgq (Sh ua)). set (np := npg (Sh ua) (Sh ua + L / 8)).
  pose proof (pg_run (Sh ua) (Sh ua + L / 8) ltac:(unfold Sh, SHADOW_OFF; clear -Ra; lia) ltac:(clear -SMB; pose proof (Z.div_pos L 8); lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  fold q in Q1, Q2, Q3, Q5, Q6. fold np in Q2, Q4, Q6.
  pose proof (shadow_run_band hi ua L HC IMG HL ltac:(clear -DT TG; lia)) as (RB & RLO & RHI & RBL & RBH). fold q np in RB, RLO, RHI, RBL, RBH.

  pose proof HA as (HG & _ & _ & _ & HM & HI3 & HBT). rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof HM as (VG & V2 & V3 & V0 & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & _ & G9).
  assert (BAND : forall k, (k < Z.to_nat np)%nat ->
            page_in_ranges (pageZ q k) (m_vm_lazy md) = true /\ forall j, 0 <= j < PG -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned (pageZ q k) + j) = false).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk RLO RHI Q4; unfold PG in *; lia).
    apply G9; rewrite UP.
    - replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. unfold PG. rewrite Z_mod_plus_full. exact Q3.
    - clear -RB Hk Q4. unfold PG in *. destruct hi; [right | left]; lia. }
  assert (NPZ : 4096 * Z.of_nat (Z.to_nat np) = PG * np) by (unfold PG; clear -Q4; lia).
  assert (ROOM : headroom md tp >= 4096 * Z.of_nat (Z.to_nat np)).
  { rewrite NPZ. unfold headroom. rewrite V3. pose proof (AInvA_boundD _ _ _ _ HA) as BD. rewrite AXb in BD.
    unfold budget_bound in BD. unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [aa_V aa_Km aa_Kf bumpV] in BD.
    assert (NP : PG * np <= SHC nv).
    { unfold SHC, PG. fold L. replace (L / (8 * 4096)) with (L / 8 / 4096) by (rewrite Zdiv_Zdiv by lia; reflexivity). clear -Q4 SMB. unfold PG in Q4. lia. }
    pose proof (PrimCredit.prim_credit_nonneg (AX (bumpV A nv))) as PCN. clear -HCR BD HB NP PCN. unfold BETA_M in *. lia. }

  assert (HT0' : SPA segs (JGs A Kc rho a) T0 rhoX tp (tr, mkCfg ms md)) by (split; [exact (proj1 HT0) | exact HJ]).
  assert (NP1 : 1 <= np).
  { assert (L8 : 9216 <= L / 8) by (apply Z.div_le_lower_bound; clear -SMB; lia). clear -Q1 Q2 L8. unfold PG in Q2. nia. }
  assert (DISJ : Forall (fun o => ranges_disjoint (obj_range rhoX o) (q, q + 4096 * Z.of_nat (Z.to_nat np))) (ss_objs (ax_S T0))).
  { destruct (objs_noband T0 [] [] A Kc rho a rhoX tp _ HW HT0' ltac:(cbn [app]; rewrite app_nil_r; exact SKT) FCT) as (l0 & l1 & l2 & EO12 & SK0' & SK2 & NB).
    destruct l2; [|discriminate SK2]. destruct l0; [|discriminate SK0']. rewrite app_nil_r in EO12. cbn [app] in EO12. rewrite EO12. eapply Forall_impl; [|exact NB]. intros o Ho. rewrite NPZ. unfold ranges_disjoint, range_noband, noband in *. cbn [fst snd].
    destruct (obj_range rhoX o) as [olo ohi]. cbn [fst snd] in Ho |- *.
    destruct (Z_le_dec ohi olo) as [E|E]; [left; exact E|].
    destruct (Z_le_dec ohi q) as [E2|E2]; [right; right; left; exact E2|].
    destruct (Z_le_dec (q + PG * np) olo) as [E3|E3]; [right; right; right; exact E3|].
    exfalso. destruct (Ho (Z.max olo q) ltac:(clear -E E2 E3; lia)) as [Y|Y]; clear -Y E E2 E3 RBL RBH NP1; unfold PG in *; lia. }
  destruct (SPA_reveal_pages T0 q (Z.to_nat np) rhoX tp tr ms md HJT Q3 RLO ltac:(rewrite NPZ; exact RHI)
              ltac:(intros k Hk; exact (proj1 (BAND k Hk)))
              ltac:(intros z Hz; rewrite NPZ in Hz; destruct (page_base_run q (Z.to_nat np) (Z_to_bv 64 z) Q3 ltac:(clear -RLO; lia) ltac:(rewrite NPZ; exact RHI) ltac:(rewrite u64_lit by (clear -Hz RLO RHI; lia); rewrite NPZ; exact Hz)) as (k & Hk & Ek & Rk);
                    rewrite u64_lit in Rk by (clear -Hz RLO RHI; lia);
                    pose proof (proj2 (BAND k Hk) (z - (q + 4096 * Z.of_nat k)) ltac:(unfold PG; clear -Rk; lia)) as X;
                    rewrite pageZ_u in X by (clear -Hk RLO RHI Q4 NPZ; unfold PG in *; lia);
                    replace (q + 4096 * Z.of_nat k + (z - (q + 4096 * Z.of_nat k))) with z in X by lia; exact X)
              ROOM DISJ) as (tp1 & rho1 & Hsp1 & HR).
  pose proof HR as (Rw & Rl & Rtp1 & Rlen & Rvis & Rz & Rk & Ro).
  assert (RHI' : q + 4096 * Z.of_nat (Z.to_nat np) <= 2 ^ 64) by (rewrite NPZ; exact RHI).
  pose proof (revealed_ext JT T0 q (Z.to_nat np) rhoX tp rho1 tp1 tr ms md HJT HR Q3 RLO RHI' ltac:(intros k Hk; exact (proj1 (BAND k Hk))) DISJ) as EXT.

  assert (RUNPG : forall k, (k < Z.to_nat np)%nat -> band_page (bv_unsigned (pageZ q k)) /\ bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk RLO RHI Q4; unfold PG in *; lia).
    split; [|exact UP]. rewrite UP. unfold band_page. clear -RB Hk Q4. unfold PG in *. destruct hi; [right | left]; lia. }
  assert (NP : PG * np <= SHC nv).
  { unfold SHC, PG. fold L. replace (L / (8 * 4096)) with (L / 8 / 4096) by (rewrite Zdiv_Zdiv by lia; reflexivity). clear -Q4 SMB. unfold PG in Q4. lia. }

  assert (HA1 : AInvA segs (AX (bumpV A nv)) rho1 (tp1 ++ tp) md).
  { apply (AInvA_reveal segs _ rhoX); [exact HA | exact EXT | |].
    - intros p Hp. destruct (Rtp1 p Hp) as ((k & Hk & ->) & Hnin). destruct (RUNPG k Hk) as [BP UP]. split; [exact BP|].
      intros z Hz. rewrite UP in Hz. rewrite view_in by (clear -Hz RLO RHI' Hk Q4 NPZ; unfold PG in *; lia). unfold rd_of.
      rewrite (Rz (Z_to_bv 64 z)); [eexists; reflexivity| |].
      + rewrite u64_lit by (clear -Hz RLO RHI' Hk NPZ; unfold PG in *; lia). clear -Hz Hk NPZ RLO. unfold PG in *. lia.
      + apply (proj2 (page_mem_false _ _)). rewrite (page_base_in_page (pageZ q k)); [exact Hnin| |].
        * rewrite UP. replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. change page_size with 4096. rewrite Z_mod_plus_full. exact Q3.
        * unfold in_page. rewrite UP, u64_lit by (clear -Hz RLO RHI' Hk NPZ; unfold PG in *; lia). change page_size with 4096. unfold PG in Hz. exact Hz.
    - pose proof (revealed_paid q (Z.to_nat np) rhoX tp rho1 tp1 md HR) as RP. rewrite NPZ in RP. clear -RP NP HCR. lia. }

  set (rho' := mkVal (rw rho) (rl rho) (rm rho1)).
  assert (RWM : forall i, rw (rhoM_of A rho') i = rw (rhoM_of A rho) i) by (intros i; reflexivity).
  assert (RLM : forall l, rl (rhoM_of A rho') l = rl (rhoM_of A rho) l) by (intros l; reflexivity).
  assert (RMM : forall x, rm (rhoM_of A rho') x = rm rho1 x) by (intros x; reflexivity).
  destruct Hagr as (A1 & A2 & A3).
  exists tp1, rho1, rho'. split; [|split; [exact Rw | split; [exact Rl|]]].
  -
    split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros x. cbn [rho' rm]. destruct (EXT x) as [E|[N I]].
      * left. rewrite E. apply Erm.
      * destruct (Z_lt_le_dec (bv_unsigned x) q) as [Y|Y]; [left; rewrite (Ro x) by (clear -Y; lia); apply Erm|].
        destruct (Z_lt_le_dec (bv_unsigned x) (q + 4096 * Z.of_nat (Z.to_nat np))) as [Y2|Y2]; [|left; rewrite (Ro x) by (clear -Y2; lia); apply Erm].
        right. left. split; [rewrite <- Erm; exact N|]. split; [exact I|]. rewrite NPZ in Y2. clear -Y Y2 RBL RBH. lia.
    + intros z Hz. cbn [rho' rm].
      assert (Hzq : q <= z < q + 4096 * Z.of_nat (Z.to_nat np)) by (rewrite NPZ; clear -Hz Q1 Q2; lia).
      assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; clear -Hzq RLO RHI'; lia).
      destruct (page_mem (page_base (Z_to_bv 64 z)) tp) eqn:PM.
      * rewrite (Rk (Z_to_bv 64 z)) by (rewrite ?Uz; assumption).

        destruct (page_base_run q (Z.to_nat np) (Z_to_bv 64 z) Q3 ltac:(clear -RLO; lia) RHI' ltac:(rewrite Uz; exact Hzq)) as (k & Hk & Ek & Rk2).
        destruct (RUNPG k Hk) as [BP UP]. apply (proj1 (page_mem_In _ _)) in PM. rewrite Ek in PM.
        pose proof (HBT _ PM BP z ltac:(rewrite UP; rewrite Uz in Rk2; unfold PG; clear -Rk2; lia)) as [b Hb].
        rewrite view_in in Hb by (clear -Hzq RLO RHI'; lia). unfold rd_of in Hb.
        destruct (rm rhoX (Z_to_bv 64 z)) eqn:E; [discriminate|]. exfalso. rewrite image_byte_none_A in Hb by (rewrite Uz; clear -Hzq RLO; lia). discriminate.
      * rewrite (Rz (Z_to_bv 64 z)) by (rewrite ?Uz; assumption). discriminate.
  -
    apply SPA_J_in; [exact Hsp1|]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
    unfold JGs. cbn [rw rho']. fold nv.
    split.
    { split; [|split].
      - intros i Hi. rewrite RWM, Rw. exact (A1 i Hi).
      - intros l. rewrite RLM, Rl. rewrite <- (A2 l). reflexivity.
      - intros x. rewrite RMM. reflexivity. }
    split; [rewrite Rw; exact Enx|].
    split; [exact HA1|]. split; [exact HP|]. split; [exact HK|].
    split; [unfold tp_ok in Htp |- *; rewrite Rw; exact Htp|].
    split; [apply (stopJ_rwrl rhoX rho1); [intros i; symmetry; apply Rw | intros l; symmetry; apply Rl | exact HU]|].
    split; [exact HN|]. split; [|exact HB].
    unfold top_high in Htop |- *. rewrite !Rw. exact Htop.
Qed.

Section G12.

Variables (ET1 CT1 CO1 T1 ET2 CT2 CO2 T2 : axst) (s1 s2 : wsub) (R1 R2 : list sobj).
Let D1 : axst := ltac2:(tb__ "0|0|
S95VT1;S1bS2dVCO1;A1A1A2").
Let D2 : axst := ltac2:(tb__ "0|0|
S95VT2;S1bS2dVCO2;A1A1A2").

Hypothesis Cert1 : ltac2:(tb__ "0|1|
S0S8S9bS8fUfa0SdS5Sa0ScS5A1A3S50SdS2eVT0;ScS2eA1M0A3SdS2eVET1;G0A3A6SaA3").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S8S9bS8fUfa0SdS5Sa0ScS5A1A3S50SdS2eVD1;ScS2eA1M0A3SdS2eVET2;G0A3A6SaA3").

Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S8S21S2dVCT1;A1A1SaA3").
Hypothesis DF1 : ltac2:(tb__ "0|4|
S0SfSbS7SbS17S17A2M0A1M1S7S19A1M2A2M3A1S9aS2dVET1;A1S2dVCT1;A1A2S10G3SeG1G2SdG0SeS17S17S8bVnx;A1S85A4ScG0A1A3ScS19A1A4A2A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S6S1cS2dVCT1;A1A1S1cS2dVET1;A1A1A3").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S0S2eS31VET1;S2dVCT1;A1A2VCT1;A3").
Hypothesis SK1 : ltac2:(tb__ "0|2|
S0S7SbSbS17S17A2S17A2M0A1S4dS15G0S63S1dS2dVCT1;A1A1A4S4dS15G0S63S9S15ScS15A1M1S9S15S52G1A3A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dVCT1;A1A1A3").
Hypothesis XC1 : ax_X CT1 = [].
Hypothesis HCO1 : ltac2:(tb__ "0|0|
S0S2eS83VCT1;S23S87Vnx;A1S1fZ0A1S85ScS22A1S26A5A2VCO1;A3").
Hypothesis WCO1 : ltac2:(tb__ "0|0|
S0S8S21S2dVCO1;A1A1SaA3").
Hypothesis He1 : ltac2:(tb__ "0|1|
S0SfS7S15A1M0A1S97VCO1;S7fVs1;A3S10G0VR1;A2A3").
Hypothesis Hchk1 : ltac2:(tb__ "0|0|
S0S8S96VCO1;S7fVs1;VR1;S4dS2fS2eS30S80A4A5SaA3").
Hypothesis HT1 : ltac2:(tb__ "0|0|
S0S2eS98Vs1;S7fS89VCO1;VR1;A5VT1;A3").
Hypothesis FBC1 : ltac2:(tb__ "0|1|
S0S8S81S19S20S1cS2dVCO1;A1M0A1A1S1bG0A1A3SaA3").
Hypothesis FBT1 : ltac2:(tb__ "0|0|
S0S8S81S19S20S1cS2dVT1;A1A1A1S1bS2dVCO1;A1A1A3SaA3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S8S90S50S1cS2dVCO1;A1A1A2SaA3").

Hypothesis WC2 : ltac2:(tb__ "0|0|
S0S8S21S2dVCT2;A1A1SaA3").
Hypothesis DF2 : ltac2:(tb__ "0|4|
S0SfSbS7SbS17S17A2M0A1M1S7S19A1M2A2M3A1S9aS2dVET2;A1S2dVCT2;A1A2S10G3SeG1G2SdG0SeS17S17S8aVnx;A1S84Vnx;A1A4SdG0SeS17S17S8cVnx;A1S86A4ScG0A1A3A3S8eA4A2A3").
Hypothesis NX2 : ltac2:(tb__ "0|0|
S0S6S1cS2dVCT2;A1A1S1cS2dVET2;A1A1A3").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S0S2eS31VET2;S2dVCT2;A1A2VCT2;A3").
Hypothesis SK2 : ltac2:(tb__ "0|2|
S0S7SbSbS17S17A2S17A2M0A1S4dS15G0S63S1dS2dVCT2;A1A1A4S4dS15G0S63S9S15SdS15S8dVnx;A1ScS15A1M1A3S9S15S52G1A3A3A4A3").
Hypothesis FC2 : ltac2:(tb__ "0|0|
S82S19S9S19S5cVW;Vst;A2S5bS5aA1A3S1bS2dVCT2;A1A1A3").
Hypothesis XC2 : ax_X CT2 = [].
Hypothesis HCO2 : ltac2:(tb__ "0|0|
S0S2eS83VCT2;S23S84Vnx;A1S1fZ0A1S86ScS22A1S26A5A2VCO2;A3").
Hypothesis WCO2 : ltac2:(tb__ "0|0|
S0S8S21S2dVCO2;A1A1SaA3").
Hypothesis He2 : ltac2:(tb__ "0|1|
S0SfS7S15A1M0A1S97VCO2;S7fVs2;A3S10G0VR2;A2A3").
Hypothesis Hchk2 : ltac2:(tb__ "0|0|
S0S8S96VCO2;S7fVs2;VR2;S4dS2fS2eS30S80A4A5SaA3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S2eS98Vs2;S7fS89VCO2;VR2;A5VT2;A3").
Hypothesis FBC2 : ltac2:(tb__ "0|1|
S0S8S81S19S20S1cS2dVCO2;A1M0A1A1S1bG0A1A3SaA3").
Hypothesis FBT2 : ltac2:(tb__ "0|0|
S0S8S81S19S20S1cS2dVT2;A1A1A1S1bS2dVCO2;A1A1A3SaA3").
Hypothesis NXC2 : ltac2:(tb__ "0|0|
S0S8S90S50S1cS2dVCO2;A1A1A2SaA3").

Lemma RS1 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7bS7eVW;Vst;A2S64Vsegs;S4fR8R7R6R5A4VET1;R4R3R2A6S64Vsegs;S4fR9R8R7R6A4VCT1;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC1.
  eapply SPA_restate; [exact WC1 | exact DF1 | exact NX1 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold L1.
  exact (site1_a2 A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma HBL1 : forall A Kc rho a rhoX tp w, SPA segs (JGs A Kc rho a) CT1 rhoX tp w ->
  Sh (bv_unsigned a) <= bv_unsigned (eval rhoX (B1 nx))
  /\ bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1) <= Sh (bv_unsigned a) + secmapsize (bv_unsigned (rw rho 12%positive)) / 8
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B1 nx)), bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1))) l)
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B1 nx)), bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1))) l).
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]].
  destruct (site1_bounds A Kc rho a rhoX tp tr md (proj2 Hw)) as (EB & EL & BB). rewrite EB, EL.
  split; [lia|]. split; [exact BB|]. split; intros [|o l2] EE; [constructor | discriminate EE | constructor | discriminate EE].
Qed.

Lemma RS2 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S7G0A1S7bS7eVW;Vst;A2S64Vsegs;S4fR8R7R6R5A4VET2;R4R3R2A6S64Vsegs;S4fR9R8R7R6A4VCT2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC2.
  destruct (site2_vals A Kc rho a rhoX tp tr md (proj2 Hw)) as (EA0 & EB & EA2 & EL & BL & _).
  eapply SPA_restate; [exact WC2 | exact DF2 | exact NX2 | | | exact Hw].
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]; apply bv_eq; rewrite EA0, EB; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; apply bv_eq; rewrite EA2, EL; reflexivity | apply Forall_nil].
  - unfold fx2. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite EL, u64_lit by lia. lia.
Qed.

Lemma HBL2 : forall A Kc rho a rhoX tp w, SPA segs (JGs A Kc rho a) CT2 rhoX tp w ->
  Sh (bv_unsigned a) <= bv_unsigned (eval rhoX (B2 nx))
  /\ bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2) <= Sh (bv_unsigned a) + secmapsize (bv_unsigned (rw rho 12%positive)) / 8
  /\ (forall l, map skel l = map skel [O_1 nx] ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B2 nx)), bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2))) l)
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B2 nx)), bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2))) l).
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]].
  destruct (site2_vals A Kc rho a rhoX tp tr md (proj2 Hw)) as (EA0 & EB & EA2 & EL & BL & V8 & M8 & SUM). rewrite EB, EL.
  destruct (site1_bounds A Kc rho a rhoX tp tr md (proj2 Hw)) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums A Kc rho a rhoX tp tr md (proj2 Hw)) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  assert (V512 : 512 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (rewrite ENS; apply Z.div_le_lower_bound; clear -R8B HN; lia).
  split; [clear -V512; lia|]. split; [clear -SUM BL; lia|]. split; [|intros [|o l2] EE; [constructor | discriminate EE]].
  intros l2 EE. destruct l2 as [|o [|o' l2']]; [constructor | | cbn in EE; discriminate EE].
  apply Forall_cons; [|apply Forall_nil].
  assert (Es : skel o = skel (O_1 nx)) by (cbn in EE; congruence).
  rewrite (obj_range_skel rhoX o (O_1 nx) Es). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
  unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
Qed.

Theorem sec_g12 : ltac2:(tb__ "0|3|
S7bOF_;S41S59S16S3fQ40M0A1M1S7G1A1M2S7dS7eVW;Vst;A2S76VW;Vst;A2S5dR7A1S65Vsegs;RaS67R8A1A3S3eG0S18R8PcA2A2S5S54Vhi;S3eG0R8A2S75R1A1A3S16S16G2S51S3eG0RcA2S75R5A1RdR3A4S7cVsegs;R11S64Vsegs;S4fR10RfR4RdA4VD2;R3R2A5RbA4F_;FtpY;FrhoY;Frho';S16S7cVsegs;RfS64Vsegs;S53ReRdRcRbA4VE0;R1RaA5R9A4FrhoX;F_;F_;Tnv;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HW HUS HKc Hokl nv HC HCONT rhoX.
  apply (triple_conseq (P:=fun w => exists tp1 rhoX' rho', slink (bv_unsigned a) (secmapsize nv) rho rho' /\ SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp) w)
           (SPA segs (JGsC A Kc rho a) E0 rhoX tp) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { destruct w as [tr [ms md]]. destruct (sec_reveal A Kc rho a rhoX tp tr ms md HW HUS HKc HC Hw) as (tp1 & rhoX' & rho' & SL & _ & _ & Hsp).
    exists tp1, rhoX', rho'. exact (conj SL Hsp). }
  apply triple_ex; intros tp1. apply triple_ex; intros rhoX'. apply triple_ex; intros rho'.
  apply (triple_pre_pure segs ok _ _ (slink (bv_unsigned a) (secmapsize nv) rho rho')); [intros w [SL _]; exact SL|]. intros SL.
  eapply triple_conseq; [intros w [_ Hw]; exact Hw | intros w Hw; exact Hw |].
  assert (E12' : rw rho' 12%positive = rw rho 12%positive) by (destruct SL as (SW & _); apply SW).
  assert (HST : stableA segs GS (JGs A Kc rho' a)) by (apply JGs_stable; assumption).
  assert (Hokf : ok_frameA segs ok (JGs A Kc rho' a)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). exact (JGs_K _ _ _ _ _ _ _ _ HJ). }
  apply (cfg_soundA segs 4000%nat [MSENT] GS [T0] [ET1] (JGs A Kc rho' a) ok Q (tp1 ++ tp) Hokf HST Cert1); [|left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step ET1 CT1 CO1 T1 (B1 nx) L1 [] [] Pre_memsetA Pret_ms Posts_memsetA s1 R1 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS1 HBL1 SK1 FC1 XC1 HCO1 WCO1 He1 Hchk1 HT1 FBC1 FBT1 NXC1
           ok A Kc rho rho' a (tp1 ++ tp) Q HW HUS HKc Hokl); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoY tpY. fold D1.
  apply (cfg_soundA segs 4000%nat [MSENT] GS [D1] [ET2] (JGs A Kc rho' a) ok Q tpY Hokf HST Cert2); [|left; reflexivity].
  intros E' rhoE' HinE'. destruct HinE' as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step ET2 CT2 CO2 T2 (B2 nx) L2 [O_1 nx] [] Pre_memsetA Pret_ms Posts_memsetA s2 R2 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS2 HBL2 SK2 FC2 XC2 HCO2 WCO2 He2 Hchk2 HT2 FBC2 FBT2 NXC2
           ok A Kc rho rho' a tpY Q HW HUS HKc Hokl); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoZ tpZ. fold D2. apply HCONT. exact SL.
Qed.
End G12.
End Reveal.

End SEC3.
End SpineCallocSec3.

(* [comment removed for export] *)
Module SpineCallocSecE0.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "sprop"; "SLit"; "valuation"; "reg_sv"; "SVar"; "eval"; "swf"; "ss_objs"; "ss_pc"; "obj_range"; "ranges_disjoint"; "ro_addr"; "sprop_below"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "shadow_addr"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "prod"; "pair"; "true"; "app"; "Some"; "option"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "CS1"; "ES1"; "ES1f"; "ES1g"; "SS0"; "SSa_S"; "V_MS"; "nxS"; "ESn"; "F_sgen"; "RT_sec"; "SSb_S"; "V_NS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "ge"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "with_vmmaps"; "ENOMEM"; "errno_ret"; "vm_reserved"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN"; "stRn_S"; "s_n"; "stKn"; "N_secn"; "R_n"; "stRn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_null"; "JLc_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "A_globals"; "J_alloc_preT"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA"; "mmap_obj_sym"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "a1x"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymComplete SymCall SymExit SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MANY.
Variable segs : list Segment.
Theorem etriple_mmap_rw_sym_anyA : ltac2:(tb__ "0|10|
S40S40S3eQ40M0A1M1S40F_;S19SbS1fG1A1S6S3bS41Vsegs;S8S18R5A1A1R8A3S0S28S58A1S70Vsegs;S11S18R6A1A1A2S27S58S59A2A3S0S6ScS18R7A1Z11A2SaZdeA1A3S0S6ScS18R8A1ZbA2R5A3S0S20S17S8S18R9A1A1R6A2S25A3S0S3bS3dG0SeR9R7A2A2R6A3S0S3bS4fR7Z1000A2Z0M2A3S1S4bG2R8A2S4bR8S50Z2Z3eA2A2A2S1fS53A1M3S3aS51S64Vsegs;RfReR10S24G3S5eR3S5fR2R1A2A4A5R14R10RfR4R2A4S1S0S20S8aS39R4U2A2S39R4U3M4A2M5S39R4U5A2A3S25A3S1S0S20S8bG5A1S29A3S1S4eS8dR3R10A2ReA2S1R14R11R10R5R3A4G1S61S39R5U0A2S39R5G4A2R4S39R5U1M6A2R1A5S1S7S6dS7R1S10S18R15A1A1A3S13S12R15R2A2S24S3bS3bS3dG0R4A2M7S4cG7R12A2A4A2F_;Fo;S1G1S1S4dS3dG0R3A2M8S3dG0R1A2M9A2S4bG9S4cG8R11A2A2A2S0S20S14Vsegs;R2A2S29A3F_;Fx;S1S23S6S6A2MaS3bS6dGaR2S1aR16A1A3S1S4dS3dG0SeR16S2aS6S6R3A3A2A2MbR2A2S4bR2S4cGbS3dG0SeR16S2bS6S6R3A3A2A2A2A2A2S4S1S4dS3dG0R6A2McS3dG0S1eS3dG0SeR17S1bR18A1A2A2R3A2A2MdA2S4bGdS4cGcR14A2A2A2A1F_;F_;Fy;Fr;R15R2S45R13S8S18R14A1A1R2A3R12R7S54S62S52R5A1S39R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S42Vsegs;S3fVsegs;R11ReRdRcA5S43S5S3fVsegs;R11S65RfSaS3dG0S56S55A1A2A1A2ReRdR1A6S3G1G1S3fVsegs;R11R1A1S1cR10S46S18R10A1MeSdS8GeA1MfA1S26S7S10GeA1S21S7S92GfRdA2S22S7A1A3A3S89GfA1A4A2S45RfGfR1A3ReR2A6La;A2A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJf;FJ;").
Proof.
  intros J Jf Jo A rho tp elen nlit Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [exact (wstep_mmap_intro_failA segs ms md _ Hh H222 Hlen Hmodb tr Hp Hrf)|].
    left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
  - destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
    eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
    right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj_sym; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End MANY.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC2E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S3bS5cVCST;R1A2S5cS93R2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S3bS5cVCST;R1A2S5cS94R2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S81VAInv;VW;Vst;VA;VKc;SdPcA1A6").
Hypothesis law_res : ltac2:(tb__ "0|1|
S6cSbS1fS3eQ40A1M0A1S51VAInv;R4R3R2R1A4S0S1fS23G0G0A2A1S57S52R2A1A1S60S5bA1A3F_;Fmd;Ftp;Frho;FA;").
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S20SfS31VW;Vst;Vtmax;A3A1S25A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S63S18S76VW;Vst;Vtmax;Z8M4A4A1S31VW;Vst;Vtmax;A3A2S27G3S24G1G2S21G0S24S6S6S7dG4A1SdS38A1A4M5S21G0G5S22G0A1A3A3S22S9A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S20SfS37VW;Vst;Vtmax;A3A1S25A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S20S6eS9S15S7aA1S35A3S25A3").
Hypothesis NXS0 : ltac2:(tb__ "0|0|
S88S5aS8S18S30VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertS1 : ltac2:(tb__ "0|3|
S0S20S49S5bUfa0S21S3bZ7050cS22S3bA1A3S5aS21S47S48S30VW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S22S47A1M2A3S21S47S48S2dVW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S20SfS18S2cVW;Vst;Vtmax;A3A1A1S25A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S63S18S2dVW;Vst;Vtmax;A3A1S18S2cVW;Vst;Vtmax;A3A1A2S27G3S24G1G2S21G0S24S6S6S95SdS32A1A4S22G0A1A3S22S9A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S8S18S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S58A1S70S5bS11S18S2cVW;Vst;Vtmax;A3A1A1A2S27S58S59A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1Z11A2SaZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZbA2SdS32A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZcA2SaZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZdA2SaZ22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZeA2SaZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZfA2SaZ0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S7aA3").
Hypothesis NXS1f : ltac2:(tb__ "0|0|
S88S5aS8S18S2eVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertSf : ltac2:(tb__ "0|3|
S0S20S49S5bUfa0S21S3bZ5e5d4S22S3bA1A3S5aS21S47S48S2eVW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S22S47A1M2A3S21S47S48S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS9S26S9S26S9S26S9S26S9S84VW;Vst;A2S83S82A1A3S7bA3S78A3S77Vtmax;Z8A2A3S16S18S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis RN : ltac2:(tb__ "0|0|
S0S1fS7A1S6aVW;Vst;Vtmax;A3S26S7S7cS5dS91S7S90S69A4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S0S20SfS66VW;Vst;Vtmax;A3A1S25A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S63S18S68VW;Vst;Vtmax;A3A1S66VW;Vst;Vtmax;A3A2S27G3S24G1G2S21G0S24S6S6SaS8fA1SdP18A1A4S22G0A1A3S22S9A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S0S3cS8S66VW;Vst;Vtmax;A3A1S8S18S68VW;Vst;Vtmax;A3A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S0S20S1dS6bVW;Vst;Vtmax;A3S74VW;Vst;A2S67VW;Vst;Vtmax;A3A3S25A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S0S20S8eS67VW;Vst;Vtmax;A3A1S25A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZaA2SaZ0A1A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS23S6S6A2M0A1S1aS2cVW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS23S23S6S6A2S6A2M0A1S5dS7G0S86S10S18S2cVW;Vst;Vtmax;A3A1A1A4S5dS7G0S86S26S7S26S7S21S7S79S26S7S85VW;A1S80A3A3S7cA3S36A3A4A3").

Theorem esec_ecall : ltac2:(tb__ "0|4|
S6cS7eS3eQ40A1M0S40F_;SbS1fG0A1S43OF_;S73VW;Vst;A2S87VW;Vst;A2S7fR7A1SbS1fS53A1M1S3aS51G0S64Vsegs;R5RaS2cVW;Vst;Vtmax;A3M2S24G1S5eR4S5fR3R2A2A4A5S4aVW;Vst;RfReRcR6RbR5R3A9S61S39R5U0A2S39R5U3A2R4S39R5U1M3A2R3A5RfR4S45R8S8S18G2A1A1R4A3RdR7S54S62S52R5A1S39R6G3A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RbRaR8A5S2eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;SbG0S42Vsegs;S3fVsegs;RbR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RdRcRaA5G2R1R9A5R8A3FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.

  clear DC1 DKRn Da ECertS1 ECertSf ENTn FB IDn NXC1 NXRn NXS0 NXS1f RN WC1 WRn Wa Wb.
  intros A Kc Jo rho tp Q HW HUS HKc HJo HF HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (etriple_pre_pure segs _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  eapply etriple_seq.
  2: { apply etriple_disj; [exact (HF rhoX)|]. apply etriple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1f, ES1g, nxS. replace (SLit (2 ^ 64 - 12)) with (SLit (bv_unsigned (errno_ret ENOMEM))) by reflexivity.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (etriple_mmap_rw_sym_anyA segs (JG W st A Kc rho) (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split; [exact HJG|].
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe7bd8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe8978 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe7bd8); [apply (Gimg 0xe7bd8); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xf13f8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xf1404 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xf13f8); [apply (Gimg 0xf13f8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.

Theorem esec_spine : ltac2:(tb__ "0|5|
S6cS7eS3eQ40A1M0S40F_;SbS1fG0A1S1fS23S19S71A2M1A1S72Vsegs;S8cR3R2R1A5S44S73VW;Vst;A2S87VW;Vst;A2S7fR8A1S6dG1S24S19S71S74VW;Vst;A2S75VCST;VXGL;RaR9A4A4R5A3SbS1fS53A1M2S3aS51G0S64Vsegs;R5RcS2cVW;Vst;Vtmax;A3M3S24G2S5eR4S5fR3R2A2A4A5S4aVW;Vst;R11R10ReR6RdR5R3A9S61S39R5U0A2S39R5U3A2R4S39R5U1M4A2R3A5R11R4S45R8S8S18G3A1A1R4A3RfR7S54S62S52R5A1S39R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbG0S42Vsegs;S3fVsegs;RcR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3RaA5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;ReRdRbA5S76VW;Vst;Vtmax;Z8A4R1RaA5R8A3FrhoE;F_;F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FJo;FKc;FA;").
Proof.
  assert (USED := (HCST, HXGL, HCSTM, HCSTS, law_res, Wa, Da, Wb, FB, NXS0, ECertS1, WC1, DC1, NXC1, IC1, R17, R11, R12, R13, R14, R15, NX1, NXS1f, ECertSf, FC1, RN, WRn, DKRn, NXRn, ENTn, IDn, R10, XC1, SK1)); clear USED.
  intros A Kc Jo rho tp Posts Q HW HUS HKc HPosts HJo HOK rhoE.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cutS 4000%nat [0x7050c] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (SS0 W st tmax) rhoE HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS0.
  - exact ECertS1.
  - intros E' rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; right; exact Hw |].
    apply (esec_ecall A Kc Jo rho tp Q HW HUS HKc HJo); [|exact HOK].
    intros rhoY.
    exact (esec_tail_null nW st tmax CST XGL HCST HXGL HCSTM HCSTS NXS1f ECertSf RN WRn DKRn NXRn ENTn IDn A Kc rho tp Posts HUS HKc HPosts rhoY).
  - left. reflexivity.
Qed.
End SEC2E.
End SpineCallocSecE0.

(* [comment removed for export] *)
Module CRebuildS.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "modulo"; "pow"; "sub"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "False"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "bview"; "ERRNO_A"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "PG"; "kPtrArrayReserve"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "AA"; "aa_cls"; "aa_ptr_committed"; "ag_pab"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ageom"; "aa_Km"; "aa_live"; "ag_thread"; "class_state"; "sc_map_beg"; "sc_map_size"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "cs_empty"; "mkAA"; "mkSC"; "qbatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.CRebuildS"; "newZ"; "chg_s"; "secA"; "zimg"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "AInvA"; "quarantine_repr"; "kAllocBegMagic"; "nthZ"; "q_foot"; "@Corelib.Init.Datatypes"; "pair"; "Some"; "list"; "option"; "None"; "cons"; "length"; "prod"; "app"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "secneeded"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "cls_foot"; "rt_zoneM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition secA (A : AA) (ua nv : Z) : AA := ltac2:(tb__ "0|0|
S36S1eVA;A1S21VA;A1S30VA;A1S50S1dS1fVA;A1S4dS1dS37Vua;S56Vnv;A1S57Vnv;A1A3S52S1dA1A3A3S22VA;A1S4dS4fS0S0A2S48S0S0S2Vua;Z1800A2Vnv;A4S29VA;A1A3S25VA;A1S24VA;A1S31VA;A1S33VA;A1S32VA;A1S34VA;A1S2fVA;A1S28VA;A1S2eVA;A1Af").

Definition newZ (ua L : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdSaS1Vua;Vz;A2S3Vz;S2Vua;VL;A2A2A2SaS1S16Vua;A1M0Vz;A2S3Vz;S2G0S4VL;Z8A2A2A2A2A2").

Definition zimg (z : Z) : Prop := ltac2:(tb__ "0|0|
SdSaS1S42Vz;A2S3Vz;Zee044A2A2SdSaS1Zee048Vz;A2S3Vz;Zee070A2A2SdSbS0Vz;Z173660A3SaS1S14Vz;A2S3Vz;S2S14Z4A2A2A2A2A2A2").
Definition chg_s (G : ageom) (ua L pw blk : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdS3eVz;A1SdSaS1S2S2aVG;A1M0Zad0A2Vz;A2S3Vz;S2G0Zc60A2A2A2SdS3bVua;VL;Vz;A3SaS1Vpw;Vz;A2S3Vz;S2Vpw;Vblk;A2A2A2A2A2A2").

Lemma sh_apart : ltac2:(tb__ "0|6|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2M3G3G3SdS1S2R8R7A2RaA2S1S2RaR9A2R8A2A2SaS1S16R9A1M4R7A2S3R7S2G4S4S2R8Z7A2G0A2A2A2A2ScSaS1S16RcA1M5R8A2S3R8S2G5S4RbG0A2A2A2A2A1F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;FL;Fua;").
Proof.
  intros ua L lo len z Hu HL HL0 Hlo Hlen Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  destruct Hs as [Hs|Hs]; lia.
Qed.
Lemma sh_apart2 : ltac2:(tb__ "0|4|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2SdS1R5R8A2S1S2R8R7A2R6A2A2SaS1S16R7A1R5A2S3R5S16R6A1A2A2ScSaS1S16RaA1M3R6A2S3R6S2G3S4R9G0A2A2A2A2A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;FL;Fua;").
Proof.
  intros ua L lo hi z Hu HL HL0 Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  destruct Hs as [Hs|Hs].
  - pose proof (Z.div_le_mono hi ua 8 ltac:(lia) Hs). lia.
  - pose proof (Z.div_le_mono (ua + L) lo 8 ltac:(lia) Hs) as D. replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by lia. rewrite Z.div_mul in D by lia. lia.
Qed.

Section Foot.
Variables (ua L : Z).
Hypothesis U8 : ua mod 8 = 0.
Hypothesis L8 : L mod 8 = 0.
Hypothesis L0 : 0 < L.
Hypothesis UI : IMG_HI <= ua.
Hypothesis UT : ua + L <= 140737479966720.
Hypothesis UB : ltac2:(tb__ "0|0|
SdS1S2Vua;VL;A2S18A2S1S17Vua;A2A2").

Lemma app_new : ltac2:(tb__ "0|1|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SdS1S2R7R6A2S18A2S1S17R7A2A2SaS1R8R6A2S3R6S2R8R7A2A2A2ScS3bVua;VL;R7A3A1F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hb Hz [X|X]; [lia|].
  pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; lia) ltac:(lia)) as BY.
  assert (E : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by lia. lia. }
  rewrite E in BY. specialize (BY X). lia.
Qed.
Lemma sh_new : ltac2:(tb__ "0|2|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SaS1S16R7A1M1R5A2S3R5S2G1S4S2R6Z7A2Z8A2A2A2A2ScS3bVua;VL;R6A3A1F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hz [X|X].
  - pose proof (sh_run_band lo len z Hlo Hlen Htop Hz) as BY. lia.
  - exact (sh_apart ua L lo len z U8 L8 ltac:(lia) Hlo Hlen Hs Hz X).
Qed.
Lemma sh2_new : ltac2:(tb__ "0|0|
S0S0S0S1Z0R3A2SaS1R4R3A2S1R3Z7fffff800000A2A2SdS1R4Vua;A2S1S2Vua;VL;A2R5A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hlo Hhi Hs Hz [X|X].
  - pose proof (sh_run_band2 lo hi z Hlo Hhi Hz) as BY. lia.
  - exact (sh_apart2 ua L lo hi z U8 L8 ltac:(lia) Hs Hz X).
Qed.

Variable A : AA.
Variable m : bview.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis Hsep : live_sep A.
Hypothesis HI3 : inv3 A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis SSP : ltac2:(tb__ "0|0|
S5aS48S0S0Vua;VL;A4S48S0S0S26S1eVA;A1A1S2S1bZ1000A2A4A2").
Hypothesis SSX : ltac2:(tb__ "0|0|
S1dS54S1dR1S1fVA;A1A3S5aS48S0S0Vua;VL;A4S48S0S0S2cR2A1S2dR2A1A4A2F_;Fch;").

Lemma space_new : ltac2:(tb__ "0|1|
S0SaS1S26S1eVA;A1A1M0R1A2S3R1S2S2G0S6Z2Z25A2A2Z1000A2A2A2ScS3bVua;VL;R2A3A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (app_new (ag_spacebeg (aa_geom A)) (2 ^ 37 + 4096) z); unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia.
Qed.
Lemma space_sh_new : ltac2:(tb__ "0|1|
S0S0S0S1S26S1eVA;A1A1M0R3A2S1R4R3A2S1R4S2S2G0S6Z2Z25A2A2Z1000A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H1 H2 H3 Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (sh2_new lo hi z); lia.
Qed.
Lemma chunk_new : ltac2:(tb__ "0|2|
S51S1dS0SbS4bS1dA1S55S1dS1fVA;A1R3A3S49S1dR2A2A3SdSaS1S2cR3A1M0R2A2S3R2S2G0S2dR3A1A2M1A2A2SaS1S16G0A1R2A2S3R2S16G1A1A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fch;Fi;").
Proof.
  intros i ch z Hi Hz. destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (topG_range (aa_geom A)) as TG. pose proof (SSX ch (nth_error_In _ _ Hi)) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as BI. unfold IMG_HI in BI. destruct D10 as (_ & _ & _ & _ & DB). unfold PG in D8.
  destruct Hz as [Hz|Hz].
  - apply (app_new (sc_map_beg ch) (sc_map_size ch) z); lia.
  - apply (sh2_new (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); lia.
Qed.

Lemma live_foot_new : ltac2:(tb__ "0|1|
S0S0S0S54S4fS0S0A2S48S0S0R3R2A4S29VA;A1A3SdSaS1S7R4S1cR3A1A2R2A2S3R2S2R4R3A2A2A2SaS1S16R4A1M0R2A2S3R2S2G0S4S2R3Z7A2Z8A2A2A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  pose proof HI3 as (_ & LIV3 & _).
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO. lia.
    + pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). fold G SB in S1, S2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
      apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -BLO SSP RZB; lia | exact Hz].
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= b - rz n /\ b + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new i ch z Hi). left. clear -Hz INB. lia.
    + apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -INB SX RZB; lia | exact Hz].
Qed.

Lemma cls_foot_new : ltac2:(tb__ "0|3|
S0SaS1Z1R1A2S1R1Z1eA2A2S0S5eS1eVA;A1M0R3S46S2bS21VA;A1R3S35A4R1A4ScSaS1S2S2S2aG0A1Zd0A2S8Z50M1R4A2A2M2R2A2S3R2S2G2G1A2A2A2A1ScS3bVua;VL;R3A3A1F_;F_;Fz;F_;Fc;").
Proof.
  intros c Hc z Hz NT.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - apply space_new. fold G SB. clear -Hz Hc. lia.
  - apply space_new. fold G SB. clear -Hz Hc M5 M6. nia.
  - apply space_new. fold G SB. clear -Hz Hc M1 M2 M3. nia.
  - apply (space_sh_new (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); fold G SB; [clear -Hc; nia | clear -M1 M2; lia | clear -Hc M1 M2 M3; nia | exact Hz].
  - exfalso. exact (NT Hz).
Qed.

Lemma q_foot_new : ltac2:(tb__ "0|0|
S44Vm;VA;A2S0S47VA;R1A2ScS3bVua;VL;R2A3A1F_;Fz;F_;").
Proof.
  intros (Q1 & _) z Hq.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  pose proof HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *.
    apply space_new. fold G SB. clear -Hz Ex X0 XA R1 R2. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2].
    assert (BLO : SB <= u - rz n /\ u + n <= SB + 2 ^ 37) by (clear -V1 V3 R1 R2 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -BLO GSB ACV; lia | clear -BLO SSP RZ; lia | exact Hz].
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= u - rz n /\ u + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new j ch z Hj). left. clear -Hz INB J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -INB D12 ACV; lia | clear -INB SX RZ; lia | exact Hz].
Qed.
End Foot.

Lemma quarantine_repr_sec_mono : ltac2:(tb__ "0|2|
S13S20S20SbS27S1eR1A1S1eR2A1A3SbS4aS2bA1S21R2A1S21R3A1A3SbS4aS38A1M0S25R3A1S25R4A1A3SbG0S24R4A1S24R5A1A3S1dS54S1dR1S1fR7A1M1A3S54S1dR2G1A3F_;Fch;S44R8R7A2S44R9R7A2F_;F_;F_;F_;F_;F_;FA';FA;Fm;").
Proof.
  intros m A A' EG EC ET EGq HS (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  split; [|split; [exact Q2 | split; [exact Q3 | split; [exact Q4 | split; [exact Q5 | split; [exact Q6 | split; [exact Q7 | split; [exact Q8 | exact Q9]]]]]]]].
  apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold batch_repr. rewrite EG, EC.
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. split; [exact I1|].
  unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, EC.
  destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|]. split; [exact J6|]. split; [exact J7|]. split; [exact J8|].
  split; [exact J9|]. split; [|exact J11].
  intros HP. destruct (J10 HP) as (ch & Hch & X). exists ch. split; [exact (HS ch Hch) | exact X].
Qed.

Lemma nth_error_snoc : forall {T} (l : list T) (x y : T) i, nth_error (l ++ [x]) i = Some y ->
  (nth_error l i = Some y /\ (i < length l)%nat) \/ (i = length l /\ y = x).
Proof.
  intros T l x y i H. destruct (Nat.lt_ge_cases i (length l)) as [Lt|Ge].
  - rewrite nth_error_app1 in H by exact Lt. left. exact (conj H Lt).
  - rewrite nth_error_app2 in H by exact Ge. destruct (i - length l)%nat as [|k] eqn:E; cbn in H.
    + right. split; [lia | congruence].
    + destruct k; discriminate H.
Qed.

Theorem sec_rebuild : ltac2:(tb__ "0|10|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2R7Z1800A2S0S2S23R4A1S8Z8M2R2A2A2S0S15S53S39RdA1A2S13S15S53S39RfA1A2S13S59R11RbR6RdA4S1G2RbA2S1S2S8G2R7A2RcA2S22R13A1A2S1S2R8Z1M3A2S28R14A1A2S10R6S11RfU8M4RfA3A2S10R7S11S2R10G2A2G4RbA3A2S10R8S11S2R11Z10M5A2G4S57R12A1A3A2S10R9S11S2R12Z18M6A2G4RcA3A2S10RaS11RbG4R13A3A2S10RbS11S42G4S19A3A2S10RcS11S2S42G2A2G4S23R11A1A3A2S10RdS11S2S42G5A2G4S23R12A1A3A2S10ReS11S2S42G6A2G4S1aA3A2S10RfS11S2S42Z30A2G4S4S22R1eA1G2A2A3A2S10R10S11S2S42Z38A2G4S2R13G3A2A3A2S10R11S11Zee040U4M7Z0M8A3A2SbS4bS40Q8M9A1MaA1MbR12S7R14G5A2A1S49GaS3fG9G1A2A2A3S10R13S11S7R15ZcA2G7S5R1dS6G1Z20A2McA2A3A2S10R14S11S7R16ZeA2U2S4R1eGcA2A3A2SfGaGaSaSbGbR16S7R18ZfA2A1S49GaR1A2MdA3SbS0S5S41G9R1A2Z4A2G3A3A2Lt;A2S10R16S11S2R1fZ1000A2G4S45A3A2S10R17S11S2R20Z1008A2G4S7R19G5A2A3A2S0SaS1G8R1A2S3R1S4R23G2A2A2A2SbGbR1aS2S16R1cA1MeR2A2A1S49GaS3fG9G8A2A2A3F_;Fg;ScSbS0S5R23G2A2G8A3A1SbGbR1aS2GeS4R24G2A2A2A1S49GaS3fG9S5R24G2A2A2A2A3F_;S0S3cR20R24R1fR1cR23R1A6SfGaGaSbGbR1dR3A1GdA3Lb;A2F_;Fz;S0ScS3cR21R25R20R1dR24R1A6A1SbGbR1dR2A1R1cR2A1A3F_;Fz;S0SaS1S18R1A2S3R1S17A2A2ScSbGbS39R2cS3fG0R2A2A2S4cGaA1MfA3A1ScSbGbS39R2cS3fG0R3A2A2GfA3A1F_;F_;Fa;S43S53S3dR2cR26R27A3R2aR29R28A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Tpw;Tub;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta.
  intros HPD Hblk HROOM HKM C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *.
  set (ub := ua + 6144) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI.
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { intros z Hz. apply (sh_run_band2 ua (ua + L) z); [unfold IMG_HI in UI; clear -UI; lia | clear -UT PL0; lia | rewrite ESHL; exact Hz]. }
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in RUNB, PDB.

  assert (APPN : forall lo len z, 0 <= lo -> 0 <= len -> lo + len <= 140737479966720 -> sepZ (ua, L) (lo, len) ->
                 (lo + len <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> lo <= z < lo + len -> ~ newZ ua L z).
  { intros lo len z H1 H2 H3 H4 H5 Hz. apply (app_new ua L L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) lo len z H1 H2 H3);
      [unfold sepZ in H4; cbn [fst snd] in H4; clear -H4; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact H5 | exact Hz]. }
  assert (NEW_img : forall z, z < IMG_HI -> ~ newZ ua L z).
  { intros z Hz [X|X]; [clear -X UI Hz; lia | pose proof (RUNB z X) as Y; unfold IMG_HI in Hz; clear -Y Hz; lia]. }
  assert (NEW_T : forall z, T <= z < T + 0x1000 -> ~ newZ ua L z).
  { intros z Hz. apply (APPN T 0x1000 z); [clear -G4; lia | clear; lia | clear -G5 ACV; lia | exact ST | clear -TB; lia | exact Hz]. }
  assert (NEW_pab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> ~ newZ ua L z).
  { intros z Hz. unfold kPtrArrayReserve in *. apply (APPN (ag_pab G) (2 ^ 23) z); [unfold IMG_HI in P1; clear -P1; lia | clear; lia | clear -P2 ACV; lia | exact SP | | exact Hz].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -P3. lia. }
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  assert (ZD : forall z, chg_s G ua L pw blk z \/ ~ chg_s G ua L pw blk z) by (intros z; unfold chg_s, zimg, newZ; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> v3 z = vE z).
  { intros z H1 H2 H3. apply VO. intros [X|[X|[X|X]]]; [exact (H2 X) | exact (H3 X) | exact (NEW_img z H1 X) |].
    pose proof (PWZ z X) as Y. clear -Y H1 P1. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> v3 z = vE z).
  { intros z H1 H2 H3 H4. apply VO. intros [X|[X|[X|X]]]; [|exact (H2 X) | exact (H3 X) | exact (H4 X)].
    unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *. clear -X H1. lia. }
  idtac "sr:1".

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, zimg, SEC_INST, ERRNO_A;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y TI; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
      assert (ZZ : (T <= z < T + 288) \/ (ag_ctx G <= z < ag_ctx G + 0x1000) \/ (ag_dtls G <= z < ag_dtls G + 0x1000) \/ (ag_fsb G <= z < ag_fsb G + 97)).
      { repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y; clear -X Y; lia|]). destruct Hc. }
      clear Hc X Y.
      assert (NZ : ~ newZ ua L z).
      { destruct ZZ as [Z1|[Z1|[Z1|Z1]]].
        - apply NEW_T. clear -Z1. lia.
        - apply (APPN (ag_ctx G) 0x1000 z); [clear -G6; lia | clear; lia | clear -G7 ACV; lia | exact SC | clear -CB; lia | exact Z1].
        - apply (APPN (ag_dtls G) 0x1000 z); [clear -G8; lia | clear; lia | clear -G9 ACV; lia | exact SD | clear -DB; lia | exact Z1].
        - rewrite FS_total_val in SF, FB. apply (APPN (ag_fsb G) 11571200 z); [clear -G2; lia | clear; lia | clear -G3 ACV; lia | exact SF | clear -FB; lia | clear -Z1; lia]. }
      assert (NP : ~ (pw <= z < pw + blk)).
      { intros X. pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & PT & PF & PC & PD) & _). fold G T in PT, PF, PC, PD. rewrite FS_total_val in PF.
        unfold kPtrArrayReserve in *. clear -Y ZZ PT PF PC PD. lia. }
      destruct (Z_lt_dec z IMG_HI) as [LO|HI].
      + apply AGI; [exact LO | | clear -ZZ G10 G13 G14; intros X; unfold IMG_HI in *; lia].
        unfold zimg, SEC_INST, ERRNO_A. unfold IMG_HI in LO. clear -ZZ LO TI CI DI G2. intros X. lia.
      + apply AGH; [clear -HI; lia | | exact NZ | exact NP]. clear -ZZ G10 G13 G14. intros X. lia. }
  idtac "sr:2".

  assert (FZ : forall z, chg_s G ua L pw blk z -> fs_footb G z = false).
  { intros z [X|[X|[X|X]]].
    - apply (fs_footb_img G z HG). unfold zimg, SEC_INST, ERRNO_A in X. clear -X. lia.
    - apply (fs_footb_T G z HG). fold T. clear -X. lia.
    - rewrite FS_total_val in SF, FB. unfold sepZ in SF. cbn [fst snd] in SF.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X].
        * pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
          unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY X PDB. lia.
        * destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          apply (sh_apart2 ua L (ag_fsb G + 36864) (ag_fsb G + 11571200) z U8 L8 ltac:(clear -PL0; lia) ltac:(clear -SF; lia) ltac:(clear -Lz R; lia) X).
    - pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + clear -Y PF. lia.
      + clear -Y PF. lia.
      + pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
        destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
        destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
        specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
        clear -BY Y P3. unfold kPtrArrayReserve in *. lia. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (secA A ua nv)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. rewrite (FZ z Zz) in Hz. discriminate Hz. }
    exact HF. }
  idtac "sr:3".

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ chg_s G ua L pw blk z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> m3 z = mE z).
  { intros z H1 H2 H3. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGI z H1 H2 H3). }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> m3 z = mE z).
  { intros z H1 H2 H3 H4. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGH z H1 H2 H3 H4). }
  assert (CHm : forall z, chg_s G ua L pw blk z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (FZ z Hz). }
  assert (PRm : forall z, chg_s G ua L pw blk z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite (CHm z Hz). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (CELL3 : forall a w v, (forall k, (k < w)%nat -> chg_s G ua L pw blk (a + Z.of_nat k)) -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hk Hc k Hkw. cbn [c_addr c_w c_val] in *. rewrite (CHm _ (Hk k Hkw)). exact (Hc k Hkw). }

  assert (SSP' : sepZ (ua, L) (ag_spacebeg (aa_geom A), kSpaceSize + 4096)) by exact SS.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG Hsep HI3 HPR HSR SSP' SX) as LFN.
  pose proof (cls_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR SSP') as CFN.
  pose proof (q_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR HSR SSP' SX HQR) as QFN.
  pose proof (chunk_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HSR SX) as CHN.
  assert (NPWpab : forall z, ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> ~ (pw <= z < pw + blk)) by (intros z H X; exact (H (PWZ z X))).

  assert (NB : ub + nv + 2048 <= ua + L /\ nv / 8 <= L / 8 - 1024 /\ rz nv = 2048 /\ is_primary nv = false).
  { split; [|split; [|split; [apply rz_large; clear -Hnv; lia | apply not_primary_large; clear -Hnv; lia]]].
    - unfold ub, L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2. clear -R1 R2. lia.
    - unfold L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2.
      pose proof (Z.div_le_mono (nv + 8192) (round_up (round_up nv 8 + 4096) 4096 + 4096) 8 ltac:(clear; lia) ltac:(clear -R1 R2; lia)) as D.
      replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). clear -D. lia. }
  destruct NB as (NB1 & NB2 & ERZ & ENP).
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  assert (INnew : forall z, ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; left; exact Hz).
  assert (INrun : forall z, Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; right; exact Hz).
  idtac "sr:4".

  assert (HLS : live_sep (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. cbn [aa_geom secA]. fold G. destruct Hin as [E|Hin]; [|exact (Hsep b n Hin)].
    injection E as <- <-. fold ub. unfold sepZ in SF, ST, SC, SD. cbn [fst snd] in SF, ST, SC, SD. fold T in ST |- *.
    split; [clear -Hnv; lia|]. split; [unfold ub; clear -UI; lia|]. split; [clear -NB1 PDT; lia|].
    split; [unfold ub; clear -SF NB1; lia|]. split; [unfold ub; clear -ST NB1; lia|]. split; [unfold ub; clear -SC NB1; lia|]. split; [unfold ub; clear -SD NB1; lia|].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. unfold ub. clear -PDB NB1. lia. }
  assert (HLB : live_block_repr m3 (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin].
    - injection E as <- <-. fold ub.
      assert (CU : forall z, ua <= z < ua + L -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INnew; exact Hz).
      assert (CS : forall z, Sh ua <= z < Sh ua + L / 8 -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INrun; exact Hz).
      pose proof (Z.div_pos nv 8 ltac:(clear -Hnv; lia) ltac:(clear; lia)) as DP.
      split; [rewrite CU by (unfold ub; clear -SMB; lia); exact VH2|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VHN]|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VH0]|].
      split; [split|split].
      + intros g Hg. rewrite CS by (rewrite ESHub; clear -Hg NB2; lia). exact (VZ g Hg).
      + intros Hm. rewrite CS by (rewrite ESHub; clear -DP NB2; lia). exact (VP Hm).
      + right. rewrite ERZ. replace (ub - 2048) with (ua + 4096) by (unfold ub; clear; lia). replace (ua + 4096 + 8) with (ua + 4104) by (clear; lia).
        split; apply CELL3; first [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | assumption].
      + destruct VH1 as (t & Ht & Hm4). exists t. split; [rewrite CU by (unfold ub; clear -SMB; lia); exact Ht | exact Hm4].
    - destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
      assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
      { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & Y & _). fold G T in Y.
        pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Z1. fold G in Z1.
        apply AGmH; [exact X | clear -Y; lia | exact (LFN b n z Hin Hz) | exact (NPWpab z Z1)]. }
      pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
      pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
      split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
      split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [split|split].
      + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
      + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
        replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
        clear -DP. lia.
      + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
      + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  idtac "sr:5".

  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live (secA A ua nv)) z).
  { intros z (b & n & Hbn & Hz). exists b, n. split; [cbn [aa_live secA]; right; exact Hbn | exact Hz]. }
  assert (HPR' : primary_repr m3 (secA A ua nv)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (secA A ua nv)) with G. change (aa_cls (secA A ua nv)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (secA A ua nv) cl); [exact Hc | reflexivity | | reflexivity | | exact LIVM | | exact (P4' cl Hc)].
    - unfold secA. rewrite (live_ids_cons G A (ua + 6144) nv cl). rewrite ENP. reflexivity.
    - intros b n Hin HP _. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin]; [|exact Hin]. injection E as <- <-. rewrite ENP in HP. discriminate HP.
    - intros z Hz.
      pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.
      assert (TAIL : ~ (T + 0xd0 + 80 * cl <= z < T + 0xd0 + 80 * cl + 80) -> m3 z = mE z).
      { intros NTe. pose proof (CFN cl Hc z Hz NTe) as NZ.
        assert (ZH : IMG_HI <= z /\ ~ (T + 2768 <= z < T + 3168)).
        { pose proof (P4' cl Hc) as PCX. fold G in PCX. unfold class_repr in PCX.
          destruct PCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
          unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz. destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]]; [| | | |exfalso; exact (NTe Hz)].
          all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
               destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _);
               destruct HI3 as ((T3 & _) & _); fold G T in T3; rewrite kSpaceSize_val in T3;
               unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
          - clear -Hz Hc GS1 T3. lia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M5 M6. nia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M1 M2 M3. nia.
          - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2.
            unfold kUserMapSize in *.
            pose proof (Z.div_le_mono (ag_spacebeg G + cl * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) cl cs_empty)) 140737479966720 8 ltac:(clear; lia) ltac:(clear -Hc M1 M2 M3 GS2 ACV; nia)) as D1.
            change (140737479966720 / 8) with 17592184995840 in D1. clear -Hz D1 D2 TB. lia. }
        apply AGmH; [exact (proj1 ZH) | exact (proj2 ZH) | exact NZ | exact (NPWpab z Y)]. }
      destruct (Z_le_dec (T + 0xd0 + 80 * cl) z) as [GE|LT]; [destruct (Z_lt_dec z (T + 0xd0 + 80 * cl + 80)) as [LT2|GE2]|].
      +
        assert (ZT : T <= z < T + 0x1000) by (clear -GE LT2 Hc; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -GE LT2 Hc; lia].
        * apply AGmH; [clear -HI; lia | clear -GE LT2 Hc; lia | exact (NEW_T z ZT) | exact (NPWpab z Y)].
      + apply TAIL. clear -GE2. lia.
      + apply TAIL. clear -LT. lia. }
  idtac "sr:6".

  assert (AGpabOld : forall z, ag_pab G <= z < pw -> m3 z = mE z).
  { intros z Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN.
    assert (ZP : ag_pab G <= z < ag_pab G + kPtrArrayReserve) by (unfold pw in Hz; clear -Hz HROOM P4 NN Hblk; lia).
    destruct HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
    apply AGmH; [clear -ZP P1; lia | clear -ZP PT; unfold kPtrArrayReserve in *; lia | exact (NEW_pab z ZP) | clear -Hz; lia]. }
  assert (HSR' : secondary_repr m3 (secA A ua nv)).
  { pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed aa_live secA]. fold G.
    assert (ELEN : Z.of_nat (length (aa_sec A ++ [mkSC ua L (secneeded nv)])) = idx + 1) by (rewrite length_app; cbn [length]; unfold idx; clear; lia).
    fold L. rewrite ELEN.
    split.
    { intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14). fold G in C5, D10, D12.
        assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; clear -D8 D9; lia).
        assert (AGC : forall z, (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> m3 z = mE z).
        { intros z Hz. pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as BI.
          destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & STh & SPb & _). fold G T in STh, SPb.
          pose proof D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
          apply AGmH; [| | exact (CHN i ch z Hi Hz) |].
          - destruct Hz as [Hz|Hz]; [clear -Hz BI; lia|]. unfold Sh, SHADOW_OFF, IMG_HI in *. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)). clear -Hz H. lia.
          - destruct Hz as [Hz|Hz]; [clear -Hz STh; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY TB. lia.
          - apply NPWpab. destruct Hz as [Hz|Hz]; [clear -Hz SPb; unfold kPtrArrayReserve in *; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            clear -BY P3. unfold kPtrArrayReserve in *. lia. }
        assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok mE (mkACell (sc_map_beg ch + off) w v) -> cell_ok m3 (mkACell (sc_map_beg ch + off) w v)).
        { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGC. left. unfold PG in D8. clear -Ho Hw Hk D8 D9. lia. }
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C1]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C2]|].
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C3]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C4]|].
        split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGpabOld; unfold pw, idx; cbn in Hk; clear -Hk Lt; lia|].
        split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
        split; [|eapply present_agree; [|exact D14]; intros z Hz; apply AGC; right; exact Hz].
        eapply present_but_mono; [exact LIVM | | exact D13]. intros z Hz _ Hm. rewrite (AGC z (or_introl Hz)). exact Hm.
      - cbn [sc_map_beg sc_map_size sc_size]. replace (Z.of_nat (length (aa_sec A))) with idx by reflexivity.
        split; [replace (ua + 0) with ua by (clear; lia); apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C0]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C8]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C16]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C24]|].
        split; [apply CELL3; [intros k Hk; right; right; right; fold pw; cbn in Hk; clear -Hk Hblk; lia | exact CPW]|].
        split; [unfold PG; exact PAL|]. split; [unfold PG; exact SMM|].
        split; [unfold L, secmapsize, PG; pose proof (round_up_ge (secneeded nv) 4096 ltac:(clear; lia)) as R; clear -R; lia|].
        split; [unfold secneeded; pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R; clear -R Hnv; lia|].
        split; [unfold dyn_in; unfold IMG_HI in UI; unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; clear -UI PL0 PDT PDB; lia|].
        split; [reflexivity|]. split; [exact PDT|].
        split; [intros z Hz _; apply PRm; apply INnew; exact Hz|].
        intros z Hz. apply PRm. apply INrun. rewrite <- ESHL. exact Hz. }
    split.
    { intros z Hz. destruct (ZD z) as [Hc|Hn]; [exact (PRm z Hc)|]. rewrite (AGm z Hn). apply SPT. fold G idx. clear -Hz. lia. }
    split; [clear -HROOM Hblk P4; lia|]. split; [exact S3|]. split; [exact S45|].
    assert (CZI : forall a w v, SEC_INST <= a -> a + Z.of_nat w <= 0xee044 -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
    { intros a w v H1 H2. apply CELL3. intros k Hk. left. unfold zimg. clear -H1 H2 Hk. lia. }
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI0]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI8]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI16]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI24]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C48]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C56]|].
    split; [apply PRESX; exact I7|].
    split; [|apply PRESX; exact I9].
    apply CZI; [unfold SEC_INST; clear; lia | cbn; clear; lia | exact CMU]. }
  idtac "sr:7".
  assert (HQR' : quarantine_repr m3 (secA A ua nv)).
  { apply (quarantine_repr_sec_mono m3 A (secA A ua nv)); try reflexivity.
    - intros ch Hch. cbn [aa_sec secA]. apply in_or_app. left. exact Hch.
    - apply (quarantine_repr_agreeQ mE m3 A A); try reflexivity.
      + exact (q_items_rz A).
      + intros z Hz. pose proof HI3 as (_ & _ & _ & Q3 & _). destruct (Q3 z Hz) as [QT _]. fold G T in QT.
        pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
        apply AGmH; [exact QH | clear -QT; lia | exact (QFN z Hz) | exact (NPWpab z Y)].
      + intros z Hz. fold G T in Hz. assert (ZT : T <= z < T + 0x1000) by (clear -Hz; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -Hz; lia].
        * pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
          apply AGmH; [clear -HI; lia | clear -Hz; lia | exact (NEW_T z ZT) | apply NPWpab; clear -ZT PT; unfold kPtrArrayReserve in *; lia].
      + intros z Hz. apply AGmI; unfold QG, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
      + exact HQR. }
  assert (HIA' : ia_inv m3 (secA A ua nv)).
  { apply (ia_inv_agreeN mE m3 A (secA A ua nv)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia]. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. assert (ZT : T <= T + 3168 < T + 0x1000) by (clear; lia).
      destruct (Z_lt_dec (T + 3168) IMG_HI) as [LO|HI].
      + rewrite AGmI; [exact X | exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -LO TI; intros Z1; lia | clear; lia].
      + pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
        rewrite AGmH; [exact X | clear -HI; lia | clear; lia | exact (NEW_T _ ZT) | apply NPWpab; clear -PT; unfold kPtrArrayReserve in *; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia.
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia. }
  idtac "sr:8".
  assert (HDEP : depot_wf m3 (secA A ua nv)).
  { unfold depot_wf in HDW |- *. change (aa_depot (secA A ua nv)) with (aa_depot A).
    pose proof HI3 as (_ & _ & _ & _ & DEP3 & _).
    eapply depot_mem_frame; [|exact HDW]. intros a Ha.
    assert (BLKZ : forall bb LL, In (bb, LL) (dblocks (aa_depot A)) -> 0xf000 < LL -> bb <= a < bb + LL -> m3 a = mE a).
    { intros bb LL Hb HLL Hab. destruct (DEP3 (bb, LL) Hb) as (DY & STb & _ & _ & _ & _ & SPb & _). cbn [fst snd] in DY.
      unfold sepZ in STb, SPb. cbn [fst snd] in STb, SPb. fold G T in STb, SPb.
      pose proof (dyn_in_big _ _ _ DY HLL) as BB. pose proof DY as (_ & _ & DT & _ & DBb). fold G in DT.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DBb.
      pose proof (SDB (bb, LL) Hb) as SN.
      apply AGmH; [clear -BB Hab; lia | clear -STb Hab; lia | | apply NPWpab; clear -SPb Hab; unfold kPtrArrayReserve in *; lia].
      apply (APPN bb LL a); [unfold IMG_HI in BB; clear -BB; lia | clear -HLL; lia | clear -DT ACV; lia | apply sepZ_sym; exact SN | exact DBb | exact Hab]. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI; [clear -Hs; lia | clear -Hs; lia | clear -Hs TI; lia].
    - apply (BLKZ bb NBSZ); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold NBSZ; clear; lia | exact Hab].
    - apply (BLKZ bb FBSZ); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold FBSZ; clear; lia | exact Hab]. }
  idtac "sr:9".

  assert (HMD : model_inv segsA (secA A ua nv) tp md).
  { unfold model_inv in HM |- *. cbn [aa_geom aa_V aa_Km aa_Kf secA]. fold G.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    split.
    { unfold vm_geom in V1 |- *. cbn [aa_sec aa_geom secA]. fold G. fold G in V1.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [|exact N9].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (N8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact PM. }
    split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [exact V7|].
    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec secA] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8' & L9 & L10).
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8'|].
    split; [|exact L10]. rewrite length_app. cbn [length]. fold idx in HKM. unfold idx in HKM. clear -HKM. lia. }
  idtac "sr:10".
  assert (HI3' : inv3 (secA A ua nv)).
  { pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3 & CNT3 & SML3 & QCI3).
    unfold inv3. cbn [aa_geom aa_live aa_sec aa_cls aa_depot secA]. fold G.
    split; [exact SG3|].
    split.
    { intros b n Hin. destruct Hin as [E|Hin].
      - injection E as <- <-. right. exists (mkSC ua L (secneeded nv)). split; [apply in_or_app; right; left; reflexivity|].
        cbn [sc_map_beg sc_size]. split; [unfold PG; clear; lia | reflexivity].
      - destruct (LIV3 b n Hin) as [P|(ch & Hch & X)]; [left; exact P | right; exists ch; split; [apply in_or_app; left; exact Hch | exact X]]. }
    split.
    { unfold sepZ in SS, ST, SP, SF, SC, SD. cbn [fst snd] in SS, ST, SP, SF, SC, SD. fold T in ST |- *.
      intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). fold G T in X1, X2, X3, X4, X6, X7.
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[-> ->]]; [exact (X5 j ch' Hj Hij)|].
        cbn [sc_map_beg sc_map_size]. pose proof (SX ch (nth_error_In _ _ Hi)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. clear -Y. lia.
      - cbn [sc_map_beg sc_map_size].
        split; [clear -SS; lia|]. split; [clear -ST; lia|]. split; [clear -SP; lia|]. split; [clear -SF; lia|]. split; [|split; [clear -SC; lia | clear -SD; lia]].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[E _]]; [|exfalso; exact (Hij (eq_sym E))].
        pose proof (SX ch' (nth_error_In _ _ Hj)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. exact Y. }
    split; [exact Q3|].
    split.
    { intros bn Hbn. destruct (DEP3 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
      split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (D8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact (SDB bn Hbn). }
    split.
    {
      cbn [List.filter snd]. rewrite ENP. cbn [negb List.map fst app].
      constructor; [|exact ND3]. intros Hin. apply (proj1 (list_elem_of_In _ _)) in Hin.
      assert (OLDU : exists ch, In ch (aa_sec A) /\ ua + 6144 = sc_map_beg ch + PG + 2048).
      { apply in_app_or in Hin as [Hin|Hin].
        - apply in_map_iff in Hin as ([b n] & Eb & Hf). cbn [fst] in Eb. subst b. apply filter_In in Hf as [Hl Hp]. cbn [snd] in Hp.
          destruct (LIV3 _ _ Hl) as [P|(ch & Hch & X & _)]; [rewrite P in Hp; discriminate Hp | exists ch; exact (conj Hch X)].
        - apply in_map_iff in Hin as ([u n] & Eu & Hf). cbn [fst] in Eu. subst u. apply filter_In in Hf as [Hq Hp]. cbn [snd] in Hp.
          unfold qitems in Hq. apply in_flat_map in Hq as (qb & Hqb & Hit).
          destruct HQR as (QB & _). pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & _ & _ & _ & _ & _ & B6 & _).
          destruct (In_nth_error _ _ Hit) as [k Hk]. destruct (B6 k _ Hk) as [_ IT]. destruct IT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & JS & _). cbn [fst snd] in JS.
          destruct (is_primary n) eqn:EPn; [discriminate Hp|]. destruct (JS eq_refl) as (ch & Hch & X & _). exists ch. exact (conj Hch X). }
      destruct OLDU as (ch & Hch & Eu). pose proof (SX ch Hch) as Y. unfold sepZ in Y. cbn [fst snd] in Y.
      destruct (In_nth_error _ _ Hch) as [i Hi]. destruct HSR as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & _).
      unfold PG in Eu, D8. clear -Y Eu D8 D9 SMB. lia. }
    rewrite length_app. cbn [length].
    assert (ELL : large_live (secA A ua nv) = large_live A + 1).
    { rewrite (large_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
      destruct (Z.leb_spec 64513 nv) as [_|X]; [reflexivity | exfalso; clear -X Hnv; lia]. }
    split; [rewrite ELL; change (qlarge (secA A ua nv)) with (qlarge A); clear -CNT3; lia|].
    split; [|exact QCI3].

    rewrite (small_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
    destruct (Z.leb_spec 64513 nv) as [_|X]; [clear -SML3; lia | exfalso; clear -X Hnv; lia]. }
  idtac "sr:11".

  unfold AInvA. change (aa_geom (secA A ua nv)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. change (aa_geom (secA A ua nv)) with G.
    split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split; [exact HDEP|]. split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split; [exact HMD|]. split; [exact HI3'|].
  eapply bandtp_mono_rm; [|exact HB]. exact DEFB.
Qed.

Section Kept.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5dR2A2SeF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5bR2A2SeF_;F_;Fa;").

Theorem sec_kept : ltac2:(tb__ "0|7|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2S23R3A1S8Z8M2R1A2A2S0S59ReR8R3RaA4S1G2R8A2S1S2S8G2R4A2R9A2S22R10A1A2S0SaS1Z0R1A2S3R1S6G1Z40A2A2A2ScS5fR9R2A2A1ScS3cRaReR9R7RdR3A6A1ScS12S5bR4A2A1SbS4bS40Q8A1M3A1M4S39R14S3fG0R5A2M5A2S39R15G5A2A3F_;F_;F_;F_;Fa;S0SaS1S18R1A2S3R1S17A2A2ScSbG4S39R13S3fG0R2A2A2S4cG3A1M6A3A1ScSbG4S39R13S3fG0R3A2A2G6A3A1F_;F_;Fa;S5cVCST;VXGL;R13S3dR13RdReA3S39R12A1S39R11A1A6F_;F_;F_;F_;F_;Tpw;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta. intros HPD Hblk HROOM RMO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB, DEFB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.

  assert (NOC : forall a, client_addrA CST A a -> ~ errno_addrA a ->
                  ~ chg_s G ua L pw blk a /\ ~ in_rangesZ IMG_S a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl NE.
    pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold rt_zone in NR. fold G T in NR.
    assert (IMGS : forall x, in_rangesZ IMG_S x -> 0x10000 <= x < IMG_HI).
    { intros x (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, IMG_HI in *. cbn [In] in Hbn.
      destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -S Y ACV; lia | clear -S PDT; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X S ACV. lia.
      + clear -X S G5. lia.
      + clear -X S PDT. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) UT) as D.
        pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by (clear -DL DU; lia). rewrite Z.div_mul in D by (clear; lia). cbn in D. clear -X D S ACV. lia.
      + pose proof (PWZ a X) as Y. clear -Y S P2. lia.
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; clear -X1 Y; lia | intros X; apply NZ; left; exact X]].
      intros [X|[X|[X|X]]]; [unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; clear -X X1; lia | clear -X X2; lia | exact (NZ X) | exact (X3 (PWZ a X))].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -Hx M Y; lia | clear -Hx M SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X Hx M. lia.
      + clear -X Hx M G10. lia.
      + clear -X Hx M SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY Hx M FB. lia.
      + pose proof (PWZ a X) as Y. clear -Y Hx M PF. lia.
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|split; [exact (HCSTS a C) | unfold IMG_HI in UI; clear -X0 UI; lia]].
      intros [X|[X|[[X|X]|X]]].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold zimg, SEC_INST, ERRNO_A in *.
        destruct X as [Hz|[Hz|[Hz|Hz]]].
        * exists 0xeddd8, (0xee044 - 0xeddd8). split; [left; reflexivity | clear -Hz; lia].
        * exists 0xee048, (0xee070 - 0xee048). split; [right; left; reflexivity | clear -Hz; lia].
        * exists 0x173660, 2. split; [right; right; right; left; reflexivity | clear -Hz; lia].
        * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
      + apply NR. right. left. clear -X. lia.
      + unfold IMG_HI in UI. clear -X X0 UI. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_pos ua 8 ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear; lia)) as D. clear -X X0 D. lia.
      + pose proof (PWZ a X) as Y. unfold IMG_HI in P1. clear -Y X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS _ X) as Y; unfold IMG_HI in Y; clear -M Ea Y; lia | clear -M Ea SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X M Ea. lia.
      + clear -X M Ea G10. lia.
      + clear -X M Ea SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY M Ea FB. lia.
      + pose proof (PWZ _ X) as Y. clear -Y M Ea PF. lia. }
  idtac "sk:1".
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (NOS : forall a, client_shadowA CST XGL A a ->
                  SHADOW_OFF <= a < HIGH_SHADOW_END /\ ~ chg_s G ua L pw blk a).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. split; [exact B0|].
    unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    intros [X|[X|[[X|X]|X]]].
    - unfold zimg, SEC_INST, ERRNO_A in X. clear -X B0. lia.
    - clear -X B0 TB G4. lia.
    - clear -X B0 PDB. lia.
    -
      assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
      { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
        pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
      destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
      + destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
        assert (NEy : ~ errno_addrA y) by (unfold errno_addrA, ERRNO_A; unfold IMG_HI in UI; clear -YIN UI; lia).
        exact (proj2 (proj2 (NOC y Cy NEy)) YIN).
      + destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia.
    - pose proof (PWZ a X) as Y. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve in *. clear -Y B0 P3. lia. }
  idtac "sk:2".
  split.
  - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|(C1 & _ & _)].
    + destruct (NOC a C1 NE) as (N1 & N2 & _).
      apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep C1) | exact N1 | exact N2].
    + destruct (NOS a C1) as (B0 & N1). unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
      apply RMO; [exact Ba | | exact N1 |].
      * unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
        -- destruct R1 as [R1 _]. clear -R1 B0. lia.
        -- fold G T in R1. clear -R1 B0 TB. lia.
        -- fold G in R1. clear -R1 B0 CB. lia.
        -- fold G in R1. clear -R1 B0 DB. lia.
        -- fold G in R1. clear -R1 B0 FB. lia.
        -- pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
      * intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST in *. cbn [In] in Hbn.
        destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
  - intros x j Hx Hj Hdef.
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
      - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3 Bx Hj. lia.
Qed.
End Kept.
End CRebuildS.

