(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv DepotCall.
From Stdlib Require FunctionalExtensionality Permutation.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.

(* [comment removed for export] *)
Module SpineCallocSecI.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecI"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_null"; "JLc_null"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition st0 : ustop := UStopLe.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S2dScScS2ScS25S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S46S0S1Z2Z8A4R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S2dScScS2ScS26S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S23S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S21S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S20S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S22S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S24S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_8 : ltac2:(tb__ "0|1|
S2dS18SaA1M0G0S2G0S3bS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S2dScScS2ScS38S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3aS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3cS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S2dS41S41S2S41S39S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma SWa_0 : ltac2:(tb__ "0|0|
S2S19S11S25S0S1Z2A3A1S1bA3"). Proof. memo_rw (SSa_S W0 st0 2) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SDa_0 : ltac2:(tb__ "0|7|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S46S0S1Z2M4Z8M5A4A1S25S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8S62G5A1S10S2bA1A4M6S16G0G6S17G0A1A3A3S17S9A1A4A2A3"). Proof. memo_rw (E_s1 W0 st0 2 8) memo_1. memo_rw (SSa_S W0 st0 2) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SWb_0 : ltac2:(tb__ "0|0|
S2S19S11S26S0S1Z2A3A1S1bA3"). Proof. memo_rw (SSb_S W0 st0 2) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SFB : ltac2:(tb__ "0|0|
S2S19S7bS9S12S5fA1S29A3S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertS1_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S4S23S0S1Z2M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WC1_0 : ltac2:(tb__ "0|0|
S2S19S11S5S20S0S1Z2A3A1A1S1bA3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S21S0S1Z2M4A3A1S5S20S0S1G4A3A1A2S1eG3S1dG1G2S16G0S1dS8S8S7aS10S27A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (ES1 W0 st0 2) memo_4. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|1|
S2S2fSdS5S20S0S1Z2M0A3A1A1SdS5S21S0S1G0A3A1A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IC1_0 : ltac2:(tb__ "0|0|
S2S1fS52A1S71S35S15S5S20S0S1Z2A3A1A1A2S1eS52S53A2A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R17_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1Z11A2SbZdeA1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R11_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZbA2S10S27A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R10_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZaA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R12_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZcA2SbZ3A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R13_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZdA2SbZ22A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R14_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZeA2SbZffffffffffffffffA1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R15_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZfA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S2S2fSdS5S20S0S1Z2A3A1A1S5fA3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ltac2:(tb__ "0|1|
S2S18S1aS8S8A2M0A1S6S20S0S1Z2A3A1S17G0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|1|
S2S18S1aS1aS8S8A2S8A2M0A1S3fSaG0S6aS14S5S20S0S1Z2A3A1A1A4S3fSaG0S6aS1cSaS1cSaS16SaS49S1cSaS69S0A1S65A3A3S61A3S2aA3A4A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|1|
S7cS9S1cS9S1cS9S1cS9S1cS9S68S0S1A2S67S66A1A3S60A3S48A3S47Z2M0Z8A2A3S13S5S20S0S1G0A3A1A1A3").
Proof. apply inclb_incl. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertSf_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ5e768S17S2eA1A3S34S16S4S22S0S1Z2M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z2A3S1cSaS61S3fS76SaS75S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 2) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z2A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S3aS0S1Z2M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS77A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 2) memo_10. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z2M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. memo_rw (stKn W0 st0 2) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z2M0A3S5cS0S1A2S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 2) memo_11. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S74S39S0S1Z2A3A1S1bA3"). Proof. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S23S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 2) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S30S31S23S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S22S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 2) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e768S17S2eA1A3S34S16S30S31S22S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section SEC0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS78R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS79R2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Hypothesis law_res : ltac2:(tb__ "0|1|
S4aSfS18S4cQ40A1M0A1S4dVAInv;R4R3R2R1A4S2S18S1aG0G0A2A1S50S4eR2A1A1S6eS35A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem calloc_sec_0 : ltac2:(tb__ "0|5|
S57OF_;S4aS63S4cQ40A1M0S44F_;SfS18G0A1S5aVsegs;S58R2R1S5eVCST;VXGL;S0S1R5R4A6A5S55S64R5A1S45Vsegs;R8S43R6A1A3S72Vsegs;R9S43R7A1A3SfS18S4fA1M1S37S4dG0S73Vsegs;R5RaS20S0S1Z2M2A3M3S1dG1S6cR4S6dR3R2A2A4A5S4bS0S1RfReRcR6RbR5R3A9S6fS36R5U0A2S36R5U3A2R4S36R5U1M4A2R3A5RfR4S59R8SdS5G3A1A1R4A3RdR7S51S70S4eR5A1S36R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SfG0S54Vsegs;RdS42Vsegs;RaR1A1S28S0S1G2A3S59R2S2cS0S1G2A3R1A3R8A5R7A4Fa;FrhoX;SfS54Vsegs;RdS42Vsegs;S4bS0S1RcRbR9A5S46S0S1G2Z8A4R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;TQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HKc Hokl Hokpl HJo HOK rhoE.
  refine (sec_spine 0%nat st0 2 CST XGL HCST HXGL HCSTM HCSTS law_res SWa_0 SDa_0 SWb_0 SFB CertS1_0 WC1_0 DC1_0 NXC1_0 IC1_0 R17_0 R11_0 R10_0 R12_0 R13_0 R14_0 R15_0
            NX1_0 XC1_0 SK1_0 FC1_0 CertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 ok A Kc Jo rho tp _ _ (stopJ_stable_le _) HKc Hokl Hokpl _ HJo HOK rhoE).
  - hw_discharge.
  - unfold PFc. left. reflexivity.
Qed.

Theorem ecalloc_tail_null_0 : ltac2:(tb__ "0|1|
S4aS63SfS18S4cQ40A1A1S64R3A1SfS56Vsegs;S42Vsegs;S4bS0S1R6R5R4A5S22S0S1Z2A3R1R3A5S5aVsegs;S58R4R3S16S1aS4S5bA2M0S1dS4S5bS5cS0S1A2S5dVCST;VXGL;R6R5A4A4S17G0A1A3A5A3FrhoX;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoX.
  refine (esec_tail_null 0%nat st0 2 CST XGL HCST HXGL HCSTM HCSTS NXS1f_0 ECertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 A Kc rho tp _ (stopJ_stable_le _) HKc _ rhoX).
  left. reflexivity.
Qed.
End SEC0.
End SpineCallocSecI.

(* [comment removed for export] *)
Module SpineCallocSecIW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.SpineCallocSecIW1"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_null"; "JLc_null"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 1.
Definition st0 : ustop := UStopLeOrPc.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S2dScScS2ScS25S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S46S0S1Z3Z8A4R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S2dScScS2ScS26S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S23S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S21S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S20S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S22S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S24S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_8 : ltac2:(tb__ "0|1|
S2dS18SaA1M0G0S2G0S3bS0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S2dScScS2ScS38S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3aS0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3cS0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S2dS41S41S2S41S39S0S1Z3A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma SWa_0 : ltac2:(tb__ "0|0|
S2S19S11S25S0S1Z3A3A1S1bA3"). Proof. memo_rw (SSa_S W0 st0 3) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SDa_0 : ltac2:(tb__ "0|7|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S46S0S1Z3M4Z8M5A4A1S25S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8S62G5A1S10S2bA1A4M6S16G0G6S17G0A1A3A3S17S9A1A4A2A3"). Proof. memo_rw (E_s1 W0 st0 3 8) memo_1. memo_rw (SSa_S W0 st0 3) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SWb_0 : ltac2:(tb__ "0|0|
S2S19S11S26S0S1Z3A3A1S1bA3"). Proof. memo_rw (SSb_S W0 st0 3) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SFB : ltac2:(tb__ "0|0|
S2S19S7bS9S12S5fA1S29A3S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertS1_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S4S23S0S1Z3M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 3) memo_3. memo_rw (ES1 W0 st0 3) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WC1_0 : ltac2:(tb__ "0|0|
S2S19S11S5S20S0S1Z3A3A1A1S1bA3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S21S0S1Z3M4A3A1S5S20S0S1G4A3A1A2S1eG3S1dG1G2S16G0S1dS8S8S7aS10S27A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (ES1 W0 st0 3) memo_4. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|1|
S2S2fSdS5S20S0S1Z3M0A3A1A1SdS5S21S0S1G0A3A1A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. memo_rw (ES1 W0 st0 3) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IC1_0 : ltac2:(tb__ "0|0|
S2S1fS52A1S71S35S15S5S20S0S1Z3A3A1A1A2S1eS52S53A2A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R17_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1Z11A2SbZdeA1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R11_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1ZbA2S10S27A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R10_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1ZaA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R12_0 : ltac2:(tb__ "0|1|
S2S8SeS5S20S0S1Z3M0A3A1ZcA2SbG0A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R13_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1ZdA2SbZ22A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R14_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1ZeA2SbZffffffffffffffffA1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R15_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z3A3A1ZfA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S2S2fSdS5S20S0S1Z3A3A1A1S5fA3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ltac2:(tb__ "0|1|
S2S18S1aS8S8A2M0A1S6S20S0S1Z3A3A1S17G0A1A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|1|
S2S18S1aS1aS8S8A2S8A2M0A1S3fSaG0S6aS14S5S20S0S1Z3A3A1A1A4S3fSaG0S6aS1cSaS1cSaS16SaS49S1cSaS69S0A1S65A3A3S61A3S2aA3A4A3"). Proof. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|1|
S7cS9S1cS9S1cS9S1cS9S1cS9S68S0S1A2S67S66A1A3S60A3S48A3S47Z3M0Z8A2A3S13S5S20S0S1G0A3A1A1A3").
Proof. apply inclb_incl. memo_rw (CS1 W0 st0 3) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertSf_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ5e768S17S2eA1A3S34S16S4S22S0S1Z3M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 3) memo_6. memo_rw (ESn W0 st0 3) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z3A3S1cSaS61S3fS76SaS75S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 3) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z3A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 3) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S3aS0S1Z3M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS77A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 3) memo_10. memo_rw (stRn_S W0 st0 3) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z3M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 3) memo_9. memo_rw (stKn W0 st0 3) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z3M0A3S5cS0S1A2S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 3) memo_11. memo_rw (s_n W0 st0 3) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S74S39S0S1Z3A3A1S1bA3"). Proof. memo_rw (s_n W0 st0 3) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S23S0S1Z3A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 3) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S30S31S23S0S1Z3M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 3) memo_3. memo_rw (ES1 W0 st0 3) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S22S0S1Z3A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 3) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e768S17S2eA1A3S34S16S30S31S22S0S1Z3M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 3) memo_6. memo_rw (ESn W0 st0 3) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section SEC0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS78R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS79R2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Hypothesis law_res : ltac2:(tb__ "0|1|
S4aSfS18S4cQ40A1M0A1S4dVAInv;R4R3R2R1A4S2S18S1aG0G0A2A1S50S4eR2A1A1S6eS35A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem calloc_sec_1 : ltac2:(tb__ "0|5|
S57OF_;S4aS63S4cQ40A1M0S44F_;SfS18G0A1S5aVsegs;S58R2R1S5eVCST;VXGL;S0S1R5R4A6A5S55S64R5A1S45Vsegs;R8S43R6A1A3S72Vsegs;R9S43R7A1A3SfS18S4fA1M1S37S4dG0S73Vsegs;R5RaS20S0S1Z3M2A3M3S1dG1S6cR4S6dR3R2A2A4A5S4bS0S1RfReRcR6RbR5R3A9S6fS36R5U0A2S36R5U3A2R4S36R5U1M4A2R3A5RfR4S59R8SdS5G3A1A1R4A3RdR7S51S70S4eR5A1S36R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SfG0S54Vsegs;RdS42Vsegs;RaR1A1S28S0S1G2A3S59R2S2cS0S1G2A3R1A3R8A5R7A4Fa;FrhoX;SfS54Vsegs;RdS42Vsegs;S4bS0S1RcRbR9A5S46S0S1G2Z8A4R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;TQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HKc Hokl Hokpl HJo HOK rhoE.
  refine (sec_spine 1%nat st0 3 CST XGL HCST HXGL HCSTM HCSTS law_res SWa_0 SDa_0 SWb_0 SFB CertS1_0 WC1_0 DC1_0 NXC1_0 IC1_0 R17_0 R11_0 R10_0 R12_0 R13_0 R14_0 R15_0
            NX1_0 XC1_0 SK1_0 FC1_0 CertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 ok A Kc Jo rho tp _ _ (stopJ_w_stable _ _ stopJ_w_1pc) HKc Hokl Hokpl _ HJo HOK rhoE).
  - hw_discharge.
  - unfold PFc. left. reflexivity.
Qed.

Theorem ecalloc_tail_null_1 : ltac2:(tb__ "0|1|
S4aS63SfS18S4cQ40A1A1S64R3A1SfS56Vsegs;S42Vsegs;S4bS0S1R6R5R4A5S22S0S1Z3A3R1R3A5S5aVsegs;S58R4R3S16S1aS4S5bA2M0S1dS4S5bS5cS0S1A2S5dVCST;VXGL;R6R5A4A4S17G0A1A3A5A3FrhoX;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoX.
  refine (esec_tail_null 1%nat st0 3 CST XGL HCST HXGL HCSTM HCSTS NXS1f_0 ECertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 A Kc rho tp _ (stopJ_w_stable _ _ stopJ_w_1pc) HKc _ rhoX).
  left. reflexivity.
Qed.
End SEC0.
End SpineCallocSecIW1.

(* [comment removed for export] *)
Module DepotCallI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.DepotCallI.INST"; "T4_i"; "s4_i"; "R4_i"; "pm__15"; "pm__16"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__9"; "sd_i"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__3"; "pm__4"; "pm__5"; "pm__6"; "pm__7"; "pm__8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "nil"; "cons"; "option"; "pair"; "Some"; "false"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sstate"; "ss_facts"; "sobj"; "ss_next"; "SVar"; "ss_objs"; "SPUle"; "sprop_below"; "SAlu"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "X4"; "omrg"; "T4d"; "X4r"; "oreb"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "KEEPD"; "X4f"; "perm4"; "F_call"; "coveredb"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "HD_stmt"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Lemma by_cases12 : ltac2:(tb__ "0|2|
S4OF_;R1Z1M0A1R2Z2M1A1S4S1S3G0R1A2S3R1G1A2A2R5R2A1F_;Fsz;F_;F_;FP;").
Proof. intros P H1 H2 sz Hsz. assert (E : sz = 1 \/ sz = 2) by lia. destruct E as [-> | ->]; assumption. Qed.

Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S35S32S32S6dS31S40A1M0A2S7A2M1A1G1Lo;Vo;G1R1Lx;S36S32S31S32S5S3bA2M2A1M3G0A2S7S36G3G0S33G2A1S33S40A1A4S64Z0A1A4X35x2").
Definition CP1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X4 st tmax 1) 1)).
Definition CP2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X4 st tmax 2) 2)).
Definition CP (sz : Z) : wsub * list sobj * axst := if sz =? 1 then CP1 else CP2.
Definition s4_i (sz : Z) : wsub := fst (fst (CP sz)).
Definition R4_i (sz : Z) : list sobj := snd (fst (CP sz)).
Definition T4_i (sz : Z) : axst := snd (CP sz).
Definition sd_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
S7fS6fS6S4dVst;Vtmax;SbVsz;A4A1S6S61VW;Vst;Vtmax;A3A1A3").

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X4f] in (X4f UStopLe 2) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S7S5bS2aZ2A2S1fA3"). Proof. cbv delta [X4f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X4f UStopLe 2) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S7S4eS2aZ2Z1A3S20A3"). Proof. cbv delta [X4r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X4r UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X4r] in (X4r UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|1|
S0S7S4eS2aZ2M0G0A3S21A3"). Proof. cbv delta [X4r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X4r UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S7S57S2aZ2Z1A3S24A3"). Proof. cbv delta [X4a pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X4a UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X4a] in (X4a UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|1|
S0S7S57S2aZ2M0G0A3S25A3"). Proof. cbv delta [X4a pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X4a UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S7S58S2aZ2Z1A3S26A3"). Proof. cbv delta [X4b pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X4b UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X4b] in (X4b UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|1|
S0S7S58S2aZ2M0G0A3S27A3"). Proof. cbv delta [X4b pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X4b UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S7S59S2aZ2Z1A3S28A3"). Proof. cbv delta [X4c pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X4c UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X4c] in (X4c UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|1|
S0S7S59S2aZ2M0G0A3S29A3"). Proof. cbv delta [X4c pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X4c UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X4] in (X4 UStopLe 2 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S7S4bS2aZ2Z1A3S1dA3"). Proof. cbv delta [X4 pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X4 UStopLe 2 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X4] in (X4 UStopLe 2 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|1|
S0S7S4bS2aZ2M0G0A3S10A3"). Proof. cbv delta [X4 pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X4 UStopLe 2 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac2:(tb__ "0|0|
S76SbZ1A1S3fS6S1dA1A1A2").
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S7S50S2aZ2SbZ1A4S11A3"). Proof. cbv delta [T40 pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (T40 UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac2:(tb__ "0|0|
S76SbZ2A1S3fS6S10A1A1A2").
Lemma pm__12_eq : ltac2:(tb__ "0|1|
S0S7S50S2aZ2M0SbG0A4S12A3"). Proof. cbv delta [T40 pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (T40 UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac2:(tb__ "0|0|
S4fS11U0A2").
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S7S51S2aZ2SbZ1A4S13A3"). Proof. cbv delta [T4a pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (T4a UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac2:(tb__ "0|0|
S4fS12U0A2").
Lemma pm__14_eq : ltac2:(tb__ "0|1|
S0S7S51S2aZ2M0SbG0A4S14A3"). Proof. cbv delta [T4a pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (T4a UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac2:(tb__ "0|0|
S4fS13U1A2").
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S7S52S2aZ2SbZ1A4SeA3"). Proof. cbv delta [T4b pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (T4b UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac2:(tb__ "0|0|
S4fS14U1A2").
Lemma pm__16_eq : ltac2:(tb__ "0|1|
S0S7S52S2aZ2M0SbG0A4SfA3"). Proof. cbv delta [T4b pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (T4b UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac2:(tb__ "0|1|
S9SeS75S6SeA1M0S74S43G0A1S5cA2A2A2").
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S7S53S2aZ2SbZ1A4S15A3"). Proof. cbv delta [T4c pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (T4c UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac2:(tb__ "0|1|
S9SfS75S6SfA1M0S74S43G0A1S5cA2A2A2").
Lemma pm__18_eq : ltac2:(tb__ "0|1|
S0S7S53S2aZ2M0SbG0A4S16A3"). Proof. cbv delta [T4c pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (T4c UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac2:(tb__ "0|0|
S4cS15U0A2").
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S7S54S2aZ2SbZ1A4S17A3"). Proof. cbv delta [T4m1 pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (T4m1 UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac2:(tb__ "0|0|
S4cS16U0A2").
Lemma pm__20_eq : ltac2:(tb__ "0|1|
S0S7S54S2aZ2M0SbG0A4S18A3"). Proof. cbv delta [T4m1 pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (T4m1 UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
S4cS17U0A2").
Lemma pm__21_eq : ltac2:(tb__ "0|0|
S0S7S55S2aZ2SbZ1A4S19A3"). Proof. cbv delta [T4m2 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T4m2 UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
S4cS18U0A2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S7S55S2aZ2M0SbG0A4S1aA3"). Proof. cbv delta [T4m2 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T4m2 UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
S4cS19U0A2").
Lemma pm__23_eq : ltac2:(tb__ "0|0|
S0S7S56S2aZ2SbZ1A4S1bA3"). Proof. cbv delta [T4m3 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T4m3 UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
S4cS1aU0A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S7S56S2aZ2M0SbG0A4S1cA3"). Proof. cbv delta [T4m3 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T4m3 UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
S4cS1bU0A2").
Lemma pm__25_eq : ltac2:(tb__ "0|0|
S0S7S4dS2aZ2SbZ1A4S22A3"). Proof. cbv delta [T4d pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T4d UStopLe 2 T4_i 1) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
S4cS1cU0A2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S7S4dS2aZ2M0SbG0A4S23A3"). Proof. cbv delta [T4d pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T4d UStopLe 2 T4_i 2) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Lemma NXE_0 : ltac2:(tb__ "0|0|
S0S2fS87S6fS41S6S60VW;Vst;Vtmax;A3A1A1A2S30A3").
Proof. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBE_0 : ltac2:(tb__ "0|0|
S0S2fS69S3cS45S41S6S60VW;Vst;Vtmax;A3A1A1A1S5dA3S30A3").
Proof. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE4_0 : ltac2:(tb__ "0|1|
S0S31S32S3bS3bA2M0A1S8S60VW;Vst;Vtmax;A3A1S33G0A1A3").
Proof. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192_0 : ltac2:(tb__ "0|1|
S6aS3cS34S3cS44S3dZ1A1S42Pc0A1M0A2S34S3cS44G0S3dVtmax;A1A2S33S3cA1A3A3S3fS6S60VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEP_0 : ltac2:(tb__ "0|0|
S6aS3cS2eS2dA1S3fS6S60VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGEN4_0 : ltac2:(tb__ "0|0|
S6aS3cS62S3fS6S60VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YP4_0 : ltac2:(tb__ "0|0|
S6bS3cS44S3dZ1A1S42S63A1A2S3fS6S60VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WX4r_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS49S6S4eVst;Vtmax;R2A3A1A1S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX4r_0 : ltac2:(tb__ "0|4|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S35S32S31S32S3bS3bA2M0A1M1S31S3cA1M2A2M3A1S7eS6S5bVst;Vtmax;A2A1S6S4eVst;Vtmax;R2A3A1A2S37G3S36G1G2S34G0S36S3bS3bS48S38Q20S42Pc0A1A3S3dR2A1A4S33G0A1A3S33S3cA1A4A2A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS67S6S4eVst;Vtmax;R2A3A1U0S3dNee0A1A3A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS67S6S57Vst;Vtmax;R2A3A1U1S3dN8e0A1A3A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS67S6S58Vst;Vtmax;R2A3A1U2S3dN840A1A3A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS67S6S59Vst;Vtmax;R2A3A1U3S3dN48A1A3A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HER_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S35S31S40A1M0A1S82S4bVst;Vtmax;R2A3S64R2A1ScR2A1A3S37G0SdR2A1A2A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S7S83ScR2A1S64R2A1S65R2A1S4bVst;Vtmax;R2A3SdR2A1A5SbR2A1A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S31S32S3bS3bA2M0A1S8S4bVst;Vtmax;R2A3A1S33G0A1A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS69S3cS45S41S6S4bVst;Vtmax;R2A3A1M0A1A1S3fG0A1A3S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS81S4bVst;Vtmax;R2A3S64R2A1ScR2A1SdR2A1S34S7S65R2A1S33S7A1A3A5S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S5S41S6S4bVst;Vtmax;R2A3A1A1S41S6S60VW;Vst;Vtmax;A3A1A1A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S3bS6cScR2A1PaM0A2S46S71S42G0A1S3dN8e0A1A3A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S3bS6cScR2A1PfA2S3dN600A1A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S3bS6cScR2A1PcA2S46S71S42PaA1S3dN840A1A3A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS69S40S5fSdR2A1A3S30A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWO_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S31S40A1S80S6S64R2A1A1S6S65R2A1A1A2S33S40A1A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPost_0 : ltac2:(tb__ "0|1|
S4S0S31S32S3bS3bA2M0A1S8S65R1A1A1S33G0A1A3Fsz;").
Proof. intros sz. reflexivity. Qed.
Lemma FBT4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS69S3cS45S41S6SbR2A1A1A1A1S3fS6S4bVst;Vtmax;R2A3A1A1A3S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S31S32S3bS3bA2M0A1S8SbR2A1A1S33G0A1A3F_;Fsz;").
Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS68S6S50Vst;Vtmax;SbR2A4A1U0A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS68S6S51Vst;Vtmax;SbR2A4A1U1A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nd_0 : nodupN perm4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_len_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S3aS39S40S43S6S52Vst;Vtmax;SbR2A4A1A1A2U30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS66S6S53Vst;Vtmax;SbR2A4A1U0A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS66S6S54Vst;Vtmax;SbR2A4A1U0A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS66S6S55Vst;Vtmax;SbR2A4A1U0A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS4aS3eS66S6S56Vst;Vtmax;SbR2A4A1U0A2A2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fSaS4dVst;Vtmax;SbR2A4S61VW;Vst;Vtmax;A3S1eR2A1A3S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sd_i]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5_0 : ltac2:(tb__ "0|0|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS6eS1eR2A1S6fA2S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sd_i]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cov_0 : ltac2:(tb__ "0|1|
S4S1S3Z1R1A2S3R1Vtmax;A2A2S0S2fS5eS3fS6S4dVst;Vtmax;SbR2A4A1M0A1SdR2A1S43G0A1A3S30A3F_;Fsz;").
Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all27; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Theorem depot_call_HD_0 : ltac2:(tb__ "0|1|
S31S32S4S4A2A1M0G0S7aR2A1S7cR2A1S4S7bR5R1A2S2S7dR2A1A1F_;Fa;S72OF_;S79S2bS47S73S2cR3A1S78S70R6S77R4A1A3S84S70R7S77R5A1A3S86U0Vst;Vtmax;S5aRdRcR7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HD st tmax CST XGL HCST HXGL HCSTD Htmax_0 NXE_0 FBE_0 F192_0 FDEP_0 FGEN4_0 YP4_0 WX4r_0 DX4r_0 SPL1_0 SPL2_0 SPL3_0 SPL4_0
           s4_i R4_i T4_i HER_0 HT4_0 XX4_0 FBX4_0 Hchk4_0 NX4_0 WG10_0 WG15_0 WG12_0 FAM4_0 NEWO_0 XPost_0 FBT4_0 XT4_0 RB1_0 RB2_0
           PERM_nd_0 PERM_len_0 MRG1_0 MRG2_0 MRG3_0 MRG4_0 sd_i ENT5_0 SID5_0 R4cov_0).
Qed.

Theorem depot_call_HDE_0 : ltac2:(tb__ "0|1|
S31S32S4S4A2A1M0G0S7aR2A1S7cR2A1S4S7bR5R1A2S2S7dR2A1A1F_;Fa;S79S2bS47S72OF_;S2cR3A1S85U0Vst;Vtmax;S5aRaR9R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTD.
  exact (depot_call_HDE st tmax CST XGL HCST HXGL HCSTD Htmax_0 NXE_0 FBE_0 F192_0 FDEP_0 FGEN4_0 YP4_0 WX4r_0 DX4r_0 SPL1_0 SPL2_0 SPL3_0 SPL4_0
           s4_i R4_i T4_i HER_0 HT4_0 XX4_0 FBX4_0 Hchk4_0 NX4_0 WG10_0 WG15_0 WG12_0 FAM4_0 NEWO_0 XPost_0 FBT4_0 XT4_0 RB1_0 RB2_0
           PERM_nd_0 PERM_len_0 MRG1_0 MRG2_0 MRG3_0 MRG4_0 sd_i ENT5_0 SID5_0 R4cov_0).
Qed.
End INST.
End DepotCallI.

(* [comment removed for export] *)
Module F0A_depot.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "prod"; "andb"; "app"; "pair"; "Some"; "cons"; "false"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SAlu"; "SLit"; "ss_facts"; "SVar"; "sprop_below"; "ss_next"; "valuation"; "sprop_eqb"; "ss_objs"; "rw"; "eval"; "sv_eqb"; "agree_below"; "holds"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "ulink"; "UStopLe"; "V_DEPTH"; "client_addrA"; "client_shadowA"; "top_high"; "unwind_stopJ"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "coveredb"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "rd_okb"; "rng_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "opp"; "modulo"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "view"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot.FD.SITE"; "site_factsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "isnil"; "dchkb"; "tjv_ok"; "dchkb_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "HDF"; "HDFE"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_depot"; "aa_geom"; "aa_live"; "aa_sec"; "qbatch"; "aa_internal_inited"; "aa_q_thread"; "ag_thread"; "ageom"; "sec_chunk"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF"; "KD"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "rhoF_of"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "JLD"; "DFP"; "JD";
"dfp_static"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tjv_ok (A : AA) (rho : valuation) (p n t : Z) (jv : junkF) : Prop := ltac2:(tb__ "0|b|
S1S1S1S4fZ0M0Vt;A2S50Vt;Z100A2A2S1S0S33S54Vt;Z4A2Z1A3S1S58S5bS62S25Vrho;A1A2M1S59S55Vp;Z10A2U4M2S82Vt;Vn;A2A3A2S58G1S59S55Vp;ZcA2G2S54Vn;S52Z2M3Z20A2A2A3A2A2A2A2S1S1S4fG0S83Vjv;A1M4A2S50G4S52G3Z40A2M5A2A2S1S1S4fG0S86Vjv;A1M6A2S50G6G5A2A2S1S1S4fG0S85Vjv;A1M7A2S50G7G5A2A2S1S1S4fG0S84Vjv;A1M8A2S50G8G5A2A2S1S58G1S59S51S94Z48A2U8M9G4A3A2S1S58G1S59S51S75S6fVA;A1A1MaZae0A2G9G6A3A2S0S9S72A1S74VA;A1SaS72A1A3S1S58G1S59S51GaZ58A2G9G7A3A2S58G1S59S51GaZ60A2G9G8A3A2A2F_;A2A2A2A2A2A2A2").
Theorem instF_facts_ok2 : ltac2:(tb__ "0|1|
S8S9S40A1S47S88S6dS1dS9S5cQ40M0A1A1S56S33S33S93S62R6R5R4R3A5S2bSbS33S33A2SeS33S33R3R2A4S70R7A1A3S90RcR4R3A3S0S8S73R9A1S7A3S87RbRaA2S0S33S5eG0S20RaPcA2A2R7A3S0S33S5eG0S20RbPdA2A2R7A3S4S33S33S4S80S80S1S67RfReRbRaR2R1A6S91R13R12R11R10S81RfReRbRaR2R1A6RbRaS92RaA1S78S6fRfA1A1A9A2Ljv;A2Lt;A2F_;F_;F_;F_;F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;Fq;Fst;FW;Fkhi;").
Proof.
  intros khi W st q A rho tp md p n HA HL HK Hii QC Hp Hn. pose proof (cls_hyp_blk khi p n HK) as HHI.
  destruct (blkF_mem A rho tp md p n HA HL HHI) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok A rho tp md HA) as [jv Hjv].
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|].
  exact (instF_here A rho tp md p n HA HL HHI Hii Hp Hn t (conj T1 (conj T2 (conj T3 T4))) jv Hjv khi W st q HK QC).
Qed.

Lemma signed_add_lit : ltac2:(tb__ "0|4|
S1dS15S33S1S4fS53S52Z2Z3eA2M0A1M1S5dQ40M2S21R3R2A2A2M3A2S4fG3G0A2A2S1S4fG1R2A2S50R2G0A2A2S0S33S5dG2S21R5S17S2cR4S18R3A1A3A2A2S51S5dG2S21R5R4A2A2R3A2A3F_;F_;Fk;Fe;Frho;").
Proof.
  intros rho e k He Hk. change (bv_signed (eval rho (SAlu ALU_ADD e (SLit k)))) with (soff rho (SAlu ALU_ADD e (SLit k))).
  change (bv_signed (eval rho e)) with (soff rho e) in *. rewrite !soff_snorm in *. unfold U in *. cbn [eval]. rewrite add_val.
  rewrite snorm_of_mod'. set (u := bv_unsigned (eval rho e)) in *.
  rewrite (snorm_congr (u + bv_unsigned (Z_to_bv 64 k)) (snorm u + k)).
  - apply snorm_id'. change (2 ^ 62) with 4611686018427387904 in *. change (2 ^ 63) with 9223372036854775808. lia.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r.
    rewrite <- (Zplus_mod_idemp_l (snorm u)), snorm_mod, Zplus_mod_idemp_l. reflexivity.
Qed.

Definition isnil {T} (l : list T) : bool := match l with [] => true | _ => false end.
Lemma isnil_sound : forall T (l : list T), isnil l = true -> l = [].
Proof. intros T [|x l] H; [reflexivity | discriminate]. Qed.
Definition dchkb (nW : nat) (q : qvar) (sz : Z) (ED TD : axst) (sD : wsub) (RD : list sobj) : bool := ltac2:(tb__ "0|a|
ScS65SbS15S15A2M0S27VED;A1A2ScS65G0S27VTD;A1A2ScS4eS32S1cS26VED;A1M1A1M2A2ScS29S14S1bG2A1S19G1A1M3A3ScS29S14S1bS1cS26S36VsD;S34Vsz;A1M4S35Vsz;A1M5VED;VRD;A5A1A1A1G3A3ScS22S2dVsD;PaM6A2S17S2cS1aG6A1M7S18N880A1A3A2ScS22S2dVsD;PfM8A2S17S2cS1aG8A1S18Z880A1A3A2ScS22S2dVsD;PcA2S17S2cG7S18N840A1A3A2ScS29S16S4cVnW;Vq;A2VRD;A3ScS29S16S4dS32A1VRD;A3ScS29S14S14S2aS14S1eR1A1G3A3Lf;SdS14S3cS3fVnW;A1A1S3eS3dA1A3A3ScS65S16S48S26G4A1S26G5A1A2A2ScS65G0S27G5A1A2S4aS19S26VTD;A1M9A1VRD;S1fG9A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma dchkb_sound : ltac2:(tb__ "0|d|
S12S88S33S28S28S31S9S16A1M0S0S8S66R7R6R5R4R3R2R1A7S7A3S1S0S9SbS15S15A2M1A1M2S27R5A1SaG1A1M3A3S1S0G2S27R4A1G3A3S1S0S8S4eS32S1cS26R5A1M4A1M5A2S7A3S1S0S8S29S14S1bG5A1S19G4A1M6A3S7A3S1S0S8S29S14S1bS1cS26S36R3S34R6A1M7S35R6A1M8R5R2A5A1A1A1G6A3S7A3S1S0S15S2dR3PaM9A2S17S2cS1aG9A1MaS18N880A1A3A3S1S0S15S2dR3PfMbA2S17S2cS1aGbA1S18Z880A1A3A3S1S0S15S2dR3PcA2S17S2cGaS18N840A1A3A3S1S0S8S29S16S4cR8R7A2R2A3S7A3S1S0S8S29S16S4dS32A1R2A3S7A3S1S0S8S29S14S14S2aS14S1eR1A1S19S26R6A1A1A3Lf;SdS14S3cS3fR8A1A1S3eS3dA1A3A3S7A3S1S0G0S48S26G7A1S26G8A1A2SaS16A1A3S1S0G2S27G8A1G3A3S0S8S4aS19S26R4A1McA1R2S1fGcA1A3S7A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FRD;FsD;FTD;FED;Fsz;Fq;FnW;").
Proof.
  intros nW q sz ED TD sD RD H. unfold dchkb in H.
  repeat (apply andb_prop in H as [?X H]).
  repeat match goal with X : isnil _ = true |- _ => apply isnil_sound in X | X : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in X end.
  apply isnil_sound in X10, X11 || idtac.
  repeat split; assumption.
Qed.

Lemma stopJ_le : ltac2:(tb__ "0|0|
S9S40A1S1dS46R2S41R1A3Frho;FW;").
Proof. intros [|l W'] rho; exact I. Qed.

Section FD.
Variable nW : nat. Variable q : qvar. Variable sz : Z.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S33S5aVCST;R1A2S5S8cR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis Hsz : 1 <= sz <= SZMAX.
Definition KEEPF (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S6S43VCST;VA;Va;A3S44VCST;VXGL;VA;Va;A4A2").

Variables (ED TD : axst) (sD : wsub) (RD : list sobj).
Hypothesis HER : ltac2:(tb__ "0|1|
S0S13S9S16A1M0A1S3aVED;S34Vsz;A1VsD;A3SfG0VRD;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S8S39VED;S34Vsz;A1VsD;VRD;S10S28S35Vsz;A1SaS28A1A3A5S7A3").
Hypothesis HTD : ltac2:(tb__ "0|0|
S0S28VTD;S8eS36VsD;S34Vsz;A1S35Vsz;A1VED;VRD;A5S19S26VED;A1A1A2A3").
Hypothesis DCHK : ltac2:(tb__ "0|0|
S0S8S66VnW;Vq;Vsz;VED;VTD;VsD;VRD;A7S7A3").
Let PARTS := dchkb_sound nW q sz ED TD sD RD DCHK.
Let XXE : ax_X ED = [] := proj1 PARTS.
Let XTD : ax_X TD = [] := proj1 (proj2 PARTS).
Let NXE : Pos.leb GW (ss_next (ax_S ED)) = true := proj1 (proj2 (proj2 PARTS)).
Let FBX : forallb (sprop_below (ss_next (ax_S ED))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 PARTS))).
Let FBT : forallb (sprop_below (ss_next (ax_S (import_postA sD (PreD sz) (PostD sz) ED RD)))) (ss_facts (ax_S ED)) = true := proj1 (proj2 (proj2 (proj2 (proj2 PARTS)))).
Let WG10 : wsub_get sD 10 = SAlu ALU_ADD (SVar 10) (SLit (-2176)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))).
Let WG15 : wsub_get sD 15 = SAlu ALU_ADD (SVar 15) (SLit 2176) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))).
Let WG12 : wsub_get sD 12 = SAlu ALU_ADD (SVar 10) (SLit (-2112)) := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))).
Let RDOK : forallb (rd_okb nW q) RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))).
Let RDWF : forallb (rng_below GW) RD = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))).
Let FCH : forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S ED))) (chain_pre W ++ F_depth free_depth) = true := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))).
Let NEWO : new_objs (ax_S (PreD sz)) (ax_S (PostD sz)) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS))))))))))).
Let XPost : ax_X (PostD sz) = [] := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).
Let RDcov : coveredb (ss_facts (ax_S TD)) RD (ss_objs (ax_S TD)) = true := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PARTS)))))))))))).

Section SITE.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp0 : list word) (md0 : Model) (p n t : Z) (jv : junkF).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HA0 : ltac2:(tb__ "0|0|
VAInv;VA;Vrho;Vtp0;Vmd0;A4").
Hypothesis HL : ltac2:(tb__ "0|0|
S2bSbS33S33A2SeS33S33Vp;Vn;A4S70VA;A1A3").
Hypothesis HHI : blk_cls p n.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S0S33S5eQ40S20Vrho;PcA2A2Vp;A3").
Hypothesis HTJ : ltac2:(tb__ "0|0|
S67VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Hypothesis QC : qcond q A.
Let rho1 : valuation := ltac2:(tb__ "0|0|
S81VA;Vrho;Vp;Vn;Vt;Vjv;A6").

Definition site_factsF (rhoE : valuation) : Prop := ltac2:(tb__ "0|1|
S1S23S32Vrho1;VrhoE;A3S1S45VA;VrhoE;A2S1S1S4fS53S52Z2Z28A2A1S5dQ40S20VrhoE;S42A2A2M0A2S4fG0S53S3dA1A2A2S8dS14S24VrhoE;A1S3cVW;A1A3A2A2A2").

Lemma fd_facts : ltac2:(tb__ "0|0|
S1dS9S5cQ40A1A1S63S79Vsegs;S69VnW;Vst;S7VA;VKc;Vrho1;A6VED;R3R2R1A6S61R4A1F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Htop).
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (FIN : forall f, In f (chain_pre W ++ F_depth free_depth) -> holds rhoE f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) FCH f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  split; [exact Hag|]. split; [exact Htop|]. split.
  - assert (D1 : holds rhoE (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoE (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia.
  - apply Forall_forall. intros f Hf. apply FIN. apply in_or_app. left. exact Hf.
Qed.

Lemma fd_R4 : ltac2:(tb__ "0|2|
S1dS61R1A1S6dS1dS9S5cQ40M0A1M1A1S56G1S95R5R4R3R2A4S0S76S6fR6A1S6fVA;A1A3S0S9S77A1S71R7A1S71VA;A1A3S30RaVRD;R4A3S5S8aS6eR9A1S5eG0R5A2A2A1F_;F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;FrhoE;").
Proof.
  intros rhoE (Hag & Htop & Hdep & Hch) Ax rx tpx mdx a HX EG ES (o & Ho & Hoa).
  destruct HTJ as [Ht Hjv].
  apply (zoneF_not_DFP A Ax rx tpx mdx (bv_unsigned a) HX EG ES).
  exact (rd_zone A rho tp0 md0 p n HA0 HL HHI Hp12 t jv Ht Hjv nW q QC rhoE Hag Htop (proj2 Hdep) Hch o
           (proj1 (forallb_forall _ _) RDOK o Ho) (proj1 (forallb_forall _ _) RDWF o Ho) (bv_unsigned a) Hoa).
Qed.

Lemma fd_entry : ltac2:(tb__ "0|1|
S1dS9S5cQ40A1A1S9S57A1M0S5fS56S61R5A1S7aVsegs;R6R5VED;SeG0S7eR4S7fR3R2A2A4A5S69VnW;Vst;S7VA;VKc;Vrho1;R7R6R5R3AaS8bS62S7dVA;VKc;R8A3S6eVA;A1S2fS2eR8VRD;S60R4R7R5A3A3VsD;A2R7R6R4A7F_;F_;F_;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md SF Hsm0 [Hag0 HJ0].
  pose proof SF as (_ & Htop & Hdep & _). unfold top_high in Htop. unfold free_depth in Hdep.
  pose proof HJ0 as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2176 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2176)))) = bv_unsigned (rw rhoE 10%positive) - 2176).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2176))) with (2 ^ 64 - 2176) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2112)))) = bv_unsigned (rw rhoE 10%positive) - 2112).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2112))) with (2 ^ 64 - 2112) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE HB HKm0 HKf0 tp tr0 md HA HK). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite WG10, WG15, WG12, !eval_absorb, Em2176, Em2112.
    rewrite signed_add_lit by (cbn [eval]; unfold V_DEPTH in Hdep; lia). cbn [eval]. unfold V_DEPTH in Htop, Hdep. lia.
  - destruct (AInvA_X A rhoE tp md HA) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (fd_R4 rhoE SF A rhoE tp md _ HX0 eq_refl eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma fd_exit_ok : ltac2:(tb__ "0|2|
S1dS9S5cQ40A1A1M0S9S57A1M1S5fS56S1dG0G1S5fS56S61RaA1S89S62S7dVA;VKc;RbA3S6eVA;A1A3S37S2fS2eRcVRD;S60R8RbR9A3A3VsD;A2S1dR2R1RcR8R7R6R4A6S3bReS60RaRdRbA3VRD;VsD;S34Vsz;A1S35Vsz;A1VED;R9A8F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC HJL. subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (fd_R4 rhoE SF _ rhoE tpL md' a HXK eq_refl eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite NEWO in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite XPost in Hr. destruct Hr.
  - intros r a j Hr. rewrite XXE in Hr. destruct Hr.
Qed.

Lemma fd_exit_core : ltac2:(tb__ "0|4|
S1dS9S5cQ40A1A1M0S9S57A1M1S5fS56S1dG0G1S5fS56S61RaA1S89S62S7dVA;VKc;RbA3S6eVA;A1A3S37S2fS2eRcVRD;S60R8RbR9A3A3VsD;A2S1dS7aVsegs;RdRcVED;SeG1S7eRbS7fRaR9A2A4A5S69VnW;Vst;S7VA;VKc;Vrho1;ReRdRcRaAaR4R3ReRaR9R8R6A6S1dS63S49R12S60ReR11RfA3VRD;VsD;S26S34Vsz;A1M2A1S26VED;A1S26S35Vsz;A1M3A1R2RdA9S79Vsegs;S38R8R7R12ReRdA5S36VsD;G2G3VED;VRD;A5R3RdR2A6S4S6dS6dS4S1dS1dS4S1dS1dS1S6cVA;R3A2S1S96S4bVCST;VXGL;VA;A3Vrho1;R2A3S79Vsegs;S69VnW;Vst;S11R3VKc;R2A6VTD;R1R11R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;TrhoC;TJL;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms0;Ftr0;Ftp;FrhoE;").
Proof.
  intros rhoE tp tr0 ms0 md rhoL tpL tr' ms' md' SF JL rhoC Hsm0 [Hag0 HJ0] HJL rho' w' HLK [Hsm' HJ'].
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0' & HU0 & HL0 & HK0 & Htp0 & _ & Htop0). unfold top_high in Htop0.
  subst JL.
  destruct (entails_frA_sound segs ED (PreD sz) sD RD rhoE tp tr0 ms0 md HER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S ED))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S ED))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros f Hf.
    exact (proj1 (holds_agree_vals _ rhoE rho' f Hag' (proj1 (forallb_forall _ _) FBX f Hf)) (proj1 (Forall_forall _ _) Hfacts4 f Hf)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE RD (vms md tp ms0)) sD) tp rhoL tpL) TD rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite HTD. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact FBT | intros _; exact HF4]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.

  assert (RNG : forall o, In o RD -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S ED))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpKf (with_depot A G2)).
  set (rho5 := rho_absorb rho' RD (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho1) (rl rho1) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' RD a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' RD a <-> in_ranges rhoE RD a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE RD a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (fd_R4 rhoE SF A' rhoE tpL md2 a HX2 eq_refl eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE RD a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' RD a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall a, SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP G2 a).
  { intros a HB'. apply (zoneF_not_DFP A A' rhoE tpL md2 a HX2 eq_refl eq_refl). unfold zoneF. cbn zeta. do 5 right. left. exact HB'. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE RD (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' RD (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' RD (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md HA0') as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpKf with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJF5 : JF nW st false A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold rho''. cbn [rw]. rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite (Hagl l). exact (proj2 Hag' l).
      + intros a. reflexivity.
    - split; [exact HA5|]. split; [exact (stopJ_le _ _)|].
      split; [rewrite (RW5 12%positive), (RW5 13%positive) by (unfold GW; lia); exact HL0|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact I|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JF nW st false A' Kc rho'') TD rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT40)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact XTD | | exact HT40 | exact HJF5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT RDcov Ho Ha). }
  exists A', rho'', rho5. split; [|split; [|exact HT5]].
  - unfold depot_onlyKf, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpKf with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [symmetry; exact (Hagm a)|].
      exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); exact Hdef|]. exact (BAND (bv_unsigned a) HBa).
Qed.

Theorem depot_call_HDF : ltac2:(tb__ "0|1|
S63OF_;S64S7cVsegs;R2S7bVKc;A1M0A3S8fVsegs;R3G0A3S6aVnW;Vst;S4bVCST;VXGL;VA;A3R4VA;VKc;Vrho1;VED;VTD;R3AaF_;F_;FQ;Fok;").
Proof.
  intros ok Q Hokl Hokpl rhoE tp Hcont k HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_soundPA segs ok (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreD sz) sD RD
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact Hchk.
  - intros rhoP tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz Hsz rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t0 tr0 ms0 md1 msv' HKG HMI Hh Hp Hs. exact (Hokl r t0 tr0 ms0 md1 msv' (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) HMI Hh Hp Hs).
    + intros G r t0 tr0 ms0 md1 x8 HKG Hp Hok. exact (Hokpl r t0 tr0 ms0 md1 x8 (KD_Kc A Kc rhoE G r t0 tr0 md1 HKG) Hp Hok).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK n' Hg' w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
  - exact HgQ.
  - exact Hw.
Qed.

Theorem depot_call_HDFE : ltac2:(tb__ "0|0|
S63OF_;S6bVnW;Vst;S4bVCST;VXGL;VA;A3VA;VKc;Vrho1;VED;VTD;R1A9FQ;").
Proof.
  intros Q rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (fd_facts rhoE tp _ Hw) as SF.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & _ & _ & HK & _ & HB & _). cbn beta iota in HB. pose proof (proj1 HA) as HG.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & HKf0).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t0 tr0 md1, KD A Kc rhoE G r t0 tr0 md1 -> alloc_top (m_vmmaps md1) = topG (aa_geom A)).
  { intros G r t0 tr0 md1 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t0 tr0 md1 HKG). }
  apply (call_completePA segs (JF nW st true A Kc rho1) (JD segsA (KD A Kc rhoE) (aa_depot A)) ED (PreD sz) sD RD
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp HER).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact Hchk.
  - intros rhoP tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE HKc HB HKm0 HKf0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz Hsz rhoP tp1 (aa_depot A) (dN_entry A rhoE HB tp md HA) (hcD_entry A rhoE HB tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md1 Hsm0 HJ0. exact (fd_entry rhoE tp tr0 ms0 md1 SF Hsm0 HJ0).
  - intros L JL tr0 ms0 md1 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    split; [exact (fd_exit_ok rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF HJL)|].
    intros rho' HLK w' Hw'.
    destruct (fd_exit_core rhoE tp tr0 ms0 md1 rhoL tpL tr' ms' md' SF Hsm0 HJ0 HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
    exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
  - exact Hw.
Qed.
End SITE.
End FD.
End F0A_depot.

(* [comment removed for export] *)
Module F0A_limbo.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "modulo"; "div"; "mul"; "leb"; "ltb"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "sec_chunk"; "aa_live"; "aa_depot"; "aa_sec"; "topG"; "AA"; "ag_ctx"; "ag_dtls"; "ageom"; "ag_fsb"; "ag_pab"; "cs_mapped_user"; "depot_state"; "sc_map_beg"; "class_state"; "cs_mapped_free_array"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "option"; "bool"; "Some"; "list"; "prod"; "false"; "pair"; "nat"; "andb"; "true"; "app"; "cons"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo.LIMBO"; "CH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_limbo"; "LZ0"; "lb_body"; "LZ0b"; "cls_meta2"; "rho_mid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "mkVal"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "present"; "bview"; "cell_ok"; "mkACell"; "maskv"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "rz"; "IMG_HI"; "IMG_LO"; "kPtrArrayReserve"; "region_beg"; "FS_total"; "free_array"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "present_but"; "AInvA"; "class_repr"; "fs_inv"; "alloc_magic_ok"; "bandtp_inv"; "geom_ok"; "inv3"; "model_inv"; "shadow_unpoisoned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "rest_invQC"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "BLK"; "CZA"; "CZI"; "GEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition lb_body (m : bview) (b n : Z) : Prop := ltac2:(tb__ "0|5|
SbScS28S25Q8M0A1M1A1M2Vm;S3Vb;Z10A2A1S2aG1S26G0Z2M3A2A2A3SbS43Vm;S44S3Vb;ZcA2U4S5Vn;S4G3Z20A2M4A2A3A2SbS43Vm;S44S3Vb;ZeA2U2S6Vn;G4A2A3A2SbS5dVm;Vb;Vn;A3SbS58Vm;Vb;Vn;A3SfG1G1SbScG2Vm;S3Vb;ZfA2A1S2aG1R1A2A3ScS11S5S27G0R1A2Z4A2Z1A3A2Lt;A2A2A2A2A2A2").
Definition LZ0 (p n : Z) (z : Z) : Prop := ltac2:(tb__ "0|3|
SdSbS0S3Vp;Z10A2Vz;A2S2Vz;S3Vp;Z8M0A2A2A2SdSbS0Vp;Vz;A2S2Vz;S1Vp;S49Vn;A1M1A2A2A2SbS0S4aVp;A1M2Vz;A2S2Vz;S1G2S6G1G0A2A2A2A2A2A2").
Lemma LZ0_dec : ltac2:(tb__ "0|1|
S11S11S11SdS36R3R2R1A3M0SeG0A1A2Fz;Fn;Fp;").
Proof. intros p n z. unfold LZ0. lia. Qed.

Definition cls_meta2 (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|3|
S52S13VG;A1M0Vc;A2S11S51G0Vc;A2S11SdSbS0R2Vz;A2S2Vz;S1R2Z80A2A2A2SdSbS0R1Vz;A2S2Vz;S1R1S24Vcs;A1A2A2A2SbS0S1S1S14VG;A1Zd0A2S7Z50M1Vc;A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2A2A2Tfa;Tri;").
Lemma class_repr_agree_pres : ltac2:(tb__ "0|2|
S42S42S1dS1aS11S23SbS0Z1R2A2S0R2Z1eA2A2S11S39R6R4R3R1A4ScS28S25Q8A1A1R8R2A1R9R2A1A3F_;Fz;S54R7S4fS13R6A1R4A2M0S1G0S20R3A1A2S16R5A1A4S41R8S4aS4fS13R7A1R5A2M1A1S4aS1G1S20R4A1A2A1A3S56RaR8R7R6R5A5S56RaR9R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc AG PU' PS' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_meta2 G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_meta2 G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold ri in *; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; unfold fa in *; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [exact PS'|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AG; right; right; lia|].
  split; [exact ND|].
  split; [exact LV|].
  split.
  - intros Hi. destruct (CI Hi) as (K1 & K2 & K3 & K4 & K5). split; [|split; [|split; [|split; [|exact K5]]]].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K1].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K2].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K3].
    + intros i x Hi'. apply CA; [|exact (K4 i x Hi')]. cbn [c_addr c_w]. intros k Hk. right; right.
      pose proof (nth_error_Some_lt _ _ _ Hi') as L. pose proof (max_count_le16 c Hc). lia.
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hn. destruct (CN Hn) as [K1 K2]. split; [exact K1|]. eapply filled_agree; [|exact K2]. intros z Hz. apply AG. right; right. lia.
Qed.

Section LIMBO.
Let segs : list Segment := segsA.

Variables (A0 : AA) (rho0 : valuation) (tp0 : list word) (md0 : Model) (p n : Z) (l1 l2 : list (Z * Z)).
Hypothesis HA0 : ltac2:(tb__ "0|0|
S55Vsegs;VA0;Vrho0;Vtp0;Vmd0;A5").
Hypothesis HLV : ltac2:(tb__ "0|1|
ScS2bS2cS11S11A2M0A1S16VA0;A1S32G0Vl1;S33G0S2eS11S11Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HCLS : blk_cls p n.
#[local] Abbreviation G := (aa_geom A0).
#[local] Abbreviation T := (ag_thread (aa_geom A0)).
#[local] Abbreviation SB := (ag_spacebeg (aa_geom A0)).
Definition GEO0 := F0A_rebuild.GEO A0 rho0 tp0 md0 n 0 HA0.
Definition BLK0 : ltac2:(tb__ "0|5|
SbS67Vp;S49Vn;A1M0A2SbScS11S5Vp;Z10M1A2Z0M2A3SbS0Z1Vn;A2SbS2S1Vp;G0A2S19S12VA0;A1A1A2SbSbS0Vn;G0A2S2G0S1Vn;Z8M3A2A2A2SbScS11S5G0G3A2G2A3SbS0G3G0A2SbSbS0G1S4bVn;A1M4A2S0G4Z800A2A2SbScS11S5G4G1A2G2A3ScS11S5Vp;G3A2G2A3A2A2A2A2A2A2A2A2A2") := ltac2:(tb__ "0|0|
S68VA0;Vrho0;Vtp0;Vmd0;Vp;Vn;Vl1;Vl2;Z0VHA0;VHLV;VHCLS;Ac").
Definition CZI0 : ltac2:(tb__ "0|10|
SbSdS0S1Vp;S49Vn;A1A2M0S14S12VA0;A1M1A1M2A2S0S1G2Z1000M3A2S3Vp;S4bVn;A1A2M4A2A2SbSdS0G0S1bG1A1M5A2S0S1G5G3A2G4A2A2SbSdS0G0S1cG1A1M6A2S0S1G6G3A2G4A2A2SbSdS0G0S1eG1A1M7A2S0S1G7S50A2G4A2A2SbSdS0G0S1fG1A1M8A2S0S1G8S4eA2G4A2A2SbSdS0G0S1S13G1A1M9S4Z2MaZ25A2A2MbA2S0S1GbG3A2G4A2A2SbS11S11S61S2cS11S11A2S2eS11S11R2R1A4S64S17VA0;A1A1A3SdS0G0R3A2S0S1R3R2A2G4A2A2F_;FL;Fbb;SbS2fS15ScS28S15A1S62S15S18VA0;A1R2A3S2aS15R1A2A3SdS0G0S22R2A1McA2S0S1GcZ20MdA2G4A2A2F_;Fch';Fj;SbS11SbS0Z1R1A2S0R1Z1eA2A2SdS0G0S1S1G9S7R2S4GaGdA2MeA2A2MfS3GeS4GaZ1dA2A2A2A2S0S1GfGeA2G4A2A2F_;Fc';SbSdSbS0S1Z643000G3A2Vp;A2S0G0Z7fff7000A2A2S0S1Z10007fff8000Z10A2Vp;A2A2S2G0S19G1A1A2A2A2A2A2A2A2A2A2A2A2") := ltac2:(tb__ "0|0|
S6aVA0;Vrho0;Vtp0;Vmd0;Vp;Vn;Vl1;Vl2;Z0VHA0;VHLV;VHCLS;Ac").
Definition CZA0 := F0A_rebuild.CZA A0 rho0 tp0 md0 p n l1 l2 0 HA0 HLV HCLS.

Lemma SHZ : ltac2:(tb__ "0|1|
S11SbS0S4aVp;A1M0R1A2S2R1S1G0S6S49Vn;A1Z8A2A2A2A2SbSbS0Z800c0600R2A2S2R2Z10007fef8000A2A2ScS29S53S12VA0;A1R2A2S2dA3A2F_;Fz;").
Proof.
  intros z Hz. pose proof BLK0 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1.
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  pose proof HA0 as (HG & _). pose proof CZI0 as (_ & _ & _ & I4 & _ & _ & _ & _ & _ & I10 & I11). rewrite FS_total_val in I4.
  destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw].
  assert (Ha : p <= p + 8 * (z - Sh p) < p + N8 n).
  { unfold Sh in Hz |- *. rewrite Hu, Hw in *. rewrite Z.div_mul in * by (clear; lia). clear -Hz. lia. }
  assert (Ea : z = Sh (p + 8 * (z - Sh p))).
  { unfold Sh. rewrite Hu. rewrite Z.div_mul by (clear; lia).
    replace (u * 8 + 8 * (z - (u + SHADOW_OFF))) with ((z - SHADOW_OFF) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
  split.
  - unfold Sh, SHADOW_OFF in Hz. rewrite Hu, Hw in Hz. rewrite !Z.div_mul in Hz by (clear; lia). clear -Hz Hu Hw I10 I11 TG B7. lia.
  - apply (fs_footb_sh G z (p + 8 * (z - Sh p)) HG); [clear -Ha I10 I11 TG; lia | rewrite FS_total_val; clear -Ha I4 B5 B8; lia | exact Ea].
Qed.
Lemma LZ_cases : ltac2:(tb__ "0|2|
S11S36Vp;Vn;R1A3SdSbS0S3Vp;S4bVn;A1A2R2A2S2R2S1Vp;S49Vn;A1M0A2A2A2SbS0S4aVp;A1M1R2A2S2R2S1G1S6G0Z8A2A2A2A2A2F_;Fz;").
Proof. intros z Hz. pose proof BLK0 as (_ & _ & _ & _ & _ & _ & B7 & B8 & _). unfold LZ0 in Hz. clear -Hz B7 B8. lia. Qed.
Lemma LZF : ltac2:(tb__ "0|0|
S11S36Vp;Vn;R1A3ScS29S53S12VA0;A1R2A2S2dA3F_;Fz;").
Proof. intros z Hz. destruct (LZ_cases z Hz) as [K|K]; [exact (proj1 (proj2 (proj2 (proj2 (CZA0 z K))))) | exact (proj2 (SHZ z K))]. Qed.

Lemma NOUT : ltac2:(tb__ "0|4|
S11S11S11SbS0R3R1A2S2R1R2A2A2SdS0S1Vp;S49Vn;A1A2R4A2S0R3S3Vp;S4bVn;A1A2A2A2SdS0R4Z7fff7000A2S0Z10007fff8000R5A2A2SdS0S1S14S12VA0;A1M0A1M1Z1000M2A2R6A2S0R5G1A2A2SdS0R6S13G0A1M3A2S0S1S1G3S4Z2Z25A2A2G2A2R7A2A2SeS36Vp;Vn;R6A3A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz SP SBD _ _ Hc. destruct (LZ_cases z Hc) as [K|K]; [clear -Hz K SP; lia|]. pose proof (proj1 (SHZ z K)) as X. clear -Hz X SBD. lia.
Qed.
Lemma NIMG : ltac2:(tb__ "0|0|
S11SbS0S4dR1A2S2R1S4cA2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K)))))))))) Hz).
  - pose proof (proj1 (SHZ z K)) as X. unfold IMG_HI in Hz. clear -Hz X. lia.
Qed.
Lemma NTP : ltac2:(tb__ "0|1|
S11SbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z1000A2A2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (CZA0 z K) Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _). clear -Hz X TB. lia.
Qed.
Lemma NMETA : ltac2:(tb__ "0|1|
S11SbS0S1S13S12VA0;A1A1S4Z2Z25A2A2M0R1A2S2R1S1G0Z1000A2A2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K)))))) Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & SB1 & _). clear -Hz X SB1. lia.
Qed.
Lemma NFA : ltac2:(tb__ "0|3|
S11S11SbS0Z1R2A2S0R2Z1eA2A2SbS0S1S1S13S12VA0;A1A1S7R3S4Z2M0Z20A2M1A2A2M2S3G1S4G0Z1dA2A2A2R2A2S2R2S1G2G1A2A2A2SeS36Vp;Vn;R3A3A1F_;F_;Fz;Fc';").
Proof.
  intros c' z Hc' Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K))))))))) c' Hc' Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & SB1 & _). clear -Hz X SB1 Hc'. lia.
Qed.
Lemma NBAND_U : ltac2:(tb__ "0|0|
S11SbS0Z7fff7000R1A2S2R1Z10007fff8000A2A2SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1F_;Fz;").
Proof.
  intros z Hz Hu. pose proof BLK0 as (_ & _ & _ & _ & B5 & _ & _ & B8 & _).
  assert (K : p - rz n <= z < p + N8 n) by (clear -Hu B5 B8; lia).
  pose proof (CZA0 z K) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (X & _) & _). clear -Hz X. lia.
Qed.

Variables (A : AA) (rho rho' : valuation) (tp : list word) (md : Model).
Hypothesis EG : ltac2:(tb__ "0|0|
ScS1dS12VA;A1S12VA0;A1A3").
Hypothesis ES : ltac2:(tb__ "0|0|
ScS2bS15A1S18VA;A1S18VA0;A1A3").
Hypothesis ED : ltac2:(tb__ "0|0|
ScS21S17VA;A1S17VA0;A1A3").
Hypothesis EL : ltac2:(tb__ "0|0|
ScS2bS2cS11S11A2A1S16VA;A1S16VA0;A1A3").
Hypothesis HA : ltac2:(tb__ "0|0|
S5eVA;Vrho;Vtp;Vmd;A4").
Let v : bview := ltac2:(tb__ "0|0|
S40Vsegs;S3bVrho;A1A2").
Let v' : bview := ltac2:(tb__ "0|0|
S40Vsegs;S3bVrho';A1A2").
Let m : bview := ltac2:(tb__ "0|0|
S45S53S12VA0;A1A1Vv;A2").
Let m' : bview := ltac2:(tb__ "0|0|
S45S53S12VA0;A1A1Vv';A2").

Variable XZ : Z -> Prop.
Hypothesis XZT : ltac2:(tb__ "0|1|
S11VXZ;R1A1SdSbS0S1S14S12VA0;A1A1M0Z50A2R2A2S2R2S1G0Z70A2A2A2SbS0S1G0Za80A2R2A2S2R2S1G0Zc60A2A2A2A2F_;Fz;").
Hypothesis XZD : ltac2:(tb__ "0|1|
S11SdVXZ;R1A1M0SeG0A1A2Fz;").
Definition CH (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS36Vp;Vn;Vz;A3VXZ;Vz;A1A2").
Hypothesis VO : ltac2:(tb__ "0|0|
S11SeS35R1A1A1ScS28S25Q8A1A1Vv';R2A1Vv;R2A1A3F_;Fz;").
Hypothesis PRES : ltac2:(tb__ "0|1|
S11S36Vp;Vn;R1A3SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1SfS25Q8A1M0G0ScS28G0A1Vv';R4A1S2aG0R1A2A3Lb;A2F_;F_;Fz;").
Hypothesis PRESXZ : ltac2:(tb__ "0|1|
S11VXZ;R1A1SfS25Q8A1M0G0ScS28G0A1Vv';R3A1S2aG0R1A2A3Lb;A2F_;Fz;").
Hypothesis BODY : ltac2:(tb__ "0|2|
ScS28S25Q8M0A1M1A1Vv';S3Vp;Z10A2A1S2aG1S26G0Z2A2A2A3S37Vm';Vp;Vn;A3F_;").

Lemma HLin : ltac2:(tb__ "0|0|
S61S2cS11S11A2S2eS11S11Vp;Vn;A4S16VA;A1A3").
Proof. rewrite EL, HLV. apply in_or_app. right. left. reflexivity. Qed.

Lemma CH_dec : ltac2:(tb__ "0|1|
S11SdS35R1A1M0SeG0A1A2Fz;").
Proof. intros z. unfold CH. destruct (LZ0_dec p n z) as [H|H]; [left; left; exact H|]. destruct (XZD z) as [H'|H']; [left; right; exact H' | right; intros [X|X]; tauto]. Qed.
Lemma NXZ_T : ltac2:(tb__ "0|1|
S11SeSbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z1000A2A2A2A1SeVXZ;R2A1A1F_;Fz;").
Proof. intros z Hz Hx. pose proof (XZT z Hx). lia. Qed.
Lemma NOUTX : ltac2:(tb__ "0|4|
S11S11S11SbS0R3R1A2S2R1R2A2A2SdS0S1Vp;S49Vn;A1A2R4A2S0R3S3Vp;S4bVn;A1A2A2A2SdS0R4Z7fff7000A2S0Z10007fff8000R5A2A2SdS0S1S14S12VA0;A1M0A1M1Z1000M2A2R6A2S0R5G1A2A2SdS0R6S13G0A1M3A2S0S1S1G3S4Z2Z25A2A2G2A2R7A2A2SeS35R6A1A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof. intros lo hi z Hz SP SBD ST SS [Hc|Hc]; [exact (NOUT lo hi z Hz SP SBD ST SS Hc) | apply (NXZ_T z); [clear -Hz ST; lia | exact Hc]]. Qed.
Lemma NIMGX : ltac2:(tb__ "0|0|
S11SbS0S4dR1A2S2R1S4cA2A2SeS35R2A1A1F_;Fz;").
Proof.
  intros z Hz [Hc|Hc]; [exact (NIMG z Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in Hz. clear -Hz TI. lia.
Qed.
Lemma NTPX : ltac2:(tb__ "0|1|
S11SdSbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z50A2A2A2SdSbS0S1G0Z70A2R1A2S2R1S1G0Za80A2A2A2SbS0S1G0Zc60A2R1A2S2R1S1G0Z1000A2A2A2A2A2SeS35R2A1A1F_;Fz;").
Proof. intros z Hz [Hc|Hc]; [apply (NTP z); [clear -Hz; lia | exact Hc] | pose proof (XZT z Hc) as X; clear -Hz X; lia]. Qed.
Lemma NMETAX : ltac2:(tb__ "0|1|
S11SbS0S1S13S12VA0;A1A1S4Z2Z25A2A2M0R1A2S2R1S1G0Z1000A2A2A2SeS35R2A1A1F_;Fz;").
Proof.
  intros z Hz [Hc|Hc]; [exact (NMETA z Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & ST & _). clear -Hz ST. lia.
Qed.
Lemma NFAX : ltac2:(tb__ "0|3|
S11S11SbS0Z1R2A2S0R2Z1eA2A2SbS0S1S1S13S12VA0;A1A1S7R3S4Z2M0Z20A2M1A2A2M2S3G1S4G0Z1dA2A2A2R2A2S2R2S1G2G1A2A2A2SeS35R3A1A1F_;F_;Fz;Fc';").
Proof.
  intros c' z Hc' Hz [Hc|Hc]; [exact (NFA c' z Hc' Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & ST & _). clear -Hz ST Hc'. lia.
Qed.
Lemma CHF : ltac2:(tb__ "0|0|
S11S35R1A1ScS29S53S12VA0;A1R2A2S2dA3F_;Fz;").
Proof. intros z [Hc|Hc]; [exact (LZF z Hc)|]. pose proof HA0 as (HG & _). apply fs_footb_T; [exact HG | pose proof (XZT z Hc); lia]. Qed.
Lemma AGm : ltac2:(tb__ "0|0|
S11SeS35R1A1A1ScS28S25Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m', m, maskv. rewrite (VO z Hz). reflexivity. Qed.
Lemma CHm : ltac2:(tb__ "0|0|
S11S35R1A1ScS28S25Q8A1A1Vm';R2A1Vv';R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m'. apply maskv_out. exact (CHF z Hz). Qed.
Lemma CELL : ltac2:(tb__ "0|0|
S11S2fS11S2fS65R1R3A2SeS35S1R5SaR2A1A2A1A1F_;Fk;S43Vm;S44R4R3R2A3A2S43Vm';S44R5R4R3A3A2F_;F_;Fx;Fw;Fa;").
Proof. intros a w x Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). Qed.
Lemma PRES_AG : ltac2:(tb__ "0|0|
S11S11S11SbS0R3R1A2S2R1R2A2A2SeS35R2A1A1F_;Fz;S41Vm;R3R2A3S41Vm';R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi Hn Hp z Hz. rewrite (AGm z (Hn z Hz)). exact (Hp z Hz). Qed.
Lemma PRES_CH : ltac2:(tb__ "0|1|
S11S35R1A1SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1SfS25Q8A1M0G0ScS28G0A1Vm';R4A1S2aG0R1A2A3Lb;A2F_;F_;Fz;").
Proof. intros z Hc Hu. rewrite (CHm z Hc). destruct Hc as [Hc|Hc]; [exact (PRES z Hc Hu) | exact (PRESXZ z Hc)]. Qed.
Lemma NBAND_UX : ltac2:(tb__ "0|0|
S11SbS0Z7fff7000R1A2S2R1Z10007fff8000A2A2SeVXZ;R2A1A1F_;Fz;").
Proof. intros z Hz Hx. pose proof (XZT z Hx) as X. pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _). clear -Hz X TB. lia. Qed.
Lemma PRES_SH : ltac2:(tb__ "0|0|
S11S11S11SbS0R3R1A2S2R1R2A2A2SbS0Z7fff7000R2A2S2R2Z10007fff8000A2A2F_;Fz;S41Vm;R3R2A3S41Vm';R4R3A3F_;F_;Fhi;Flo;").
Proof.
  intros lo hi Hb Hp z Hz. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (Hp z Hz)].
  exact (PRES_CH z Hc (NBAND_U z (Hb z Hz))).
Qed.
Lemma PRESB : ltac2:(tb__ "0|1|
S11S11S54Vm;R2R1S16VA;A1M0A4S54Vm';R3R2G0A4F_;Fhi;Flo;").
Proof.
  intros lo hi Hp z Hz HL. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (Hp z Hz HL)].
  apply (PRES_CH z Hc). intros Hu. apply HL. exists p, n. split; [exact HLin | exact Hu].
Qed.

Lemma HAn : ltac2:(tb__ "0|1|
SbS5aS12VA0;A1M0A1SbS47Vv;G0A2SbS57S46S53G0A1Vv;A2VA;A2SbS5fVm;VA;A2SbS5cVsegs;VA;Vtp;Vmd;A4SbS5bVA;A1S59Vv;Vtp;A2A2A2A2A2A2A2").
Proof. pose proof HA as X. unfold AInvQC in X. cbn zeta in X. rewrite EG in X. exact X. Qed.

Lemma HRTC : rtc_inv v' G.
Proof.
  pose proof HAn as (HG & HR & _). unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & F1 & F2 & FT & FS & FB & C1 & C2 & TC & SC & D1 & D2 & TD & SD).
  pose proof CZI0 as (I1 & I2 & I3 & I4 & I5 & _). rewrite FS_total_val in I4.
  destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
  - exact (NIMGX z K).
  - apply NTPX. clear -K. lia.
  - apply (NOUTX (ag_ctx G) (ag_ctx G + 4096) z); [clear -K; lia | exact I2 | exact (proj1 (proj2 (proj2 (geom_bands _ HG)))) | clear -TC; lia | exact SC].
  - apply (NOUTX (ag_dtls G) (ag_dtls G + 4096) z); [clear -K; lia | exact I3 | exact (proj1 (proj2 (proj2 (proj2 (geom_bands _ HG))))) | clear -TD; lia | exact SD].
  - apply (NOUTX (ag_fsb G) (ag_fsb G + 11571200) z); [clear -K; lia | exact I4 | exact FB | clear -FT; lia | exact FS].
Qed.
Lemma HFS : ltac2:(tb__ "0|0|
S57S46S53S12VA0;A1A1Vv';A2VA;A2").
Proof.
  pose proof HAn as (_ & _ & HF & _). rewrite (restrictv_ext (fs_footb G) v v') by (intros z Hz; apply VO; intros Hc; rewrite (CHF z Hc) in Hz; discriminate).
  exact HF.
Qed.
Lemma SH_band : ltac2:(tb__ "0|0|
S11S11S11S0Z0R3A2S0R3Z7fffff800007A2SbS0S4aR5A1R3A2S2R3S4aR4A1A2A2SbS0Z7fff7000R4A2S2R4Z10007fff8000A2A2F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H0 H1 Hz. unfold Sh, SHADOW_OFF in Hz. pose proof (Z.div_pos lo 8 H0 ltac:(lia)). pose proof (Z.div_le_mono hi 140737479966727 8 ltac:(lia) H1) as X.
  change (140737479966727 / 8) with 17592184995840 in X. lia.
Qed.
Lemma HLB : live_block_reprC m' A.
Proof.
  pose proof HAn as (_ & _ & _ & (Hsep & Hlive & _) & _). intros b sz Hin H2'.
  assert (CASE : (b, sz) = (p, n) \/ In (b, sz) (l1 ++ l2)).
  { rewrite EL, HLV in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|Hin]]; [right; apply in_or_app; left; exact Hin | left; symmetry; exact E | right; apply in_or_app; right; exact Hin]. }
  destruct CASE as [E|Hin'].
  - injection E as -> ->. apply BODY. rewrite <- (CHm (p - 16)); [exact H2' | left; left; clear; lia].
  - pose proof (fun z Hz HC => F0A_rebuild.CZ_live A0 rho0 tp0 md0 p n l1 l2 1 HA0 HLV HCLS ltac:(clear; lia) b sz z Hin' Hz HC) as NO0.
    assert (NO : forall z, (b - rz sz <= z < b + sz \/ Sh b <= z < Sh b + (sz + 7) / 8) -> ~ CH z).
    { intros z Hz [Hc|Hc]; [apply (NO0 z Hz); unfold F0A_rebuild.CZ; destruct (LZ_cases z Hc) as [K|K]; [left | right]; exact K|].
      destruct (Hsep b sz Hin) as (L1' & L2' & L3' & _ & _ & _ & _ & L8'). rewrite EG in L3'. pose proof (XZT z Hc) as X.
      destruct Hz as [Hz|Hz].
      - assert (HinA0 : In (b, sz) (aa_live A0)) by (rewrite <- EL; exact Hin). destruct (in_split _ _ HinA0) as (k1 & k2 & Hsplit).
        pose proof (N8_facts sz L1') as (NB1 & _).
        exact (proj1 (F0A_rebuild.CZA A0 rho0 tp0 md0 b sz k1 k2 0 HA0 Hsplit L8' z ltac:(clear -Hz NB1; lia)) ltac:(clear -X; lia)).
      - pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _ & TG' & _).
        assert (SHB : 2147446784 <= z < 17594333495296).
        { apply (SH_band b (b + sz + 7) z); [unfold IMG_HI in L2'; clear -L2'; lia | clear -L3' TG'; lia|]. split; [exact (proj1 Hz)|].
          eapply Z.lt_le_trans; [exact (proj2 Hz)|]. apply RebuildRZ.Sh_add_le; [unfold IMG_HI in L2'; clear -L2'; lia | clear -L1'; lia | clear; lia]. }
        clear -SHB X TB. lia. }
    destruct (Hsep b sz Hin) as (L1 & _). pose proof (rz_bound sz) as RB.
    assert (H2 : m (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- AGm by (apply NO; left; clear -L1 RB; lia); exact H2').
    destruct (Hlive b sz Hin H2) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    pose proof (Z.div_le_mono sz (sz + 7) 8 ltac:(lia) ltac:(lia)) as DL. pose proof (Z.div_pos sz 8 ltac:(lia) ltac:(lia)) as D0.
    split; [exact H2'|].
    split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B2]|].
    split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B3]|].
    split; [split|split].
    + intros g Hg. rewrite AGm by (apply NO; right; lia). exact (B4 g Hg).
    + intros Hm. rewrite AGm; [exact (B5 Hm)|]. apply NO. right.
      replace ((sz + 7) / 8) with (sz / 8 + 1) by (apply Z.div_unique with (sz mod 8 - 1); [pose proof (Z.mod_pos_bound sz 8); lia | pose proof (Z.div_mod sz 8); lia]). lia.
    + apply (alloc_magic_ok_agree m m' b sz); [|lia|exact B6]. intros z Hz. apply AGm. apply NO. left. lia.
    + destruct B7 as (tb & Ht' & Hm4). exists tb. split; [|exact Hm4]. rewrite AGm by (apply NO; left; lia). exact Ht'.
Qed.
Lemma HPR : primary_repr m' A.
Proof.
  pose proof HAn as (HG & _ & _ & (_ & _ & (PL & P0 & P31 & PC) & _) & _). unfold primary_repr. rewrite EG.
  split; [exact PL|]. split; [exact P0|]. split; [exact P31|]. intros c Hc. pose proof (PC c Hc) as PCc. rewrite EG in PCc.
  pose proof PCc as PCd. unfold class_repr in PCd.
  destruct PCd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & N6 & _ & _ & _ & PU & PS & _).
  destruct GEO0 as (_ & _ & SB1 & SB2 & _ & _ & _ & _ & _ & TG & _).
  apply (class_repr_agree_pres m m' G A c _ Hc); [| | | exact PCc].
  - intros z [Hz|[Hz|Hz]]; apply AGm.
    + apply NMETAX. unfold region_info, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz. clear -Hz Hc. lia.
    + apply (NFAX c z Hc). unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. clear -Hz N6. lia.
    + apply NTPX. clear -Hz Hc. lia.
  - apply PRESB. exact PU.
  - apply PRES_SH; [|exact PS]. intros z Hz. apply (SH_band _ _ z) in Hz; [exact Hz | |];
      unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *; clear -N2 N3 SB1 SB2 TG Hc; lia.
Qed.

Lemma HSR : secondary_repr m' A.
Proof.
  pose proof HAn as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & Hsec & _).
  unfold secondary_repr in Hsec |- *. rewrite EG, ES in Hsec |- *.
  destruct Hsec as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  assert (CI : forall cc, IMG_LO <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= IMG_HI -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_agree. intros k Hk. apply AGm. apply NIMGX. lia. }
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI0 as (_ & _ & _ & _ & I5' & _ & _ & I8' & _).
  pose proof HA0 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). destruct (F0A_rebuild.SG3_pab A0 rho0 tp0 md0 HA0) as [PAB3 PABT3].
  pose proof S45 as [S4m (S4a & _ & S4t & _ & S4b)]. unfold kPtrArrayReserve in *.
  unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S4b.
  assert (NPAB : forall z, ag_pab G <= z < ag_pab G + 2 ^ 23 -> ~ CH z).
  { intros z Hz. apply (NOUTX (ag_pab G) (ag_pab G + 2 ^ 23) z Hz); [exact I5' | exact S4b | clear -PABT3; lia | exact PAB3]. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. pose proof D10 as (D10a & _ & _ & _ & WB).
    destruct (SEC3 i ch Hi) as (X1 & X2 & _). rewrite kSpaceSize_val in X1.
    assert (NH : forall z, sc_map_beg ch <= z < sc_map_beg ch + 32 -> ~ CH z).
    { intros z Hz. apply (NOUTX (sc_map_beg ch) (sc_map_beg ch + 32) z Hz (I8' i ch Hi));
        unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; clear -WB X1 X2 D8 D9 MB; lia. }
    assert (CA : forall off w x, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w x) -> cell_ok m' (mkACell (sc_map_beg ch + off) w x)).
    { intros off w x Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NH. clear -Ho Hw Hk. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split.
    { eapply cell_ok_agree; [|exact C5]. cbn [c_addr c_w]. intros k Hk. apply AGm. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
      apply NPAB. clear -Hk L S2. lia. }
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [apply PRESB; exact D13 |].
    apply PRES_SH; [|exact D14]. intros z Hz. apply (SH_band _ _ z) in Hz; [exact Hz | unfold IMG_HI in MB; clear -MB; lia | clear -D12 TG; lia]. }
  split; [apply PRES_AG; [|exact SP]; intros z Hz; apply NPAB; clear -Hz S2; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST, IMG_LO, IMG_HI in *.
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [apply PRES_AG; [|exact I7]; intros z Hz; apply NIMGX; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I8]|].
  apply PRES_AG; [|exact I9]. intros z Hz. apply NIMGX. unfold IMG_LO, IMG_HI. clear -Hz. lia.
Qed.

Lemma HIA : ia_inv m' A.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & Hia & _).
  refine (ia_inv_agree m m' A A eq_refl _ Hia). intros z Hz. apply AGm. exact (NIMGX z Hz).
Qed.
Lemma HTI : thread_inv m' G.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). rewrite EG in HTH. destruct HTH as [TH1 TH2]. split.
  - rewrite AGm; [exact TH1|]. apply NTPX. clear. lia.
  - intros z Hz. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (TH2 z Hz)].
    apply (PRES_CH z Hc). intros Hu. destruct Hc as [Hc|Hc]; [exact (NTP z ltac:(clear -Hz; lia) Hc)|].
    pose proof BLK0 as (_ & _ & _ & _ & B5 & _ & _ & B8 & _). assert (K : p - rz n <= z < p + N8 n) by (clear -Hu B5 B8; lia). exact (proj1 (CZA0 z K) ltac:(clear -Hz; lia)).
Qed.
Lemma HMI : misc_inv m'.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & Hmisc).
  refine (misc_inv_agree m m' _ Hmisc). intros z Hz. apply AGm. exact (NIMGX z Hz).
Qed.
Lemma HDEP : depot_wf m' A.
Proof.
  pose proof HAn as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & Hdep & _).
  pose proof HA0 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & DEP3 & _).
  unfold depot_wf in Hdep |- *. rewrite ED in Hdep |- *. eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI0 as (_ & _ & _ & _ & _ & _ & I7 & _).
  assert (BLK' : forall bb L, In (bb, L) (dblocks (aa_depot A0)) -> bb <= a < bb + L -> ~ CH a).
  { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & DT & _ & _ & _ & SS & _). unfold sepZ in DT, SS. cbn [fst snd] in DI, DT, SS.
    destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
    exact (NOUTX bb (bb + L) a Hab (I7 bb L Hbb) WB ltac:(clear -DT; lia) ltac:(clear -SS; lia)). }
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply NIMGX. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
  - apply (BLK' bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
  - apply (BLK' bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
Qed.
Lemma HBTP : bandtp_inv v' tp.
Proof.
  pose proof HAn as (_ & _ & _ & _ & _ & _ & HB). eapply bandtp_mono; [|exact HB]. intros z Hz Hd.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hz.
  destruct (CH_dec z) as [Hc|Hn]; [|rewrite (VO z Hn); exact Hd].
  destruct Hc as [Hc|Hc]; [|exfalso; exact (NBAND_UX z Hz Hc)].
  destruct (PRES z Hc (NBAND_U z Hz)) as [b Hb]. rewrite Hb. discriminate.
Qed.

Theorem limbo_in : ltac2:(tb__ "0|0|
S5eVA;Vrho';Vtp;Vmd;A4").
Proof.
  pose proof HAn as (HG & _ & _ & (R1 & _ & _ & _ & (R5 & R5m) & _) & HM & HI3 & _).
  unfold AInvQC. cbn zeta. rewrite EG. fold segs. fold v'. fold m'.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split; [|exact (conj HM (conj HI3 HBTP))].
  split; [exact R1|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|].
  split; [split; [exact R5|]; apply CELL; [|exact R5m]; intros k Hk; apply NIMGX; unfold QG, IMG_LO, IMG_HI; cbn in Hk; clear -Hk; lia|].
  split; [exact HDEP|]. split; [exact HIA|]. split; [rewrite EG; exact HTI | exact HMI].
Qed.
End LIMBO.

Theorem AInvQC_frame_top : ltac2:(tb__ "0|0|
S1aS3cS3cS2bS25Q40A1A1S60S5eR5R4R2R1A4S11S2R1S19S12R7A1A1A2ScS28S25Q8A1A1S40S63S3bR6A1R2A3S40S63S3bR7A1R2A3A3F_;Fz;S5eR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvQC in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view InvLaws.segsA (rm rho)) in *. set (m' := view InvLaws.segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  pose proof (geom_old _ HG) as (_ & F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & _ & S1 & S2 & _). fold G in F1, F2, T1, T2, C1, C2, D1, D2, S1, S2.
  pose proof (topG_range G) as TG.
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).
  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros z Hz _; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zimg' : forall z, IMG_LO <= z < IMG_HI -> m' z = m z) by (intros z Hz; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz S2; lia).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz T2; lia).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz C2; lia).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz D2; lia).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros z Hz; apply AV; clear -Hz F2; lia).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z).
  { intros z Hz. apply AV. destruct HPAB as [_ (_ & _ & P3 & _)]. clear -Hz P3. lia. }
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply AV. destruct (In_nth_error _ _ Hch) as [i Hi]. destruct R4 as [S1' _].
    destruct (S1' i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & _). fold G in D12. clear -Hz D12. lia. }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z).
  { intros z Hz. apply AV. unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. clear -Hz TG. lia. }
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  { replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. unfold fs_footb in E. cbn zeta in E.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4.Sh_lt_HSE (ag_fsb G + FS_total) ltac:(clear -F2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
    apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [_ E]; apply Z.ltb_lt in E; rewrite ?FS_total_val in *; clear -E F2 SL TG; lia. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].
  Ltac zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split.
  {
    intros b n Hin H2'. destruct (R1 b n Hin) as (S1' & S2' & S3' & _). pose proof (rz_bound n) as RZ. pose proof HI3 as (_ & LIV3 & _).
    assert (CZ : (forall z, b - rz n <= z < b -> mk' z = mk z) /\ b + n + 7 < 2 ^ 47).
    { apply (chunk_zone G (aa_sec A) mk mk' (fun z Hz => MK z (Zsp z Hz)) (fun ch z Hch Hz => MK z (Zsec ch z Hch Hz)) HG A b n eq_refl eq_refl R3 R4 ltac:(unfold IMG_HI in *; clear -S2'; lia) ltac:(clear -S1'; lia)).
      - intros EP. destruct R3 as (_ & _ & _ & P4). fold G in P4.
        pose proof (primary_cls n ltac:(clear -S1'; lia) EP) as Hc. pose proof (P4 _ Hc) as X. cbn zeta.
        destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
        exact (LV b n Hin EP eq_refl).
      - intros EP. destruct (LIV3 b n Hin) as [X|X]; [rewrite EP in X; discriminate X | exact X]. }
    destruct CZ as [BEL UB].
    assert (H2 : mk (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- BEL by (clear -RZ; lia); exact H2').
    destruct (R2 b n Hin H2) as (L1 & L2 & L3 & L4 & L5 & L6).
    split; [exact H2'|].
    split; [eapply (cell_ok_agree mk mk'); [cbn [c_addr c_w]; intros k Hk; apply BEL; clear -Hk RZ; lia | exact L2]|].
    split; [eapply (cell_ok_agree mk mk'); [cbn [c_addr c_w]; intros k Hk; apply BEL; clear -Hk RZ; lia | exact L3]|].
    split.
    - destruct L4 as [L4a L4b]. unfold IMG_HI in *. pose proof (div8_superadd b (n + 7) ltac:(clear -S2'; lia) ltac:(clear -S1'; lia)) as D8.
      pose proof (Z.div_pos n 8 ltac:(clear -S1'; lia) ltac:(clear; lia)). pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)).
      split.
      + intros g Hg. rewrite (AGsh mk mk' (fun z Hz => MK z (Zband z Hz)) b (b + n + 7)); [exact (L4a g Hg) | clear -S2'; lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; clear -Hg D8 H H0; lia].
      + intros Hn. rewrite (AGsh mk mk' (fun z Hz => MK z (Zband z Hz)) b (b + n + 7)); [exact (L4b Hn) | clear -S2'; lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; clear -D8 H H0; lia].
    - split; [eapply alloc_magic_ok_z; [exact BEL | exact L5]|].
      destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite BEL by (clear -RZ; lia); exact Ht | exact Hm4]. }
  split; [eapply (primary_repr_z G mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split.
  { split; [exact R5|]. eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply MK. apply Zimg'. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  split.
  { pose proof HI3 as (_ & _ & _ & _ & DEP3 & _). unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a Ha. apply MK.
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply Zimg'. exact (dstat_img a Hs).
    - apply AV. destruct (DEP3 (bb, NBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia.
    - apply AV. destruct (DEP3 (bb, FBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia. }
  split; [eapply (ia_inv_z mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Definition LZ0b (p n z : Z) : bool := ltac2:(tb__ "0|3|
S34S34S30S8S3Vp;Z10A2Vz;A2S9Vz;S3Vp;Z8M0A2A2A2S30S8Vp;Vz;A2S9Vz;S1Vp;S49Vn;A1M1A2A2A2A2S30S8S4aVp;A1M2Vz;A2S9Vz;S1G2S6G1G0A2A2A2A2A2").
Lemma LZ0b_spec : ltac2:(tb__ "0|0|
S11S11S11S10ScS29S38R3R2R1A3S31A3S36R3R2R1A3A2Fz;Fn;Fp;").
Proof. intros p n z. unfold LZ0b, LZ0. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto. Qed.
Definition rho_mid (zb : Z -> bool) (rho rho' : valuation) : valuation := ltac2:(tb__ "0|1|
S3dS3fVrho;A1S3eVrho;A1S25Q40M0A1S29S28S25Q8A1A1L_;Vzb;S27G0R1A2A1S3bVrho';R1A2S3bVrho;R1A2X29x2La;A3").
Lemma view_mid : ltac2:(tb__ "0|1|
S11S29F_;S3cS3cS11ScS28S25Q8A1A1M0S40S48S3bS3aR4R3R2A3A1R1A3S29G0L_;R4R1A1S40S48S3bR2A1R1A3S40S48S3bR3A1R1A3X29x2A3Fz;Frho';Frho;Fzb;").
Proof.
  intros zb rho rho' z. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  - rewrite !view_in by lia. unfold rd_of, rho_mid. cbn [rm]. rewrite u64_lit by lia. destruct (zb z); reflexivity.
  - rewrite !view_out by lia. destruct (zb z); reflexivity.
  - rewrite !view_out by lia. destruct (zb z); reflexivity.
Qed.

Lemma lb_body_agree : ltac2:(tb__ "0|1|
S42S42S1aS11S11S0Z1R1A2S11SdSbS0S3R4S4bR3A1A2R1A2S2R1S1R4R3A2A2A2SbS0S4aR4A1M0R1A2S2R1S1G0S6S1R3Z7A2Z8A2A2A2A2A2ScS28S25Q8A1A1R7R2A1R8R2A1A3F_;Fz;S37R7R4R3A3S37R7R5R4A3F_;F_;F_;Fn;Fb;FA;Fmb;Fma;").
Proof.
  intros ma mb A b n Hn AG HB.
  set (A1 := mkAA (aa_geom A) (aa_cls A) (aa_cache_inited A) (aa_sec A) (aa_ptr_committed A) [(b, n)]
                  (aa_q_thread A) (aa_q_global A) (aa_depot A) (aa_fs_hint A) (aa_fs_busy A) (aa_internal_inited A) (aa_V A) (aa_Km A) (aa_Kf A)).
  assert (L1 : live_block_repr ma A1) by (intros b0 n0 [E|[]]; injection E as <- <-; exact HB).
  assert (L1' : live_block_repr mb A1).
  { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP.live_block_repr_agree ma mb A1 A1 eq_refl); [| |exact L1].
    - intros b0 n0 z [E|[]] Hz. injection E as <- <-. exact (AG z Hz).
    - intros b0 n0 [E|[]]. injection E as <- <-. exact Hn. }
  exact (L1' b n (or_introl eq_refl)).
Qed.

Theorem AInvQC_limbo_top : ltac2:(tb__ "0|c|
S1aS3cS2bS25Q40A1A1M0S60S11S11S2bS2cS11S11A2M1A1M2G2S1aS3cS3cG0S60S11S29F_;S55S48ReRdRcRbA5ScG2S16RfA1S32G1R9S33G1S2eS11S11RbRaA4R8A3A3A3S66RcRbA2ScS1dS12R9A1S12R11A1A3ScS2bS15A1S18RaA1S18R12A1A3ScS21S17RbA1S17R13A1A3ScG2S16RcA1S16R14A1A3S5eRdRcRaR9A4S11ScS29RaR1A1S31A3SdSbS0S1S14S12R18A1M3A1M4Z50A2R2A2S2R2S1G4Z70A2A2A2SbS0S1G4Za80A2R2A2S2R2S1G4Zc60A2A2A2A2F_;Fz;S11S2R1S19G3A1A2SeS36R15R14R2A3A1ScS29RdR3A1S2dA3ScS28S25Q8M5A1M6A1M7S40S48S3bR11A1M8R4A3S40S48S3bR12A1M9R4A3MaA3F_;F_;F_;Fz;S11S36R15R14R1A3SeSbS0R16R2A2S2R2S1R16R15A2A2A2A1SfG6G6ScG7GaS2aG6R1A2MbA3Lb;A2F_;F_;Fz;S11ScS29RdR1A1S31A3SfG6G6ScG7S40S48G9R3A3GbA3Lb;A2F_;Fz;ScG7S40S48S3bR10A1S3R16Z10A2A3S2aG6S26G5Z2A2A2A3S37S45S53S12R1bA1A1S40S48G8A2A2R17R16A3F_;S5eR13R11R10RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fxzb;Fmd;Ftp;Frho';Frho;FA;Fl2;Fl1;Fn;Fp;Fmd0;Ftp0;Frho0;FA0;").
Proof.
  intros A0 rho0 tp0 md0 p n l1 l2 A rho rho' tp md xzb HA0 HLV HCLS EG ES ED EL HA XZT VO PRES PRESXZ BODY.
  set (zb := fun z => LZ0b p n z || xzb z). set (rmid := rho_mid zb rho rho').
  assert (VM : forall z, view segsA (rm rmid) z = if zb z then view segsA (rm rho') z else view segsA (rm rho) z) by (intros z; apply view_mid).
  assert (ZB : forall z, zb z = true <-> (LZ0 p n z \/ xzb z = true)).
  { intros z. unfold zb. rewrite orb_true_iff, LZ0b_spec. tauto. }
  assert (VMin : forall z, (LZ0 p n z \/ xzb z = true) -> view segsA (rm rmid) z = view segsA (rm rho') z).
  { intros z Hz. rewrite VM. rewrite (proj2 (ZB z) Hz). reflexivity. }
  assert (VMout : forall z, ~ (LZ0 p n z \/ xzb z = true) -> view segsA (rm rmid) z = view segsA (rm rho) z).
  { intros z Hz. rewrite VM. destruct (zb z) eqn:E; [exfalso; exact (Hz (proj1 (ZB z) E)) | reflexivity]. }
  pose proof (F0A_rebuild.BLK A0 rho0 tp0 md0 p n l1 l2 0 HA0 HLV HCLS) as (_ & _ & B3 & B4 & B5 & B6 & _).
  pose proof (F0A_rebuild.GEO A0 rho0 tp0 md0 n 0 HA0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  assert (VMall : forall z, z < topG (aa_geom A0) -> view segsA (rm rmid) z = view segsA (rm rho') z).
  { intros z Hz. destruct (LZ0_dec p n z) as [Hc|Hn]; [exact (VMin z (or_introl Hc))|]. destruct (xzb z) eqn:EX; [exact (VMin z (or_intror EX))|].
    rewrite (VMout z ltac:(intros [X|X]; [exact (Hn X) | rewrite EX in X; discriminate X])). symmetry. exact (VO z Hz Hn EX). }
  assert (HMID : AInvQC A rmid tp md).
  { assert (XZD : forall z, xzb z = true \/ ~ xzb z = true) by (intros z; destruct (xzb z); [left; reflexivity | right; discriminate]).
    apply (limbo_in A0 rho0 tp0 md0 p n l1 l2 HA0 HLV HCLS A rho rmid tp md EG ES ED EL HA (fun z => xzb z = true) XZT XZD VMout).
    - intros z Hz Hu. rewrite (VMin z (or_introl Hz)). exact (PRES z Hz Hu).
    - intros z Hz. rewrite (VMin z (or_intror Hz)). exact (PRESXZ z Hz).
    - intros H2. rewrite (VMin (p - 16) ltac:(left; left; clear; lia)) in H2.
      apply (lb_body_agree (maskv (fs_footb (aa_geom A0)) (view segsA (rm rho'))) _ A p n B3); [|exact (BODY H2)].
      intros z Hz. unfold maskv. rewrite VMall; [reflexivity|].
      destruct Hz as [Hz|Hz]; [clear -Hz B4 B5; lia|].
      assert (E8 : (n + 7) / 8 = N8 n / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity).
      rewrite E8 in Hz. pose proof (proj1 (SHZ A0 rho0 tp0 md0 p n l1 l2 HA0 HLV HCLS z Hz)) as X. clear -X TG. lia. }
  apply (AInvQC_frame_top A rmid rho' tp md HMID). intros z Hz. rewrite EG in Hz. symmetry. exact (VMall z Hz).
Qed.
End F0A_limbo.

