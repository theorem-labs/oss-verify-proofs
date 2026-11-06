(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx DepotCall.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.

(* [comment removed for export] *)
Module SpineCallocSecI.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecI"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_null"; "JLc_null"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
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
S2S19S32S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S4S23S0S1Z2M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S2S19S32S35Ufa0S16S2eZ5e5d4S17S2eA1A3S34S16S4S22S0S1Z2M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z2A3S1cSaS61S3fS77SaS76S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 2) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z2A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S3aS0S1Z2M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS75A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 2) memo_10. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z2M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. memo_rw (stKn W0 st0 2) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z2M0A3S5cS0S1A2S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 2) memo_11. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S74S39S0S1Z2A3A1S1bA3"). Proof. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S23S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 2) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S30S31S23S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S22S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 2) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e5d4S17S2eA1A3S34S16S30S31S22S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.SpineCallocSecIW1"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_null"; "JLc_null"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
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
S2S19S32S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S4S23S0S1Z3M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 3) memo_3. memo_rw (ES1 W0 st0 3) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S2S19S32S35Ufa0S16S2eZ5e5d4S17S2eA1A3S34S16S4S22S0S1Z3M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 3) memo_6. memo_rw (ESn W0 st0 3) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z3A3S1cSaS61S3fS77SaS76S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 3) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z3A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 3) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S40S5S3aS0S1Z3M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS75A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 3) memo_10. memo_rw (stRn_S W0 st0 3) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z3M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 3) memo_9. memo_rw (stKn W0 st0 3) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z3M0A3S5cS0S1A2S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 3) memo_11. memo_rw (s_n W0 st0 3) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S74S39S0S1Z3A3A1S1bA3"). Proof. memo_rw (s_n W0 st0 3) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S23S0S1Z3A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 3) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S30S31S23S0S1Z3M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 3) memo_3. memo_rw (ES1 W0 st0 3) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6bS34SdS5S22S0S1Z3A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 3) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e5d4S17S2eA1A3S34S16S30S31S22S0S1Z3M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 3) memo_6. memo_rw (ESn W0 st0 3) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.DepotCallI.INST"; "T4_i"; "s4_i"; "R4_i"; "pm__15"; "pm__16"; "pm__10"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__9"; "sd_i"; "pm__0"; "pm__1"; "pm__2"; "pm__25"; "pm__26"; "pm__3"; "pm__4"; "pm__5"; "pm__6"; "pm__7"; "pm__8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "nil"; "cons"; "option"; "pair"; "Some"; "false"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sstate"; "ss_facts"; "sobj"; "ss_next"; "SVar"; "ss_objs"; "SPUle"; "sprop_below"; "SAlu"; "valuation"; "SExt"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "X4"; "omrg"; "T4d"; "X4r"; "oreb"; "T40"; "T4a"; "T4b"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "X4a"; "X4b"; "X4c"; "KEEPD"; "X4f"; "perm4"; "F_call"; "coveredb"; "in_famb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E4d"; "C5"; "F_gen"; "V_CNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cst_ok"; "in_rangesZ"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE"; "HDE_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "HD_stmt"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
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

Ltac PM_sub0 t := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t.
Ltac PM_all0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "proj1"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "prod"; "andb"; "app"; "pair"; "Some"; "cons"; "false"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "sobj"; "SAlu"; "SLit"; "ss_facts"; "SVar"; "sprop_below"; "ss_next"; "valuation"; "sprop_eqb"; "ss_objs"; "rw"; "eval"; "sv_eqb"; "agree_below"; "holds"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_okPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "chain_pre"; "free_depth"; "F_depth"; "Wcan"; "ulink"; "UStopLe"; "V_DEPTH"; "client_addrA"; "client_shadowA"; "top_high"; "unwind_stopJ"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "coveredb"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "rd_okb"; "rng_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "opp"; "modulo"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "view"; "@stdpp.bitvector.definitions"; "bv"; "bv_signed"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot.FD.SITE"; "site_factsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "isnil"; "dchkb"; "tjv_ok"; "dchkb_sound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "HDF"; "HDFE"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_depot"; "aa_geom"; "aa_live"; "aa_sec"; "qbatch"; "aa_internal_inited"; "aa_q_thread"; "ag_thread"; "ageom"; "sec_chunk"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKF"; "KD"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "junkF"; "rhoF_of"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "JLD"; "DFP"; "JD";
"dfp_static"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "instF_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone.
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
Module F0A_x0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "ss_next"; "ss_objs"; "SLit"; "SVar"; "ss_facts"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "option"; "app"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_x0A"; "XR_0A"; "XM_0A"; "REST_0A"; "XK_0A"; "sX_0A"; "XEX_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "q_0A"; "Xf_0A"; "W_0A"; "st_0A"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nkeep"; "nocellsF"; "FQX"; "rcellb"; "rclsb"; "rshpb"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "A_globals"; "L_free"; "stack_win"; "unwind_objs"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A.
Import ListNotations.
Open Scope Z_scope.

Definition XEX_0A : list axform := XEX_of Xf_0A.
Definition XM_0A : axst := XM_of Xf_0A.
Definition XK_0A : axst := XK_of 0 XM_0A.
Definition REST_0A : list sobj := REST_of 0 XM_0A.
Definition XR_0A : axst := XR_of XK_0A.
Definition sX_0A : wsub := sX_of XR_0A W_0A st_0A.

Ltac vmr := vm_compute; reflexivity.
Lemma AXE_0A : ltac2:(tb__ "0|0|
S0S12SbA1S2fS1fS1dA2S11SbS19A2A3"). Proof. Time vmr. Qed.
Lemma XXM_0A : ax_X XM_0A = []. Proof. vmr. Qed.
Lemma OBJS_0A : ltac2:(tb__ "0|1|
S0S10S1A1S5SaS19A1A1M0S13S1S22S1S24U0A1G0A3S1aA3A3"). Proof. Time vmr. Qed.
Lemma KEEP_0A : ltac2:(tb__ "0|0|
S0S10S1A1S23S1S1S25S22S1S24U0A1S5SaS19A1A1A3A4S23S1S1S25S14S1S35S13S1S36S20A1S33A3A3A4A3"). Proof. Time vmr. Qed.
Lemma EQK_0A : ltac2:(tb__ "0|1|
S0SbScS19S2eSaS19A1M0S22S1S24U0A1S5G0A1A3A2A2S1bA3"). Proof. vmr. Qed.
Lemma WXR_0A : ltac2:(tb__ "0|0|
S0SeS9SaS18A1A1SfA3"). Proof. Time vmr. Qed.
Lemma DXR_0A : ltac2:(tb__ "0|4|
S0S12S17S10S17S3S3A2M0A1M1S10S2A1M2A2M3A1S2cSaS1bA1SaS18A1A2S11G3S16G1G2S14G0S16S3S3S6S31A1S7P18A1A4S15G0A1A3S15S2A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQR_0A : ltac2:(tb__ "0|0|
S0SbScS1bSaS18A1A2S18A3"). Proof. vmr. Qed.
Lemma NXR_0A : ltac2:(tb__ "0|0|
S0S2aS4SaS18A1A1S4SaS1bA1A1A3"). Proof. vmr. Qed.
Lemma ENT_0A : ltac2:(tb__ "0|0|
S0SeSdS18S34S32S20S21A3S1cA3SfA3"). Proof. Time vmr. Qed.
Lemma SID_0A : ltac2:(tb__ "0|0|
S0SeS2dS1cS2bA2SfA3"). Proof. Time vmr. Qed.
Lemma NXF_0A : ltac2:(tb__ "0|0|
S0SeS38S30S4SaS1fA1A1A2SfA3"). Proof. vmr. Qed.

Lemma RCLS_0A : ltac2:(tb__ "0|0|
S0SeS28S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RCIV_0A : rcivb REST_0A = true. Proof. Time vmr. Qed.
Lemma RCELL_0A : ltac2:(tb__ "0|0|
S0SeS27S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma RWR_0A : rwrb REST_0A = true. Proof. vmr. Qed.
Lemma RSHP_0A : ltac2:(tb__ "0|0|
S0SeS29S1eS1aA2SfA3"). Proof. Time vmr. Qed.
Lemma FQS_0A : ltac2:(tb__ "0|0|
S0S12S2A1S37S2S8SaS1fA1A1U0A3S11S2S26S1eA1A2A3"). Proof. vmr. Qed.
Lemma BXM_0A : ax_base XM_0A = base_sv. Proof. vmr. Qed.
End F0A_x0A.

(* [comment removed for export] *)
Module F0A_xi0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "cons"; "false"; "list"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "JL_free"; "KcA"; "L_free"; "Wcan"; "client_addrA"; "client_shadowA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "Xf_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_x0A.
Import ListNotations.
Open Scope Z_scope.

Section XI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S2cVCST;R1A2S2S2cS32R2A2S4S35S33R2A2S36R2S34A2A2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Theorem f0_exit_0A : ltac2:(tb__ "0|4|
S31OF_;S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S30Vsegs;R19S24Vsegs;S27U0M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Proof. exact (f0_exit CST XGL HCST HXGL HCSTF 0%nat UStopLe QA Xf_0A XM_0A XK_0A XR_0A (firstn (nkeep 0) (ss_objs (ax_S XM_0A))) REST_0A sX_0A XEX_0A AXE_0A OBJS_0A EQK_0A WXR_0A DXR_0A NXR_0A EQR_0A ENT_0A SID_0A RCLS_0A RCIV_0A RCELL_0A RWR_0A RSHP_0A FQS_0A). Qed.
Theorem ef0_exit_0A : ltac2:(tb__ "0|4|
S1eS19S5ScS22Q40M0A1A1M1S0S0S0S14S0OF_;S1S0S21G0S6R7PcA2A2R5A3S1S0S21G0S6R8PdA2A2R5A3S2eS8S0S0A2S7S0S0R7R6A4S20RbA1A3S26R8R7A2S1S9S1fRdA1SeA3S15S2aReA2S29RdS12RfRdRbRaR9R8A6A2S1S0S13R9A1S2bA3S0S2S1cVCST;R12R1A3S1dVCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S1eS5S5G1S28R16R4A2S2dRfS12R17R15R13R12R11R10A6R4A3S2fVsegs;S24Vsegs;S27U0M2S16SbR6R17R5A6S25R4R3A5S11Vsegs;S23R16R15SaS8SfS10A2M3S7SfS10S1aS17S1bG2A1S16A3S18VAInv;VCST;VXGL;R18R17A5A4SdG3A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
Proof. exact (ef0_exit CST XGL HCST HXGL HCSTF 0%nat UStopLe QA Xf_0A XM_0A XK_0A XR_0A (firstn (nkeep 0) (ss_objs (ax_S XM_0A))) REST_0A sX_0A XEX_0A AXE_0A OBJS_0A EQK_0A WXR_0A DXR_0A NXR_0A EQR_0A ENT_0A SID_0A RCLS_0A RCIV_0A RCELL_0A RWR_0A RSHP_0A FQS_0A). Qed.
End XI.
End F0A_xi0A.

