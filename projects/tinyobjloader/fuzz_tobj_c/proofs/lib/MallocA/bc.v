(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From Stdlib Require Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.

(* [comment removed for export] *)
Module SegQ3DM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "bool"; "list"; "true"; "app"; "false"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "SVar"; "sobj"; "sprop"; "sv"; "SLit"; "SPBranch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MC"; "MI"; "MRET"; "TsD0M"; "TsDBM"; "TsRCM"; "TsRIM"; "MB"; "MT4"; "PostQ3R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "PD"; "NXR"; "O_mtx00"; "RETR"; "STK"; "SWD"; "cb_cells"; "mkR"; "post_ruR"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DH"; "DI"; "DQCs"; "DQIs"; "DTs"; "RC"; "RI"; "DH0"; "DHn"; "PostQ3Rs"; "TsDB"; "TsRI"; "runD0"; "runDB"; "runDI"; "runDT"; "runRC"; "runRI"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "O_gmax"; "regs3"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM.
Import ListNotations.
Open Scope Z_scope.

Definition PostQ3R0 : axst := ltac2:(tb__ "0|2|
S33S2fS49S4eS34A2S7S12S30S32S31S11Pa0A1M0S11Pa1A1S11Pa2A1S11Pa3A1A4A2S0S12S2eS0S12S4dS2S12A1M1A3A3A3G1S7S13S4aS4cA1S0S13S16S48G0S15Z0A1A3S2S13A1A3A3S2dA6").
Definition MRET : vmap := ltac2:(tb__ "0|2|
S0S3S9S14A2M0S1S9S14Pa0S11Pb8A1A4S0G0S1S9S14Pd0M1S11G1A1A4S2G0A1A3A3").
Definition MT4 : vmap := ltac2:(tb__ "0|0|
S21S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A1").
Definition MB : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A3A3A1").
Definition MI : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pa3S0S9Pa4S0S9Pa5S0S9Pa6S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A1").
Definition MC : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa6S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A1").

Definition TsD0M : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S3SaScA2M0S1SaScS2bS24A4S0G0S1SaScS3dS2aA4S2G0A1A3A3").
Definition TsDBM : list (axst * vmap) := ltac2:(tb__ "0|0|
S35SaS3SaScA2SaS1SaScR1S29A4LT;S40A4").
Definition TsRIM : list (axst * vmap) := ltac2:(tb__ "0|0|
S35SaS3SaScA2SaS1SaScR1S23A4LT;S41A4").
Definition TsRCM : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S3SaScA2M0S1SaScS3eS22A4S0G0S1SaScS3fS24A4S2G0A1A3A3").
Lemma chkD0M : ltac2:(tb__ "0|0|
S1dS4SdS10SbS2cA1A1S42S25A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDBM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS36A1A1S43S26A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDIM : ltac2:(tb__ "0|1|
S1dS4SdS10SbS37A1A1S44S0S3SaScA2M0S1SaScS39S23A4S2G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkRIM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS3cA1A1S47S28A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDTM : ltac2:(tb__ "0|1|
S1dS4SdS10SbS3aA1A1S45S0S3SaScA2M0S1SaScS38S22A4S2G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkRCM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS3bA1A1S46S27A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxPD : ltac2:(tb__ "0|1|
S1eS1dS4S17SbS2cA1M0A1S8A3S4fS4bS10G0A1A2A2"). Proof. exact (proj1 nxsD). Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_D_D0M : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S25A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S2cR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ PD runD0 TsD0M runD0_eq chkD0M (proj1 nxPD) (proj2 nxPD) J rho tp HJ HC). Qed.
Theorem seg_D_DBM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S26A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S36R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ DH runDB TsDBM runDB_eq chkDBM (proj1 (proj1 (proj2 nxsD))) (proj2 (proj1 (proj2 nxsD))) J rho tp HJ HC). Qed.
Theorem seg_D_DIM : ltac2:(tb__ "0|1|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2M0S1SaScR3R2A4S0G0S1SaScS39S23A4S2G0A1A3A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S37R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ DI runDI [(DQIs, MI)] runDI_eq chkDIM (proj1 (proj1 (proj2 (proj2 nxsD)))) (proj2 (proj1 (proj2 (proj2 nxsD)))) J rho tp HJ HC). Qed.
Theorem seg_D_RIM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S28A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3cR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ RI runRI TsRIM runRI_eq chkRIM (proj1 (proj1 (proj2 (proj2 (proj2 nxsD))))) (proj2 (proj1 (proj2 (proj2 (proj2 nxsD))))) J rho tp HJ HC). Qed.
Theorem seg_D_DTM : ltac2:(tb__ "0|1|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2M0S1SaScR3R2A4S0G0S1SaScS38S22A4S2G0A1A3A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3aR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ DTs runDT [(DQCs, MC)] runDT_eq chkDTM (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 nxsD)))))) (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 nxsD)))))) J rho tp HJ HC). Qed.
Theorem seg_D_RCM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S27A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3bR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ RC runRC TsRCM runRC_eq chkRCM (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 nxsD)))))) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 nxsD)))))) J rho tp HJ HC). Qed.
End TR.
End SegQ3DM.

(* [comment removed for export] *)
Module SegQ3M_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "bool"; "prod"; "nil"; "true"; "list"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "ss_next"; "valuation"; "SPBranch"; "SPNot"; "ss_lenient"; "swf"; "SAlu"; "SMd"; "DUnknown"; "cell"; "mkCell"; "mkObj"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "ZQ"; "OH"; "mkR"; "NXR"; "vXK"; "vXL"; "F_R"; "LEXIT"; "LHEAD"; "MERGE"; "SW"; "regsM"; "regsR"; "spR"; "sw_cells"; "vXF"; "vXS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "add"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3M_states"; "MCUTS"; "MC"; "MG"; "MH"; "PM1"; "vMCC"; "vMCS"; "vMNC"; "vMN"; "O_hb"; "SWMe"; "VM"; "objsM"; "regsMH"; "vMC"; "F_MG"; "F_MH"; "MCOPY"; "MHEAD"; "MMRG"; "MRET2"; "SWM"; "TsM0"; "TsMC"; "TsMG"; "TsMH"; "runM0"; "runMC"; "runMG"; "runMH"; "vSRC"; "LM0"; "LMC"; "LMG"; "LMH"; "O_dst"; "O_src"; "O_tlk"; "VM0"; "VMc"; "endC"; "junk_m"; "regsMC"; "regsMG"; "spM"; "swm_cells"; "vCPV"; "vDST"; "vMNN"; "vMNS"; "vMX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "vGN"; "vGS"; "vGF"; "O_gq"; "QG"; "vGB"; "DEPTH_R"; "NX3"; "cbC"; "vMIN"; "vSTKq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_SLL"; "BC_GEU"; "M_MUL"; "ALU_SRL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition MHEAD : Z := 0x3e34c.
Definition MCOPY : Z := 0x3e384.
Definition MMRG : Z := 0x3e398.
Definition MRET2 : Z := 0x3e1d8.
Definition spM : sv := add (SVar 10) (SLit (-96)).
Definition vMC := SVar 160. Definition vMCS := SVar 161. Definition vMCC := SVar 162.
Definition vMN := SVar 163. Definition vMNN := SVar 164. Definition vMNS := SVar 165. Definition vMNC := SVar 166. Definition vMX := SVar 167.
Definition vSRC := SVar 169. Definition vDST := SVar 170. Definition vCPV := SVar 188.

Definition swm_cells (tk tf tl ts : sv) : list cell := ltac2:(tb__ "0|0|
S0S18S19SbN58A1Z8SbS53A1A3S34Vtk;Vtf;Vtl;Vts;A4A3").
Definition SWM (tk tf tl ts : sv) : sobj := ltac2:(tb__ "0|0|
S1aSePaA1SbNa8A1SbZ0A1S6cVtk;Vtf;Vtl;Vts;A4S17A5").
Definition SWMe (e : bool) : sobj := ltac2:(tb__ "0|0|
S3ScLe;Ve;S54S2aS35S2bS36A4S54S26S26S26S26A4X3x2").
Definition O_hb (vb : sv) (n s c : sv) : sobj := ltac2:(tb__ "0|4|
S89Vvb;Z0M0Z18S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8M3A4Vn;A4S0G2S1G1SaS1S1cS2Z8G3A4Vs;A4S0G2S1G1SaS1S1cS2Z10G3A4Vc;A4S5G2A1A3A3A3A4").
Definition O_tlk (v : sv) : sobj := ltac2:(tb__ "0|3|
S89S2bZ0M0Z8S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8A4Vv;A4S5G2A1A3A4").
Definition O_src : sobj := ltac2:(tb__ "0|3|
S89S5dZ0M0Z8S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8A4S6dA4S5G2A1A3A4").
Definition O_dst (cells : list (Z * nat * sv)) : sobj := carved vDST 0 8 cells.
Definition endC : sv := ltac2:(tb__ "0|0|
S3dS3dS47SbZ18A1A2S15S83S46SbZ3A1A3A2").
Definition junk_m : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SaA2M0S1S2SaU6SePacA1A4S0G0S1S2SaU7SePadA1A4S0G0S1S2SaUdSePb0A1A4S0G0S1S2SaU1cSePb4A1A4S0G0S1S2SaU1dSePb5A1A4S0G0S1S2SaU1eSePb6A1A4S0G0S1S2SaU1fSePb7A1A4S5G0A1A3A3A3A3A3A3A3").
Definition regsMH : list sv := ltac2:(tb__ "0|2|
S88S32S8S4S2SaA2M0S0G0S1S2SaU1SbS53A1A4S0G0S1S2SaU2S6bA4S0G0S1S2SaU5S47A4S0G0S1S2SaU8SbS8bS76Za0A2A1M1A4S0G0S1S2SaU9S7bA4S0G0S1S2SaUaG1A4S0G0S1S2SaUbS33A4S0G0S1S2SaUcS71A4S0G0S1S2SaUeS4dA4S0G0S1S2SaUfSbZ3fdA1A4S0G0S1S2SaU10SbZffffffffffffe000A1A4S0G0S1S2SaU11SbZ2000A1A4S0G0S1S2SaU12SbS76A1A4S0G0S1S2SaU13S7cA4S0G0S1S2SaU14S7aA4S5G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S68A3A2").
Definition regsMC : list sv := ltac2:(tb__ "0|1|
S88S4cS0S4S2SaA2M0S1S2SaU6S3dS46S44A2A4S0G0S1S2SaU7S5dA4S0G0S1S2SaUdS45A4S0G0S1S2SaU1cS6eA4S0G0S1S2SaU1dS67A4S5G0A1A3A3A3A3A3A2").
Definition regsMG : list sv := ltac2:(tb__ "0|1|
S88S4cS0S4S2SaA2M0S1S2SaU6S3dS46S44A2A4S0G0S1S2SaUdS45A4S5G0A1A3A3A2").

Definition F_MH (e : bool) : list sprop := ltac2:(tb__ "0|2|
S8SdS8aS78A1S8SdS0SdS12S11S82S72SbZ0A1M0A3A1S0SdS12S11S82S15S86S45SbZdA1A3G0A3A1S5SdA1M1A3A3S3S7SdA1Le;Ve;S0SdS12S11S82S2aG0A3A1G1A3G1X3x2A3A3").
Definition F_MG (e : bool) : list sprop := ltac2:(tb__ "0|0|
S8SdS4fVe;A1S0SdS12S11S87SbZ3fdA1S3dS46S44A2A3A1S5SdA1A3A3").
Definition objsM (e : bool) : list sobj := ltac2:(tb__ "0|1|
S8ScS0ScS75S72S74S77S73A4S0ScS48S4dS47S45S44A4S0ScS48S47S6fS70S46A4S5ScA1M0A3A3A3S3S7ScA1Le;Ve;S0ScS64S26A1G0A3G0X3x2A3").

Definition PM1 : axst := ltac2:(tb__ "0|0|
S28S2fS31S27S30S26S26S26S26A4A1S0ScS75S72S74S77S73A4S0ScS48S74S4dS45S44A4S5ScA1A3A3S8SdS2cS0SdS12S11S84S16S85S73SbZ64A1A3S16S85S72SbZ190000A1A3A3A1S0SdS12S11S84S15S83S72SbZdA1A3S73A3A1S5SdA1A3A3A3S79A6").
Definition MH (e : bool) : axst := ltac2:(tb__ "0|0|
S28S51S4cS27S49Ve;A1A1S4bVe;A1S4fVe;A1S29A6").
Definition MC (e : bool) : axst := ltac2:(tb__ "0|0|
S28S50S69S27S49Ve;A1A1S8ScS4bVe;A1S0ScS63S0ScS62S5S4S4S1cS2A2SaA2A1A1S5ScA1A3A3A3S4eVe;A1S29A6").
Definition MG (e : bool) : axst := ltac2:(tb__ "0|0|
S28S52S6aS27S49Ve;A1A1S4bVe;A1S4eVe;A1S29A6").

Definition MCUTS : list Z := ltac2:(tb__ "0|0|
S0S1cS51S0S1cS50S0S1cS52S0S1cS2eS0S1cS2dS5S1cA1A3A3A3A3A3").
Definition runM0 : list leafA := runA 300 MCUTS PM1.
Definition runMH (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU190S3fS42Ve;A1A3").
Definition runMC (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU64S3fS40Ve;A1A3").
Definition runMG (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU190S3fS41Ve;A1A3").
Lemma runM0_eq : ltac2:(tb__ "0|0|
S21S7S20A1S3cU12cS3fS43A3S59A3"). Proof. unfold runM0. reflexivity. Qed.
Lemma runMH_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU190S3fS42R1A1A3S5cR1A1A3Fe;"). Proof. intros e. unfold runMH. reflexivity. Qed.
Lemma runMC_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU64S3fS40R1A1A3S5aR1A1A3Fe;"). Proof. intros e. unfold runMC. reflexivity. Qed.
Lemma runMG_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU190S3fS41R1A1A3S5bR1A1A3Fe;"). Proof. intros e. unfold runMG. reflexivity. Qed.

Definition VM0 : list positive := ltac2:(tb__ "0|0|
S0S1bPa0S0S1bPa1S0S1bPa2S0S1bPccS0S1bPcdS0S1bPceS0S1bPcfS0S1bPd0S5S1bA1A3A3A3A3A3A3A3A3").
Definition VM (e : bool) : list positive := ltac2:(tb__ "0|1|
S8S1bS0S1bPa0S0S1bPa1S0S1bPa2S0S1bPa3S0S1bPa4S0S1bPa5S0S1bPa6S0S1bPa7S0S1bPccS0S1bPcdS0S1bPceS0S1bPcfS0S1bPd0S5S1bA1M0A3A3A3A3A3A3A3A3A3A3A3A3A3S3S7S1bA1Le;Ve;S0S1bPb8S0S1bPb9S0S1bPbaS0S1bPbbG0A3A3A3A3G0X3x2A3").
Definition VMc (e : bool) : list positive := ltac2:(tb__ "0|0|
S8S1bS4aVe;A1S0S1bPa9S0S1bPaaS0S1bPbcS5S1bA1A3A3A3A3").
Definition LM0 : list axst := Eval vm_compute in (map la_state runM0).
Definition LMHt : list axst := Eval vm_compute in (map la_state (runMH true)).
Definition LMHf : list axst := Eval vm_compute in (map la_state (runMH false)).
Definition LMCt : list axst := Eval vm_compute in (map la_state (runMC true)).
Definition LMCf : list axst := Eval vm_compute in (map la_state (runMC false)).
Definition LMGt : list axst := Eval vm_compute in (map la_state (runMG true)).
Definition LMGf : list axst := Eval vm_compute in (map la_state (runMG false)).
Definition LMH (e : bool) : list axst := if e then LMHt else LMHf.
Definition LMC (e : bool) : list axst := if e then LMCt else LMCf.
Definition LMG (e : bool) : list axst := if e then LMGt else LMGf.
Definition TsM0 : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS65A1A4LT;S5eA4").
Definition TsMH (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS4aVe;A1A1A4LT;S61Ve;A1A4").
Definition TsMC (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS66Ve;A1A1A4LT;S5fVe;A1A4").
Definition TsMG (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS4aVe;A1A1A4LT;S60Ve;A1A4").
Lemma chkM0 : ltac2:(tb__ "0|0|
S21S3S24SfS1eS43A1A1S59S55A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkMH : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS42R1A1A1A1S5cR1A1S58R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma chkMC : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS40R1A1A1A1S5aR1A1S56R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma chkMG : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS41R1A1A1A1S5bR1A1S57R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma nxM : ltac2:(tb__ "0|4|
S22S22S21S3S13S1eS43A1M0A1S9A3S80S3eSfG0A1A2A2S22S3S22S21S3S13S1eS42R1A1A1M1A1S9A3S80S3eSfG1A1A2A2Fe;S22S3S22S21S3S13S1eS40R1A1A1M2A1S9A3S80S3eSfG2A1A2A2Fe;S3S22S21S3S13S1eS41R1A1A1M3A1S9A3S80S3eSfG3A1A2A2Fe;A2A2A2").
Proof.
  split; [split; [reflexivity | unfold Pos.le; cbn; discriminate]|].
  split; [intros [|]; split; [reflexivity | unfold Pos.le; cbn; discriminate | reflexivity | unfold Pos.le; cbn; discriminate]|].
  split; intros [|]; split; first [reflexivity | (unfold Pos.le; cbn; discriminate)].
Qed.
Lemma presM_wf : ltac2:(tb__ "0|3|
S22S21S3S1fS43A1S6A3S22S21S3S14S1eS43A1A1S6A3S22S3S22S21S3S1fS42R1A1M0A1S6A3S21S3S14S1eG0A1A1S6A3A2Fe;S22S3S22S21S3S1fS40R1A1M1A1S6A3S21S3S14S1eG1A1A1S6A3A2Fe;S3S22S21S3S1fS41R1A1M2A1S6A3S21S3S14S1eG2A1A1S6A3A2Fe;A2A2A2A2").
Proof. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. repeat split; destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_M0 : ltac2:(tb__ "0|0|
S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S55A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S43R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ PM1 runM0 TsM0 runM0_eq chkM0 (proj1 (proj1 nxM)) (proj2 (proj1 nxM)) J rho tp HJ HC). Qed.
Theorem seg_MH : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S58R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S42R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 400%nat _ (MH e) (runMH e) (TsMH e) (runMH_eq e) (chkMH e) (proj1 (proj1 (proj2 nxM) e)) (proj2 (proj1 (proj2 nxM) e)) J rho tp HJ HC). Qed.
Theorem seg_MC : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S56R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S40R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 100%nat _ (MC e) (runMC e) (TsMC e) (runMC_eq e) (chkMC e) (proj1 (proj1 (proj2 (proj2 nxM)) e)) (proj2 (proj1 (proj2 (proj2 nxM)) e)) J rho tp HJ HC). Qed.
Theorem seg_MG : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S57R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S41R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 400%nat _ (MG e) (runMG e) (TsMG e) (runMG_eq e) (chkMG e) (proj1 (proj2 (proj2 (proj2 nxM)) e)) (proj2 (proj2 (proj2 (proj2 nxM)) e)) J rho tp HJ HC). Qed.
End TR.
End SegQ3M_states.

(* [comment removed for export] *)
Module SegQ3R_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "list"; "pair"; "bool"; "true"; "option"; "Some"; "prod"; "None"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "sv"; "valuation"; "SLit"; "ss_facts"; "rm"; "eval"; "rw"; "SAlu"; "SPBranch"; "SVar"; "sprop_below"; "ss_next"; "SPAlign"; "SPNot"; "SPUle"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "True"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "aa_cache_inited"; "aa_geom"; "ag_thread"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXSplit"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "ZQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "gsz"; "vTN"; "ReQ3e"; "ReQ3n"; "vTB"; "vGF"; "KEEP3"; "O_gmax"; "O_gq"; "O_mtx"; "O_tq"; "vMIN"; "O_glb"; "vGN"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "BC_EQ"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "PreR2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "F_sp"; "X4e"; "X4n"; "X1e"; "X1n"; "X2e"; "X2n"; "gn'"; "HVP"; "KEPT6e"; "KEPT6n"; "NFe"; "NFn"; "XSPLIT"; "FRM"; "MEe"; "MEn"; "REST1e"; "REST2n"; "RMEM"; "X2e'"; "X2n'"; "X5e"; "X5n"; "tlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel.Recycle"; "JRQ"; "@Stdlib.Lists.List"; "forallb"; "removelast"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "pow"; "modulo"; "le"; "mul"; "add"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "qhdr_repr"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep"; "last_addr"; "hd_addr"; "qlinks_to"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kQuarantineMax"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "A1T"; "rhoT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "JQ3"; "qbounded"; "qzone"; "QFP"; "QRD"; "batch_mem"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece"; "keeps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "entsM"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "@Stdlib.Sorting.Permutation"; "Permutation"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FRM (A0 : AA) (rho0 rho : valuation) : Prop := ltac2:(tb__ "0|7|
S1fS93S83Vrho0;Vrho;A3S1fS45Q40M0A1M1S20S8bVA0;S46G0R1A2M2A2A1S1eS8S45Q8A1M3A1M4S13Vrho;R2A2S13Vrho0;R2A2M5A3F_;Fa;S1fS2cS20S8aVA0;R1A2A1S1eG4S78S30S13Vrho;A1R2A3S78S30S13Vrho0;A1R2A3A3F_;Fz;G1S1fS70S7fG2A2S6dG2S7eA2A2S20S1eG4G5SbG3A1M6A3A1S20S1eG4S13Vrho;R3A2G6A3A1F_;F_;Fa;A2A2A2").

Definition tlinks (m : bview) (pre : list qbatch) : Prop := ltac2:(tb__ "0|1|
S4S24A1M0OLpre;Vpre;S22S24G0S7bVm;S6cS24Vpre;A2S79Vpre;A1A3Ll;Lq;X4x2").

Definition RMEM (m : bview) (G : ageom) (pre rest : list qbatch) : Prop := ltac2:(tb__ "0|0|
S1fS90S24S8cVm;A1S3S24Vpre;Vrest;A3A3S1fS69Vm;Vpre;A2S1fS77Vm;Vrest;A2S76Vm;S72S2aVG;A1Z50A2S2S24A1A3A2A2A2").

Definition HVP (rho : valuation) (all : list qbatch) : Prop := ltac2:(tb__ "0|2|
S1fS1eS45Q40M0A1M1S15Vrho;PccA2S47G0S73ScS24Vall;A2A1A2A3S1fS1eG1S15Vrho;PcdA2S47G0S7aVall;A1A2A3S1fS1eG1S15Vrho;PceA2S47G0S79Vall;A1A2A3S1fS1eG1S15Vrho;PcfA2S47G0S75Vall;A1A2A3S1eG1S15Vrho;Pd0A2S47G0S80A2A3A2A2A2A2").

Definition KEPT6n : list sobj := ltac2:(tb__ "0|0|
S3SeS0SeS82S81A3S0SeS40S11Z100A1A1S0SeS3fS84S44S38A2S3cS3bS37A4S0SeS3eS2SeA1A3A3A3A3").
Definition REST2n : list sobj := ltac2:(tb__ "0|0|
S0SeS41S36S36S36S36A4S0SeS43S18Pc9A1A1S2SeA1A3A3").
Definition X1n : axst := ltac2:(tb__ "0|0|
S2fS3aS4bS2dS3aA1S3SeS5bS63A3A2A2").
Lemma X1n_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S3aS0S31S33S0S1U0S0S1U1S0S1U2S0S1U4S0S1U5S0S1U6S0S1U3S0S1U7S2S1A1A3A3A3A3A3A3A3A3A1S2S31A1A3A2S9S2eS55A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X2n : axst := ltac2:(tb__ "0|0|
S2fS55S4bS2dS55A1S5bA2A2").
Definition F_sp : sprop := SPUle (SLit 140735332483072) (SVar 10).
Definition X2n' : axst := ltac2:(tb__ "0|0|
S4cS57S3SdS12S2dS57A1A1S0SdS51S2SdA1A3A3A2").
Definition XSPLIT : list axform := ltac2:(tb__ "0|4|
S0S31S34U0M0S11Na8A1A2S0S31S34G0S11Nb8M1A1A2S0S31S34G0S11Nc0M2A1A2S0S31S35G0G2A2S0S31S35U2M3G1A2S0S31S33S0S1G0S0S1U1S0S1G3S0S1U3S0S1U6S0S1U8S0S1U4S0S1U5S0S1U7S2S1A1A3A3A3A3A3A3A3A3A3A1S2S31A1A3A3A3A3A3A3").
Definition X4n : axst := Eval vm_compute in (match apply_axforms X2n' XSPLIT with Some X => X | None => X2n' end).
Lemma X4n_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S66S5eA2S9S2eS53A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition gn' : sv := add vGN vTN.
Definition NFn : list sprop := ltac2:(tb__ "0|0|
S0SdS1cS17S49S58S11Z0A1A3A1S0SdS1dS11S7cA1S3cA2S0SdS1bPcdZ3A2S0SdS17S4aS37S16S48S58S11ZdA1A3A3S2SdA1A3A3A3A3").
Definition X5n : axst := ltac2:(tb__ "0|0|
S4cS53S3SdS12S2dS53A1A1S5dA3A2").
Definition MEn : vmap := ltac2:(tb__ "0|1|
S0SaS2bSfA2M0S5S2bSfPccS58A4S0G0S5S2bSfPcdS3cA4S0G0S5S2bSfPceS3bA4S0G0S5S2bSfPcfS37A4S0G0S5S2bSfPd0S42A4S2G0A1A3A3A3A3A3").
Lemma X5n_ent : ltac2:(tb__ "0|0|
S1eS6S8fS68S50S61A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X2n'_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS57A1M0A1A1S3SdS12G0A1S0SdS51S2SdA1A3A3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X5n_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS53A1M0A1A1S3SdS12G0A1S5dA3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition KEPT6e : list sobj := ltac2:(tb__ "0|0|
S3SeS0SeS82S81A3S0SeS40S11Z100A1A1S0SeS3fS38S18Pc9A1S3bS37A4S0SeS3eS2SeA1A3A3A3A3").
Definition REST1e : list sobj := ltac2:(tb__ "0|0|
S0SeS41S36S36S36S36A4S2SeA1A3").
Definition X1e : axst := ltac2:(tb__ "0|0|
S2fS39S4bS2dS39A1S3SeS5aS62A3A2A2").
Lemma X1e_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S39S0S31S33S0S1U0S0S1U1S0S1U2S0S1U4S0S1U5S0S1U6S0S1U3S2S1A1A3A3A3A3A3A3A3A1S2S31A1A3A2S9S2eS54A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X2e : axst := ltac2:(tb__ "0|0|
S2fS54S4bS2dS54A1S5aA2A2").
Definition X2e' : axst := ltac2:(tb__ "0|0|
S4cS56S3SdS12S2dS56A1A1S0SdS51S2SdA1A3A3A2").
Definition X4e : axst := Eval vm_compute in (match apply_axforms X2e' XSPLIT with Some X => X | None => X2e' end).
Lemma X4e_eq : ltac2:(tb__ "0|0|
S1eS8S2eA1S32S65S5eA2S9S2eS52A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition NFe : list sprop := ltac2:(tb__ "0|1|
S0SdS1cS17S49S38S11Z0A1A3A1S0SdS1dS11S7cA1S18Pc9M0A1A2S0SdS1bG0Z3A2S0SdS17S4aS37S16S48S38S11ZdA1A3A3S2SdA1A3A3A3A3").
Definition X5e : axst := ltac2:(tb__ "0|0|
S4cS52S3SdS12S2dS52A1A1S5cA3A2").
Definition MEe : vmap := ltac2:(tb__ "0|1|
S0SaS2bSfA2M0S5S2bSfPccS38A4S0G0S5S2bSfPcdS18Pc9A1A4S0G0S5S2bSfPceS3bA4S0G0S5S2bSfPcfS37A4S0G0S5S2bSfPd0S42A4S2G0A1A3A3A3A3A3").
Lemma X5e_ent : ltac2:(tb__ "0|0|
S1eS6S8fS67S50S60A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X2e'_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS56A1M0A1A1S3SdS12G0A1S0SdS51S2SdA1A3A3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X5e_below : ltac2:(tb__ "0|1|
S1eS6S6bSdS19S1aS2dS52A1M0A1A1S3SdS12G0A1S5cA3A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma U_sll2' : ltac2:(tb__ "0|3|
S10SfSfS1eS2cS46Q40M0S14R3S16S48R2R1A3A2A2S6fS71S46G0S14R3R2A2A2S6eZ2M1S6fS46G0S14R3R1A2A2Z40M2A2A2A2S6eG1G2A2A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 63) with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  unfold bv_wrap. reflexivity.
Qed.
Lemma U_sllk : ltac2:(tb__ "0|3|
S10SfS2cS1fS70Z0R1A2S6dR1Z40M0A2A2S1eS2cS46Q40M1S14R4S16S48R3S11R2A1A3A2A2S6fS71S46G1S14R4R3A2A2S6eZ2M2R2A2A2S6eG2G0A2A2A3F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk. rewrite U_sll2'. cbn [eval]. rewrite u64_lit by lia. rewrite (Z.mod_small k 64) by lia. reflexivity. Qed.
Lemma qzone_perm : ltac2:(tb__ "0|1|
S25S4S24A1M0G0S2cS95S24S94R4A1S3S24R3R2A3A3S23S89S8dR5R4R3A3R2A2S89R5R2A2A2F_;Fz;Fg;Ft;FA;").
Proof.
  intros A t g z HP. unfold qzone. change (qall (set_q A t g)) with (t ++ g). split; intros H; apply Exists_exists in H as (b & Hb & Hz); apply Exists_exists; exists b; (split; [|exact Hz]).
  - eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb].
  - eapply Permutation_in; [exact HP | exact Hb].
Qed.

Section Recycle.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.

Definition JRQ (A0 : AA) (rho0 : valuation) (A1 : AA) (pre rest : list qbatch) : jpredA := ltac2:(tb__ "0|0|
S10S4S45Q40A1A1S4S92A1S91S1fVK;VA1;R4R3R2R1A5S1fS64S78S30S13R4A1A2S29VA1;A1Vpre;Vrest;A4S5fVA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma JRQ_stable : ltac2:(tb__ "0|1|
S25S10S25S4S24A1M0G0S4fS30S83S6aR5R4R3R2R1A5A3Frest;Fpre;FA1;Frho0;FA0;").
Proof.
  intros A0 rho0 A1 pre rest rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A1); eauto|]. split; [rewrite Erm; exact HR|].
  destruct HF as ((F1 & F1') & F2 & F3 & F4). split; [|rewrite Erm; auto].
  split; [intros i Hi; rewrite (F1 i Hi); apply (proj1 Hag); exact Hi | intros l; rewrite (F1' l); apply (proj1 (proj2 Hag))].
Qed.
Lemma JRQ_okf : ltac2:(tb__ "0|1|
S74OF_;S25S10S25S4S24A1M0G0S25S4eS30R7VK;R1A1A3FA;S4eS30R7S6aR6R5R4R3R2A5A3F_;Frest;Fpre;FA1;Frho0;FA0;Fok;").
Proof. intros ok A0 rho0 A1 pre rest HOK rho tp tr ms md msv' (HK & _). exact (HOK A1 rho tp tr ms md msv' HK). Qed.

Lemma entry_Rn : ltac2:(tb__ "0|4|
S25S10S10S4S45Q40A1A1S74S20S1eS4S24A1M0S27R5A1S2S24A1M1A3A1S20S1eG0S26R6A1G1A3A1S1eS6S28R7A1S7A3S88R8A1S8eS3dS86R9S7aS26R9A1M2A1S79G2A1R8A4R7A3S4dS30S87S30VK;RaA3S3aR8R7R6A6S21S10S10S1fS4dS30S6aRcRbS85RcA1G1S3S24S26RcA1S27RcA1A3M3A5S50R1R9R8A6S1fS59R1G3A2S6dS7dS75G3A1A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp w HTL HGL HCI HBND [Hag Hkeep] H0. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho' ReQ3n X1n tp _ X1n_eq H0) as H. clear H0.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (gl := aa_q_global A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.

  destruct (rhoT_vals A (hd_addr gl) (last_addr gl) rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A (hd_addr gl) (last_addr gl) rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E204 : rw rho' 204%positive = Z_to_bv 64 (Z.of_nat (length gl))) by (rewrite KV by (cbn; tauto); exact R204).
  assert (E205 : rw rho' 205%positive = Z_to_bv 64 (hd_addr gl)) by (rewrite KV by (cbn; tauto); exact R205).
  assert (E206 : rw rho' 206%positive = Z_to_bv 64 (last_addr gl)) by (rewrite KV by (cbn; tauto); exact R206).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 (qsize gl)) by (rewrite KV by (cbn; tauto); exact R207).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.

  pose proof (SPA_facts_hold segsA _ rho' X1n tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FGT : holds rho' F_gt) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  assert (Hhigh : holds rho' F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  destruct (stack_win_range _ rho' _ _ Hsm ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. fold tl gl in HBP, HND, HBM, HLT, HLG, HHT, HHG.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ Z.of_nat (length gl) < 2 ^ 35 /\ 0 <= qsize tl /\ 0 <= qsize gl
                 /\ 8192 * Z.of_nat (length tl) <= qsize tl /\ 8192 * Z.of_nat (length gl) <= qsize gl).
  { destruct HBND as [B1 B2]. fold tl gl in B1, B2. apply Forall_app in HBP as [HBPt HBPg]. apply Forall_app in HBM as [HBMt HBMg].
    pose proof (qsize_ge A _ _ HBPt HBMt). pose proof (qsize_ge A _ _ HBPg HBMg). unfold kQuarantineBatchSize, kQuarantineMax in *. lia. }
  destruct LEN2 as (LT & LG & ST0 & SG0 & SGEt & SGEg). destruct HBND as [BT BG]. fold tl gl in BT, BG. unfold kQuarantineMax in BG.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia. }
  pose proof (conj HBP HND : q_pure A) as HQP.
  destruct (batch_slot A HQP HAU HG0 _ (in_or_app _ _ _ (or_intror (In_last gl qb_dflt HGL)))) as (yb & GB1 & GB2 & GB3 & GB4 & GB5 & GB6 & GB7 & _).
  change (qb_addr (last gl qb_dflt)) with (last_addr gl) in GB1, GB5, GB6, GB7. set (gb := last_addr gl) in *. unfold HIGH_SHADOW_END in GB5.
  assert (GBhi : gb + 8192 <= 140737479966720) by (clear -GB6 G14 ACV; lia).
  destruct (batch_slot A HQP HAU HG0 _ (in_or_app _ _ _ (or_intror (In_hd gl qb_dflt HGL)))) as (yh & GH1 & GH2 & GH3 & GH4 & GH5 & GH6 & GH7 & _).
  change (qb_addr (hd qb_dflt gl)) with (hd_addr gl) in GH1, GH5, GH6, GH7. unfold HIGH_SHADOW_END in GH5.

  assert (OBJS : ss_objs (ax_S X1n) = KEPT6n ++ REST2n) by reflexivity.
  set (rho3 := rho_absorb rho' REST2n (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6n REST2n (SVar 13) 0 32 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6n REST2n vGB 0 8 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)
                ltac:(unfold vGB; cbn [eval]; rewrite E206, u64_lit by (fold gb; lia); fold gb; lia)) as [AV5 PR5].
  fold rho3 v3 in AV1, PR1, AV5, PR5. cbn [eval] in AV1, PR1. rewrite U13 in AV1, PR1.
  unfold vGB in AV5, PR5. cbn [eval] in AV5, PR5. rewrite E206, u64_lit in AV5, PR5 by (fold gb; lia). fold gb in AV5, PR5.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  assert (C_lnk : cell_ok v3 (mkACell gb 8 (hd_addr tl))) by (replace gb with (gb + 0) at 1 by lia; exact (av_cell v3 gb 0 8 _ _ rho' (fun j => AV5 _ _ _ j (or_introl eq_refl)) E201)).
  clear AV1 AV5.
  set (P := fun z : Z => T + 80 <= z < T + 112 \/ gb <= z < gb + 8).
  assert (INR : forall a, in_ranges rho' REST2n a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. cbn [REST2n In] in Ho.
    destruct Ho as [<-|[<-|[]]]; unfold O_tq, O_glb, carved, vGB in Hz; rewrite obj_range_mk in Hz by lia;
      cbn [fst snd eval] in Hz; rewrite ?U13, ?E206, ?u64_lit in Hz by (fold gb; lia); fold gb in Hz; lia. }
  assert (FR : forall z, ~ P z -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST2n (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST2n a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).

  assert (LASTIN : In (last gl qb_dflt) (qall A)) by (unfold qall; fold tl gl; apply in_or_app; right; apply In_last; exact HGL).
  assert (ADDR_INJ : forall b, In b (qall A) -> qb_addr b = gb -> b = last gl qb_dflt).
  { intros b Hb E. apply (NoDup_map_In_inj qb_addr (qall A)); [unfold qall; fold tl gl; exact HND | exact Hb | exact LASTIN | exact E]. }
  assert (IT_OUT : forall it, In it (qitems (qall A)) -> forall z, ifoot it z -> ~ P z).
  { intros it Hit z Hz HP.
    assert (QF : q_foot A z).
    { destruct (qitems_In A it Hit) as (b & Hb & Hib). unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it. split; [exact Hib|].
      unfold ifoot, it_ab in Hz. exact Hz. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    destruct (qitems_In A it Hit) as (b & Hb & Hib).
    pose proof (proj1 (Forall_forall _ _) (proj1 HQP) b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hib) as (IP1 & IP2 & IP3 & IP4).
    pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1.
    assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
    unfold P in HP. unfold ifoot, it_ab in Hz.
    destruct HP as [HP|HP]; [lia|].
    destruct (is_primary (snd it)) eqn:EP.
    - pose proof (item_batch_apart A HQP HIDS HAU HG0 it _ Hit EP LASTIN) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP.
      pose proof (item_zones A HQP HAU HG0 it Hit EP) as IZ. cbv zeta in IZ. destruct IZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). unfold it_ab, HIGH_SHADOW_END in *.
      destruct Hz as [Hz|Hz]; lia.
    - pose proof (HKSECQ it Hit EP) as [SQ SQ2]. rewrite KSV in SQ.
      assert (SHhi : Sh (fst it) + (snd it + 7) / 8 <= 0x10007fff8000).
      { unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (fst it) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fst it) 8 ltac:(lia)).
        pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)). lia. }
      destruct Hz as [Hz|Hz]; lia. }
  assert (BX_OUT : forall b, In b (qall A) -> forall z, qb_addr b + (if Z.eq_dec (qb_addr b) gb then 8 else 0) <= z < qb_addr b + 8192 -> ~ P z).
  { intros b Hb z Hz HP.
    assert (QF : q_foot A z).
    { unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. destruct (Z.eq_dec (qb_addr b) gb); lia. }
    pose proof (HSEP z QF) as NT. fold T in NT.
    unfold P in HP. destruct HP as [HP|HP]; [lia|].
    destruct (Z.eq_dec (qb_addr b) gb) as [E|NE]; [lia|].
    pose proof (batches_apart A HQP HAU HG0 b _ Hb LASTIN NE) as AP. change (qb_addr (last gl qb_dflt)) with gb in AP. lia. }
  assert (BF_OUT : forall b, In b (qall A) -> forall z, bfoot b z -> ~ P z).
  { intros b Hb z [Hz|Hz].
    - apply (BX_OUT b Hb). unfold kQuarantineBatchSize in Hz. destruct (Z.eq_dec (qb_addr b) gb); lia.
    - apply Exists_exists in Hz as (it & Hit & Hz). apply (IT_OUT it); [|exact Hz]. unfold qitems. apply in_flat_map. exists b. exact (conj Hb Hit). }
  assert (LK_OUT : forall b, In b (qall A) -> b <> last gl qb_dflt -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb NE z Hz. apply (BX_OUT b Hb). destruct (Z.eq_dec (qb_addr b) gb) as [E|_]; [exfalso; exact (NE (ADDR_INJ b Hb E)) | lia]. }
  assert (PQW : forall z, P z -> QW A z).
  { intros z HP. unfold P in HP. destruct HP as [HP|HP].
    - right. left. left. fold T. lia.
    - left. unfold qzone. apply Exists_exists. exists (last gl qb_dflt). split; [exact LASTIN|]. left. change (qb_addr (last gl qb_dflt)) with gb. unfold kQuarantineBatchSize. lia. }
  assert (PPR : forall z, P z -> exists b, v3 z = Some b).
  { intros z HP. unfold P in HP. destruct HP as [HP|HP]; [apply PR1 | apply PR5]; lia. }
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [exfalso; exact (NQ (PQW z HP)) | exact (FR z NP)].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PPR z HP) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (A1T A) rho3 tp tr md).
  { unfold A1T. apply (kq_perm segsA K HL A [] (gl ++ tl) rho3 tp tr md); [|exact HK3]. unfold qall. fold tl gl. cbn [app]. apply Permutation_app_comm. }
  assert (INT : forall b, In b tl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; left; exact Hb).
  assert (ING : forall b, In b gl -> In b (qall A)) by (intros b Hb; unfold qall; fold tl gl; apply in_or_app; right; exact Hb).
  assert (TL_NOT_LAST : forall b, In b tl -> b <> last gl qb_dflt).
  { intros b Hb E. subst b.
    pose proof (NoDup_app_disj (map qb_addr tl) (map qb_addr gl) gb) as X. rewrite map_app in HND.
    apply (X HND); [apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | exact Hb] | apply in_map_iff; exists (last gl qb_dflt); split; [reflexivity | apply In_last; exact HGL]]. }
  assert (HR3 : RMEM v3 (aa_geom (A1T A)) [] (gl ++ tl)).
  { unfold RMEM. cbn [app tlinks]. split; [|split; [exact I | split]].
    - apply Forall_forall. intros b Hb.
      assert (Hb' : In b (qall A)) by (apply in_app_or in Hb as [Hb|Hb]; [exact (ING b Hb) | exact (INT b Hb)]).
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b Hb')); [intros z Hz; exact (FR z (BF_OUT b Hb' z Hz))|].
      exact (proj1 (Forall_forall _ _) HBM b ltac:(unfold qall in Hb'; fold tl gl in Hb'; exact Hb')).
    - apply qlinks_to_0. apply qlinks_to_app; [exact HTL | |].
      + apply (qlinks_to_relast v' v3 gl 0 (hd_addr tl) HGL); [| exact C_lnk | apply qlinks_to_0; exact HLG].
        intros b z Hb Hz. apply FR. apply (LK_OUT b (ING b (in_removelast_q _ _ Hb))); [|exact Hz].
        intros E. subst b. rewrite map_app in HND. exact (removelast_not_last gl HGL (NoDup_app_r _ _ HND) Hb).
      + apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
        intros b z Hb Hz. apply FR. exact (LK_OUT b (INT b Hb) (TL_NOT_LAST b Hb) z Hz).
    - unfold A1T. cbn [aa_geom set_q]. fold T. unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; lia|]. exact C_t3. }
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  assert (HF3 : FRM A rho rho3).
  { split; [|split; [|split]].
    - apply (agree_vals_trans NPRE rho (rhoT A (hd_addr gl) (last_addr gl) rho)); [exact (agree_below_vals _ _ _ RAG)|].
      apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag) | split; intros; reflexivity].
    - intros a NQ. rewrite <- ERM. apply FRrm. intros HP. apply NQ. left. left. exact (PQW _ HP).
    - intros z NQ. fold v3. rewrite <- EV'. apply FR. intros HP. apply NQ. left. exact (PQW _ HP).
    - intros a HB Hdef. rewrite FRrm; [rewrite ERM; exact Hdef|].
      intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -HP HB TBD GB5. lia. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ X1n rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' X1n KEPT6n REST2n tp tr ms md OBJS HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. fold X2n in HU.
  set (J3 := JRQ A rho (A1T A) [] (gl ++ tl)).
  assert (H2 : SPA segsA J3 X2n rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK1 (conj HR3 HF3))]).

  assert (H2' : SPA segsA J3 X2n' rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact X2n'_below |]. intros HF. apply Forall_app. split; [exact HF|]. apply Forall_cons; [|apply Forall_nil].
    unfold F_sp. cbn [holds eval]. rewrite u64_lit by lia. change (rw rho3 10%positive) with (rw rho' 10%positive). clear -SW1 SW2 SW3. lia. }
  pose proof (SPA_axforms segsA J3 _ rho3 X2n' X4n tp _ X4n_eq H2') as H4.

  assert (EGN : eval rho3 gn' = Z_to_bv 64 (Z.of_nat (length gl) + Z.of_nat (length tl))) by (apply eval_add_z; [exact E204 | exact E200 | lia | lia | lia]).
  assert (EGS : eval rho3 gsz = Z_to_bv 64 (qsize gl + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (H5 : SPA segsA J3 X5n rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H4 | exact X5n_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold NFn.
    repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken]. rewrite EGN. cbn [eval]. unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E.
      assert (0 < Z.of_nat (length gl)) by (destruct gl; [congruence | cbn; lia]). lia.
    - unfold vGF. cbn [holds eval]. change (rw rho3 205%positive) with (rw rho' 205%positive). rewrite E205, !u64_lit by (unfold HIGH_SHADOW_END; lia). unfold HIGH_SHADOW_END. lia.
    - cbn [holds]. split; [lia|]. change (rw rho3 205%positive) with (rw rho' 205%positive). rewrite E205, u64_lit by lia.
      clear -GH7. pose proof (Z.div_mod (hd_addr gl) 8192 ltac:(lia)) as D. rewrite GH7, Z.add_0_r in D. rewrite D. replace (8192 * (hd_addr gl / 8192)) with (1024 * (hd_addr gl / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
    - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite U_sllk by lia. rewrite EGN, EGS, !u64_lit by lia.
      rewrite Z.mod_small by lia. lia. }
  destruct (entM_SPA J3 X5n PreR2 MEn rho3 tp _ X5n_ent (JRQ_stable _ _ _ _ _) H5) as (H6 & AG6 & V6 & RM6).
  exists (rho_sub rho3 (infer_sub NPRE (ax_S X5n) (ax_S PreR2))). split; [exact H6|]. split.
  - unfold HVP. rewrite length_app, Nat2Z.inj_add, qsize_app.
    split; [rewrite (V6 _ _ (or_introl eq_refl)); exact EGN|].
    split; [rewrite (V6 _ _ (or_intror (or_introl eq_refl))); unfold vGF; cbn [eval]; change (rw rho3 205%positive) with (rw rho' 205%positive); rewrite E205; f_equal; unfold hd_addr; destruct gl; [congruence | reflexivity]|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_introl eq_refl)))); unfold vTB; cbn [eval]; change (rw rho3 202%positive) with (rw rho' 202%positive); rewrite E202; f_equal; unfold last_addr; rewrite (last_app_ne gl tl qb_dflt HTL); reflexivity|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))); exact EGS|].
    rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))). unfold vMIN. cbn [eval]. exact E208.
  - assert (EGS' : eval rho' gsz = Z_to_bv 64 (qsize gl + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
    rewrite qsize_app. unfold F_gt in FGT. cbn [holds branch_taken] in FGT. rewrite EGS' in FGT. cbn [eval] in FGT.
    apply not_true_is_false in FGT. apply negb_false_iff in FGT. unfold bv_ltu in FGT. apply Z.ltb_lt in FGT. rewrite !u64_lit in FGT by (unfold kQuarantineMax; lia). exact FGT.
Qed.

Lemma entry_Re : ltac2:(tb__ "0|3|
S25S2cS2cS10S10S4S45Q40A1A1S74S20S1eS4S24A1M0S27R7A1S2S24A1M1A3A1S1eG0S26R8A1G1A3S1eS6S28R9A1S7A3S88RaA1S8eS3dS86RbRaR9R8A4R7A3S4dS30S87S30VK;RcA3S39R8R7R6A6S21S10S10S1fS4dS30S6aReRbS85ReA1G1S3S24S26ReA1S27ReA1A3M2A5S50R1R9R8A6S1fS59R1G2A2S6dS7dS75G2A1A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;Fgb;Fgf;FA;").
Proof.
  intros A gf gb rho rho' tp w HTL HGL HCI HBND [Hag Hkeep] H0. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho' ReQ3e X1e tp _ X1e_eq H0) as H. clear H0.
  pose proof (proj2 H) as [HK HQ]. cbn [w_tr w_cfg cfg_model fst snd] in HK, HQ.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (tl := aa_q_thread A) in *. set (T := ag_thread (aa_geom A)).
  destruct (kq_facts segsA K HL A rho' tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (topG_range (aa_geom A)) as ACV. pose proof kSpaceSize_val as KSV.
  pose proof HG as HG0. apply geom_old in HG. rewrite FS_total_val, KSV in HG. unfold HIGH_SHADOW_END, IMG_HI, PG in HG.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI.
  destruct HRIG as (E151 & E152 & E155 & E156). fold T in E151.
  destruct (rhoT_vals A gf gb rho) as (R200 & R201 & R202 & R203 & R204 & R205 & R206 & R207 & R208 & R209 & RRM & RAG).
  assert (KV : forall v, In v KEEP3 -> rw rho' v = rw (rhoT A gf gb rho) v) by exact Hkeep.
  assert (E200 : rw rho' 200%positive = Z_to_bv 64 (Z.of_nat (length tl))) by (rewrite KV by (cbn; tauto); exact R200).
  assert (E201 : rw rho' 201%positive = Z_to_bv 64 (hd_addr tl)) by (rewrite KV by (cbn; tauto); exact R201).
  assert (E202 : rw rho' 202%positive = Z_to_bv 64 (last_addr tl)) by (rewrite KV by (cbn; tauto); exact R202).
  assert (E203 : rw rho' 203%positive = Z_to_bv 64 (qsize tl)) by (rewrite KV by (cbn; tauto); exact R203).
  assert (E207 : rw rho' 207%positive = Z_to_bv 64 0) by (rewrite KV by (cbn; tauto); rewrite R207, HGL; reflexivity).
  assert (E208 : rw rho' 208%positive = Z_to_bv 64 kQuarantineMin) by (rewrite KV by (cbn; tauto); exact R208).
  clear KV R200 R201 R202 R203 R204 R205 R206 R207 R208 R209.
  pose proof (SPA_facts_hold segsA _ rho' X1e tp _ H) as HFa.
  assert (U13 : bv_unsigned (rw rho' 13%positive) = T + 80).
  { assert (X : holds rho' (SPBranch BC_EQ (SVar 13) (add vT (SLit 80)))) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
    cbn [holds branch_taken] in X. unfold add, vT in X. cbn [eval] in X. unfold bv_eqb in X.
    apply Z.eqb_eq in X. rewrite add_val, E151, !u64_lit in X by lia. rewrite Z.mod_small in X by lia. exact X. }
  assert (FGT : holds rho' F_gt) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  assert (Hhigh : holds rho' F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
  destruct (stack_win_range _ rho' _ _ Hsm ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  destruct HQ as (HBM & HLT & HLG & HHT & HHG & HMTX). destruct HQP as [HBP HND]. unfold qall in HBP, HND, HBM. rewrite HGL, app_nil_r in HBP, HND, HBM. fold tl in HBP, HND, HBM, HLT, HHT.
  assert (LEN2 : Z.of_nat (length tl) < 2 ^ 35 /\ 0 <= qsize tl /\ 8192 * Z.of_nat (length tl) <= qsize tl).
  { destruct HBND as [B1 B2]. fold tl in B1. pose proof (qsize_ge A _ _ HBP HBM). unfold kQuarantineBatchSize in *. lia. }
  destruct LEN2 as (LT & ST0 & SGEt). destruct HBND as [BT _]. fold tl in BT.
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia. }
  assert (HQP : q_pure A) by (split; unfold qall; rewrite HGL, app_nil_r; assumption).
  assert (QALL : qall A = tl) by (unfold qall; rewrite HGL, app_nil_r; reflexivity).
  destruct (batch_slot A HQP HAU HG0 (hd qb_dflt tl) ltac:(rewrite QALL; apply In_hd; exact HTL)) as (yh & GH1 & GH2 & GH3 & GH4 & GH5 & GH6 & GH7 & _).
  change (qb_addr (hd qb_dflt tl)) with (hd_addr tl) in GH1, GH5, GH6, GH7. unfold HIGH_SHADOW_END in GH5.
  assert (OBJS : ss_objs (ax_S X1e) = KEPT6e ++ REST1e) by reflexivity.
  set (rho3 := rho_absorb rho' REST1e (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v' := view segsA (rm rho')).
  destruct (absorb_view_cells segsA rho' _ tr (vms md tp ms) (vmd md) KEPT6e REST1e (SVar 13) 0 32 _ Hsm OBJS ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite U13; lia) ltac:(cbn [eval]; rewrite U13; lia)) as [AV1 PR1].
  fold rho3 v3 in AV1, PR1. cbn [eval] in AV1, PR1. rewrite U13 in AV1, PR1.
  assert (C_t0 : cell_ok v3 (mkACell (T + 80) 8 0)) by (replace (T + 80) with (T + 80 + 0) by lia; exact (av_cell v3 (T + 80) 0 8 ZQ 0 rho' (fun j => AV1 0 8%nat ZQ j (or_introl eq_refl)) eq_refl)).
  assert (C_t3 : cell_ok v3 (mkACell (T + 80 + 24) 8 0)) by exact (av_cell v3 (T + 80) 24 8 ZQ 0 rho' (fun j => AV1 24 8%nat ZQ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) eq_refl).
  clear AV1.
  set (P := fun z : Z => T + 80 <= z < T + 112).
  assert (INR : forall a, in_ranges rho' REST1e a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. cbn [REST1e In] in Ho.
    destruct Ho as [<-|[]]; unfold O_tq, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd eval] in Hz; rewrite ?U13 in Hz; lia. }
  assert (FR : forall z, ~ P z -> v3 z = v' z).
  { intros z Hz. unfold v3, v'. apply view_agree. intros Hr. unfold rho3, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho' REST1e (Z_to_bv 64 z)) as [Hin|]; [|reflexivity]. exfalso. apply Hz. pose proof (INR _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X. }
  assert (FRrm : forall a, ~ P (bv_unsigned a) -> rm rho3 a = rm rho' a).
  { intros a Hz. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' REST1e a) as [Hin|]; [|reflexivity]. exfalso. exact (Hz (INR _ Hin)). }
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (QF_OUT : forall z, q_foot A z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; unfold P in HP; lia).
  assert (BF_OUT : forall b, In b (qall A) -> forall z, bfoot b z -> ~ P z).
  { intros b Hb z Hz. apply QF_OUT. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. unfold bfoot in Hz.
    destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
    split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz. }
  assert (LK_OUT : forall b, In b (qall A) -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ P z).
  { intros b Hb z Hz. apply QF_OUT. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. lia. }
  assert (PQW : forall z, P z -> QW A z) by (intros z HP; unfold P in HP; right; left; left; fold T; lia).
  assert (HK3 : K A rho3 tp tr md).
  { apply (kq_view segsA K HL A rho' rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | exact HK].
    - intros z NQ. destruct (PD z) as [HP|NP]; [exfalso; exact (NQ (PQW z HP)) | exact (FR z NP)].
    - intros z _ Hd. destruct (PD z) as [HP|NP]; [destruct (PR1 z ltac:(unfold P in HP; lia)) as [b Hb]; fold v3; rewrite Hb; discriminate | fold v3 v' in Hd |- *; rewrite (FR z NP); exact Hd]. }
  assert (HK1 : K (A1T A) rho3 tp tr md).
  { unfold A1T. apply (kq_perm segsA K HL A [] (aa_q_global A ++ tl) rho3 tp tr md); [|exact HK3]. unfold qall. fold tl. cbn [app]. apply Permutation_app_comm. }
  rewrite HGL. cbn [app].
  assert (HR3 : RMEM v3 (aa_geom (A1T A)) [] tl).
  { unfold RMEM. cbn [app tlinks]. split; [|split; [exact I | split]].
    - apply Forall_forall. intros b Hb. assert (Hb' : In b (qall A)) by (rewrite QALL; exact Hb).
      apply (batch_mem_frame A v' v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b Hb')); [intros z Hz; exact (FR z (BF_OUT b Hb' z Hz))|].
      exact (proj1 (Forall_forall _ _) HBM b Hb).
    - apply qlinks_to_0. apply (qlinks_to_frame v' v3 tl 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. exact (LK_OUT b ltac:(rewrite QALL; exact Hb) z Hz).
    - unfold A1T. cbn [aa_geom set_q]. fold T. unfold qhdr_repr. cbn [length]. change (T + 0x50) with (T + 80).
      split; [exact C_t0|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros z Hz; apply PR1; unfold P; lia|]. exact C_t3. }
  assert (ERM : forall a, rm rho' a = rm rho a) by (intros a; rewrite <- (proj2 (proj2 Hag) a), RRM; reflexivity).
  assert (EV' : forall z, v' z = view segsA (rm rho) z) by (intros z; unfold v'; apply view_agree; intros _; apply ERM).
  assert (HF3 : FRM A rho rho3).
  { split; [|split; [|split]].
    - apply (agree_vals_trans NPRE rho (rhoT A gf gb rho)); [exact (agree_below_vals _ _ _ RAG)|].
      apply (agree_vals_trans NPRE _ rho'); [exact (agree_below_vals _ _ _ Hag) | split; intros; reflexivity].
    - intros a NQ. rewrite <- ERM. apply FRrm. intros HP. apply NQ. left. left. exact (PQW _ HP).
    - intros z NQ. fold v3. rewrite <- EV'. apply FR. intros HP. apply NQ. left. exact (PQW _ HP).
    - intros a HB Hdef. rewrite FRrm; [rewrite ERM; exact Hdef|].
      intros HP. unfold P in HP. pose proof (geom_bands _ HG0) as (_ & TBD & _). fold T in TBD.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -HP HB TBD. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ X1e rho' tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho' X1e KEPT6e REST1e tp tr ms md OBJS HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. fold X2e in HU.
  set (J3 := JRQ A rho (A1T A) [] tl).
  assert (H2 : SPA segsA J3 X2e rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK1 (conj HR3 HF3))]).
  assert (H2' : SPA segsA J3 X2e' rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact X2e'_below |]. intros HF. apply Forall_app. split; [exact HF|]. apply Forall_cons; [|apply Forall_nil].
    unfold F_sp. cbn [holds eval]. rewrite u64_lit by lia. change (rw rho3 10%positive) with (rw rho' 10%positive). clear -SW1 SW2 SW3. lia. }
  pose proof (SPA_axforms segsA J3 _ rho3 X2e' X4e tp _ X4e_eq H2') as H4.
  assert (EGS : eval rho3 gsz = Z_to_bv 64 (0 + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
  assert (H5 : SPA segsA J3 X5e rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H4 | exact X5e_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold NFe.
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold vTN. cbn [holds branch_taken eval]. change (rw rho3 200%positive) with (rw rho' 200%positive). rewrite E200. unfold bv_eqb. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E.
      assert (0 < Z.of_nat (length tl)) by (destruct tl; [congruence | cbn; lia]). lia.
    - cbn [holds eval]. change (rw rho3 201%positive) with (rw rho' 201%positive). rewrite E201, !u64_lit by (unfold HIGH_SHADOW_END; lia). unfold HIGH_SHADOW_END. lia.
    - cbn [holds]. split; [lia|]. change (rw rho3 201%positive) with (rw rho' 201%positive). rewrite E201, u64_lit by lia.
      clear -GH7. pose proof (Z.div_mod (hd_addr tl) 8192 ltac:(lia)) as D. rewrite GH7, Z.add_0_r in D. rewrite D. replace (8192 * (hd_addr tl / 8192)) with (1024 * (hd_addr tl / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
    - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite U_sllk by lia. rewrite EGS. unfold vTN. cbn [eval]. change (rw rho3 200%positive) with (rw rho' 200%positive).
      rewrite E200, !u64_lit by lia. rewrite Z.mod_small by lia. lia. }
  destruct (entM_SPA J3 X5e PreR2 MEe rho3 tp _ X5e_ent (JRQ_stable _ _ _ _ _) H5) as (H6 & AG6 & V6 & RM6).
  exists (rho_sub rho3 (infer_sub NPRE (ax_S X5e) (ax_S PreR2))). split; [exact H6|]. split.
  - unfold HVP.
    split; [rewrite (V6 _ _ (or_introl eq_refl)); unfold vTN; cbn [eval]; exact E200|].
    split; [rewrite (V6 _ _ (or_intror (or_introl eq_refl))); cbn [eval]; exact E201|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_introl eq_refl)))); unfold vTB; cbn [eval]; exact E202|].
    split; [rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_introl eq_refl))))); rewrite EGS; f_equal; lia|].
    rewrite (V6 _ _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))). unfold vMIN. cbn [eval]. exact E208.
  - assert (EGS' : eval rho' gsz = Z_to_bv 64 (0 + qsize tl)) by (apply eval_add_z; [exact E207 | exact E203 | lia | lia | lia]).
    unfold F_gt in FGT. cbn [holds branch_taken] in FGT. rewrite EGS' in FGT. cbn [eval] in FGT.
    apply not_true_is_false in FGT. apply negb_false_iff in FGT. unfold bv_ltu in FGT. apply Z.ltb_lt in FGT. rewrite !u64_lit in FGT by (unfold kQuarantineMax; lia). lia.
Qed.

End Recycle.
End SegQ3R_skel.

(* [comment removed for export] *)
Module CertMallocSU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SVar"; "SLit"; "sprop"; "SPBranch"; "SPNot"; "sv"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "nat"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "rstS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SecLog2 CertMallocST.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_g4 : list sprop := ltac2:(tb__ "0|1|
SaS5S7S6S1S2S0S3S10A1S2S0S3Vnx;A1M0S4Z1000A1A3A3S2S0S2S0G0S4Z1800A1A3S3PcA1A3A3A1S9S5A1A3").
End NX.

Definition DPENT : Z := 0x7e850.
Definition DPRET : Z := 0x3c58c.
Definition U4p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S11VE;S9ScSbS8A2A1S13Vnx;A1A3").
Definition runT5 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
SfS14Ufa0SaSeS12S9SeA1A3VT;SdA5").
End CertMallocSU.

