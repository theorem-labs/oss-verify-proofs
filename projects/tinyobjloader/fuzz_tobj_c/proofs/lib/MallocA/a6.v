(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From Stdlib Require NArith PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.

(* [comment removed for export] *)
Module SegQ3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Datatypes"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "KEEP3"; "PreQ3e"; "PreQ3n"; "TsTe"; "TsTn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece"; "keeps"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.
Import ListNotations.
Open Scope Z_scope.

Definition NX := nxs3.

Theorem seg_Q3Tn_sound : ltac2:(tb__ "0|0|
S3SaOF_;S1S7S14Q40A1A1SbS5S0R4R5A3S4S0ScR6A3S6S1S13S6R2S11A3S12SdR8R2A3S9S0RaS2S0RbR4R3R8A5R7A4F_;F_;Frho';FT;S9S0R7S2S0R8SfR6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;").
Proof. intros. eapply (piece_soundK 600%nat _ PreQ3n run_Tn TsTn KEEP3 run_Tn_eq chk_Tn); try eassumption; try apply NX. apply keep3_lt. Qed.
Theorem seg_Q3Tn_complete : ltac2:(tb__ "0|0|
S3S1S7S14Q40A1A1SaOF_;S4S0ScR4A3S6S1S13S6R2S11A3S12SdR7R2A3S8S0S2S0R9R4R3R7A5R6A3F_;F_;Frho';FT;S8S0S2S0R6SfR5R4A5R3A3F_;F_;FQ;Ftp;Frho;FJ;").
Proof. intros. eapply (piece_completeK 600%nat _ PreQ3n run_Tn TsTn KEEP3 run_Tn_eq chk_Tn); try eassumption; try apply NX. apply keep3_lt. Qed.

Theorem seg_Q3Te_sound : ltac2:(tb__ "0|0|
S3SaOF_;S1S7S14Q40A1A1SbS5S0R4R5A3S4S0ScR6A3S6S1S13S6R2S10A3S12SdR8R2A3S9S0RaS2S0RbR4R3R8A5R7A4F_;F_;Frho';FT;S9S0R7S2S0R8SeR6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;").
Proof. intros. eapply (piece_soundK 600%nat _ PreQ3e run_Te TsTe KEEP3 run_Te_eq chk_Te); try eassumption; try apply NX. apply keep3_lt. Qed.
Theorem seg_Q3Te_complete : ltac2:(tb__ "0|0|
S3S1S7S14Q40A1A1SaOF_;S4S0ScR4A3S6S1S13S6R2S10A3S12SdR7R2A3S8S0S2S0R9R4R3R7A5R6A3F_;F_;Frho';FT;S8S0S2S0R6SeR5R4A5R3A3F_;F_;FQ;Ftp;Frho;FJ;").
Proof. intros. eapply (piece_completeK 600%nat _ PreQ3e run_Te TsTe KEEP3 run_Te_eq chk_Te); try eassumption; try apply NX. apply keep3_lt. Qed.
End SegQ3.

(* [comment removed for export] *)
Module SegQ3R_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "bool"; "app"; "true"; "prod"; "false"; "list"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sobj"; "sprop"; "cell"; "mkCell"; "SPBranch"; "SPNot"; "DUnknown"; "mkObj"; "ss_lenient"; "ss_next"; "swf"; "SMd"; "SAlu"; "SPAlign"; "SPUle"; "FcsrFrm0"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "ZQ"; "mkR"; "vCUR"; "NXR"; "LHEAD"; "SW"; "vCSZ"; "LEXIT"; "OH"; "O_cur"; "spR"; "vCN"; "F_H"; "Head0"; "Headk"; "PreR"; "STK"; "Xg"; "regsR"; "vN"; "F_nz"; "OC"; "O_gqC"; "O_gqH"; "RR"; "regsC"; "s'"; "vK"; "vS"; "DOREC"; "F_Hk"; "MERGE"; "O_mtx00"; "O_prv"; "RRET"; "regsH"; "regsX"; "vPRV"; "vPSZ"; "vTF"; "vTS"; "Cont0"; "Contk"; "Exit0"; "Exitk"; "F_H0"; "F_R"; "F_go"; "F_stop"; "PH"; "PX"; "QCHK"; "SWD"; "cb_cells"; "junk_ru2"; "run0"; "runP"; "runS1"; "runS2"; "runk"; "sw_cells"; "vJK"; "vJL"; "vLB"; "vXF"; "vXK"; "vXL"; "vXS"; "FRlo"; "O_cbD"; "PD"; "PM"; "PostQ3R"; "RETR"; "SW00"; "Ts0"; "TsP"; "Tsk"; "WLOW"; "junk_ru"; "post_ruR"; "regsD"; "regsM"; "regsRR"; "spD"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "add"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"; "vGN"; "DEPTH_R"; "vGS"; "O_gmax"; "vMIN"; "O_gq"; "regs3"; "vGF"; "LSLOW"; "NX3"; "O_mtx"; "vGB"; "RECY"; "cbC"; "vSTKq"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "M_MUL"; "BC_EQ"; "ALU_SLL"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "A_globals"; "V_DEPTH"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece"; "chkN"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition LHEAD : Z := 0x3e22c.
Definition LEXIT : Z := 0x3e288.
Definition MERGE : Z := 0x3e1b8.
Definition QCHK : Z := 0x3e2f8.
Definition DOREC : Z := 0x3e498.
Definition RRET : Z := 0x3e2a0.
Definition RETR : Z := 0x3e2bc.
Definition NXR : positive := 216%positive.

Definition vN := SVar 160. Definition vCUR := SVar 161. Definition vLB := SVar 162. Definition vS := SVar 163.
Definition vCN := SVar 164. Definition vCSZ := SVar 165. Definition vPRV := SVar 166. Definition vPSZ := SVar 167.
Definition vK := SVar 168. Definition vTF := SVar 169. Definition vTS := SVar 170.

Definition vJK := SVar 192. Definition vJL := SVar 193.
Definition junk_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S1SbA2M0S2S1SbU1ScPabA1A4S0G0S2S1SbU6ScPacA1A4S0G0S2S1SbU7ScPadA1A4S0G0S2S1SbU8ScPaeA1A4S0G0S2S1SbU9ScPafA1A4S0G0S2S1SbU11ScPb0A1A4S0G0S2S1SbU12ScPb1A1A4S0G0S2S1SbU13ScPb2A1A4S0G0S2S1SbU14ScPb3A1A4S0G0S2S1SbU1cScPb4A1A4S0G0S2S1SbU1dScPb5A1A4S0G0S2S1SbU1eScPb6A1A4S0G0S2S1SbU1fScPb7A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition junk_ru2 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S1SbA2M0S2S1SbU1ScPabA1A4S0G0S2S1SbU8ScPaeA1A4S0G0S2S1SbU9ScPafA1A4S0G0S2S1SbU12ScPb1A1A4S0G0S2S1SbU13ScPb2A1A4S0G0S2S1SbU14ScPb3A1A4S0G0S2S1SbU1cScPb4A1A4S0G0S2S1SbU1dScPb5A1A4S0G0S2S1SbU1eScPb6A1A4S0G0S2S1SbU1fScPb7A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3").
Definition spR : sv := add (SVar 10) (SLit (-80)).

Definition spD : sv := add (SVar 10) (SLit (-192)).
Definition WLOW : sobj := ltac2:(tb__ "0|0|
S15S74S7cScS98A1SdZc0A1A2SdZ0A1S3S10A1S14A5").
Definition FRlo : sobj := ltac2:(tb__ "0|0|
S15ScPaA1SdNc0A1SdNb8A1S3S10A1S14A5").
Definition O_cbD (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S15S7cScPaA1SdNb8A1A2SdZ0A1SdZ10A1Vcells;S14A5").
Definition cb_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SdZ0A1Z8M0S8eA3S0S10S11SdG0A1G0S8fA3S3S10A1A3A3").
Definition SW00 : sobj := ltac2:(tb__ "0|0|
S15ScPaA1SdNa8A1SdZ0A1S3S10A1S14A5").
Definition sw_cells (tk tf tl ts : sv) : list cell := ltac2:(tb__ "0|1|
S0S10S11SdN38A1Z8M0Vts;A3S0S10S11SdN40A1G0Vtl;A3S0S10S11SdN48A1G0Vtf;A3S0S10S11SdN50A1G0Vtk;A3S0S10S11SdN30A1G0ScP28A1A3S0S10S11SdN28A1G0ScP27A1A3S0S10S11SdN20A1G0ScP26A1A3S0S10S11SdN18A1G0ScP1dA1A3S0S10S11SdN10A1G0ScP1cA1A3S0S10S11SdN8A1G0ScPbA1A3S3S10A1A3A3A3A3A3A3A3A3A3A3").
Definition SW (tk tf tl ts : sv) : sobj := ltac2:(tb__ "0|0|
S15ScPaA1SdNa8A1SdZ0A1S5cVtk;Vtf;Vtl;Vts;A4S14A5").
Definition STK (cb : list cell) (sw : sobj) : list sobj := ltac2:(tb__ "0|0|
S0SeS6eS0SeS64S0SeS65Vcb;A1S0SeVsw;S3SeA1A3A3A3A3").
Definition O_cur (nx sz : sv) : sobj := ltac2:(tb__ "0|4|
S9dS22Z0M0Z10S0S7S7S1fS1A2M1SbA2M2S2G1SbS2S1fS1G0U8M3A4Vnx;A4S0G2S2G1SbS2S1fS1Z8G3A4Vsz;A4S3G2A1A3A3A4").
Definition O_prv (nx sz : sv) : sobj := ltac2:(tb__ "0|4|
S9dS45Z0M0Z10S0S7S7S1fS1A2M1SbA2M2S2G1SbS2S1fS1G0U8M3A4Vnx;A4S0G2S2G1SbS2S1fS1Z8G3A4Vsz;A4S3G2A1A3A3A4").
Definition ZQ : sv := SLit 0.
Definition mkR (pc : Z) (regs : list sv) (objs extra : list sobj) (F : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S99S1eVpc;Vregs;S7fS1dSaSbA1S5SeVobjs;S5SeS97Vextra;A3A3VF;Vnx;S8A9S3S7SbSbA2A1A2").

Definition F_R : list sprop := ltac2:(tb__ "0|0|
S5SfS96S82A1S0SfS13S12S92S81SdZ0A1A3A1S0SfS1cSdS9eA1S88A2S0SfS1bPcdZ3A2S0SfS12S90S83S1aS93S81SdZdA1A3A3S3SfA1A3A3A3A3A3").
Definition regsR : list sv := ltac2:(tb__ "0|1|
S7eS87S0S7S1SbA2M0S2S1SbUbS85A4S3G0A1A3A2").
Definition PreR : axst := ltac2:(tb__ "0|1|
S21S8dS32S5SeS30S3S10A1S6aA2S0SeS8bSdZ100A1A1S0SeS84S3SeA1M0A3A3A3S0SeS86S81S88S8cS83A4G0A3S4eS8aA6").

Definition regsH (cur k prv : sv) : list sv := ltac2:(tb__ "0|1|
S7eS32S5S7S1SbA2M0S0G0S2S1SbU2S2aA4S0G0S2S1SbUaSdS80A1A4S0G0S2S1SbU5Vcur;A4S0G0S2S1SbUeVk;A4S0G0S2S1SbUfVprv;A4S0G0S2S1SbU10S33A4S3G0A1A3A3A3A3A3A3S6fA3A2").
Definition F_H0 : list sprop := ltac2:(tb__ "0|0|
S5SfS96S82A1S0SfS13S12S92S33SdZ0A1A3A1S0SfS1cSdS9eA1S22A2S0SfS1bPa1Z3A2S3SfA1A3A3A3A3").
Definition F_H : list sprop := ltac2:(tb__ "0|0|
S5SfS4dS0SfS13S12S90S85S3cA3A1S3SfA1A3A3").
Definition F_Hk : list sprop := ltac2:(tb__ "0|0|
S5SfS2cS0SfS1cSdS9eA1S45A2S0SfS1bPa6Z3A2S0SfS13S12S92S3bSdZ0A1A3A1S3SfA1A3A3A3A3").
Definition OH (sw : sobj) : list sobj := ltac2:(tb__ "0|0|
S5SeS30S3S10A1Vsw;A2S0SeS8bSdZ101A1A1S0SeS84S3SeA1A3A3A3").
Definition O_gqH : sobj := ltac2:(tb__ "0|0|
S86S33S22S5fS3cA4").
Definition PH : axst := ltac2:(tb__ "0|0|
S21S24S43S22S20S20A3S28S25S20S20S20S20A4A1S0SeS37S3SeA1A3S2cS23A6").
Definition regsX : list sv := ltac2:(tb__ "0|1|
S7eS32S5S7S1SbA2M0S0G0S2S1SbU2S2aA4S0G0S2S1SbUaSdS80A1A4S0G0S2S1SbU5ScPbcA1A4S0G0S2S1SbUeScPbdA1A4S0G0S2S1SbUfScPbeA1A4S0G0S2S1SbU10ScPbfA1A4S0G0S2S1SbU6ScPacA1A4S0G0S2S1SbU7ScPadA1A4S0G0S2S1SbU11ScPb0A1A4S3G0A1A3A3A3A3A3A3A3A3A3S56A3A2").
Definition PX : axst := ltac2:(tb__ "0|0|
S21S27S44S28S25S20S20S20S20A4A1S0SeS37S3SeA1A3S5SfS4dS0SfS12S90S85S3cA3S3SfA1A3A3S23A6").
Definition regsM : list sv := ltac2:(tb__ "0|2|
S7eS32S0S7S1SbA2M0S2S1SbU2S2aA4S0G0S2S1SbUaSdS80A1A4S0G0S2S1SbU5SdZ100A1A4S0G0S2S1SbU6S20A4S0G0S2S1SbUeS19S91S81SdZ190000A1A3A4S0G0S2S1SbUfS19S91S83SdZ64A1M1A3A4S0G0S2S1SbU10S81A4S0G0S2S1SbU11G1A4S3G0A1A3A3A3A3A3A3A3A3A2").
Definition PM : axst := ltac2:(tb__ "0|0|
S21S3fS72S28S25S20S20S20S20A4A1S0SeS86S81S88S8cS83A4S3SeA1A3S5SfS4eS0SfS13S12S90S19S91S83SdZ64A1A3S19S91S81SdZ190000A1A3A3A1S0SfS13S12S90S1aS93S81SdZdA1A3S83A3A1S3SfA1A3A3A3S8aA6").

Definition Head0 : axst := ltac2:(tb__ "0|0|
S21S24S43S22S20S20A3S28S25S20S20S20S20A4A1S0SeS37S0SeS29S2bS26A2S3SeA1A3A3S2cS23A6").
Definition Headk : axst := ltac2:(tb__ "0|0|
S21S24S43S22S3bS45A3S28S25S5dS47S5eS48A4A1S0SeS37S0SeS29S2bS26A2S0SeS41S20S46A2S3SeA1A3A3A3S3eS23A6").

Definition s' : sv := ltac2:(tb__ "0|0|
S1aS94S3cS26A3").
Definition regsC (nz : bool) (k1 : sv) : list sv := ltac2:(tb__ "0|1|
S7eS32S5S7S1SbA2M0S0G0S2S1SbU2S2aA4S0G0S2S1SbUaSdS80A1A4S0G0S2S1SbU5S4SbLnz;Vnz;S2bS20X4x2A4S0G0S2S1SbUeVk1;A4S0G0S2S1SbUfS22A4S0G0S2S1SbU10S7cS33SdN1A1A2A4S0G0S2S1SbU6S22A4S0G0S2S1SbU7S3aA4S0G0S2S1SbU11S2bA4S3G0A1A3A3A3A3A3A3A3A3A3S56A3A2").
Definition F_nz (nz : bool) : sprop := ltac2:(tb__ "0|1|
S4SfLnz;Vnz;S12S95S2bSdZ0A1A3M0S13G0A1X4x2").
Definition F_go : sprop := ltac2:(tb__ "0|0|
S13S12S90S85S3aA3A1").
Definition F_stop : sprop := ltac2:(tb__ "0|0|
S12S90S85S3aA3").
Definition OC (sw : sobj) : list sobj := OH sw.
Definition O_gqC (nz : bool) : sobj := ltac2:(tb__ "0|0|
S86S7cS33SdN1A1A2S2bS4SbLnz;Vnz;S5fS20X4x2S3aA4").
Definition Cont0 (nz : bool) : axst := ltac2:(tb__ "0|0|
S21S24S39Vnz;SdZ1A1A2S35S25S20S22S20S26A4A1S0SeS36Vnz;A1S0SeS29S20S26A2S3SeA1A3A3S5SfS2cS0SfS4fS0SfS34Vnz;A1S3SfA1A3A3A3S23A6").
Definition Exit0 (nz : bool) : axst := ltac2:(tb__ "0|1|
S21S27S39Vnz;SdZ1A1M0A2S35S25G0S22S22S26A4A1S0SeS36Vnz;A1S0SeS29S20S26A2S3SeA1A3A3S5SfS2cS0SfS50S0SfS34Vnz;A1S3SfA1A3A3A3S23A6").
Definition Contk (nz : bool) : axst := ltac2:(tb__ "0|0|
S21S24S39Vnz;S7cS3bSdZ1A1A2A2S35S25S5dS47S5eS7cS48S26A2A4A1S0SeS36Vnz;A1S0SeS29S20S26A2S0SeS41S22S46A2S3SeA1A3A3A3S5SfS3eS0SfS4fS0SfS34Vnz;A1S3SfA1A3A3A3S23A6").
Definition Exitk (nz : bool) : axst := ltac2:(tb__ "0|1|
S21S27S39Vnz;S7cS3bSdZ1A1A2M0A2S35S25G0S47S22S7cS48S26A2A4A1S0SeS36Vnz;A1S0SeS29S20S26A2S0SeS41S22S46A2S3SeA1A3A3A3S5SfS3eS0SfS50S0SfS34Vnz;A1S3SfA1A3A3A3S23A6").

Definition vXK := SVar 184. Definition vXF := SVar 185. Definition vXL := SVar 186. Definition vXS := SVar 187.
Definition Xg : axst := ltac2:(tb__ "0|0|
S21S27S44S28S25S61S60S62S63A4A1S3SeA1S96S82A1S23A6").
Definition O_mtx00 : sobj := ltac2:(tb__ "0|4|
S9dSdZ0A1S9cS80Z98A2M0S9cS80Z9cA2S0S7S7S1fS1A2M1SbA2M2S2G1SbS2S1fS1S9cS80Z99A2U1M3A4S20A4S0G2S2G1SbS2S1fS1G0G3A4S20A4S0G2S2G1SbS2S1fS1S9cS80Z9aA2U2A4S20A4S3G2A1A3A3A3A4").
Definition regsD : list sv := ltac2:(tb__ "0|1|
S7eS44S0S7S1SbA2M0S2S1SbU1SdS42A1A4S0G0S2S1SbUbS2aA4S3G0A1A3A3A2").
Definition PD : axst := ltac2:(tb__ "0|1|
S21S3dS71S5SeS30S3S10A1S25S61S60S62S63A4A2S0SeS40S0SeS84S3SeA1M0A3A3A3G0S96S82A1S23A6").

Definition SWD (tk tf tl ts : sv) : sobj := ltac2:(tb__ "0|2|
S15ScPaA1SdNa8A1M0SdZ0A1S5S10S5cVtk;Vtf;Vtl;Vts;A4S0S10S11G0Z8M1ScP2dA1A3S0S10S11SdNa0A1G1ScP2cA1A3S0S10S11SdN98A1G1ScP2bA1A3S0S10S11SdN90A1G1ScP2aA1A3S0S10S11SdN88A1G1ScP29A1A3S0S10S11SdN80A1G1ScPb3A1A3S0S10S11SdN78A1G1ScPb2A1A3S0S10S11SdN70A1G1ScPb1A1A3S0S10S11SdN68A1G1ScPafA1A3S0S10S11SdN60A1G1ScPaeA1A3S0S10S11SdN58A1G1SdS42A1A3S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3S14A5").

Definition regsRR : list sv := ltac2:(tb__ "0|1|
S7eS87S0S7S1SbA2M0S2S1SbU2S2aA4S0G0S2S1SbU1ScPb8A1A4S0G0S2S1SbU5ScPb9A1A4S0G0S2S1SbU6ScPbaA1A4S0G0S2S1SbU7ScPbbA1A4S0G0S2S1SbUaScPbcA1A4S0G0S2S1SbUbScPbdA1A4S0G0S2S1SbUcScPbeA1A4S0G0S2S1SbUdScPbfA1A4S0G0S2S1SbUeScPc0A1A4S0G0S2S1SbUfScPc1A1A4S0G0S2S1SbU10ScPc2A1A4S0G0S2S1SbU11ScPc3A1A4S0G0S2S1SbU1cScPc4A1A4S0G0S2S1SbU1dScPc5A1A4S0G0S2S1SbU1eScPc6A1A4S0G0S2S1SbU1fScPc7A1A4S0G0S2S1SbU8ScPaeA1A4S0G0S2S1SbU9ScPafA1A4S0G0S2S1SbU12ScPb1A1A4S0G0S2S1SbU13ScPb2A1A4S0G0S2S1SbU14ScPb3A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition RR : axst := ltac2:(tb__ "0|1|
S21S42S73S5SeS30S55S54ScPa0A1ScPa1A1ScPa2A1ScPa3A1A4A2S0SeS40S0SeS84S3SeA1M0A3A3A3G0S96S82A1S23A6").
Definition post_ruR : list (nat * sv) := ltac2:(tb__ "0|1|
S0S7S1SbA2M0S2S1SbU5ScPb9A1A4S0G0S2S1SbU6ScPbaA1A4S0G0S2S1SbU7ScPbbA1A4S0G0S2S1SbUaScPbcA1A4S0G0S2S1SbUbScPbdA1A4S0G0S2S1SbUcScPbeA1A4S0G0S2S1SbUdScPbfA1A4S0G0S2S1SbUeScPc0A1A4S0G0S2S1SbUfScPc1A1A4S0G0S2S1SbU10ScPc2A1A4S0G0S2S1SbU11ScPc3A1A4S0G0S2S1SbU1cScPc4A1A4S0G0S2S1SbU1dScPc5A1A4S0G0S2S1SbU1eScPc6A1A4S0G0S2S1SbU1fScPc7A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PostQ3R : axst := ltac2:(tb__ "0|1|
S21S69S7eS87S70A2S5SeS30S55S54ScPa0A1ScPa1A1ScPa2A1ScPa3A1A4A2S0SeS40S0SeS84S3SeA1M0A3A3A3G0S96S82A1S23A6").

Definition runP : list leafA := ltac2:(tb__ "0|0|
S7bU258S0S1fS24S0S1fS27S0S1fS3fS0S1fS89S0S1fS53S3S1fA1A3A3A3A3A3S2fA3").
Definition run0 : list leafA := ltac2:(tb__ "0|0|
S7bU12cS0S1fS24S0S1fS27S0S1fZ3e268S3S1fA1A3A3A3S2dA3").
Definition runk : list leafA := ltac2:(tb__ "0|0|
S7bU12cS0S1fS24S0S1fS27S0S1fZ3e268S3S1fA1A3A3A3S2eA3").
Definition runS1 : list leafA := ltac2:(tb__ "0|0|
S7bU64S0S1fS3dS3S1fA1A3S31A3").
Definition runS2 : list leafA := runA 100 [] RR.
Lemma runP_eq : ltac2:(tb__ "0|0|
S75S9S7aA1S7bU258S0S1fS24S0S1fS27S0S1fS3fS0S1fS89S0S1fS53S3S1fA1A3A3A3A3A3S2fA3S58A3"). Proof. unfold runP. reflexivity. Qed.
Lemma run0_eq : ltac2:(tb__ "0|0|
S75S9S7aA1S7bU12cS0S1fS24S0S1fS27S0S1fZ3e268S3S1fA1A3A3A3S2dA3S57A3"). Proof. unfold run0. reflexivity. Qed.
Lemma runk_eq : ltac2:(tb__ "0|0|
S75S9S7aA1S7bU12cS0S1fS24S0S1fS27S0S1fZ3e268S3S1fA1A3A3A3S2eA3S5bA3"). Proof. unfold runk. reflexivity. Qed.
Lemma runS1_eq : ltac2:(tb__ "0|0|
S75S9S7aA1S7bU64S0S1fS3dS3S1fA1A3S31A3S59A3"). Proof. unfold runS1. reflexivity. Qed.
Lemma runS2_eq : ltac2:(tb__ "0|0|
S75S9S7aA1S7bU64S3S1fA1S38A3S5aA3"). Proof. unfold runS2. reflexivity. Qed.

Definition TsP : list axst := ltac2:(tb__ "0|0|
S0S77S52S0S77S51S0S77S52S0S77S51S0S77S67S3S77A1A3A3A3A3A3").
Definition Ts0 : list axst := ltac2:(tb__ "0|0|
S0S77S4bS6A1S0S77S49S6A1S0S77S4bS8A1S0S77S49S8A1S3S77A1A3A3A3A3").
Definition Tsk : list axst := ltac2:(tb__ "0|0|
S0S77S4cS6A1S0S77S4aS6A1S0S77S4cS8A1S0S77S4aS8A1S3S77A1A3A3A3A3").
Lemma chkP : ltac2:(tb__ "0|0|
S75S4S9aS58S6cA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk0 : ltac2:(tb__ "0|0|
S75S4S9aS57S6bA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkk : ltac2:(tb__ "0|0|
S75S4S9aS5bS6dA2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkS1 : ltac2:(tb__ "0|0|
S75S4S9aS59S0S77S66S3S77A1A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkS2 : ltac2:(tb__ "0|0|
S75S4S9aS5aS0S77S68S3S77A1A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxs : ltac2:(tb__ "0|5|
S76S76S75S4S16S78S2fA1M0A1S8A3S9bS7dS17G0A1A2A2S76S76S75S4S16S78S2dA1M1A1S8A3S9bS7dS17G1A1A2A2S76S76S75S4S16S78S2eA1M2A1S8A3S9bS7dS17G2A1A2A2S76S76S75S4S16S78S31A1M3A1S8A3S9bS7dS17G3A1A2A2S76S75S4S16S78S38A1M4A1S8A3S9bS7dS17G4A1A2A2A2A2A2A2").
Proof. repeat split; try reflexivity; unfold Pos.le; cbn; discriminate. Qed.

Lemma pres_wf : ltac2:(tb__ "0|0|
S76S75S4S79S2fA1S6A3S76S75S4S18S78S2fA1A1S6A3S76S75S4S79S2dA1S6A3S76S75S4S18S78S2dA1A1S6A3S76S75S4S79S2eA1S6A3S76S75S4S18S78S2eA1A1S6A3S76S75S4S79S31A1S6A3S76S75S4S18S78S31A1A1S6A3S76S75S4S79S38A1S6A3S75S4S18S78S38A1A1S6A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQ3R_states.

(* [comment removed for export] *)
Module CertCallocS1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "bool"; "None"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "cell"; "SVar"; "mkCell"; "SPUle"; "SAlu"; "SPUlt"; "SPBranch"; "FcsrFrm0"; "mkSS"; "sobj"; "SMd"; "SPNot"; "DUnknown"; "SPAlign"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "BC_GEU"; "M_MUL"; "M_MULHU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "P0c"; "prodc"; "F_hi_p"; "F_lo_p"; "V_C"; "V_S"; "s1_exits"; "rup8p"; "F_arg"; "s1_cuts"; "stop_le"; "stop_pc"; "E_pre"; "F_s1"; "mhc"; "neededp"; "pre_regs_c"; "s1_cuts_pc"; "s1_cuts_pcs"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "mkA"; "last_link"; "AE_A"; "A_globals"; "V_DEPTH"; "ae_calloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "mkVNA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "V_TSZ"; "vSB"; "rzf_hi"; "rzf_lo"; "rzf_rz"; "RT_m1"; "neededx"; "vRIS"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1.S1"; "E_regs_g"; "E_regs"; "F_fam"; "F_fam_p"; "sw_c"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import ListNotations.
Open Scope Z_scope.

Notation vSB := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.vSB.
Notation vRIS := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.vRIS.
Notation RT_m1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.RT_m1.
Notation rup8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.rup8.
Notation F_hi := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.F_hi.
Notation F_lo := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.F_lo.
Notation rzf_lo := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.rzf_lo.
Notation rzf_hi := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.rzf_hi.
Notation rzf_rz := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.rzf_rz.
Notation neededx := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.neededx.
Notation V_TSZ := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.V_TSZ.
Notation O_insta := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_insta.
Notation O_insta2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_insta2.
Notation O_instb := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_instb.
Notation O_rss := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_rss.
Notation O_cfb := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_cfb.
Notation O_cfc := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_cfc.
Notation O_rms := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_rms.
Notation O_ppf := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_ppf.
Notation O_hooks := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_hooks.
Notation O_lsan := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_lsan.
Notation O_cft := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_cft.
Notation O_afl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_afl.
Notation O_csd := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_csd.
Notation O_die := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.O_die.

Definition V_C : positive := 143%positive.
Definition V_S : positive := 144%positive.

Definition prodc : sv := ltac2:(tb__ "0|0|
S17S22SeS29A1SeS28A1A3").
Definition mhc : sv := ltac2:(tb__ "0|0|
S17S23SeS29A1SeS28A1A3").

Definition F_s1 : list sprop := ltac2:(tb__ "0|1|
S0SbS1aP9bZ10A2S0SbS10SaS65A1S52A2S0SbS10S52SaS5bS5bZ7fffff800000S64A2Z1000A2A1A2S0SbS13S1fS58S11S1eS52SaS64A1A3A3S0SbS10SaZ1A1SePcA1M0A2S0SbS12G0SaS5aZ2Z27A2A1A2S0SbS18S13S1fS11S1eSePaA1SaN858A1A3SaZ0A1A3A1S2SbA1A3A3A3A3A3A3A3").
Definition F_arg : list sprop := ltac2:(tb__ "0|1|
S0SbS10SaZ1A1M0SeS28A1A2S0SbS10G0SeS29A1A2S0SbS13S1fS32SaZ0A1A3S0SbS10G0S25A2S0SbS12S25SaS5aZ2Z27A2A1A2S2SbA1A3A3A3A3A3").

Definition rup8p : sv := ltac2:(tb__ "0|0|
S11S20S11S1eS25SaZ7A1A3SaZfffffffffffffff8A1A3").
Definition F_hi_p : list sprop := ltac2:(tb__ "0|0|
S0SbS10SaZfc01A1S25A2S2SbA1A3").
Definition F_lo_p : list sprop := ltac2:(tb__ "0|0|
S0SbS12S25SaZfc01A1A2S0SbS10S2bSaZfc00A1A2S2SbA1A3A3").
Definition neededp (k : Z) : sv := ltac2:(tb__ "0|1|
S6ScL_;M0S59Vk;Z0A2SaZ18A1G0S59Vk;Z8A2S11S1eS2bSaZ1000A1A3S11S1eS2bSaS55Vk;A1A1A3X6x2X6x2").

Definition pre_regs_c : list sv := ltac2:(tb__ "0|1|
S4cS4eS0S5S1ScA2M0S3S1ScU4SaS62A1A4S0G0S3S1ScUaSeS28A1A4S0G0S3S1ScUbSeS29A1A4S2G0A1A3A3A3A2").

Section S1.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.
Let FACTS : list sprop := ltac2:(tb__ "0|0|
S4SbS4SbS4SbS45VW;Vst;A2S43S42A1A3S50A3S31A3").
Let OBJS (sw : sobj) : list sobj := ltac2:(tb__ "0|0|
S4S16S0S16Vsw;S4S16S46VW;A1S3fA3A3S56A3").

Definition P0c (fx : list sprop) : axst := ltac2:(tb__ "0|0|
S3cS15S41S3eA1S34S4bS14S7ScA1VOBJS;S44A1S4SbS4SbVFACTS;S2cA3Vfx;A3S4fS8A9S2S5ScScA2A1A2").

Definition sw_c (nt : sv) : sobj := ltac2:(tb__ "0|9|
S1bSePaA1M0SeS40A1SaZ0A1M1S0SdSfSaN918A1Z8M2SaZ3c464A1A3S0SdSfSaN908A1G2G1A3S0SdSfSaN900A1G2SaZ10A1A3S0SdSfSaN8f8A1G2SeP2fA1A3S0SdSfSaN8f0A1G2SeP2eA1A3S0SdSfSaN8e8A1G2SeP2dA1A3S0SdSfSaN8e0A1G2SeP2cA1A3S0SdSfSaN8d8A1G2SeP2bA1A3S0SdSfSaN8d0A1G2S11S1eG0SaN59A1A3A3S0SdSfSaN8c8A1G2S11S1eG0SaN858A1M3A3M4A3S0SdSfSaN8c0A1G2SaZ1A1M5A3S0SdSfSaN8b8A1G2G5A3S0SdSfSaN8b0A1G2SaZedd98A1A3S0SdSfSaN8a8A1G2G4A3S0SdSfSaN8a0A1G2Vnt;A3S0SdSfSaN898A1G2SaZ3cbbcA1A3S0SdSfSaN890A1G2G5A3S0SdSfSaN888A1G2SaZ5e53cA1M6A3S0SdSfSaN880A1G2SeS28A1A3S0SdSfSaN878A1G2SeS29A1A3S0SdSfSaN870A1G2G0A3S0SdSfSaN868A1G2SaZ5e5acA1A3S0SdSfG3G2S11S1eG0SaN848A1M7A3A3S0SdSfSaN850A1Z4M8SeS51A1A3S0SdSfSaN84cA1G8G1A3S0SdSfG7G2G6A3S0SdSfSaN50A1G2G0A3S0SdSfSaN40A1G2SeP2aA1A3S0SdSfSaN38A1G2SeP29A1A3S0SdSfSaN30A1G2SeP28A1A3S0SdSfSaN28A1G2SeP27A1A3S0SdSfSaN20A1G2SeP26A1A3S0SdSfSaN18A1G2SeP1dA1A3S0SdSfSaN10A1G2SeP1cA1A3S0SdSfSaN8A1G2SePbA1A3S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S19A5").
Definition sw_s1 : sobj := sw_c (SVar 12).

Definition E_regs_g (nt : sv) (nd : sv) (k : Z) : list sv := ltac2:(tb__ "0|6|
S4cS4dS38A1S0S5S1ScA2M0S3S1ScU1SaZ3c480A1A4S0G0S3S1ScU2S11S1eSePaA1M1SaN910A1A3A4S0G0S3S1ScU4SaS62A1A4S0G0S3S1ScU8SaS6S1dL_;S59Vk;Z8M2A2Z0Z1M3X6x2A1A4S0G0S3S1ScU9Vnt;A4S0G0S3S1ScUaSaZedd98A1M4A4S0G0S3S1ScUbS11S1eS63SaZd0A1A3A4S0G0S3S1ScUcVnd;A4S0G0S3S1ScUdSaG2A1M5A4S0G0S3S1ScU12G5A4S0G0S3S1ScU13Vnd;A4S0G0S3S1ScU14SaS55Vk;A1A1A4S0G0S3S1ScU15Vnt;A4S0G0S3S1ScU16G4A4S0G0S3S1ScU17S11S1eG1SaN858A1A3A4S0G0S3S1ScU18SaZfffffffffffffff8A1A4S0G0S3S1ScU19SaZ7A1A4S0G0S3S1ScU1aS63A4S0G0S3S1ScU1bSaG3A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition E_regs (k : Z) : list sv := ltac2:(tb__ "0|0|
S5cSePcA1S57Vk;A1Vk;A3").
Definition F_fam (k : Z) : list sprop := ltac2:(tb__ "0|2|
S0SbS10SaS54Vk;A1A1SePcA1M0A2S0SbS12G0SaS53Vk;A1A1A2S0SbS10SaZ1A1SeS51A1M1A2S0SbS10G1SaVtmax;A1A2S2SbA1A3A3A3A3").
Definition F_fam_p (k : Z) : list sprop := ltac2:(tb__ "0|1|
S0SbS10SaS54Vk;A1A1S25A2S0SbS12S25SaS53Vk;A1A1A2S0SbS10SaZ1A1SeS51A1M0A2S0SbS10G0SaVtmax;A1A2S2SbA1A3A3A3A3").

Definition E_pre (k : Z) : axst := ltac2:(tb__ "0|0|
S3cS15Z40a18S5cS25S33Vk;A1Vk;A3S4bS14S7ScA1VOBJS;S60S25A1A1S4SbS4SbVFACTS;S2cA3S5fVk;A1A3S4fS8A9S2S5ScScA2A1A2").
Definition E_s1 (k : Z) : axst := ltac2:(tb__ "0|0|
S3cS15Z40a18S5dVk;A1S4bS14S7ScA1VOBJS;S61A1S4SbVFACTS;S5eVk;A1A3S4fS8A9S2S5ScScA2A1A2").
End S1.

Definition s1_cuts (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|1|
S0S1cS24S3bVn;A1M0Vst;S26A3S0S1cS24G0Vst;S27A3S2S1cA1A3A3").
Definition s1_exits (n : nat) (st : ustop) (tmax : Z) : list axst := ltac2:(tb__ "0|0|
S37S1dS1cS30S3bVn;A1Vst;Vtmax;A3S0S1dZ0S0S1dZ1S0S1dZ2S0S1dZ3S0S1dZ4S0S1dZ5S0S1dZ6S0S1dZ7S0S1dZ8S2S1dA1A3A3A3A3A3A3A3A3A3A4").
Definition s1_cert (n : nat) (st : ustop) (tmax : Z) : bool := ltac2:(tb__ "0|0|
S49S39Ufa0S0S1dZ40a18S2S1dA1A3S38S2dVn;Vst;A2S2aVn;Vst;Vtmax;A3A6").
Definition s1_ecert (n : nat) (st : ustop) (tmax : Z) : bool := ltac2:(tb__ "0|2|
S4aS39Ufa0S0S1dZ40a18S2S1dA1A3S38S37S1cS48S1cS47R1Z1SaZ0M0A1M1A3Lc;S2dVn;Vst;A2A4S37S1cS48S1cS47R1G0G1A3Le;S2aVn;Vst;Vtmax;A3A4A6").

Definition stop_pc (W : list ulink) : list sprop := ltac2:(tb__ "0|2|
S5S5ScScA2M0ScA2S9SbA1M1Lx;S3dSeP1cA1VW;A2G0ScG0G1Lp;R2ScScS0SbS18S13S21R3SaZ1000A1A3A1S2SbA1A3Lnbp;Lbp;X5x1Lpc;Lp;X5x1").
Definition stop_le (W : list ulink) : list sprop := ltac2:(tb__ "0|2|
S5S5ScScA2M0ScA2S9SbA1M1Lx;S3dSeP1cA1VW;A2G0ScG0G1Lp;R2ScScS0SbS10R1R2A2S2SbA1A3Lnbp;Lbp;X5x1Lpc;Lp;X5x1").
Definition s1_cuts_pc (n : nat) : list axst := ltac2:(tb__ "0|3|
S0S1cS24S3bVn;A1M0S3aS4SbS26S2fG0A1M1A3A3S0S1cS24G0S3aS4SbS27G1A3A3S0S1cS24G0S3aS4SbS26S2eG0A1M2A3A3S0S1cS24G0S3aS4SbS27G2A3A3S2S1cA1A3A3A3A3").

Definition s1_cuts_pcs (n : nat) (st : ustop) : list axst := ltac2:(tb__ "0|3|
S0S1cS24S3bVn;A1M0Vst;S4SbS26S2fG0A1M1A3A3S0S1cS24G0Vst;S4SbS27G1A3A3S0S1cS24G0Vst;S4SbS26S2eG0A1M2A3A3S0S1cS24G0Vst;S4SbS27G2A3A3S2S1cA1A3A3A3A3").
Definition s1_ecert_pcs (n : nat) (st : ustop) (tmax : Z) : bool := ltac2:(tb__ "0|2|
S4aS39Ufa0S0S1dZ40a18S2S1dA1A3S38S37S1cS48S1cS47R1Z1SaZ0M0A1M1A3Lc;S36Vn;Vst;A2A4S37S1cS48S1cS47R1G0G1A3Le;S2aVn;Vst;Vtmax;A3A4A6").
Definition s1_cert_pc (n : nat) (tmax : Z) : bool := ltac2:(tb__ "0|0|
S49S39Ufa0S0S1dZ40a18S2S1dA1A3S38S35Vn;A1S2aVn;S3aVtmax;A3A6").

End CertCallocS1.

(* [comment removed for export] *)
Module InvD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_Km"; "aa_Kf"; "aa_depot"; "DG"; "aa_V"; "aa_ptr_committed"; "aa_sec"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_q_global"; "aa_q_thread"; "mkAA"; "dFB"; "dFP"; "dN"; "dNB"; "ag_top"; "ageom"; "depot_state"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "app"; "bool"; "false"; "length"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD.WithSegs"; "AInvX"; "with_depot"; "bumpK"; "ledger_inv_nd"; "model_inv_nd"; "rest_inv_nd"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_maps"; "VmMaps"; "alloc_top"; "vm_limit"; "vm_noaccess"; "vm_reserved"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "fs_footb"; "geom_ok"; "in_maps"; "inv3"; "bandtp_inv"; "fs_inv"; "ia_inv"; "live_block_repr"; "live_sep"; "misc_inv"; "primary_repr"; "quarantine_repr"; "secondary_repr"; "thread_inv"; "vm_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "depot_inv"; "DFP"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "gap_ok"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "maskv"; "restrictv"; "rtc_inv"; "view"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Let segs : list Segment := segsA.

Definition rest_inv_nd (m : bview) (A : AA) : Prop := ltac2:(tb__ "0|0|
S0S45VA;A1S0S44Vm;VA;A2S0S47Vm;VA;A2S0S49Vm;VA;A2S0S48Vm;VA;A2S0S2S0S43Vm;VA;A2S0S4aVm;S4VA;A1A2S46Vm;A1A2A2A2A2A2A2A2A2").

Definition ledger_inv_nd (A : AA) (md : Model) (tp : list word) : Prop := ltac2:(tb__ "0|a|
S30Vmd;A1S32S0S1S22S28S37Q40M0A1M1G1A2M2A1S36R1A1M3S4fVsegs;A1A3S0S52S31R1A1M4S51S50A3S0S5dS23G2G3G4A3A1S0S5cVA;R1A2S0S2S0S2S0S0S1dZ0M5SaVA;A1M6A2S1dG6S1eS20Z8S5VA;A1M7A2S5aA2A2A2S0S0G1G1S4eG2S27G1G1R2R1A4M8S31R3A1A3S1fG5S38G0R2A2A2M9F_;Fs;Fb;S0S3fR1S58S59A3S3fR1S56S57A3A2A2S0S1dS21S26S1cSbVA;A1A2A1G7A2G1G1S4eG2G8S35R3A1A3G9F_;Fs;Fb;A2A2A2A2A2A2A2A2A2TV;").

Definition model_inv_nd (A : AA) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|2|
S0S4bVA;Vmd;A2S0S1dS1eS54Vmd;Vtp;A2S5eVA;A1A2S5bVA;A1A2S0S1S3bS34S30Vmd;A1M0A1S55A3S0S1dZ0M1S9VA;A1A2S0S1dG1S5VA;A1A2S0S1dG1S6VA;A1A2S0S1S3bS33G0A1S19S4VA;A1A1A3S2cVA;Vmd;Vtp;A3A2A2A2A2A2A2A2").

Definition AInvX (A : AA) (rho : valuation) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|1|
S63Vsegs;S3aVrho;A1A2S5fS4VA;A1S1aS0S3eR1A1S0S62R2R1A2S0S42S61S3dR1A1M0R2A2VA;A2S0S2eS60G0R2A2VA;A2S0S2dVA;Vtp;Vmd;A3S0S40VA;A1S41R2Vtp;A2A2A2A2A2A2A2TG;Tm;").

Lemma fs_footb_DFP : ltac2:(tb__ "0|0|
S3S3bS3eS4R2A1A1S40R3A1S4dS7R4A1R3A2S1S24S3dS4R5A1R4A2S25A3F_;F_;F_;Fa;FA;").
Proof.
  intros A a HG HI3 Ha.
  pose proof (geom_nums _ HG) as (F1 & F2 & _). rewrite FS_total_val in F2. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (Sh_in_band (ag_fsb (aa_geom A) + FS_frames_off) ltac:(rewrite FS_frames_off_val; unfold IMG_HI in F1; lia)) as SB1.
  assert (SU : Sh (ag_fsb (aa_geom A) + 11571200) <= SHADOW_BAND_HI).
  { unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END. pose proof (Z.div_le_upper_bound (ag_fsb (aa_geom A) + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  destruct HI3 as (_ & _ & _ & _ & X5 & _).
  assert (BLK : forall b L, In (b, L) (dblocks (aa_depot A)) -> b <= a < b + L -> fs_footb (aa_geom A) a = false).
  { intros b L Hb Hab. destruct (X5 (b, L) Hb) as (DI & _ & _ & _ & SF & _). cbn [fst snd] in DI, SF. unfold sepZ in SF. cbn [fst snd] in SF.
    destruct DI as (_ & _ & _ & _ & WB). rewrite FS_total_val in SF.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [clear -SF Hab; lia | clear -SF Hab; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -WB Hab SB1 SU. lia. }
  destruct Ha as [Hs|[(b & Hb & Hab)|(b & Hb & Hab)]].
  - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_HI in F1.
    apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; [lia | lia |].
    left. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in SB1. lia.
  - apply (BLK b NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
  - apply (BLK b FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
Qed.

Theorem AInvA_X : ltac2:(tb__ "0|1|
S3S39S22S37Q40A1A1S2fS3cVsegs;R4R3R2R1A5S0S29R5R4R3R2A4S0S4cVsegs;S7R5A1M0R4R2R3A5S1dS17G0A1S1eS1eS5R5A1S6R5A1A2Z1A2A2A2A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. pose proof (AInvA_depot A rho tp md HA) as HD.
  destruct HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & L6 & L7 & L8 & L9).
  split; [| split; [exact HD | exact L6]].
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split.
  { destruct HRest as (R1 & R2 & R3 & R4 & R5 & _ & R7 & R8 & R9).
    exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj I (conj R7 (conj R8 R9)))))))). }
  split; [|exact (conj HI3 HB)].
  exact (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj I (conj I (conj L7 (conj L8 L9))))))))))))))).
Qed.

Theorem X_AInvA : ltac2:(tb__ "0|0|
S3S39S22S37Q40A1A1S2fS29R4R3R2R1A4S4cVsegs;S7R5A1R4R2R3A5S1dS17S7R6A1A1S1eS1eS5R6A1S6R6A1A2Z1A2A2S3cVsegs;R7R6R5R4A5F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB) [DM DV] L6.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split.
  { destruct HRest as (R1 & R2 & R3 & R4 & R5 & _ & R7 & R8 & R9).
    refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj _ (conj R7 (conj R8 R9)))))))).
    unfold depot_wf. eapply depot_mem_frame; [|exact DM]. intros a Ha. apply maskv_out. exact (fs_footb_DFP A a HG HI3 Ha). }
  split; [|exact (conj HI3 HB)].
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & _ & L7 & L8 & L9).
  exact (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj DV (conj L6 (conj L7 (conj L8 L9))))))))))))))).
Qed.

Definition bumpK (A : AA) : AA := ltac2:(tb__ "0|0|
S14S4VA;A1SdVA;A1ScVA;A1SbVA;A1SaVA;A1S11VA;A1S13VA;A1S12VA;A1S7VA;A1SfVA;A1SeVA;A1S10VA;A1S9VA;A1S1eS5VA;A1Z1A2S6VA;A1Af").
Definition with_depot (A : AA) (G : DG) : AA := ltac2:(tb__ "0|0|
S14S4VA;A1SdVA;A1ScVA;A1SbVA;A1SaVA;A1S11VA;A1S13VA;A1S12VA;A1VG;SfVA;A1SeVA;A1S10VA;A1S9VA;A1S5VA;A1S6VA;A1Af").

Lemma AInvX_bumpK : ltac2:(tb__ "0|0|
S3S39S22S37Q40A1A1S2fS29R4R3R2R1A4S29S2bR5A1R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|exact (conj HI3 HB)].
  unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
  rewrite (prim_credit_same A (bumpK A) eq_refl).
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpK] in HM |- *.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & L6 & L7 & L8 & L9 & L10).
  split; [exact V1|]. split; [unfold BETA1 in *; set (pc := prim_credit A) in *; clearbody pc; clear -V2 V5; lia|]. split; [exact V3|]. split; [exact V4|]. split; [clear -V5; lia|].
  split; [exact V6|]. split; [exact V7|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact I|].
  split; [exact I|]. split; [unfold kPtrArrayCommit in *; clear -L7 V5; lia|].
  split; [exact L8|split; [clear -L9; lia | exact L10]].
Qed.

Theorem AInvA_bumpK : ltac2:(tb__ "0|0|
S3S39S22S37Q40A1A1S2fS3cVsegs;R4R3R2R1A5S3cVsegs;S2bR5A1R4R3R2A5F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. destruct (AInvA_X A rho tp md HA) as (HX & HD & L6).
  apply X_AInvA; [exact (AInvX_bumpK A rho tp md HX) | exact HD | cbn [aa_depot aa_Km aa_Kf bumpK]; lia].
Qed.

Lemma AInvX_mat : ltac2:(tb__ "0|0|
S3S39S22S37Q40A1A1S2fS2fS29R5R4R3R2A4S53Vsegs;R4R3R2A4S29R7R6R5R3A4F_;F_;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' (HG & HR & HF & HRest & HM & HI3 & HB) (Hex & Hpaid & _). unfold AInvX in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [| exact (conj HI3 HB)].
  destruct Hex as (mat' & ->).
  assert (EV : m_vmmaps (with_vm_backing (m_vm_lazy md) mat' md) = m_vmmaps md) by apply m_vmmaps_with_vm_backing.
  assert (EL : m_vm_lazy (with_vm_backing (m_vm_lazy md) mat' md) = m_vm_lazy md) by apply m_vm_lazy_with_vm_backing.
  unfold model_inv_nd, vm_geom, ledger_inv_nd in HM |- *. rewrite EV, EL, Hpaid. exact HM.
Qed.

Lemma with_depot_depot : ltac2:(tb__ "0|0|
S3S8S1S1bS7S2aR2R1A2A1R1A3FG;FA;"). Proof. reflexivity. Qed.
Lemma bumpK_with_depot : ltac2:(tb__ "0|0|
S3S8S1S3S2bS2aR2R1A2A1S14S4R2A1SdR2A1ScR2A1SbR2A1SaR2A1S11R2A1S13R2A1S12R2A1R1SfR2A1SeR2A1S10R2A1S9R2A1S1eS5R2A1Z1A2S6R2A1AfA3FG;FA;").
Proof. reflexivity. Qed.

Lemma AInvX_depot_same : ltac2:(tb__ "0|1|
S3S8S8S39S22S37Q40A1A1S2fS1S22S3bA1M0S18R4A1S18R5A1A3S1G0S15R5A1S15R6A1A3S1G0S16R6A1S16R7A1A3S29S2aR9R8A2R6R5R4A4S29S2aRaR8A2R7R6R5A4F_;F_;F_;F_;Fmd;Ftp;Frho;FG';FG;FA;").
Proof.
  intros A G G' rho tp md EN EF EP (HG & HR & HF & HRest & HM & HI3 & HB).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|split; [|exact HB]].
  - unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD, dep_cost, dep_pages in HM |- *.
    rewrite (prim_credit_same A (with_depot A G) eq_refl) in HM. rewrite (prim_credit_same A (with_depot A G') eq_refl).
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec with_depot] in HM |- *. rewrite EN, EF, EP. exact HM.
  - unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global with_depot] in HI3 |- *.
    unfold dblocks in HI3 |- *. rewrite EN, EF. exact HI3.
Qed.
End WithSegs.
End InvD.

(* [comment removed for export] *)
Module F0A_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "nat"; "prod"; "app"; "andb"; "bool"; "false"; "length"; "list"; "option"; "fst"; "None"; "negb"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sprop"; "sv"; "SAlu"; "cell"; "SVar"; "mkObj"; "SPUle"; "SPUlt"; "DUnknown"; "SPBranch"; "mkCell"; "ss_facts"; "ss_next"; "SPNot"; "SPAlign"; "mkSS"; "ob_base"; "ob_lo"; "SAluW"; "SExt"; "ob_dflt"; "ob_hi"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "sv_eqb"; "ob_cells"; "swf"; "FcsrFrm0"; "SPEq"; "c_off"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "axwf"; "entailsA"; "la_reason"; "la_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "BC_EQ"; "ALU_AND"; "BC_NE"; "ALU_XOR"; "ALU_OR"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXRebase"; "AXUnbase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "vN8"; "qvar"; "vH3"; "vN8g"; "OFF_QC"; "PreQ1"; "cA"; "hw2"; "m8"; "map_objsF"; "on_obj"; "optR"; "vNLO"; "F_QB"; "OFF_PUT"; "O_qcF"; "add_cellsF"; "drop_cellsF"; "sD_of"; "sM_of"; "sQ_of"; "set_factsF"; "updrF"; "usz_e"; "vHW"; "FACTS"; "F_cas"; "F_p"; "F_typ"; "MSE"; "OBJS0"; "OFF_TR"; "O_blkN"; "O_gmax"; "O_hdr"; "O_iamP"; "O_pc24F"; "O_pckF"; "O_q80"; "O_sh"; "O_stQ"; "O_stT1"; "O_stT2"; "PSE"; "PostMS"; "PostQ1"; "RD_of"; "RM_of"; "RQ_of"; "RT_f"; "TM0_of"; "TQ0_of"; "VFACT"; "VOBJ"; "W_full"; "add_factsF"; "cQ"; "cp_baseF"; "iam_base"; "is_obj"; "len_e"; "rup_e"; "set_cellsF"; "shb"; "showLsF"; "vMINq"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "vPK"; "O_bh"; "vBS"; "vK"; "vNX"; "vQB"; "vQF"; "vQN"; "vQS"; "vSB"; "O_item"; "O_nb"; "O_sb"; "PostQ1A"; "PostQ1Be"; "PostQ1Bf"; "PreQ1A"; "PreQ1Be"; "PreQ1Bf"; "vCP"; "vCS"; "vMX"; "vST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "O_dpm"; "O_mlim"; "PostD"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "O_T0"; "O_T40"; "O_cfa"; "O_ctx8"; "O_ctx98"; "O_mcs"; "O_pga"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "TP_A";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "SHADOW_OFF"; "kQuarantineCacheMax"; "kQuarantineMax"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "AE_A"; "A_globals"; "V_FREE_A1"; "ae_free"; "free_depth"; "mkA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "NW2"; "O_T3168"; "O_ia"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "O_afl"; "O_cft"; "O_csd"; "O_die"; "O_hooks"; "O_rms"; "@Stdlib.Lists.List"; "combine"; "existsb"; "filter"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "pred"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition CASX : Z := 0x3bf94.
Definition DEPE : Z := 0x7e850.
Definition PSE : Z := 0x5f5bc.
Definition BIGX : Z := 0x406c8.
Definition MSE : Z := 0xde378.
Definition ENQE : Z := 0x40834.
Definition DRNE : Z := 0x3df8c.
Definition RETF : Z := 0x5e23c.
Definition OFF_QC : Z := -2176.
Definition OFF_TR : Z := -2112.
Definition OFF_PUT : Z := -2208.
Definition FUELF : nat := 4000%nat.

Definition vNLO : sv := SVar 103.
Definition vHW : sv := SVar 104.
Definition vN8 : sv := SVar 105.
Definition vN8g : sv := SVar 106.
Definition vH3 : sv := SVar 107.
Definition vMINq : sv := SVar 136.

Definition W_full : sobj := ltac2:(tb__ "0|0|
S18S17PaA1S17Sd4A1S11Z0A1S1S16A1S1bA5").

Definition O_blkN : sobj := ltac2:(tb__ "0|0|
S18S17PcA1S11Z0A1S4fS1S16A1S1bA5").

Definition iam_base : sv := ltac2:(tb__ "0|0|
S15S42S15S43S17PcA1S11Z20A1A3S11Z3A1A3").
Definition O_iamP : sobj := ltac2:(tb__ "0|1|
S18S89S11Zf2608A1M0S11Zf2610A1S0S16S1dG0Z8S11Z0A1A3S1S16A1A3S1bA5").

Definition O_hdr : sobj := ltac2:(tb__ "0|2|
S18S17PcA1S11N10A1M0S11N8A1S0S16S1dG0Z4M1S67A3S0S16S1dS11NcA1G1S5bA3S1S16A1A3A3S1bA5").

Definition O_stT1 : sobj := ltac2:(tb__ "0|0|
S18SbeS11Zad0A1S11Zae0A1S1S16A1S1bA5").
Definition O_stT2 : sobj := ltac2:(tb__ "0|0|
S18SbeS11Zae8A1S11Zc60A1S1S16A1S1bA5").

Definition O_q80 : sobj := ltac2:(tb__ "0|3|
S95S11Z0A1S91S96Z50A2M0S91S96Z58A2S0S4S4S37S3A2M1S14A2M2S2G1S14S2S37S3G0U8A4S11Sd1A1A4S1G2A1A3A4").
Definition O_gmax : sobj := ltac2:(tb__ "0|4|
S95S11Z0A1S91S96Z40A2M0S91S96Z50A2S0S4S4S37S3A2M1S14A2M2S2G1S14S2S37S3G0U8M3A4S11Sd2A1A4S0G2S2G1S14S2S37S3S91S96Z48A2G3A4S90A4S1G2A1A3A3A4").

Definition shb : sv := ltac2:(tb__ "0|0|
S15S41S15S43S17PcA1S11Z3A1A3S11Sd0A1A3").
Definition O_sh : sobj := ltac2:(tb__ "0|0|
S18S8eS11Z0A1S52S1S16A1S1bA5").

Inductive qvar := QA | QBe | QBf.
Definition cQ : sv := SAlu ALU_ADD vT (SLit 80).
Definition cA : sv := SAlu ALU_ADD vT (SLit 208).
Definition O_qcF (qn qf qb qs : sv) : sobj := ltac2:(tb__ "0|4|
S95S87Z0M0Z20S0S4S4S37S3A2M1S14A2M2S2G1S14S2S37S3G0U8M3A4Vqn;A4S0G2S2G1S14S2S37S3Z8G3A4Vqf;A4S0G2S2G1S14S2S37S3Z10G3A4Vqb;A4S0G2S2G1S14S2S37S3Z18G3A4Vqs;A4S1G2A1A3A3A3A3A4").
Definition O_pc24F (k : sv) : sobj := ltac2:(tb__ "0|4|
S95S55Z780M0Z790S0S4S4S37S3A2M1S14A2M2S2G1S14S2S37S3G0U4M3A4Vk;A4S0G2S2G1S14S2S37S3Z784G3A4SaeA4S0G2S2G1S14S2S37S3Z788U8A4SadA4S1G2A1A3A3A3A4").
Definition cp_baseF : sv := ltac2:(tb__ "0|0|
S15S41S55S15S42S15S41S99S11N1A1A3S11Z2A1A3A3").
Definition O_pckF : sobj := ltac2:(tb__ "0|1|
S18S88S11Z790A1M0S11Z794A1S0S16S1dG0Z4SacA3S1S16A1A3S1bA5").
Definition O_stQ : sobj := ltac2:(tb__ "0|3|
S95S55Za10M0Za18S0S4S4S37S3A2M1S14A2M2S2G1S14S2S37S3G0U8A4SafA4S1G2A1A3A4").

Definition RT_f : list sobj := ltac2:(tb__ "0|0|
S0S12Se3Z1A1S0S12Sc7S0S12Sc8S0S12ScbS0S12SccS0S12ScdS0S12Sc9S0S12ScaS0S12Sc2S0S12Sc3S0S12SbfS0S12Sc0S0S12Se2S0S12Sc1S0S12Sc5S0S12Sc6S0S12Sc4S0S12Se6S0S12Se7S0S12Sb5S0S12Sb6S0S12Se8S0S12Se9S0S12Se5S0S12Se4S0S12S75S0S12S70S0S12Sa5S0S12S78S0S12S77S0S12S79S0S12S72S0S12S71S0S12S76S0S12S6fS1S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition VOBJ (q : qvar) : list sobj := ltac2:(tb__ "0|4|
S50SaS12A1Lq;Vq;S0S12S5eSa0S9fS9eSa1A4M0S0S12S9aS9dS9bS9cA3S0S12Sa3S1S16A1M1A1S1S12A1M2A3A3A3S0S12S5eS11Z0A1S9fS9eSa1A4S0S12S73S99A1S0S12S74S0S12Sa4G1A1G2A3A3A3M3A3S0S12G0S0S12S9aS9dS9bS11Z3fdA1A3G3A3A3X50x3").
Definition F_QB : list sprop := ltac2:(tb__ "0|0|
S0S13S1aS11Z0A1S99A2S0S13S19S99S11Z100A1A2S0S13S21P9bZ10A2S0S13S19S11ScfA1Sa2A2S0S13S19Sa2S11S93S93Z7fffff800000Sd3A2Z1000A2A1A2S1S13A1A3A3A3A3A3").
Definition VFACT (q : qvar) : list sprop := ltac2:(tb__ "0|3|
S50SaS13A1Lq;Vq;S0S13S21P7aZ3A2M0S0S13S20S1cS44Sa0S11Z0A1A3A1M1S0S13S1aS9cS11Z3fdA1A2S1S13A1M2A3A3A3S5cS5S13S5cS0S13G0S0S13G1G2A3A3A3X50x3").
Definition PreQ1 (q : qvar) : axst := ltac2:(tb__ "0|0|
S50S3aLq;Vq;Sa9SaaSabX50x3").
Definition PostQ1 (q : qvar) : axst := ltac2:(tb__ "0|0|
S50S3aLq;Vq;Sa6Sa7Sa8X50x3").

Definition F_p : list sprop := ltac2:(tb__ "0|8|
S0S13S19S11S91Z7fff7f800000Z1000A2A1S17PaA1A2S0S13S21PcM0Z4A2S0S13S19S11S91ScfZ10A2A1S17G0A1M1A2S0S13S1aS15S41G1S17PdA1M2A3S11Z7fffff800000A1M3A2S0S13S19S11Z1A1G2A2S0S13S20S1cS44G1S11Z0A1A3A1S0S13S1aG1S11S92Z2M4Z2fA2A1M5A2S0S13S21P69Z3M6A2S0S13S19G2S4fA2S0S13S1aS4fS15S41G2S11Z8A1M7A3A2S0S13S19S15S41G1S4fA3G3A2S0S13S19G7S4fA2S0S13S1aS4fG5A2S0S13S35S15S42S52S11G6A1A3S4fA2S0S13S1aS52S11S92G4Z2cA2A1A2S1S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition m8 : sv := ltac2:(tb__ "0|0|
S15S42S15S41S17PcA1S11N10A1A3S11Z3A1A3").
Definition hw2 : sv := SExt true 32 vHW.
Definition F_cas : list sprop := ltac2:(tb__ "0|4|
S0S13S20S1cS46S15S45S56S11ZffA1M0A3S11Z2M1A1M2A3A1S0S13S1aS67S11S92G1Z20A2A1A2S0S13S1cS44S25S42G2S57A3G2A3S0S13S1cS44S25S42G0S57A3G0A3S0S13S1cS44S25S42S11Z3A1M3S57A3G3A3S1S13A1A3A3A3A3A3").

Definition F_typ : list sprop := ltac2:(tb__ "0|2|
S0S13S20S1cS46S26S10Q8M0S51A3S11Z3A1M1A3A1S0S13S20S1cS46S11Z1A1S15S45S26S8G0S15S43S51S11Z8A1A3A3G1A3A3A1S0S13S1aS51S11S92Z2Z20A2A1A2S1S13A1A3A3A3").
Definition FACTS (W : list ulink) (st : ustop) (q : qvar) : list sprop := ltac2:(tb__ "0|0|
S5S13S5S13S5S13S5S13S5S13SdcVW;Vst;A2SdbSd9A1A3Se0A3S6aA3S69A3S83Vq;A1A3").

Definition OBJS0 (W : list ulink) (q : qvar) : list sobj := ltac2:(tb__ "0|0|
S5S12S5S12S0S12S85S5S12SddVW;A1Sd6A3A3S80A3S84Vq;A1A3").
Definition P0_f (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|1|
SdaS22Sd8Sd5A1SbaSbcS0S4S3S14A2M0S2S3S14U4S11SceA1A4S0G0S2S3S14UbS17Sd7A1A4S1G0A1A3A3A2SbbS34SdS14A1S6dVW;Vq;A2S68VW;Vst;Vq;A3Se1S8A9S1S4S14S14A2A1A2").

Definition map_objsF (A : axst) (f : sobj -> sobj) : axst := ltac2:(tb__ "0|0|
S39VA;A1S30S3bVA;S22S2dR1A1S2eR1A1S2aR1A1S29R1A1S2fR1A1Sb9S12S12Vf;S2cR1A1A4S1eR1A1S1fR1A1S2bR1A1A9A2TS;").
Definition set_factsF (A : axst) (f : list sprop) : axst := ltac2:(tb__ "0|0|
S39VA;A1S30S3bVA;S22S2dR1A1S2eR1A1S2aR1A1S29R1A1S2fR1A1S2cR1A1Vf;S1fR1A1S2bR1A1A9A2TS;").
Definition add_factsF (A : axst) (f : list sprop) : axst := ltac2:(tb__ "0|0|
S64VA;S5S13S1eS39VA;A1A1Vf;A3A2").
Definition updrF (E : axst) (pc : Z) (ru : list (nat * sv)) : axst := ltac2:(tb__ "0|0|
S39VE;A1S30S3bVE;S22Vpc;SbaS2eR1A1Vru;A2S2aR1A1S29R1A1S2fR1A1S2cR1A1S1eR1A1S1fR1A1S2bR1A1A9A2TS;").

Definition is_obj (b lo : sv) (o : sobj) : bool := ltac2:(tb__ "0|0|
S6S31S23Vo;A1Vb;A2S31S24Vo;A1Vlo;A2A2").
Definition on_obj (b lo : sv) (f : sobj -> sobj) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S7S12L_;S8aVb;Vlo;Vo;A3Vf;Vo;A1Vo;X7x2").
Definition drop_cellsF (offs : list Z) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S18S23Vo;A1S24Vo;A1S28Vo;A1SecS16S16SeSebS37S37S31S36R2A1S11R1A1A2Lz;Voffs;A3A1Lc;S32Vo;A1A3S27Vo;A1A5").
Definition add_cellsF (cs : list cell) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S18S23Vo;A1S24Vo;A1S28Vo;A1S5S16Vcs;S32Vo;A1A3S27Vo;A1A5").
Definition set_cellsF (cs : list cell) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S18S23Vo;A1S24Vo;A1S28Vo;A1Vcs;S27Vo;A1A5").

Definition axf (A : axst) (xs : list axform) : axst := ltac2:(tb__ "0|0|
SbS3aA1S3aLx;S4eVA;Vxs;A2S3aR1LA';VA;Xbx2").
Definition optR (o : option (list sobj)) : list sobj := match o with Some r => r | None => [] end.

Definition entsF (L T : axst) : bool := ltac2:(tb__ "0|2|
S6S6S6S3eVL;VT;S97SbdS39VL;A1S39VT;A1M0A3M1A3SdfG1SbdA2A2S3dVT;A1A2S33G0A1A2").

Definition S1c_of (L1 : axst) (facts0 : list sprop) (sz : Z) : axst := ltac2:(tb__ "0|1|
S64S58VL1;S59S17PaA1S17Sd4A1S12S5fS0S16S1dS11N848M0A1Z4S11Vsz;A1A3S1S16A1A3S60S0S37G0S0S37N840S0S37N838S0S37N830S0S37N828S1S37A1A3A3A3A3A3R1A2A2Lo;A3A2Vfacts0;A2").

Definition C2_of (S1 : axst) : axst := ltac2:(tb__ "0|2|
S86S58VS1;S59S17PcA1S11N10A1M0S8dS0S16S1dG0Z4M1S51A3S0S16S1dS11NcA1G1S5bA3S1S16A1A3A3A1A3A2S6bA2").

Definition XD : list axform := ltac2:(tb__ "0|1|
S0S4aS4bU0M0S11S53A1A2S0S4aS4bU1S11S6eA1A2S0S4aS4bU2S11N48A1A2S0S4aS4dG0S53A2S1S4aA1A3A3A3A3").
Definition ED_of (EfD : axst) : axst := axf EfD XD.
Definition sD_of (ED : axst) (sz : Z) : wsub := ltac2:(tb__ "0|0|
S97P1S39VED;A1S39Sb4Vsz;A1A1A3").
Definition RD_of (ED : axst) (sz : Z) : list sobj := ltac2:(tb__ "0|0|
S5aSb2VED;Sb4Vsz;A1S61VED;Vsz;A2A3A1").
Definition TD_of (ED : axst) (sz : Z) : axst := ltac2:(tb__ "0|0|
Sb1Sb3S61VED;Vsz;A2Sb4Vsz;A1Sb7Vsz;A1VED;S7dVED;Vsz;A2A5S1eS39VED;A1A1A2").
Definition XDr : list axform := ltac2:(tb__ "0|0|
S0S4aS4cU0A1S0S4aS4cU1A1S1S4aA1A3A3").
Definition TDr_of (TD : axst) : axst := axf TD XDr.

Definition CD_of (TDr : axst) : axst := ltac2:(tb__ "0|1|
SefS1fS39VTDr;A1A1A1S38S58VTDr;S59S17PaA1S11S53A1S12S5fS0S16S1dS11N848M0A1Z4S17R2A1A3S1S16A1A3S60S0S37G0S1S37A1A3R1A2A2Lo;A3A2Tv;").

Definition C3_of (Eps : axst) : axst := ltac2:(tb__ "0|2|
S65VEps;S7aS0S4S3S14A2M0S2S3S14UbS4fA4S0G0S2S3S14UfS17PdA1M1A4S0G0S2S3S14U12G1A4S1G0A1A3A3A3A3").

Definition C4_of (Ems : axst) : axst := ltac2:(tb__ "0|1|
S65VEms;S6cS0S4S3S14A2M0S2S3S14UcS52A4S1G0A1A3A3").
Definition PostMS : axst := liftA (P_ret_memset memset_entryA).
Definition sM_of (C4 : axst) : wsub := ltac2:(tb__ "0|0|
S97P1S39VC4;A1S39Sb0A1A3").
Definition RM_of (C4 : axst) : list sobj := ltac2:(tb__ "0|0|
S5aSb2VC4;Sb0S62VC4;A1A3A1").
Definition TM0_of (C4 : axst) : axst := ltac2:(tb__ "0|0|
Sb3S62VC4;A1Sb0S7bVC4;S7eVC4;A1A5").
Definition TM_of (C4 : axst) : axst := ltac2:(tb__ "0|0|
Sb1S81VC4;A1S1eS39VC4;A1A1A2").

Definition XQ : list axform := ltac2:(tb__ "0|1|
S0S4aS4bU1M0S11S5dA1A2S0S4aS4dG0S5dA2S1S4aA1A3A3").
Definition EQ_of (Eq : axst) : axst := axf Eq XQ.
Definition sQ_of (EQ : axst) (q : qvar) : wsub := ltac2:(tb__ "0|0|
S97P1S39VEQ;A1S39S54Vq;A1A1A3").
Definition RQ_of (EQ : axst) (q : qvar) : list sobj := ltac2:(tb__ "0|0|
S5aSb2VEQ;S54Vq;A1S63VEQ;Vq;A2A3A1").
Definition TQ0_of (EQ : axst) (q : qvar) : axst := ltac2:(tb__ "0|0|
Sb3S63VEQ;Vq;A2S54Vq;A1S7cVq;A1VEQ;S7fVEQ;Vq;A2A5").
Definition TQ_of (EQ : axst) (q : qvar) : axst := ltac2:(tb__ "0|0|
Sb1S82VEQ;Vq;A2S1eS39VEQ;A1A1A2").

Definition showLsF (l : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
Sb9S3cS4S37S98A2S3cS2S37S98S2dS39S40R1A1A1A1S3fR1A1A4LL;Vl;A4").

Definition leaves_at (l : list leafA) (pcs : list Z) : bool := ltac2:(tb__ "0|2|
S6Sb8S9S3cVl;A2S9S37Vpcs;A2A2SedS4S4S37S98A2M0S37A2M1G1S94ScS37S98ScG0S37R1A3A3SfG0S37R1A3A2Lp;SeaG0S37S8fVl;A1Vpcs;A4A3A2").

Definition sdiffF (E C : axst) (nd nf : nat) : bool := ltac2:(tb__ "0|6|
S6S6SbS4SaS4S14S14A2M0A1M1SaS13A1M2A2M3A1S7Lx;SdeS39VE;A1M4S39VC;A1M5A2G3G3S7Lp;R1G1G2S6Sb8S9G0R2A2Vnd;A2Sb8S9S13R1A2Vnf;A2A2Lf;Ld;X4x1Lp;S8Xbx2S33G5A1A2SeeS1fG5A1S1fG4A1A2A2").

Definition casx : sv := ltac2:(tb__ "0|0|
S15S47S56S15S45S15S47S56S11Z3A1A3S11ZffA1A3A3").
Definition usz_e : sv := ltac2:(tb__ "0|0|
S15S48S15S42S15S43S51S11Z10A1A3S11Z20A1A3S26S8Q20S5bA3A3").
Definition rup_e : sv := ltac2:(tb__ "0|0|
S15S45S15S41S66S11Z7A1A3S11Zfffffffffffffff8A1A3").
Definition d3F : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4S14S14A2M0S2S14S14S8cS4fA4S0G0S2S14S14S66S17PdA1A4M1S0G0G1S1G0A1A3A3A3").
Definition len_e : sv := ltac2:(tb__ "0|2|
S15S49S15S41S15S43S15S41S15S41S17PcA1M0S4fA3S11N8A1A3S11Z3A1M1A3S11Z1A1A3S15S43G0G1A3A3").
Definition d4F : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S14S14A2M0S2S14S14S8bS52A4S1G0A1A3").
End F0A_states.

