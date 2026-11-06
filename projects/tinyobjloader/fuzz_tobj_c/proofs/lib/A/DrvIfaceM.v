(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "bool"; "pair"; "true"; "None"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SPUle"; "cell"; "mkObj"; "DUnknown"; "FcsrFrm0"; "SPAlign"; "mkCell"; "mkSS"; "swf"; "DList"; "SAlu"; "SPBranch"; "SPEq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM"; "jm"; "vARGC"; "vL2"; "O_deepM0"; "S_M"; "S_U"; "O_arg0"; "O_hdrU"; "X_M"; "X_U"; "arg0_facts"; "facts_M"; "facts_M0"; "facts_U"; "objs_M"; "objs_U"; "regs_M"; "regs_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "sp0"; "vA0"; "DEEP"; "vTP"; "O_errno"; "O_ferr0"; "O_realfw"; "O_realrd"; "O_stage2"; "O_stderrp"; "O_tri0"; "exit_statics"; "fps_statics"; "fregs_T"; "vL0"; "vTID"; "O_a1p"; "O_arg1"; "O_hdr2"; "O_rds"; "X_rds"; "top_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "O_cflag"; "O_file0"; "O_realv"; "O_sbuf0"; "O_ssp"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "main_entry"; "TP"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "O_tid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain"; "RA_MAIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axwf"; "mkAX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "X_lits"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Budget Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MAddr.
  Definition openat_pc : Z := 0xdeb5c.
  Definition open_ret : Z := 0x8c3d0.
  Definition usage_pc : Z := 0x8c528.
  Definition copen_pc : Z := 0x8c620.
  Definition oom1_pc : Z := 0x8c638.
  Definition fw_stub : Z := 0x4f0b0.
End MAddr.
Import MAddr.

Definition jm (k : nat) : sv := SVar (Pos.of_nat (140 + k)).
Definition regs_M : list sv := ltac2:(tb__ "0|4|
S0S9SaZ0A1M0S0S9SaS54A1S0S9S42S2cSaN30A1A2S0S9SaZ10800A1S0S9S2fS0S9S1aU5A1S0S9S1aU6A1S0S9S1aU7A1S0S9S42S2cSaZ8A1A2M1S0S9SaZ2A1M2S0S9G2S0S9G1S0S9S1aUcA1S0S9S1aUdA1S0S9S1aUeA1S0S9S1aUfA1S0S9S1aU10A1S0S9S1aU11A1S0S9SaS4aA1S0S9S42S42S2cSaZ10A1M3A2G3A2S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9S1aU1cA1S0S9S1aU1dA1S0S9S1aU1eA1S0S9S1aU1fA1S1S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition O_deepM0 : sobj := ltac2:(tb__ "0|0|
SfS2cSaS4eS4dS2eZ80A2A1A1SaN30A1S1SeA1S10A5").

Definition objs_M : list sobj := ltac2:(tb__ "0|1|
S2SbS0SbS1dS0SbS34S0SbS3eS0SbS3cS0SbS3dS0SbS30S0SbS52S0SbS36S0SbS44S0SbS46S0SbS43S0SbS45S0SbS33S0SbS32S0SbS47S0SbS35S0SbS31S1SbA1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S2SbS38S2SbS37S2SbS0SbS3fG0A3S50A3A3A3A3").

Definition X_M : list (sv * sv) := ltac2:(tb__ "0|2|
S2S8S9S9A2M0S0G0S4S9S9SaZ14d40A1SaZ80M1A1A4S0G0S4S9S9S42S2cSaS4eS4dS2eG1A2A1A1A2SaS2eA1A4S0G0S40S1G0A1A3A3A3S5aA3").

Definition X_U : list (sv * sv) := ltac2:(tb__ "0|2|
S0S8S9S9A2M0S4S9S9SaZ14d40A1SaZ80M1A1A4S0G0S4S9S9S42S2cSaS4eS4dS2eG1A2A1A1A2SaS2eA1A4S1G0A1A3A3").

Definition facts_M0 : list sprop := ltac2:(tb__ "0|0|
S2ScS0ScS12P1Z4A2S0ScSdSaZ7fff80000000A1S2cA2S0ScSdS2cSaS4fS4cZ2Z2fA2Ze0A2A1A2S0ScS19S2fSaS4bA1A2S0ScSdSaZ1A1S3bA2S0ScSdS3bSaZ3fffffA1A2S1ScA1A3A3A3A3A3A3S41A3").
Definition facts_M : list sprop := facts_M0 ++ arg1_factsM.

Definition S_M : axst := ltac2:(tb__ "0|0|
S57S14S4aS2aS39S11S6S9A1S28S25PbeS7A9S22SaS51A1A3").

Lemma S_M_wf : ltac2:(tb__ "0|0|
S49S48S3S56S1eA1S5A3S48S3S15S55S1eA1A1S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vARGC : sv := SVar 2.
Definition vL2 : sv := SVar 12.
Definition O_hdrU : sobj := ltac2:(tb__ "0|2|
SfS2cSaZ0A1M0SaZ10A1S0SeS13G0Z8M1S1bA3S0SeS13SaG1A1G1S2dA3S1SeA1A3A3S10A5").
Definition O_arg0 : sobj := ltac2:(tb__ "0|0|
SfS2dSaZ0A1S1cS1SeA1S16P2A1A5").
Definition regs_U : list sv := ltac2:(tb__ "0|3|
S0S9SaZ0A1M0S0S9SaS54A1S0S9S42S2cSaN30A1A2S0S9SaZ10800A1S0S9S2fS0S9S1aU5A1S0S9S1aU6A1S0S9S1aU7A1S0S9S42S2cSaZ8A1A2M1S0S9S1bS0S9S1bS0S9G1S0S9S42S42S2cS17S58S1bSaZ3A1A3A2SaZ10A1A2M2S0S9S1aUdA1S0S9S1aUeA1S0S9S1aUfA1S0S9S1aU10A1S0S9S1aU11A1S0S9SaS4aA1S0S9G2S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9G0S0S9S1aU1cA1S0S9S1aU1dA1S0S9S1aU1eA1S0S9S1aU1fA1S1S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition objs_U : list sobj := ltac2:(tb__ "0|0|
S2SbS0SbS1dS0SbS34S0SbS21S0SbS20S0SbS30S0SbS52S0SbS36S0SbS44S0SbS46S0SbS43S0SbS45S0SbS33S0SbS32S0SbS47S0SbS35S0SbS31S1SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S2SbS38S2SbS37S50A3A3A3").
Definition arg0_facts : list sprop := ltac2:(tb__ "0|4|
S0ScSdSaZ7fff80000018A1S2dA2S0ScSdS42S2cSaZ18A1A2S2dA2S0ScSdS2dSaS4cZ2M0Z2fA2A1M1A2S0ScSdS42S2dS1cA2M2G1A2S0ScSdS3aSaZ1ffffA1A2S0ScSdS42S3aSaZ8A1A2S1cA2S0ScSdS1cSaS4cG0Z16A2A1A2S0ScS12P4Z3A2S0ScSdG2S42S2cS53A2M3A2S0ScSdG3G1A2S0ScSdS53SaS4cG0Z17A2A1A2S1ScA1A3A3A3A3A3A3A3A3A3A3A3").
Definition facts_U : list sprop := ltac2:(tb__ "0|0|
S2ScS26S2ScS0ScSdSaZ1A1S1bA2S0ScSdS1bSaZ400A1A2S0ScS18S59S1bSaZ2A1A3S1ScA1A3A3A3S24A3A3").
Definition S_U : axst := ltac2:(tb__ "0|0|
S57S14S4aS2bS39S11S6S9A1S29S27PbeS7A9S23SaS51A1A3").

Lemma S_U_wf : ltac2:(tb__ "0|0|
S49S48S3S56S1fA1S5A3S48S3S15S55S1fA1A1S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
