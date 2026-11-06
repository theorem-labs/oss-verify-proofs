(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SPUle"; "SLit"; "SAlu"; "cell"; "sobj"; "SPAlign"; "FcsrFrm0"; "SVar"; "mkSS"; "DUnknown"; "SMd"; "SPBranch"; "mkObj"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vK"; "kbytes"; "vDn"; "vDt"; "vKn"; "c8"; "vC"; "vDp"; "vE"; "vV"; "spm"; "tv0"; "z0"; "bdP"; "B32"; "two47"; "B_EW"; "O_data"; "O_vec"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "nd0"; "tvP"; "vUD"; "vW"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_GE"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_push"; "vC1"; "vAp"; "ndp0"; "X_vp"; "canon_vp"; "vp_facts"; "slot_facts"; "Pre_vp"; "ndpG"; "slot_of"; "C_zg"; "C_zk"; "E_vr"; "E_vr0"; "FUEL_vp"; "O_Fp"; "O_Wp"; "O_alp"; "P_push_fail"; "P_push_fail_S"; "P_push_grown"; "P_push_grown_S"; "P_push_keep"; "P_push_keep_S"; "Pre_vp_S"; "T_fail"; "T_grownF"; "T_keep"; "T_keepF"; "cutpcs_vp"; "hse_fact"; "push_grown_facts"; "vDg"; "vKg"; "zg_var"; "zk_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_push.VPAddr"; "vp_ret"; "vp_entry"; "vp_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Module VPAddr.
  Definition vp_entry : Z := 0x9aeac.
  Definition vp_ret : Z := 0x9afd0.
  Definition vp_reserve_ret : Z := 0x9af04.
  Definition vp_loop : Z := 0x9af6c.
End VPAddr.
Import VPAddr.

Definition FUEL_vp : nat := 300%nat.
Definition vAp : sv := SVar 13.
Definition vC1 : sv := SAlu ALU_ADD vC (SLit 1).

Definition O_Fp (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S11PaA1SbN30A1SbZ0A1Vcells;S13A5").
Definition O_Wp : sobj := ltac2:(tb__ "0|0|
S16S28Z30A1S25SbZ0A1S2SdA1S13A5").
Definition O_alp : sobj := ltac2:(tb__ "0|2|
S16S3eSbZ0M0A1M1SbZ30A1S0SdS23G0SbS74A1A2S0SdS23Z8SbS75A1A2S0SdS23Z10G1A2S0SdS23Z18SbS76A1A2S0SdS23Z20G1A2S0SdS23Z28S37A2S2SdA1A3A3A3A3A3A3S13A5").

Definition vp_facts : list sprop := ltac2:(tb__ "0|c|
S0S8SfPaM0Z4M1A2S0S8SaS11G0A1M2SbS2dA1M3A2S0S8SaS11P1eA1M4ScS39S28Z30M5A1M6S25A3A2S0S8SaG4S28Zd0A1A2S0S8SaG4S28Z70A1A2S0S8SaG4G6A2S0S8SaG4G2A2S0S8S15S3bSbN10a0A1S25A3S0S8S15S3bS25SbS7bS7cZ2Z26A2A1A1A3S0S8SfPcZ3M7A2S0S8SaSbZ1000A1M8S27A2S0S8SaScS39S27SbZ20A1A3G4A2S0S8SaS27G3A2S0S8SfPdG7A2S0S8SaG8S3eA2S0S8SaScS39S3eSbG5A1A3G4A2S0S8SaS3eG3A2S0S8SfPfG1A2S0S8SaS21G4A2S0S8SaScS39S21S1fS1eA1M9A3G4A2S0S8SaS21G3A2S0S8SaSbZ1A1S26A2S0S8SaS26G8A2S0S8SaS24S1eA2S0S8SaS1eSbS2cA1MaA2S0S8SaS1fS3dA1SbS2eA1A2S0S8SaG9GaA2S0S8SaSbZ7fff7f800000A1MbG4A2S0S8SaG4SbZ7fffff800000A1A2S0S8SaGbG2A2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S27SbZ20A1A4S0G0S1S9S9S3eSbZ30A1A4S0G0S1S9S9Vd;S1fVk;A1A4S2G0A1A3A3A3").
Definition canon_vp (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5SeS0SeS4cS2SdA1A1S0SeS4dS0SeS30Vd;Vc;Vk;S26A4S0SeS4eS0SeS2fVd;S1fVk;A1A2S2SeA1A3A3A3A3A3S67A3").
Definition Pre_vp_S : sstate := ltac2:(tb__ "0|0|
S12S6fS6dS6aS10S6S9A1S41S21S24S1eA3S42S69S7A9").
Definition Pre_vp : axst := ltac2:(tb__ "0|0|
S66S55S40S21S1eA2A2").

Definition cutpcs_vp : list Z := ltac2:(tb__ "0|0|
S0S1aS77S0S1aS70S2S1aA1A3A3").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => Pre_vp end.
Definition leafP_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S73S18Vk;S68S4bS5aVS;Vpc;A4S44A4").

Definition E_vr0 : axst := Eval vm_compute in leafP_at Pre_vp vr_entry 0.

Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0S61S65U1M0SbN40M1A1A2S0S61S62G0G1A2S2S61A1A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vcall).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P13ScS39S25SbZ40A1A3A4S78PaS19S49A1S19S34A1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S3S18S1cA2M0S1S18S1cS33S35A4S0G0S1S18S1cS31S1dS29S2S3S3S9S1aA2S9A2A1M1S2S71A1A3A4S0G0S1S18S1cS32S1dS36G1S2bS38S22A2A3A4S2G0A1A3A3A3").
Definition Xk_v : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S27SbZ20A1A4S0G0S1S9S9S3eSbZ30A1A4S2G0A1A3A3").
Goal entails_frA E_vr Pre_vr s_v = Some R_v /\ call_checkPA E_vr Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_vback : list axform := ltac2:(tb__ "0|2|
S0S61S62U1M0Z40A2S0S61S64S0S4G0S0S4U0M1S0S4U2S0S4U3S0S4U4S0S4U5S0S4U6S0S4U7S2S4A1A3A3A3A3A3A3A3A3A1S0S61S63G1A1S2S61A1A3A3A3").
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_grown Xk_v.
Definition T_keep : axst := Eval vm_compute in optAp (apply_axforms T_keep0 xf_vback).
Definition T_fail : axst := Eval vm_compute in optAp (apply_axforms T_fail0 xf_vback).
Definition T_grown : axst := Eval vm_compute in optAp (apply_axforms T_grown0 xf_vback).

Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|2|
S0S8SaS1fS24A1M0S1fVk;A1M1A2S0S8SaScS39G0S26A3G1A2S2S8A1A3A3").
Definition vDg : sv := SVar 141.
Definition vKg : sv := SVar 142.

Definition hse_fact : sprop := SPUle (SLit IMG_HI) vDt.
Definition T_keepF : axst := ltac2:(tb__ "0|0|
S79S5S8S43S1eA1S0S8S5bS2S8A1A3A3S58A2").
Definition T_grownF : axst := ax_add_facts (slot_facts vKg) T_grown.

Definition L_zk : axst := Eval vm_compute in leafP_at T_keepF vp_loop 0.
Definition L_zg : axst := Eval vm_compute in leafP_at T_grownF vp_loop 0.
Definition C_zk : axst := Eval vm_compute in bl_cut L_zk 13 vE [11; 15; 16]%nat [].
Definition C_zg : axst := Eval vm_compute in bl_cut L_zg 13 vE [11; 15; 16]%nat [].
Definition zk_var : sv := Eval vm_compute in bl_var L_zk vE.
Definition zg_var : sv := Eval vm_compute in bl_var L_zg vE.

Definition slot_of (d : sv) : sv := ltac2:(tb__ "0|0|
ScS39Vd;S1fS24A1A3").
Definition P_push_fail_S : sstate := ltac2:(tb__ "0|1|
S12S6eS6cS6bS69A1S0S3S4S9A2M0S1S4S9UaSbZ0A1A4S2G0A1A3A2S6aS10S6S9A1S41S21S24S1eA3S42S72S7A9").
Definition P_push_fail : axst := ltac2:(tb__ "0|0|
S66S50S40S21S1eA2A2").
Definition P_push_keep_S : sstate := ltac2:(tb__ "0|1|
S12S6eS6cS6bS69A1S0S3S4S9A2M0S1S4S9UaS46S21A1A4S2G0A1A3A2S6aS10S6S9A1S41S21S3dS1eA3S5S8S0S8SaS3dS1eA2S2S8A1A3S5S8S43S1eA1S42A3A3S72S7A9").
Definition P_push_keep : axst := ltac2:(tb__ "0|0|
S66S54S40S21S1eA2A2").
Definition push_grown_facts : list sprop := ltac2:(tb__ "0|4|
S5S8S0S8SaS3dS22A2S0S8SfP8cZ4M0A2S0S8S17S15S3cS20SbZ0A1A3A1S0S8SaSbZ1000A1S20A2S0S8SaS20S11P1eA1M1A2S0S8SaScS39S20S1fS22A1M2A3G1A2S0S8SaS20SbS2dA1A2S0S8SaSbS7aA1S20A2S0S8SaS14S3aSbG0A1G2A3ScS39S14S3aSbZ6A1S1fS3dA1A3S14S3aSbZ20A1S26A3A3A2S0S8SaG2SbS2cA1M3A2S0S8SaSbZ1A1G2A2S0S8SaS22G3A2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3S43S22A1A3").
Definition P_push_grown_S : sstate := ltac2:(tb__ "0|1|
S12S6eS6cS6bS69A1S0S3S4S9A2M0S1S4S9UaS46S20A1A4S2G0A1A3A2S6aS10S6S9A1S41S20S3dS22A3S5S8S5cS42A3P8eS7A9").
Definition P_push_grown : axst := ltac2:(tb__ "0|0|
S66S52S40S20S22A2A2").

Definition ndp0 : ndesc := ltac2:(tb__ "0|0|
S1dS29S2S3S3S9S1aA2S9A2A1S2bS3dS1eA2A3").
Definition ndpG (d k : sv) : ndesc := ltac2:(tb__ "0|1|
S1dS0S3S9S9A2M0S1S9S9Vd;S1fVk;A1A4S2G0A1A3S2S3S3S9S1aA2S9A2A1S2bS3dVk;A2A3").
Definition cutsP : list edescA := ltac2:(tb__ "0|6|
S0S3S3S18S1cA2M0S3S1aS9A2M1A2M2S1G0G1S1S18S1cS44S3fA4S1S1aS9Z64S2aA4A4S0G2S1G0G1S1S18S1cS59S3fA4S1S1aS9Z50S2aA4M3A4S0G2S1G0G1S1S18S1cS56S1dS29S2S3S3S9S1aA2S9A2A1S2S71A1A3A4G3A4S0G2S1G0G1S1S18S1cS57S45S5dS5eA2M4A4G3A4S0G2S1G0G1S1S18S1cS48S3fA4S1S1aS9Z3cM5S60A4A4S0G2S1G0G1S1S18S1cS47G4A4S1S1aS9G5S5fA4A4S2G2A1A3A3A3A3A3A3").
Definition exitsP : list edescA := ltac2:(tb__ "0|4|
S0S3S3S18S1cA2M0S3S1aS9A2M1A2M2S1G0G1S1S18S1cS4aS3fA4S1S1aS9Z5aS2aA4A4S0G2S1G0G1S1S18S1cS53S3fA4S1S1aS9Z0S2aA4M3A4S0G2S1G0G1S1S18S1cS4fS1dS29S2S3S3S9S1aA2S9A2A1S2S71A1A3A4G3A4S0G2S1G0G1S1S18S1cS51S45S20S22A2A4G3A4S2G2A1A3A3A3A3").
