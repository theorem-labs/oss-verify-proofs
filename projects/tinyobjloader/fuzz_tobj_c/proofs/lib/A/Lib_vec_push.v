(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SPUle"; "SLit"; "SAlu"; "cell"; "sobj"; "DUnknown"; "SPAlign"; "mkObj"; "FcsrFrm0"; "SVar"; "mkSS"; "SMd"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "kbytes"; "vK"; "vDt"; "vDn"; "vC"; "vE"; "vKn"; "c8"; "z0"; "vDp"; "vV"; "spm"; "tv0"; "bdP"; "B32"; "two47"; "B_EW"; "O_data"; "O_vec"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "nd0"; "tvP"; "vUD"; "vW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXMerge"; "AXSelect"; "AXUnbase"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_GE"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_push"; "vC1"; "ndp0"; "vAp"; "X_vp"; "canon_vp"; "vDg"; "vp_facts"; "ndpG"; "slot_facts"; "E_msg1"; "E_msk1"; "Pre_vp"; "T_mg0"; "T_mk0"; "mid_obj"; "slot_obj"; "slot_of"; "vKg"; "E_msg0"; "E_msk0"; "E_vr"; "E_vr0"; "FUEL_vp"; "O_Fp"; "O_Wp"; "O_alp"; "P_push_fail"; "P_push_fail_S"; "P_push_grown"; "P_push_grown_S"; "P_push_keep"; "P_push_keep_S"; "Pre_ms"; "Pre_vp_S"; "T_fail"; "T_grownF"; "T_keep"; "T_keepF"; "T_mg"; "T_mk"; "V_XB"; "V_XL"; "cutpcs_vp"; "hse_fact"; "push_grown_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_push.VPAddr"; "vp_ret"; "memset_pc"; "vp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Module VPAddr.
  Definition vp_entry : Z := 0x9c834.
  Definition vp_ret : Z := 0x9c908.
  Definition vp_reserve_ret : Z := 0x9c884.
  Definition vp_memset_ret : Z := 0x9c8d8.
  Definition memset_pc : Z := 0x5cce8.
End VPAddr.
Import VPAddr.

Definition FUEL_vp : nat := 300%nat.
Definition vAp : sv := SVar 13.
Definition vC1 : sv := SAlu ALU_ADD vC (SLit 1).

Definition O_Fp (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S13PaA1SbN30A1SbZ0A1Vcells;SfA5").
Definition O_Wp : sobj := ltac2:(tb__ "0|0|
S11S2aZ30A1S28SbZ0A1S2SdA1SfA5").
Definition O_alp : sobj := ltac2:(tb__ "0|2|
S11S45SbZ0M0A1M1SbZ30A1S0SdS26G0SbS80A1A2S0SdS26Z8SbS81A1A2S0SdS26Z10G1A2S0SdS26Z18SbS82A1A2S0SdS26Z20G1A2S0SdS26Z28S38A2S2SdA1A3A3A3A3A3A3SfA5").

Definition vp_facts : list sprop := ltac2:(tb__ "0|c|
S0S8S10PaM0Z4M1A2S0S8SaS13G0A1M2SbS2eA1M3A2S0S8SaS13P1eA1M4ScS3fS2aZ30M5A1M6S28A3A2S0S8SaG4S2aZd0A1A2S0S8SaG4S2aZ70A1A2S0S8SaG4G6A2S0S8SaG4G2A2S0S8S16S41SbN10a0A1S28A3S0S8S16S41S28SbS86S87Z2Z26A2A1A1A3S0S8S10PcZ3M7A2S0S8SaSbZ1000A1M8S29A2S0S8SaScS3fS29SbZ20A1A3G4A2S0S8SaS29G3A2S0S8S10PdG7A2S0S8SaG8S45A2S0S8SaScS3fS45SbG5A1A3G4A2S0S8SaS45G3A2S0S8S10PfG1A2S0S8SaS21G4A2S0S8SaScS3fS21S1fS20A1M9A3G4A2S0S8SaS21G3A2S0S8SaSbZ1A1S24A2S0S8SaS24G8A2S0S8SaS23S20A2S0S8SaS20SbS2dA1MaA2S0S8SaS1fS43A1SbS2fA1A2S0S8SaG9GaA2S0S8SaSbZ7fff7f800000A1MbG4A2S0S8SaG4SbZ7fffff800000A1A2S0S8SaGbG2A2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S29SbZ20A1A4S0G0S1S9S9S45SbZ30A1A4S0G0S1S9S9Vd;S1fVk;A1A4S2G0A1A3A3A3").
Definition canon_vp (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5SeS0SeS5aS2SdA1A1S0SeS5bS0SeS31Vd;Vc;Vk;S24A4S0SeS5cS0SeS30Vd;S1fVk;A1A2S2SeA1A3A3A3A3A3S71A3").
Definition Pre_vp_S : sstate := ltac2:(tb__ "0|0|
S14S7bS78S75S12S6S9A1S47S21S23S20A3S49S74S7A9").
Definition Pre_vp : axst := ltac2:(tb__ "0|0|
S70S64S46S21S20A2A2").

Definition cutpcs_vp : list Z := ltac2:(tb__ "0|0|
S0S1dS83S0S1dS7aS2S1dA1A3A3").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => Pre_vp end.
Definition leafP_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S7fS18Vk;S72S59S6dVS;Vpc;A4S4eA4").

Definition E_vr0 : axst := Eval vm_compute in leafP_at Pre_vp vr_entry 0.

Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0S3aS3bU1M0SbN40M1A1A2S0S3aS3eG0G1A2S2S3aA1A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vcall).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S1eS9A2S1S1eS9P13ScS3fS28SbZ40A1A3A4S7dPaS19S57A1S19S35A1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S18S1bA2M0S1S18S1bS34S36A4S0G0S1S18S1bS32S1cS2bS2S4S4S9S1dA2S9A2A1M1S2S7cA1A3A4S0G0S1S18S1bS33S1cS37G1S2cS39S25A2A3A4S2G0A1A3A3A3").
Definition Xk_v : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S29SbZ20A1A4S0G0S1S9S9S45SbZ30A1A4S2G0A1A3A3").
Goal entails_frA E_vr Pre_vr s_v = Some R_v /\ call_checkPA E_vr Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_vback : list axform := ltac2:(tb__ "0|2|
S0S3aS3eU1M0Z40A2S0S3aS3dS0S3G0S0S3U0M1S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S0S3U7S2S3A1A3A3A3A3A3A3A3A3A1S0S3aS3cG1A1S2S3aA1A3A3A3").
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_grown Xk_v.
Definition T_keep : axst := Eval vm_compute in optAp (apply_axforms T_keep0 xf_vback).
Definition T_fail : axst := Eval vm_compute in optAp (apply_axforms T_fail0 xf_vback).
Definition T_grown : axst := Eval vm_compute in optAp (apply_axforms T_grown0 xf_vback).

Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|2|
S0S8SaS1fS23A1M0S1fVk;A1M1A2S0S8SaScS3fG0S24A3G1A2S2S8A1A3A3").
Definition vDg : sv := SVar 141.
Definition vKg : sv := SVar 142.

Definition hse_fact : sprop := SPUle (SLit IMG_HI) vDt.
Definition T_keepF : axst := ltac2:(tb__ "0|0|
S84S5S8S4bS20A1S0S8S6eS2S8A1A3A3S67A2").
Definition T_grownF : axst := ax_add_facts (slot_facts vKg) T_grown.

Definition E_msk0 : axst := Eval vm_compute in leafP_at T_keepF memset_pc 0.
Definition E_msg0 : axst := Eval vm_compute in leafP_at T_grownF memset_pc 0.
Definition xf_mcall : list axform := ltac2:(tb__ "0|1|
S0S3aS3bU3S1fS23A1M0A2S0S3aS3bU4ScS3fG0S24A3A2S2S3aA1A3A3").
Definition slot_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S11ScS3fVd;S1fS23A1A3SbZ0A1S24S2SdA1SfA5").
Definition E_msk1 : axst := Eval vm_compute in optAp (apply_axforms E_msk0 xf_mcall).
Definition E_msg1 : axst := Eval vm_compute in optAp (apply_axforms E_msg0 xf_mcall).
Definition E_msk : axst := ltac2:(tb__ "0|0|
S1aS4dS73S19S4dA1U4S52S21A1A3A2").
Definition E_msg : axst := ltac2:(tb__ "0|0|
S1aS4cS73S19S4cA1U4S52S48A1A3A2").

Definition V_XB : positive := 53%positive.
Definition V_XL : positive := 54%positive.
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_m (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S1eS9A2M0S1S1eS9S6bVd;A4S0G0S1S1eS9S6cS1fVk;A1A4S7dPaS19VE;A1S19S63A1A3A3A3").
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_msk Pre_ms (s_m E_msk vDt vK)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_msg Pre_ms (s_m E_msg vDg vKg)).
Goal entails_frA E_msk Pre_ms (s_m E_msk vDt vK) = Some R_mk /\ call_checkPA E_msk Pre_ms (s_m E_msk vDt vK) R_mk [L_ms] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_msg Pre_ms (s_m E_msg vDg vKg) = Some R_mg /\ call_checkPA E_msg Pre_ms (s_m E_msg vDg vKg) R_mg [L_ms] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_mk0 : axst := Eval vm_compute in T_afterA Pre_ms E_msk (s_m E_msk vDt vK) R_mk L_ms.
Definition T_mg0 : axst := Eval vm_compute in T_afterA Pre_ms E_msg (s_m E_msg vDg vKg) R_mg L_ms.

Definition mid_obj (d : sv) : sobj := ltac2:(tb__ "0|1|
S11Vd;S1fS23A1M0ScS3fG0S24A3S2SdA1SfA5").
Definition xf_mback : list axform := ltac2:(tb__ "0|2|
S0S3aS3dS0S3U0S0S3U4S0S3U5S0S3U6S0S3U1S0S3U7S0S3U2S0S3U3M0S0S3U8S2S3A1A3A3A3A3A3A3A3A3A3A1S0S3aS3cG0A1M1S0S3aG1S2S3aA1A3A3A3").
Definition T_mk1 : axst := ltac2:(tb__ "0|0|
S1aS50S73S19S50A1U1S51S21A1A3A2").
Definition T_mg1 : axst := ltac2:(tb__ "0|0|
S1aS4fS73S19S4fA1U1S51S48A1A3A2").
Definition T_mk : axst := Eval vm_compute in optAp (apply_axforms T_mk1 xf_mback).
Definition T_mg : axst := Eval vm_compute in optAp (apply_axforms T_mg1 xf_mback).

Definition slot_of (d : sv) : sv := ltac2:(tb__ "0|0|
ScS3fVd;S1fS23A1A3").
Definition P_push_fail_S : sstate := ltac2:(tb__ "0|1|
S14S79S77S76S74A1S0S4S3S9A2M0S1S3S9UaSbZ0A1A4S2G0A1A3A2S75S12S6S9A1S47S21S23S20A3S49S7eS7A9").
Definition P_push_fail : axst := ltac2:(tb__ "0|0|
S70S5eS46S21S20A2A2").
Definition P_push_keep_S : sstate := ltac2:(tb__ "0|1|
S14S79S77S76S74A1S0S4S3S9A2M0S1S3S9UaS53S21A1A4S2G0A1A3A2S75S12S6S9A1S47S21S43S20A3S5S8S0S8SaS43S20A2S2S8A1A3S5S8S4bS20A1S49A3A3S7eS7A9").
Definition P_push_keep : axst := ltac2:(tb__ "0|0|
S70S62S46S21S20A2A2").
Definition push_grown_facts : list sprop := ltac2:(tb__ "0|4|
S5S8S0S8SaS43S25A2S0S8S10P8cZ4M0A2S0S8S17S16S42S22SbZ0A1A3A1S0S8SaSbZ1000A1S22A2S0S8SaS22S13P1eA1M1A2S0S8SaScS3fS22S1fS25A1M2A3G1A2S0S8SaS22SbS2eA1A2S0S8SaSbS85A1S22A2S0S8SaS15S40SbG0A1G2A3ScS3fS15S40SbZ6A1S1fS43A1A3S15S40SbZ20A1S24A3A3A2S0S8SaG2SbS2dA1M3A2S0S8SaSbZ1A1G2A2S0S8SaS25G3A2S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3S4bS25A1A3").
Definition P_push_grown_S : sstate := ltac2:(tb__ "0|1|
S14S79S77S76S74A1S0S4S3S9A2M0S1S3S9UaS53S22A1A4S2G0A1A3A2S75S12S6S9A1S47S22S43S25A3S5S8S6fS49A3P8eS7A9").
Definition P_push_grown : axst := ltac2:(tb__ "0|0|
S70S60S46S22S25A2A2").

Definition ndp0 : ndesc := ltac2:(tb__ "0|0|
S1cS2bS2S4S4S9S1dA2S9A2A1S2cS43S20A2A3").
Definition ndpG (d k : sv) : ndesc := ltac2:(tb__ "0|1|
S1cS0S4S9S9A2M0S1S9S9Vd;S1fVk;A1A4S2G0A1A3S2S4S4S9S1dA2S9A2A1S2cS43Vk;A2A3").
Definition cutsP : list edescA := ltac2:(tb__ "0|6|
S0S4S4S18S1bA2M0S4S1dS9A2M1A2M2S1G0G1S1S18S1bS4eS44A4S1S1dS9Z64S27A4A4S0G2S1G0G1S1S18S1bS68S44A4S1S1dS9Z50S27A4M3A4S0G2S1G0G1S1S18S1bS65S1cS2bS2S4S4S9S1dA2S9A2A1S2S7cA1A3A4G3A4S0G2S1G0G1S1S18S1bS66S4aS48S54A2M4A4G3A4S0G2S1G0G1S1S18S1bS6aS44A4S1S1dS9Z3cS27A4M5A4S0G2S1G0G1S1S18S1bS69G4A4G5A4S2G2A1A3A3A3A3A3A3").
Definition exitsP : list edescA := ltac2:(tb__ "0|5|
S0S4S4S18S1bA2M0S4S1dS9A2M1A2M2S1G0G1S1S18S1bS58S44A4S1S1dS9Z5aS27A4A4S0G2S1G0G1S1S18S1bS56S44A4S1S1dS9Z46S27A4M3A4S0G2S1G0G1S1S18S1bS55S4aS48S54A2A4G3A4S0G2S1G0G1S1S18S1bS61S44A4S1S1dS9Z0S27A4M4A4S0G2S1G0G1S1S18S1bS5dS1cS2bS2S4S4S9S1dA2S9A2A1S2S7cA1A3A4G4A4S0G2S1G0G1S1S18S1bS5fS4aS22S25A2A4G4A4S2G2A1A3A3A3A3A3A3").
