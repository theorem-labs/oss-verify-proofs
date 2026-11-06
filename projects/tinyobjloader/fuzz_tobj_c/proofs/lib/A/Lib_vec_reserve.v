(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "sobj"; "SAlu"; "SMd"; "DUnknown"; "mkObj"; "SPAlign"; "FcsrFrm0"; "SVar"; "mkSS"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "tv_factsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "nd0"; "kbytes"; "vK"; "vW"; "vDt"; "c8"; "vDn"; "vKn"; "vE"; "vAl"; "vV"; "z0"; "vDp"; "X_vr"; "bdP"; "ndG"; "vC"; "vr_facts"; "B32"; "canon_objs"; "ndN"; "pC"; "spm"; "tv0"; "O_Fv"; "O_W"; "O_alv"; "O_data"; "O_vec"; "Pre_vr"; "T_c8okA"; "T_cW0okA"; "kn15"; "pR"; "two47"; "B_EW"; "C_c15"; "C_cW1"; "C_r8"; "C_rW0"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "FUEL_vr"; "KLG"; "N15"; "N8"; "NW0"; "NW1"; "PHI"; "P_fail"; "P_fail_S"; "P_grown"; "P_grown_S"; "P_keep"; "P_keep_S"; "Pre_c"; "Pre_vr_S"; "T_c8n"; "T_c8ok"; "T_c8ok0"; "T_cW0n"; "T_cW0ok"; "T_cW0ok0"; "T_r15f"; "T_r15ok"; "T_r15ok0"; "T_rW1f"; "T_rW1ok"; "T_rW1ok0"; "X15"; "X8"; "XW0"; "XW1"; "cutpcs_vr"; "grown_facts"; "tvP"; "two48"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "drop_obj_at"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "bitem"; "ASv"; "BI"; "ALog"; "KU"; "ZK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "calloc_pc"; "vr_entry"; "vr_nc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA"; "ndR"; "P_fail"; "P_ok"; "Pre_ra"; "tv0"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "AE_A"; "Pre_calloc"; "UStopLe"; "ulink"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA.ReallocAddr"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRAddr.
  Definition vr_entry : Z := 0x9311c.
  Definition vr_nc : Z := 0x9318c.
  Definition vr_ret : Z := 0x931e4.
  Definition vr_realloc_ret : Z := 0x9321c.
  Definition vr_calloc_ret : Z := 0x932f8.
  Definition calloc_pc : Z := 0x5e064.
End VRAddr.
Import VRAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_vr : nat := 400%nat.
Definition two48 : Z := 2 ^ 48.
Definition B_EW : Z := 2863311530.
Definition B32 : Z := 4294967295.

Definition vV : sv := SVar 12. Definition vW : sv := SVar 13. Definition vAl : sv := SVar 14.
Definition vDt : sv := SVar 15. Definition vC : sv := SVar 16. Definition vK : sv := SVar 17. Definition vE : sv := SVar 18.
Definition vDp : sv := SVar 19.
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.

Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S14PaA1SaN40A1SaZ0A1Vcells;S10A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S37Z40A1S2dSaZ0A1S2ScA1S10A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|1|
S11S2bSaZ0M0A1SaZ20A1S0ScS26G0Vd;A2S0ScS26Z8Vc;A2S0ScS26Z10Vk;A2S0ScS26Z18Ve;A2S2ScA1A3A3A3A3S10A5").
Definition O_alv : sobj := ltac2:(tb__ "0|2|
S11S2aSaZ0M0A1M1SaZ30A1S0ScS26G0SaS9eA1A2S0ScS26Z8SaS9fA1A2S0ScS26Z10G1A2S0ScS26Z18SaSa0A1A2S0ScS26Z20G1A2S0ScS26Z28S70A2S2ScA1A3A3A3A3A3A3S10A5").
Definition O_data (d bytes : sv) : sobj := ltac2:(tb__ "0|0|
S11Vd;SaZ0A1Vbytes;S2ScA1S10A5").

Definition vr_facts : list sprop := ltac2:(tb__ "0|b|
S0S9S12PaM0Z4M1A2S0S9SbS14G0A1M2SaS43A1M3A2S0S9SbS14P1eA1M4SeS71S37Z40A1M5S2dA3A2S0S9SbG4S37Za0A1A2S0S9SbG4G5A2S0S9SbG4G2A2S0S9S16S73SaN1060A1S2dA3S0S9S16S73S2dSaSa5Sa6Z2Z27A2A1A1A3S0S9S12PcZ3M6A2S0S9SbSaZ1000A1M7S2bA2S0S9SbSeS71S2bSaZ20A1A3G4A2S0S9SbS2bG3A2S0S9S12PeG6A2S0S9SbG7S2aA2S0S9SbSeS71S2aSaZ30A1A3G4A2S0S9SbS2aG3A2S0S9S12PfG1A2S0S9SbS25G4A2S0S9SbSeS71S25S22S23A1M8A3G4A2S0S9SbS25G3A2S0S9SbSaZ1A1S29A2S0S9SbS29G7A2S0S9SbS24SaS6fA1A2S0S9SbS31S23A2S0S9SbS23SaS33A1M9A2S0S9SbS22S24A1SaS44A1A2S0S9SbG8G9A2S0S9SbSaZ7fff7f800000A1MaG4A2S0S9SbG4SaZ7fffff800000A1A2S0S9SbGaG2A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vr (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2bSaZ20A1A4S0G0S1S8S8S2aSaZ30A1A4S0G0S1S8S8Vd;S22Vk;A1A4S2G0A1A3A3A3").
Definition Pre_vr_S : sstate := ltac2:(tb__ "0|0|
S15S8dS8aS87S13S5S8A1S6SdS0SdS39S2ScA1A1S0SdS3aS0SdS3dS25S31S23S29A4S0SdS3bS0SdS3cS25S22S23A1A2S2SdA1A3A3A3A3A3S84A3S32S86S7A9").
Definition Pre_vr : axst := ltac2:(tb__ "0|0|
S83S5bS2eS25S23A2A2").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S1fS8eS0S1fS9dS0S1fS8cS2S1fA1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_vr end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S9cS18Vk;S85S4dS6cVS;Vpc;A4S3eA4").

Definition X15 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 0.
Definition XW1 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 1.
Definition XW0 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 2.
Definition X8 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 3.

Definition kn15 : sv := ltac2:(tb__ "0|0|
SeS71SeS74S23SaZ1A1A3S23A3").
Definition inj (kn : sv) : list sprop := ltac2:(tb__ "0|3|
S0S9SbSfS72SaZ4A1M0S22S23A1A3SfS72SaZ3A1S22Vkn;A1M1A3A2S0S9SbSfS72G0G1A3SeS71SfS72SaZ6A1S22S24A1A3SfS72SaZ20A1S29A3A3A2S0S9SbG1SaS33A1M2A2S0S9SbSaZ1A1G1A2S0S9SbVkn;G2A2S2S9A1A3A3A3A3A3").
Definition N15 : axst := ax_add_facts (inj kn15) X15.
Definition NW1 : axst := ax_add_facts (inj vW) XW1.
Definition NW0 : axst := ax_add_facts (inj vW) XW0.
Definition N8 : axst := ax_add_facts (inj (SLit 8)) X8.

Definition E_r15 : axst := Eval vm_compute in leafA_at N15 ra_entry 0.
Definition E_rW1 : axst := Eval vm_compute in leafA_at NW1 ra_entry 0.
Definition C_c15 : axst := Eval vm_compute in leafA_at N15 calloc_pc 0.
Definition C_cW1 : axst := Eval vm_compute in leafA_at NW1 calloc_pc 0.
Definition E_cW0 : axst := Eval vm_compute in leafA_at NW0 calloc_pc 0.
Definition E_c8 : axst := Eval vm_compute in leafA_at N8 calloc_pc 0.
Definition C_rW0 : axst := Eval vm_compute in leafA_at NW0 ra_entry 0.
Definition C_r8 : axst := Eval vm_compute in leafA_at N8 ra_entry 0.

Definition tvf0 : list sprop := ltac2:(tb__ "0|0|
S1eS1S8S8S25S22S23A1A4A1").

Definition xf_rcall : list axform := ltac2:(tb__ "0|2|
S0S76S7bU1M0SaN60M1A1A2S0S76S77G0G1A2S2S76A1A3A3").
Definition E_r15x : axst := Eval vm_compute in optA (apply_axforms E_r15 xf_rcall).
Definition E_rW1x : axst := Eval vm_compute in optA (apply_axforms E_rW1 xf_rcall).
Definition E_r15f : axst := ax_add_facts tvf0 E_r15x.
Definition E_rW1f : axst := ax_add_facts tvf0 E_rW1x.
Definition s_r (E : axst) : wsub := ltac2:(tb__ "0|0|
S0S3S20S8A2S1S20S8P13SeS71S2dSaZ60A1A3A4S95PaS19VE;A1S19S92A1A3A3").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_r15 : list sobj := Eval vm_compute in optR (entails_frA E_r15f RA.Pre_ra (s_r E_r15f)).
Definition R_rW1 : list sobj := Eval vm_compute in optR (entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f)).
Goal entails_frA E_r15f RA.Pre_ra (s_r E_r15f) = Some R_r15 /\ call_checkPA E_r15f RA.Pre_ra (s_r E_r15f) R_r15 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f) = Some R_rW1 /\ call_checkPA E_rW1f RA.Pre_ra (s_r E_rW1f) R_rW1 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_cW0' : axst := E_cW0.
Definition E_c8' : axst := E_c8.
Definition Pre_c : axst := ltac2:(tb__ "0|0|
S98S97S2S9aA1S99A3").
Definition s_c (E : axst) : wsub := ltac2:(tb__ "0|0|
S95PaS19VE;A1S19S5aA1A3").
Definition R_cW0 : list sobj := Eval vm_compute in optR (entails_frA E_cW0' Pre_c (s_c E_cW0')).
Definition R_c8 : list sobj := Eval vm_compute in optR (entails_frA E_c8' Pre_c (s_c E_c8')).
Goal entails_frA E_cW0' Pre_c (s_c E_cW0') = Some R_cW0 /\ call_checkPA E_cW0' Pre_c (s_c E_cW0') R_cW0 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_c8' Pre_c (s_c E_c8') = Some R_c8 /\ call_checkPA E_c8' Pre_c (s_c E_c8') R_c8 [L_calloc_null AE_A [] UStopLe; L_calloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PD_ra : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S3S18S1cA2M0S1S18S1cS90S8fS93S2S7dA1M1A2A4S0G0S1S18S1cS91S8fS94G1A2A4S2G0A1A3A3").
Definition Xk_r : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S2bSaZ20A1A4S0G0S1S8S8S2aSaZ30A1A4S2G0A1A3A3").
Definition T_r15f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_fail Xk_r.
Definition T_r15ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_ok Xk_r.
Definition T_rW1f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_fail Xk_r.
Definition T_rW1ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_ok Xk_r.
Definition T_cW0n0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_null AE_A [] UStopLe).
Definition T_cW0ok0 : axst := Eval vm_compute in T_afterA Pre_c E_cW0' (s_c E_cW0') R_cW0 (L_calloc_ok AE_A [] UStopLe).
Definition T_c8n0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_null AE_A [] UStopLe).
Definition T_c8ok0 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_ok AE_A [] UStopLe).

Definition T_cW0n : axst := T_cW0n0.
Definition T_c8n : axst := T_c8n0.
Definition pC (T : axst) : sv := reg_sv (ax_S T) 10.
Definition reshape_blk (T : axst) (kn : sv) : axst := ltac2:(tb__ "0|3|
Sa1S1aVT;Sa2S19VT;A1U1S11S36VT;A1M0SaZ0A1S22Vkn;A1M1S2ScA1S10A5A3A2S6S3S8S8A2M2S9bG2U3S1bVT;A1A3S0G2S1S8S8G0G1A4S2G2A1A3A3A2").
Definition T_cW0okA : axst := reshape_blk T_cW0ok0 vW.
Definition T_c8okA : axst := reshape_blk T_c8ok0 (SLit 8).
Definition T_cW0ok2 : axst := ltac2:(tb__ "0|0|
S1aS40S78S19S40A1U7A2A2").
Definition T_c8ok2 : axst := ltac2:(tb__ "0|0|
S1aS3fS78S19S3fA1U7A2A2").
Definition T_cW0ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_cW0ok0, kbytes vW)) T_cW0ok2.
Definition T_c8ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_c8ok0, kbytes (SLit 8))) T_c8ok2.

Definition xf_rback : list axform := ltac2:(tb__ "0|2|
S0S76S77U1M0Z60A2S0S76S7aS0S4G0S0S4U0M1S0S4U2S0S4U3S0S4U4S0S4U5S0S4U6S0S4U7S2S4A1A3A3A3A3A3A3A3A3A1S0S76S79G1A1S2S76A1A3A3A3").
Definition T_r15f : axst := Eval vm_compute in optA (apply_axforms T_r15f0 xf_rback).
Definition T_rW1f : axst := Eval vm_compute in optA (apply_axforms T_rW1f0 xf_rback).
Definition T_r15okB : axst := Eval vm_compute in optA (apply_axforms T_r15ok0 xf_rback).
Definition T_rW1okB : axst := Eval vm_compute in optA (apply_axforms T_rW1ok0 xf_rback).
Definition pR (T : axst) : sv := reg_sv (ax_S T) 10.
Definition T_r15ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_r15ok0, kbytes kn15)) T_r15okB.
Definition T_rW1ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_rW1ok0, kbytes vW)) T_rW1okB.

Definition canon_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S6SdS0SdS39S2ScA1A1S0SdS3aS0SdS3dVd;S31Vk;S29A4S0SdS3bS0SdS3cVd;S22Vk;A1A2S2SdA1A3A3A3A3A3S84A3").
Definition P_keep_S : sstate := ltac2:(tb__ "0|1|
S15S8bS89S88S86A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S87S13S5S8A1S34S25S23A2S0S9SbS24S23A2S32A3S96S7A9").
Definition P_keep : axst := ltac2:(tb__ "0|0|
S83S59S2eS25S23A2A2").
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S15S8bS89S88S86A1S0S3S4S8A2M0S1S4S8UaSaZ0A1A4S2G0A1A3A2S87S13S5S8A1S34S25S23A2S32S96S7A9").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S83S55S2eS25S23A2A2").
Definition vDn : sv := SVar 140. Definition vKn : sv := SVar 141.
Definition grown_facts : list sprop := ltac2:(tb__ "0|4|
S0S9SbS24S28A2S0S9S12P8cZ4M0A2S0S9S17S16S75S27SaZ0A1A3A1S0S9SbSaZ1000A1S27A2S0S9SbS27S14P1eA1M1A2S0S9SbSeS71S27S22S28A1M2A3G1A2S0S9SbS27SaS43A1A2S0S9SbSaSa3A1S27A2S0S9SbSfS72SaG0A1G2A3SeS71SfS72SaZ6A1S22S24A1A3SfS72SaZ20A1S29A3A3A2S0S9SbG2SaS33A1M3A2S0S9SbSaZ1A1G2A2S0S9SbS31S28A2S0S9SbS28G3A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_grown_S : sstate := ltac2:(tb__ "0|1|
S15S8bS89S88S86A1S0S3S4S8A2M0S1S4S8UaSaZ1A1A4S2G0A1A3A2S87S13S5S8A1S34S27S28A2S6S9S6dS32A3P8eS7A9").
Definition P_grown : axst := ltac2:(tb__ "0|0|
S83S57S2eS27S28A2A2").

Definition PHI (w k : sv) : bitem := ltac2:(tb__ "0|2|
S7fZ1Z0M0S0S3S1fS7cA2M1S1S1fS7cZ6S7eS22Vw;A1A1A4S0G1S1S1fS7cN4S7eS22Vk;A1A1A4S0G1S1S1fS7cZ20S7eS29A1A4S2G1A1A3A3A3G0A4").
Definition KLG (k : sv) : bitem := ltac2:(tb__ "0|1|
S7fZ0Sa4Z2S81A2S0S3S1fS7cA2M0S1S1fS7cN1S80Vk;A1A4S2G0A1A3S82A4").
Definition bdP (w k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S7dS53Vw;Vk;A2S0S7dS4eVk;A1S2S7dA1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S25S22S23A1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S22S28A1A4S2G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS38S2S3S3S8S1fA2S8A2A1S2fS24S23A2A3").
Definition ndN (kn : sv) : ndesc := ltac2:(tb__ "0|0|
S1dS38S2S3S3S8S1fA2S8A2A1S2fS24Vkn;A2A3").
Definition ndG (p kn : sv) : ndesc := ltac2:(tb__ "0|1|
S1dS0S3S8S8A2M0S1S8S8Vp;S22Vkn;A1A4S2G0A1A3S2S3S3S8S1fA2S8A2A1S2fS24Vkn;A2A3").

Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS3eS21A4S1S1fS8Z64S2cA4A4S0G2S1G0G1S1S18S1cS4fS21A4S1S1fS8Z50S2cA4M3A4S0G2S1G0G1S1S18S1cS52S21A4G3A4S0G2S1G0G1S1S18S1cS51S21A4G3A4S0G2S1G0G1S1S18S1cS50S21A4G3A4S0G2S1G0G1S1S18S1cS62S35S41A1A4S1S1fS8Z3cS2cA4M4A4S0G2S1G0G1S1S18S1cS63S30S42S64A1S41A2A4G4A4S0G2S1G0G1S1S18S1cS65S35S24A1M5A4G4A4S0G2S1G0G1S1S18S1cS66S30S42S67A1S24A2A4G4A4S0G2S1G0G1S1S18S1cS5fG5A4G4A4S0G2S1G0G1S1S18S1cS60S30S36S61A1S24A2A4G4A4S0G2S1G0G1S1S18S1cS5cS35SaZ8A1M6A1A4G4A4S0G2S1G0G1S1S18S1cS5dS30S36S5eA1G6A2A4G4A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S18S1cA2M0S3S1fS8A2M1A2M2S1G0G1S1S18S1cS68S21A4S1S1fS8Z5aS2cA4M3A4S0G2S1G0G1S1S18S1cS6bS21A4G3A4S0G2S1G0G1S1S18S1cS6aS21A4G3A4S0G2S1G0G1S1S18S1cS69S21A4G3A4S0G2S1G0G1S1S18S1cS4bS21A4S1S1fS8Z46S2cA4M4A4S0G2S1G0G1S1S18S1cS4cS21A4G4A4S0G2S1G0G1S1S18S1cS45S21A4G4A4S0G2S1G0G1S1S18S1cS46S21A4G4A4S0G2S1G0G1S1S18S1cS4aS21A4G4A4S0G2S1G0G1S1S18S1cS49S21A4G4A4S0G2S1G0G1S1S18S1cS48S21A4G4A4S0G2S1G0G1S1S18S1cS47S21A4G4A4S0G2S1G0G1S1S18S1cS58S21A4S1S1fS8Z0S2cA4M5A4S0G2S1G0G1S1S18S1cS54S1dS38S2S3S3S8S1fA2S8A2A1M6S2S7dA1A3A4G5A4S0G2S1G0G1S1S18S1cS56S1dS6eG6S2fS24S28A2A3A4G5A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
