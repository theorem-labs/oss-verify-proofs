(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "prod"; "app"; "false"; "None"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "SMd"; "sobj"; "SAlu"; "mkObj"; "DUnknown"; "SPAlign"; "SVar"; "FcsrFrm0"; "SPBranch"; "mkSS"; "tfact"; "DArr"; "SAluW"; "SExt"; "SLBytes"; "SMdW"; "SPNot"; "TF2le"; "reg_sv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr"; "vK"; "kbytes"; "vW"; "nd0"; "vDt"; "c8"; "vC"; "vDn"; "vKn"; "vE"; "vAl"; "vV"; "z0"; "vDp"; "X_vr"; "bdP"; "kn15"; "vr_facts"; "B32"; "canon_objs"; "inj"; "ndG"; "ndN"; "spm"; "tv0"; "O_Fv"; "O_W"; "O_alv"; "O_data"; "O_vec"; "Pre_vr"; "T_c8okA"; "X15"; "X8"; "XW1"; "injR"; "kbytesN"; "pC"; "pR"; "two47"; "vL"; "B_EW"; "C_c15"; "C_cW1"; "C_r8"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "KLG"; "N15"; "N8"; "NW1"; "PHI"; "P_fail"; "P_fail_S"; "P_grown"; "P_grown_S"; "P_keep"; "P_keep_S"; "Pre_c"; "Pre_vr_S"; "T_c8n"; "T_c8ok"; "T_c8ok0"; "T_r15f"; "T_r15ok"; "T_r15ok0"; "T_rW1f"; "T_rW1ok"; "T_rW1ok0"; "cutpcs_vr"; "darr"; "flds"; "grown_facts"; "injZ"; "knR"; "tmpl"; "tvP"; "two48"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "AXUnbase"; "AXRebase"; "AXSplit"; "drop_obj_at"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "mulop"; "aluop"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "BC_LTU"; "M_DIV"; "M_DIVU"; "M_MULH"; "M_MULHSU"; "M_MULHU"; "M_REM"; "M_REMU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "bitem"; "ASv"; "BI"; "ALog"; "KU"; "ZK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.VRDAddr"; "vr_ret"; "calloc_pc"; "vr_entry"; "vr_nc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.RA"; "ndR"; "P_fail"; "P_ok"; "Pre_ra"; "tv0"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "AE_A"; "Pre_calloc"; "UStopLeOrPc"; "Wcan"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.RA.ReallocAddr"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_realloc_darr. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRDAddr.
  Definition vr_entry : Z := 0x949d4.
  Definition vr_nc : Z := 0x94a4c.
  Definition vr_ret : Z := 0x94aa4.
  Definition vr_realloc_ret : Z := 0x94adc.
  Definition vr_calloc_ret : Z := 0x94bbc.
  Definition calloc_pc : Z := 0x5e1f8.
End VRDAddr.
Import VRDAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_vr : nat := 400%nat.
Definition two48 : Z := 2 ^ 48.
Definition B_EW : Z := 2863311530.
Definition B32 : Z := 4294967295.

Definition vV : sv := SVar 12. Definition vW : sv := SVar 13. Definition vAl : sv := SVar 14.
Definition vDt : sv := SVar 15. Definition vC : sv := SVar 16. Definition vK : sv := SVar 17. Definition vE : sv := SLit 16.
Definition vL : sv := SVar 53.
Definition flds : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4S21S21A2M0S1S21S21Z0Z8M1A4S0G0S1S21S21G1G1A4S2G0A1A3A3").
Definition tmpl : list tfact := ltac2:(tb__ "0|0|
S0S18S1fS6U0U1S53A4S2S18A1A3").
Definition darr (c : sv) : odefault := ltac2:(tb__ "0|0|
S19Z10Vc;S74S78A4").
Definition vDp : sv := SVar 19.
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.
Definition kbytesN (k : sv) : sv := ltac2:(tb__ "0|4|
S9S9Lk;Vk;S21SbSb2Z10R1A2A1Lz;S22S2cVk;A1M0Li;S86S9S9G0Lb;La;M1Lop;M2G2S85G1Lop;M3G3S8S23S9G0La;Lw;Lsgn;S22S9S21G0Lk0;Li;Ll;X9x8").

Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11S14PaA1SbN40A1SbZ0A1Vcells;S12A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S42Z40A1S38SbZ0A1S2SdA1S12A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|1|
S11S36SbZ0M0A1SbZ20A1S0SdS30G0Vd;A2S0SdS30Z8Vc;A2S0SdS30Z10Vk;A2S0SdS30Z18Ve;A2S2SdA1A3A3A3A3S12A5").
Definition O_alv : sobj := ltac2:(tb__ "0|2|
S11S35SbZ0M0A1M1SbZ30A1S0SdS30G0SbSb8A1A2S0SdS30Z8SbSb9A1A2S0SdS30Z10G1A2S0SdS30Z18SbSbaA1A2S0SdS30Z20G1A2S0SdS30Z28S7bA2S2SdA1A3A3A3A3A3A3S12A5").
Definition O_data (d bytes : sv) : sobj := ltac2:(tb__ "0|0|
S11Vd;SbZ0A1Vbytes;S2SdA1S73S31A1A5").

Definition vr_facts : list sprop := ltac2:(tb__ "0|c|
S0SaS13PaM0Z4M1A2S0SaScS14G0A1M2SbS52A1M3A2S0SaScS14P1eA1M4S10S83S42Z40A1M5S38A3A2S0SaScG4S42Za0A1A2S0SaScG4G5A2S0SaScG4G2A2S0SaS16S87SbN1060A1S38A3S0SaS16S87S38SbSb3Sb4Z2Z27A2A1A1A3S0SaS13PcZ3M6A2S0SaScG2S36A2S0SaScS10S83S36SbZ20A1A3G3A2S0SaScS36G3A2S0SaS13PeG6A2S0SaScSbZ1000A1M7S35A2S0SaScS10S83S35SbZ30A1A3G4A2S0SaScS35G3A2S0SaS13PfG1A2S0SaScS2fG4A2S0SaScS10S83S2fS2cS2bA1M8A3G4A2S0SaScS2fG3A2S0SaScSbZ1A1M9S34A2S0SaScS34G7A2S0SaScS2dSbS7aA1A2S0SaScS31S2bA2S0SaScS2bSbS3dA1MaA2S0SaScS2cS2dA1SbS54A1A2S0SaScG8GaA2S0SaScS2dS10S83S31G9A3A2S0SaScSbZ7fff7f800000A1MbG4A2S0SaScG4SbZ7fffff800000A1A2S0SaScGbG2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vr (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S36SbZ20A1A4S0G0S1S9S9S35SbZ30A1A4S0G0S1S9S9Vd;S2cVk;A1A4S2G0A1A3A3A3").
Definition Pre_vr_S : sstate := ltac2:(tb__ "0|0|
S17Sa3Sa0S9dS15S7S9A1S5SfS0SfS44S2SdA1A1S0SfS45S0SfS48S2fS31S2bS34A4S0SfS46S0SfS47S2fS2cS2bA1A2S2SfA1A3A3A3A3A3S9aA3S3cS9cS6A9").
Definition Pre_vr : axst := ltac2:(tb__ "0|0|
S99S68S39S2fS2bA2A2").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S21Sa4S0S21Sb7S0S21Sa2S2S21A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_vr end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sb6S24Vk;S9bS5bS72VS;Vpc;A4S49A4").

Definition X15 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 0.
Definition XW1 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 1.
Definition X8 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 2.

Definition kn15 : sv := ltac2:(tb__ "0|0|
S10S83S10S88S2bSbZ1A1A3S2bA3").
Definition inj (kn : sv) : list sprop := ltac2:(tb__ "0|3|
S0SaScSeS84SbZ4A1M0S2cS2bA1A3SeS84SbZ3A1S2cVkn;A1M1A3A2S0SaScSeS84G0G1A3S10S83SeS84SbZ6A1S2cS2dA1A3SeS84SbZ20A1S34A3A3A2S0SaScG1SbS3dA1M2A2S0SaScSbZ1A1G1A2S0SaScVkn;G2A2S2SaA1A3A3A3A3A3").
Definition injR (kn : sv) : list sprop := ltac2:(tb__ "0|0|
S0SaScS2bS31A2S0SaS16S8aS2bVkn;A3S2SaA1A3A3").
Definition injZ : list sprop := ltac2:(tb__ "0|0|
S0SaScS31SbZ0A1A2S2SaA1A3").
Definition N15 : axst := ltac2:(tb__ "0|0|
Sa5S5SaS4eS3bA1S3fS3bA1A3S4bA2").
Definition NW1 : axst := ltac2:(tb__ "0|0|
Sa5S5SaS4eS2dA1S3fS2dA1A3S4dA2").
Definition N8 : axst := ltac2:(tb__ "0|0|
Sa5S5SaS76S3fSbZ8A1A1A3S4cA2").

Definition E_r15 : axst := Eval vm_compute in leafA_at N15 ra_entry 0.
Definition E_rW1 : axst := Eval vm_compute in leafA_at NW1 ra_entry 0.
Definition C_c15 : axst := Eval vm_compute in leafA_at N15 calloc_pc 0.
Definition C_cW1 : axst := Eval vm_compute in leafA_at NW1 calloc_pc 0.
Definition E_c8 : axst := Eval vm_compute in leafA_at N8 calloc_pc 0.
Definition C_r8 : axst := Eval vm_compute in leafA_at N8 ra_entry 0.

Definition tvf0 : list sprop := ltac2:(tb__ "0|0|
S2aS1S9S9S2fS2cS2bA1A4A1").

Definition xf_rcall : list axform := ltac2:(tb__ "0|2|
S0S7cS81U1M0SbN60M1A1A2S0S7cS7fG0G1A2S2S7cA1A3A3").
Definition E_r15x : axst := Eval vm_compute in optA (apply_axforms E_r15 xf_rcall).
Definition E_rW1x : axst := Eval vm_compute in optA (apply_axforms E_rW1 xf_rcall).
Definition E_r15f : axst := ax_add_facts tvf0 E_r15x.
Definition E_rW1f : axst := ax_add_facts tvf0 E_rW1x.
Definition knR (E : axst) : sv := match reg_sv (ax_S E) 13 with SMd M_MUL _ k => k | x => x end.
Definition s_r (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S22S9A2M0S1S22S9P13S10S83S38SbZ60A1A3A4S0G0S1S22S9PeS2bA4S0G0S1S22S9P21S77VE;A1A4S0G0S1S22S9P35S53A4SacPaS25VE;A1S25Sa9A1A3A3A3A3A3").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_r15 : list sobj := Eval vm_compute in optR (entails_frA E_r15f RA.Pre_ra (s_r E_r15f)).
Definition R_rW1 : list sobj := Eval vm_compute in optR (entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f)).
Goal entails_frA E_r15f RA.Pre_ra (s_r E_r15f) = Some R_r15 /\ call_checkPA E_r15f RA.Pre_ra (s_r E_r15f) R_r15 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_rW1f RA.Pre_ra (s_r E_rW1f) = Some R_rW1 /\ call_checkPA E_rW1f RA.Pre_ra (s_r E_rW1f) R_rW1 [RA.P_fail; RA.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_ccall : list axform := ltac2:(tb__ "0|2|
S0S7cS81U2M0SbZ10M1A1A2S0S7cS7fG0G1A2S2S7cA1A3A3").
Definition E_c8' : axst := Eval vm_compute in optA (apply_axforms E_c8 xf_ccall).
Definition Pre_c : axst := ltac2:(tb__ "0|0|
SafSaeSb1U1A1Sb0A3").
Definition s_c (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S22S9A2M0S1S22S9P34S2fA4S0G0S1S22S9P35S31A4SacPaS25VE;A1S25S67A1A3A3A3").
Definition R_c8 : list sobj := Eval vm_compute in optR (entails_frA E_c8' Pre_c (s_c E_c8')).
Goal entails_frA E_c8' Pre_c (s_c E_c8') = Some R_c8 /\ call_checkPA E_c8' Pre_c (s_c E_c8') R_c8 [L_calloc_null AE_A (Wcan 1) UStopLeOrPc; L_calloc_ok AE_A (Wcan 1) UStopLeOrPc] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PD_ra : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S24S28A2M0S1S24S28Sa7Sa6SaaS2S93A1M1A2A4S0G0S1S24S28Sa8Sa6SabG1A2A4S2G0A1A3A3").
Definition Xk_r : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S36SbZ20A1A4S0G0S1S9S9S35SbZ30A1A4S2G0A1A3A3").
Definition T_r15f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_fail Xk_r.
Definition T_r15ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_r15f (s_r E_r15f) R_r15 RA.P_ok Xk_r.
Definition T_rW1f0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_fail Xk_r.
Definition T_rW1ok0 : axst := Eval vm_compute in T_afterA3 RA.Pre_ra E_rW1f (s_r E_rW1f) R_rW1 RA.P_ok Xk_r.
Definition xf_cbackN : list axform := ltac2:(tb__ "0|2|
S0S7cS80U1M0A1S0S7cS7eS0S3U0S0S3U2S0S3U3S0S3U4M1S0S3G0S0S3U5S0S3U6S0S3U7S2S3A1A3A3A3A3A3A3A3A3A1S0S7cS7dG1A1S2S7cA1A3A3A3").
Definition xf_cback : list axform := ltac2:(tb__ "0|2|
S0S7cS80U1M0A1S0S7cS7eS0S3U0S0S3U2S0S3U3S0S3U4S0S3U5M1S0S3G0S0S3U6S0S3U7S0S3U8S2S3A1A3A3A3A3A3A3A3A3A3A1S0S7cS7dG1A1S2S7cA1A3A3A3").
Definition T_c8n00 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_null AE_A (Wcan 1) UStopLeOrPc).
Definition T_c8ok00 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_ok AE_A (Wcan 1) UStopLeOrPc).
Definition T_c8n0 : axst := Eval vm_compute in optA (apply_axforms T_c8n00 xf_cbackN).
Definition T_c8ok0 : axst := Eval vm_compute in optA (apply_axforms T_c8ok00 xf_cback).

Definition T_c8n : axst := T_c8n0.
Definition pC (T : axst) : sv := reg_sv (ax_S T) 10.
Definition reshape_blk (T : axst) (kn : sv) : axst := ltac2:(tb__ "0|3|
SbbS26VT;SbcS25VT;A1U1S11S50VT;A1M0SbZ0A1S4fVkn;A1M1S2SdA1S12A5A3A2S5S4S9S9A2M2Sb5G2U3S27VT;A1A3S0G2S1S9S9G0G1A4S2G2A1A3A3A2").
Definition T_c8okA : axst := reshape_blk T_c8ok0 (SLit 8).
Definition T_c8ok2 : axst := ltac2:(tb__ "0|0|
S26S4aS82S25S4aA1U7A2A2").
Definition T_c8ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_c8ok0, kbytesN (SLit 8))) T_c8ok2.

Definition xf_rback : list axform := ltac2:(tb__ "0|2|
S0S7cS7fU1M0Z60A2S0S7cS7eS0S3G0S0S3U0M1S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S0S3U7S2S3A1A3A3A3A3A3A3A3A3A1S0S7cS7dG1A1S2S7cA1A3A3A3").
Definition T_r15f : axst := Eval vm_compute in optA (apply_axforms T_r15f0 xf_rback).
Definition T_rW1f : axst := Eval vm_compute in optA (apply_axforms T_rW1f0 xf_rback).
Definition T_r15okB : axst := Eval vm_compute in optA (apply_axforms T_r15ok0 xf_rback).
Definition T_rW1okB : axst := Eval vm_compute in optA (apply_axforms T_rW1ok0 xf_rback).
Definition pR (T : axst) : sv := reg_sv (ax_S T) 10.
Definition T_r15ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_r15ok0, kbytes kn15)) T_r15okB.
Definition T_rW1ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_rW1ok0, kbytes vW)) T_rW1okB.

Definition canon_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfS44S2SdA1A1S0SfS45S0SfS48Vd;S31Vk;S34A4S0SfS46S0SfS47Vd;S2cVk;A1A2S2SfA1A3A3A3A3A3S9aA3").
Definition P_keep_S : sstate := ltac2:(tb__ "0|1|
S17Sa1S9fS9eS9cA1S0S4S3S9A2M0S1S3S9UaSbZ1A1A4S2G0A1A3A2S9dS15S7S9A1S3eS2fS2bA2S0SaScS2dS2bA2S3cA3SadS6A9").
Definition P_keep : axst := ltac2:(tb__ "0|0|
S99S66S39S2fS2bA2A2").
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S17Sa1S9fS9eS9cA1S0S4S3S9A2M0S1S3S9UaSbZ0A1A4S2G0A1A3A2S9dS15S7S9A1S3eS2fS2bA2S3cSadS6A9").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S99S62S39S2fS2bA2A2").
Definition vDn : sv := SVar 140. Definition vKn : sv := SVar 141.
Definition grown_facts : list sprop := ltac2:(tb__ "0|4|
S0SaScS2dS33A2S0SaS13P8cZ4M0A2S0SaS1eS16S89S32SbZ0A1A3A1S0SaScSbZ1000A1S32A2S0SaScS32S14P1eA1M1A2S0SaScS10S83S32S2cS33A1M2A3G1A2S0SaScS32SbS52A1A2S0SaScSbSbdA1S32A2S0SaScSeS84SbG0A1G2A3S10S83SeS84SbZ6A1S2cS2dA1A3SeS84SbZ20A1S34A3A3A2S0SaScG2SbS3dA1M3A2S0SaScSbZ1A1G2A2S0SaScS31S33A2S0SaScS33G3A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_grown_S : sstate := ltac2:(tb__ "0|1|
S17Sa1S9fS9eS9cA1S0S4S3S9A2M0S1S3S9UaSbZ1A1A4S2G0A1A3A2S9dS15S7S9A1S3eS32S33A2S5SaS75S3cA3P8eS6A9").
Definition P_grown : axst := ltac2:(tb__ "0|0|
S99S64S39S32S33A2A2").

Definition PHI (w k : sv) : bitem := ltac2:(tb__ "0|2|
S95Z1Z0M0S0S4S21S92A2M1S1S21S92Z6S94S2cVw;A1A1A4S0G1S1S21S92N4S94S2cVk;A1A1A4S0G1S1S21S92Z20S94S34A1A4S2G1A1A3A3A3G0A4").
Definition KLG (k : sv) : bitem := ltac2:(tb__ "0|1|
S95Z0Sb2Z2S97A2S0S4S21S92A2M0S1S21S92N1S96Vk;A1A4S2G0A1A3S98A4").
Definition bdP (w k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S93S60Vw;Vk;A2S0S93S5cVk;A1S2S93A1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S2fS2cS2bA1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S9S9A2M0S1S9S9S32S2cS33A1A4S2G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S29S43S2S4S4S9S21A2S9A2A1S3aS2dS2bA2A3").
Definition ndN (kn : sv) : ndesc := ltac2:(tb__ "0|0|
S29S43S2S4S4S9S21A2S9A2A1S3aS2dVkn;A2A3").
Definition ndG (p kn : sv) : ndesc := ltac2:(tb__ "0|1|
S29S0S4S9S9A2M0S1S9S9Vp;S4fVkn;A1A4S2G0A1A3S2S4S4S9S21A2S9A2A1S3aS2dVkn;A2A3").

Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|6|
S0S4S4S24S28A2M0S4S21S9A2M1A2M2S1G0G1S1S24S28S49S2eA4S1S21S9Z64S37A4A4S0G2S1G0G1S1S24S28S5dS2eA4S1S21S9Z50S37A4M3A4S0G2S1G0G1S1S24S28S5fS2eA4G3A4S0G2S1G0G1S1S24S28S5eS2eA4G3A4S0G2S1G0G1S1S24S28S6cS41S3bA1A4S1S21S9Z3cS37A4M4A4S0G2S1G0G1S1S24S28S6dS40S51S6eA1S3bA2A4G4A4S0G2S1G0G1S1S24S28S6fS41S2dA1A4G4A4S0G2S1G0G1S1S24S28S70S40S51S71A1S2dA2A4G4A4S0G2S1G0G1S1S24S28S69S41SbZ8A1M5A1A4G4A4S0G2S1G0G1S1S24S28S6aS40S50S6bA1G5A2A4G4A4S2G2A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S4S4S24S28A2M0S4S21S9A2M1A2M2S1G0G1S1S24S28S4bS2eA4S1S21S9Z5aS37A4M3A4S0G2S1G0G1S1S24S28S4dS2eA4G3A4S0G2S1G0G1S1S24S28S4cS2eA4G3A4S0G2S1G0G1S1S24S28S59S2eA4S1S21S9Z46S37A4M4A4S0G2S1G0G1S1S24S28S5aS2eA4G4A4S0G2S1G0G1S1S24S28S55S2eA4G4A4S0G2S1G0G1S1S24S28S56S2eA4G4A4S0G2S1G0G1S1S24S28S58S2eA4G4A4S0G2S1G0G1S1S24S28S57S2eA4G4A4S0G2S1G0G1S1S24S28S65S2eA4S1S21S9Z0S37A4M5A4S0G2S1G0G1S1S24S28S61S29S43S2S4S4S9S21A2S9A2A1M6S2S93A1A3A4G5A4S0G2S1G0G1S1S24S28S63S29S79G6S3aS2dS33A2A3A4G5A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
