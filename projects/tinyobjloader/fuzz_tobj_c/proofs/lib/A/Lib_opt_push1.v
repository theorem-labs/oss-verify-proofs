(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "sobj"; "SMd"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "SPAlign"; "SPBranch"; "SPEq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1"; "pC"; "CM"; "pK"; "pD"; "ndC"; "vDEF"; "vVALS"; "hx"; "HNEXT"; "pR"; "vALo"; "z0"; "TA_2s"; "X_op"; "canon_op"; "op_facts"; "slot4_at"; "slotL"; "vVIDX"; "C_L"; "OS"; "VB"; "OS2"; "dstj"; "inJ"; "inL"; "inL_at"; "slot4"; "F_cells"; "Pre_op"; "TA_Ls"; "TF_2"; "bd_op"; "body_regs"; "cBnd"; "gV"; "gV_facts"; "nd0"; "FUEL_op"; "K_cp2"; "P_op0"; "P_op1"; "R_facts"; "TF_L"; "Wp"; "X_Lin0"; "X_Lin1"; "X_back0"; "X_back1"; "nd0'"; "nd1"; "ndF"; "pCM"; "shv"; "srcj"; "vPRES"; "C_J2"; "Cb"; "E_2d0"; "E_2v0"; "E_vrL0"; "K_cp1"; "O_Fo"; "O_Wo"; "O_alo"; "O_deflt"; "O_vals"; "O_vec4"; "T_fail2d"; "T_fail2v"; "T_failL"; "T_grown2d"; "T_grown2ds"; "T_grown2v"; "T_grown2vs"; "T_grownL"; "T_grownLs"; "T_keep2d"; "T_keep2ds"; "T_keep2v"; "T_keep2vs"; "T_keepL"; "T_keepLs"; "X_Lin0f"; "X_Lin1f"; "X_back0f"; "X_back1f"; "cutpcs_all"; "cutpcs_op"; "joff"; "s_vr"; "tv0"; "tvQ"; "vKg2d"; "vKg2v"; "vKgL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "c8"; "vV"; "spm"; "vC"; "vDp"; "vK"; "vDt"; "Pre_vr"; "two47"; "P_fail"; "P_grown"; "P_keep"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SUB"; "BC_GE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "pow"; "sub"; "add"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "SHB"; "leavesA_at"; "A_globals"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vec4_facts"; "kb4"; "tv_vec"; "O_dat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.VRNAddr"; "vr_ret"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1.OPAddr"; "ra2"; "op_J2"; "op_L"; "raL"; "op_ret"; "op_entry"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr.

Definition CM : Z := 1.

Module OPAddr.
  Definition op_entry : Z := 0xa5d68.
  Definition op_L : Z := 0xa5e1c.
  Definition op_J2 : Z := 0xa5ef4.
  Definition op_ret : Z := 0xa6024.
  Definition raL : Z := 0xa5e30.
  Definition ra2 : Z := 0xa5f1c.
End OPAddr.
Import OPAddr.

Definition FUEL_op : nat := 600%nat.

Definition vVIDX : sv := SVar 14. Definition vVALS : sv := SVar 33. Definition vDEF : sv := SVar 34.
Definition vPRES : sv := SVar 35. Definition vALo : sv := SVar 36.

Definition Wp : sv := ltac2:(tb__ "0|0|
SeS91S10S92SaS1fA1S30A3SaS9eS9cZ2S1fA2Z1A2A1A3").

Definition Cb : sv := ltac2:(tb__ "0|0|
SeS91S10S92SaS1fA1S30A3SaS9eS1fZ1A2A1A3").

Definition O_Fo (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13SdPaA1SaN80A1SaZ0A1Vcells;S11A5").
Definition O_Wo : sobj := ltac2:(tb__ "0|0|
S13S80Z80A1S82SaZ0A1S3ScA1S11A5").
Definition O_vec4 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S13S7fSaZ0M0A1SaZ20A1S0ScS7eG0Vd;A2S0ScS7eZ8Vc;A2S0ScS7eZ10Vk;A2S0ScS7eZ18SaZ4A1A2S3ScA1A3A3A3A3S11A5").
Definition O_alo : sobj := ltac2:(tb__ "0|2|
S13S28SaZ0M0A1M1SaZ30A1S0ScS7eG0SaSbcA1A2S0ScS7eZ8SaSbdA1A2S0ScS7eZ10G1A2S0ScS7eZ18SaSbeA1A2S0ScS7eZ20G1A2S0ScS7eZ28S90A2S3ScA1A3A3A3A3A3A3S11A5").
Definition O_vals : sobj := ltac2:(tb__ "0|0|
S13S24SaZ0A1SaS9cZ4S1fA2A1S3ScA1S11A5").
Definition O_deflt : sobj := ltac2:(tb__ "0|0|
S13S23SaZ0A1SaS9cZ4S1fA2A1S3ScA1S11A5").

Definition op_facts : list sprop := ltac2:(tb__ "0|b|
S5S9S0S9S15PaM0Z4M1A2S0S9SbSdG0A1M2SaS86A1M3A2S0S9SbSdP1eA1M4SeS91S80Z80A1M5S82A3A2S0S9SbG4S80Z120A1A2S0S9SbG4S80Zc0A1A2S0S9SbG4G5A2S0S9SbG4G2A2S0S9S16S94SaN10a0A1S82A3S0S9S16S94S82SaSa0S9dZ2M6Z26A2A1A1A3S0S9S15PcZ3M7A2S0S9SbSaZ1000A1M8S7fA2S0S9SbSeS91S7fSaZ20A1A3G4A2S0S9SbS7fG3A2S0S9S15P24G7A2S0S9SbG8S28A2S0S9SbSeS91S28SaZ30A1A3G4A2S0S9SbS28G3A2S0S9S15P21G6A2S0S9SbG8S24A2S0S9SbSeS91S24SaS9cG1S1fA2A1M9A3G4A2S0S9SbS24G3A2S0S9S15P22G6A2S0S9SbG8S23A2S0S9SbSeS91S23G9A3G4A2S0S9SbS23G3A2S0S9SbS55SaZ1A1A2S0S9SbS30SaS9dG6Z1bA2A1A2S0S9SbS81S57A2S0S9SbSaZ7fff7f800000A1MaG4A2S0S9SbG4SaZ7fffff800000A1A2S0S9SbGaG2A2S3S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3SacS84S81S83PfA4A3").
Definition X_op (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4S8S8A2M0S1S8S8S7fSaZ20A1A4S0G0S1S8S8S28SaZ30A1A4S0G0S1S8S8S24SaS9cZ4S1fA2A1M1A4S0G0S1S8S8S23G1A4S0G0S1S8S8Vd;SadVk;A1A4S3G0A1A3A3A3A3A3").
Definition canon_op (fc : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfS5cVfc;A1S0SfS5dS0SfS61Vd;Vc;Vk;A3S0SfS5eS0SfS60S0SfS5fS0SfSafVd;Vk;A2S3SfA1A3A3A3A3A3A3A3SaaA3").
Definition Pre_op : axst := ltac2:(tb__ "0|1|
Sa7S14Sb7S98S9aS0S4S2S8A2M0S1S2S8UbSaS1fA1A4S3G0A1A3A2S97S12S6S8A1S2cS3ScA1S84S81S83A4S2dS96S7A9S2bS84S83A2A2").
Definition tv0 : list (sv * sv) := tv_vec vDt vK.
Definition bd_op (k : sv) : list bitem := bd_cnt Wp k.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS79S3S4S4S8S18A2S8A2A1S3eS83A1A3").

Definition cutpcs_op : list Z := ltac2:(tb__ "0|0|
S0S18Sb1S0S18Sb4S0S18Sb3S3S18A1A3A3A3").
Definition optAo (x : option axst) : axst := match x with Some s => s | None => Pre_op end.
Definition leafO_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sb8S1aVk;Sa9S44S76VS;Vpc;A4S3bA4").

Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0ScS7eN78S55A2S0ScS7eN70S28A2S0ScS7eN68SdP2fA1A2S0ScS7eN60SdP2eA1A2S0ScS7eN58SdP2dA1A2S0ScS7eN50SdP2cA1A2S0ScS7eN48SdP2bA1A2S0ScS7eN40SdP2aA1A2S0ScS7eN38SdP29A1A2S0ScS7eN30SdP28A1A2S0ScS7eN28SdP27A1A2S0ScS7eN20SdP26A1A2S0ScS7eN18SdP1dA1A2S0ScS7eN10SdP1cA1A2S0ScS7eN8SdPbA1A2S3ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pD : sv := SVar 240. Definition pC : sv := SVar 241. Definition pK : sv := SVar 242.
Definition gV : positive := 250%positive.
Definition HNEXT : positive := 260%positive.
Definition shv (k : Z) : sv := ltac2:(tb__ "0|0|
SeS91SdS41A1SaS9fSa8Vk;A2A1A3").
Definition gV_facts : list sprop := ltac2:(tb__ "0|2|
S0S9S17SeS95SdS41A1M0SaZ3A1A3M1S7fA2S0S9SbG0SaS9eS9dZ2Z3dA2Z1A2A1A2S0S9SbG1S7fA2S0S9SbS7fG1A2S3S9A1A3A3A3A3").

Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S98Sb9S2S8S25SbaU0M0U20A2A4S5S4S2S8A2M1S0G1S1S2S8G0SdP14A1A4S0G1S1S2S8U2S80Z80A1A4S0G1S1S2S8U3SdP17A1A4S0G1S1S2S8U4SdP18A1A4S0G1S1S2S8U8SeS91S7fSaZ8A1A3A4S0G1S1S2S8U9SaS1fA1A4S0G1S1S2S8U12S24A4S0G1S1S2S8U13S7fA4S0G1S1S2S8U14SeS91SdS41A1SaSa8A1A3A4S0G1S1S2S8U15S23A4S0G1S1S2S8U16S53Z3A1A4S0G1S1S2S8U17S30A4S0G1S1S2S8U18SeS91S7fSaZ18A1A3A4S0G1S1S2S8U19SabA4S0G1S1S2S8U1aS53Z1M2A1A4S0G1S1S2S8U1bSaS9eS9eS9dZ2Z40A2G2A2S1fA2A1A4S3G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition cBnd : sprop := ltac2:(tb__ "0|0|
SbS1eSaS9fS9cS1fS9dZ2Z1bA2A2S1fA2A1A2").
Definition OS (pc : Z) (regs : list (nat * sv)) (d c k : sv) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
Sa7S14Vpc;S3fVregs;A1S97S12S6S8A1S2cS3aVd;Vc;Vk;A4S5S9Vfacts;S5S9S0S9S40S3S9A1A3S5S9S42S5S9SacVd;Vc;Vk;Pf0A4S2dA3A3A3A3Vnx;S7A9S2bVd;Vk;A2A2").

Definition inL : sprop := ltac2:(tb__ "0|0|
SbSeS91S1eSaZ1A1A3S10S92SaS1fA1S30A3A2").
Definition C_L : axst := ltac2:(tb__ "0|1|
S32Sb4S0S4S2S8A2M0S1S2S8UbS1eA4S3G0A1A3S21S1eS20S0S9S37S3S9A1A3S26A7").

Definition inJ : sprop := SPUle pC Cb.
Definition C_J2 : axst := ltac2:(tb__ "0|5|
Sa7S14Sb3S98S3fS0S4S2S8A2M0S1S2S8UbS1eA4S3G0A1M1A3A1S0G0S1S2S8U14M2S25G2A1A4S0G0S1S2S8U16M3S25G3A1A4S0G0S1S2S8U18M4S25G4A1A4G1A3A3A3A2S97S12S6S8A1S2cS3aS21S1eS20A4S5S9S0S9S36S0S9S40S3S9A1A3A3S5S9S42S5S9SacS21S1eS20Pf0A4S2dA3A3A3S26S7A9S2bS21S20A2A2").
Definition ndC : ndesc := ltac2:(tb__ "0|0|
S1dSaeS21S20A2S3S4S4S8S18A2S8A2A1S3eS20A1A3").

Definition E_vrL0 : axst := Eval vm_compute in leafO_at C_L vr_entry 0.
Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0Sa2Sa6U1M0SaN40M1A1A2S0Sa2Sa3G0G1A2S3Sa2A1A3A3").
Definition E_vrL : axst := Eval vm_compute in optAo (apply_axforms E_vrL0 xf_vcall).
Definition s_vr (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S19S8A2M0S1S19S8P13SeS91S82SaZ40A1A3A4S0G0S1S19S8P3bS4aA4S9bPaS1bVE;A1S1bS85A1A3A3A3").
Definition optRo (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_vrL : list sobj := Eval vm_compute in optRo (entails_frA E_vrL Pre_vr (s_vr E_vrL)).
Definition PD_vrN : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S1aS1cA2M0S1S1aS1cS89S8bA4S0G0S1S1aS1cS87S1dS8cS3S4S4S8S18A2S8A2A1M1S3SbbA1A3A4S0G0S1S1aS1cS88S1dS8dG1S8aS8fS8eA2A3A4S3G0A1A3A3A3").
Definition Xk_op : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4S8S8A2M0S1S8S8S7fSaZ20A1A4S0G0S1S8S8S28SaZ30A1A4S0G0S1S8S8S24SaS9cZ4S1fA2A1M1A4S0G0S1S8S8S23G1A4S3G0A1A3A3A3A3").

Definition T_keepL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_keep Xk_op.
Definition T_failL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_fail Xk_op.
Definition T_grownL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_grown Xk_op.

Definition xf_vback : list axform := ltac2:(tb__ "0|1|
S0Sa2Sa3U1M0Z40A2S0Sa2Sa5S0S2U7S0S2G0S0S2U0S0S2U2S0S2U3S0S2U8S0S2U9S0S2U4S0S2U5S0S2U6S3S2A1A3A3A3A3A3A3A3A3A3A3A1S0Sa2Sa4G0A1S3Sa2A1A3A3A3").
Definition T_keepL : axst := Eval vm_compute in optAo (apply_axforms T_keepL0 xf_vback).
Definition T_failL : axst := Eval vm_compute in optAo (apply_axforms T_failL0 xf_vback).
Definition T_grownL : axst := Eval vm_compute in optAo (apply_axforms T_grownL0 xf_vback).

Definition slotL : sprop := ltac2:(tb__ "0|0|
SbSeS91S1eSaS1fA1A3S20A2").
Definition TA_L : axst := ltac2:(tb__ "0|1|
S32Sb0S0S4S2S8A2M0S1S2S8U1SaSb5A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S21S1eS20S0S9S37S0S9S2fS3S9A1A3A3S26A7").
Definition TF_L : axst := ltac2:(tb__ "0|1|
S32Sb0S0S4S2S8A2M0S1S2S8U1SaSb5A1A4S0G0S1S2S8UaSaZ0A1A4S3G0A1A3A3S21S1eS20S3S9A1S26A7").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S1dSaeS21S20A2S3S4S4S8S18A2S8A2A1S3SbbA1A3").

Definition pR : sv := SVar 243.
Definition joff : sv := ltac2:(tb__ "0|0|
SeS93SaS9cZ4S1fA2A1S27A3").

Definition dstj : sv := ltac2:(tb__ "0|0|
SeS91S77SeS91S21S10S92S1eSaZ4A1A3A3A3").
Definition srcj (b : sv) : sv := SAlu ALU_ADD joff b.
Definition slot4 : sprop := ltac2:(tb__ "0|1|
SbSeS91S10S92S1eSaZ4M0A1A3SaS9cG0S1fA2A1A3SadS20A1A2").
Definition R_facts : list sprop := ltac2:(tb__ "0|0|
S0S9SbSaZ1A1S27A2S0S9SbS27SaS9cZ4S1fA2A1A2S3S9A1A3A3").
Definition K_cp1 : axst := ltac2:(tb__ "0|2|
S32Za5e7cS0S4S2S8A2M0S1S2S8UaS35A4S0G0S1S2S8UdS35A4S0G0S1S2S8UbS54S23A1M1A4S0G0S1S2S8UeG1A4S0G0S1S2S8UcS27A4S3G0A1A3A3A3A3A3S21S1eS20S5S9S0S9S37S0S9S2fS0S9S39S3S9A1A3A3A3S48A3S26A7").

Definition TA_Ls : axst := ltac2:(tb__ "0|1|
S32Sb0S0S4S2S8A2M0S1S2S8U1SaSb5A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S21S1eS20S0S9S37S0S9S2fS0S9S39S3S9A1A3A3A3S26A7").

Definition E_2v0 : axst := Eval vm_compute in leafO_at C_J2 vr_entry 0.
Definition E_2d0 : axst := Eval vm_compute in leafO_at C_J2 vr_entry 1.
Definition E_2v : axst := Eval vm_compute in optAo (apply_axforms E_2v0 xf_vcall).
Definition E_2d : axst := Eval vm_compute in optAo (apply_axforms E_2d0 xf_vcall).
Definition R_2v : list sobj := Eval vm_compute in optRo (entails_frA E_2v Pre_vr (s_vr E_2v)).
Definition R_2d : list sobj := Eval vm_compute in optRo (entails_frA E_2d Pre_vr (s_vr E_2d)).
Definition T_keep2v0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2v (s_vr E_2v) R_2v P_keep Xk_op.
Definition T_fail2v0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2v (s_vr E_2v) R_2v P_fail Xk_op.
Definition T_grown2v0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2v (s_vr E_2v) R_2v P_grown Xk_op.
Definition T_keep2d0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2d (s_vr E_2d) R_2d P_keep Xk_op.
Definition T_fail2d0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2d (s_vr E_2d) R_2d P_fail Xk_op.
Definition T_grown2d0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_2d (s_vr E_2d) R_2d P_grown Xk_op.
Definition T_keep2v : axst := Eval vm_compute in optAo (apply_axforms T_keep2v0 xf_vback).
Definition T_fail2v : axst := Eval vm_compute in optAo (apply_axforms T_fail2v0 xf_vback).
Definition T_grown2v : axst := Eval vm_compute in optAo (apply_axforms T_grown2v0 xf_vback).
Definition T_keep2d : axst := Eval vm_compute in optAo (apply_axforms T_keep2d0 xf_vback).
Definition T_fail2d : axst := Eval vm_compute in optAo (apply_axforms T_fail2d0 xf_vback).
Definition T_grown2d : axst := Eval vm_compute in optAo (apply_axforms T_grown2d0 xf_vback).

Definition OS2 (pc : Z) (regs : list (nat * sv)) (d c k : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|4|
Sa7S14Vpc;S98S3fVregs;A1S0S4S2S8A2M0S1S2S8U14M1S25G1A1A4S0G0S1S2S8U16M2S25G2A1A4S0G0S1S2S8U18M3S25G3A1A4S3G0A1A3A3A3A2S97S12S6S8A1S2cS3aVd;Vc;Vk;A4S5S9Vfacts;S5S9S0S9S40S3S9A1A3S5S9S42S5S9SacVd;Vc;Vk;Pf0A4S2dA3A3A3A3S26S7A9S2bVd;Vk;A2A2").
Definition TA_2 (src : sv) : axst := ltac2:(tb__ "0|1|
S34Sb0S0S4S2S8A2M0S1S2S8U1SaSb2A1A4S0G0S1S2S8UaSaZ1A1A4S0G0S1S2S8U12Vsrc;A4S3G0A1A3A3A3S21S1eS20S0S9S36S0S9S2fS3S9A1A3A3A6").
Definition TA_2s (src : sv) : axst := ltac2:(tb__ "0|1|
S34Sb0S0S4S2S8A2M0S1S2S8U1SaSb2A1A4S0G0S1S2S8UaSaZ1A1A4S0G0S1S2S8U12Vsrc;A4S3G0A1A3A3A3S21S1eS20S0S9S36S0S9S2fS0S9S39S3S9A1A3A3A3A6").
Definition TF_2 : axst := ltac2:(tb__ "0|2|
S34Sb0S0S4S2S8A2M0S1S2S8U1SaSb2A1A4S0G0S1S2S8UaSaZ0A1A4S0G0S1S2S8U12M1S25G1A1A4S3G0A1A3A3A3S21S1eS20S3S9A1A6").
Definition K_cp2 (src : sv) : axst := ltac2:(tb__ "0|2|
S34Za5f78S0S4S2S8A2M0S1S2S8U1SaSb2A1A4S0G0S1S2S8UaS35A4S0G0S1S2S8UdS35A4S0G0S1S2S8UbS54Vsrc;A1M1A4S0G0S1S2S8U12G1A4S0G0S1S2S8UcS27A4S3G0A1A3A3A3A3A3A3S21S1eS20S5S9S0S9S36S0S9S2fS0S9S39S3S9A1A3A3A3S48A3A6").

Definition P_op1 : axst := ltac2:(tb__ "0|5|
Sa7S14Sb6S98S99S96A1S0S4S2S8A2M0S1S2S8UaSaZ1A1A4S3G0A1A3A2S97S12S6S8A1S2cS3ScA1SdP8cM1A1M2SdP8dA1M3SdP8eA1M4A4S5S9S0S9SbG3S4aA2S3S9A1A3S5S9SacG2G3G4G1A4S2dA3A3P8fS7A9S2bG2G4A2A2").
Definition P_op0 : axst := ltac2:(tb__ "0|5|
Sa7S14Sb6S98S99S96A1S0S4S2S8A2M0S1S2S8UaSaZ0A1A4S3G0A1A3A2S97S12S6S8A1S2cS3ScA1SdP8cM1A1M2SdP8dA1M3SdP8eA1M4A4S5S9SacG2G3G4G1A4S2dA3P8fS7A9S2bG2G4A2A2").
Definition tvQ : list (sv * sv) := tv_vec (SVar 140) (SVar 142).
Definition nd1 : ndesc := ltac2:(tb__ "0|0|
S1dS7aS3S4S4S8S18A2S8A2A1S3eSdP8eA1A1A3").
Definition nd0' : ndesc := ND tvQ [] [].
Definition PD_op : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S1aS1cA2M0S1S1aS1cS47S50A4S0G0S1S1aS1cS46S4fA4S3G0A1A3A3").

Definition X_Lin0 : axst := Eval vm_compute in leafO_at Pre_op op_L 0.
Definition X_Lin1 : axst := Eval vm_compute in leafO_at Pre_op op_L 1.
Definition cutpcs_all : list Z := ltac2:(tb__ "0|0|
S0S18Sb1S0S18Sb4S0S18Sb3S0S18Za5e7cS0S18Za5f78S3S18A1A3A3A3A3A3").
Definition leafK_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sb8S1aVk;Sa9S44S75VS;Vpc;A4S3bA4").

Definition VB (c : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
SeS91S10S92SaZ20A1SeS93SaS9fS86Z1000A2A1Vc;A3A3SaVph;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsO : list edescA := ltac2:(tb__ "0|7|
S0S4S4S1aS1cA2M0S4S18S8A2M1A2M2S1G0G1S1S1aS1cS3bS43A4S1S18S8Z64S29A4A4S0G2S1G0G1S1S1aS1cS31S22A4S1S18S8Z32M3S33S1eZ14A2A4A4S0G2S1G0G1S1S1aS1cS3cS22A4S1S18S8G3S33S1eZ12A2A4A4S0G2S1G0G1S1S1aS1cS49S51A4S1S18S8Z2dS29A4A4S0G2S1G0G1S1S1aS1cS5bS22A4S1S18S8G3SeS91S33S1eZ1A2S27A3A4A4S0G2S1G0G1S1S1aS1cS56S22A4S1S18S8Z28S29A4A4S0G2S1G0G1S1S1aS1cS2aS24A1S22A4S1S18S8Z1eM4SaS9fZaS9cZ4S1fA2A2A1A4M5A4S0G2S1G0G1S1S1aS1cS2aS23A1S22A4G5A4S0G2S1G0G1S1S1aS1cS3dS51A4S1S18S8G4S29A4A4S0G2S1G0G1S1S1aS1cS45S24A1S22A4S1S18S8G4S27A4M6A4S0G2S1G0G1S1S1aS1cS45S23A1S22A4G6A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3").

Definition X_back0 : axst := Eval vm_compute in leafK_at K_cp1 op_L 0.
Definition X_back1 : axst := Eval vm_compute in leafK_at K_cp1 op_L 1.
Definition exitsO : list edescA := ltac2:(tb__ "0|9|
S0S4S4S1aS1cA2M0S4S18S8A2M1A2M2S1G0G1S1S1aS1cS4bS43A4S1S18S8Z5aS29A4M3A4S0G2S1G0G1S1S1aS1cS4cS43A4G3A4S0G2S1G0G1S1S1aS1cS5aS22A4S1S18S8Z32M4S33S1eZ13A2A4A4S0G2S1G0G1S1S1aS1cS4dS22A4S1S18S8G4S33S1eZ0M5A2A4M6A4S0G2S1G0G1S1S1aS1cS4eS22A4G6A4S0G2S1G0G1S1S1aS1cS59S22A4S1S18S8Z23S29A4M7A4S0G2S1G0G1S1S1aS1cS58S22A4G7A4S0G2S1G0G1S1S1aS1cS47S50A4S1S18S8G5S29A4M8A4S0G2S1G0G1S1S1aS1cS46S4fA4G8A4S3G2A1A3A3A3A3A3A3A3A3A3").

Definition isub (E : axst) (P : axst) : wsub := ltac2:(tb__ "0|0|
SbfS78VE;A1S85VP;VE;A4").
Definition vDgL : sv := Eval vm_compute in wsub_get (isub E_vrL P_grown) 140%positive.
Definition vKgL : sv := Eval vm_compute in wsub_get (isub E_vrL P_grown) 141%positive.
Definition vDg2v : sv := Eval vm_compute in wsub_get (isub E_2v P_grown) 140%positive.
Definition vKg2v : sv := Eval vm_compute in wsub_get (isub E_2v P_grown) 141%positive.
Definition vDg2d : sv := Eval vm_compute in wsub_get (isub E_2d P_grown) 140%positive.
Definition vKg2d : sv := Eval vm_compute in wsub_get (isub E_2d P_grown) 141%positive.

Definition slot4_at (k : sv) : sprop := ltac2:(tb__ "0|1|
SbSeS91S10S92S1eSaZ4M0A1A3SaS9cG0S1fA2A1A3SadVk;A1A2").
Definition T_keepLs : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS20A1S3S9A1A3S6fA2").
Definition T_grownLs : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS7dA1S3S9A1A3S69A2").
Definition T_keep2vs : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS20A1S3S9A1A3S6dA2").
Definition T_grown2vs : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS7cA1S3S9A1A3S67A2").
Definition T_keep2ds : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS20A1S3S9A1A3S6bA2").
Definition T_grown2ds : axst := ltac2:(tb__ "0|0|
Sa1S0S9S2eS7bA1S3S9A1A3S65A2").
Definition s_keepL : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS70A1S1bS3cA1A3").
Definition s_grownL : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS6aA1S1bS3cA1A3").
Definition s_failL : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS64A1S1bS49A1A3").
Definition s_keep2v : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS6eA1S1bS2aS24A1A1A3").
Definition s_grown2v : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS68A1S1bS2aS24A1A1A3").
Definition s_fail2v : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS63A1S1bS3dA1A3").
Definition s_keep2d : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS6cA1S1bS2aS23A1A1A3").
Definition s_grown2d : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS66A1S1bS2aS23A1A1A3").
Definition s_fail2d : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS62A1S1bS3dA1A3").

Definition inL_at (c : sv) : sprop := ltac2:(tb__ "0|0|
SbSeS91Vc;SaZ1A1A3S10S92SaS1fA1S30A3A2").
Definition X_Lin0f : axst := ltac2:(tb__ "0|0|
Sa1S0S9S38S81A1S3S9A1A3S4bA2").
Definition X_Lin1f : axst := ltac2:(tb__ "0|0|
Sa1S0S9S38S81A1S3S9A1A3S4cA2").
Definition pCM : sv := ltac2:(tb__ "0|0|
SeS91S1eSaS1fA1A3").
Definition X_back0f : axst := ltac2:(tb__ "0|0|
Sa1S0S9S38S52A1S3S9A1A3S4dA2").
Definition X_back1f : axst := ltac2:(tb__ "0|0|
Sa1S0S9S38S52A1S3S9A1A3S4eA2").
Definition s_Lin0 : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS71A1S1bS31A1A3").
Definition s_Lin1 : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS72A1S1bS31A1A3").
Definition s_back0 : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS73A1S1bS31A1A3").
Definition s_back1 : wsub := ltac2:(tb__ "0|0|
S9bS96S1bS74A1S1bS31A1A3").
