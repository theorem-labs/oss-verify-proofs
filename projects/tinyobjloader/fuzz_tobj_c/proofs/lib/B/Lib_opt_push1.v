(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "cell"; "SPUle"; "SVar"; "SAlu"; "sobj"; "SMd"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "SPAlign"; "SPBranch"; "SPEq"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "c8"; "vV"; "spm"; "vC"; "vDp"; "vK"; "vDt"; "Pre_vr"; "two47"; "P_fail"; "P_grown"; "P_keep"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push1"; "pC"; "CM"; "pK"; "pD"; "ndC"; "vDEF"; "vVALS"; "HNEXT"; "hx"; "vALo"; "z0"; "TA_2s"; "X_op"; "canon_op"; "op_facts"; "slot4_at"; "slotL"; "vVIDX"; "C_L"; "OS"; "VB"; "dnzB"; "OS2"; "dstB"; "inJ"; "inL"; "inL_at"; "pR"; "slot4"; "Pre_op"; "TA_Ls"; "TF_2"; "bd_op"; "body_regs"; "cBnd"; "gV"; "gV_facts"; "nd0"; "notB"; "FUEL_op"; "F_cells"; "K_cp2"; "P_op0"; "P_op1"; "R_facts"; "TF_L"; "Wp"; "X_Lin0"; "X_Lin1"; "X_back0"; "X_back1"; "nd0'"; "nd1"; "ndF"; "pCM"; "shv"; "vPRES"; "C_J2"; "Cb"; "E_2d0"; "E_2v0"; "E_vrL0"; "F_cells_src"; "K_cp1"; "O_Fo"; "O_Wo"; "O_alo"; "O_deflt"; "O_vals"; "O_vec4"; "T_fail2d"; "T_fail2v"; "T_failL"; "T_grown2d"; "T_grown2ds"; "T_grown2v"; "T_grown2vs"; "T_grownL"; "T_grownLs"; "T_keep2d"; "T_keep2ds"; "T_keep2v"; "T_keep2vs"; "T_keepL"; "T_keepLs"; "X_Lin0f"; "X_Lin1f"; "X_back0f"; "X_back1f"; "cutpcs_all"; "cutpcs_op"; "pSRC"; "s_vr"; "tv0"; "tvQ"; "vKg2d"; "vKg2v"; "vKgL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SUB"; "BC_GE"; "ALU_SLL"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "pow"; "sub"; "add"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "SHB"; "leavesA_at"; "A_globals"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vec4_facts"; "kb4"; "tv_vec"; "O_dat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.VRNAddr"; "vr_ret"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push1.OPAddr"; "ra2"; "op_J2"; "op_L"; "raL"; "op_ret"; "op_entry"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr.

Definition CM : Z := 1.

Module OPAddr.
  Definition op_entry : Z := 0xa3f44.
  Definition op_L : Z := 0xa400c.
  Definition op_J2 : Z := 0xa40f8.
  Definition op_ret : Z := 0xa4248.
  Definition raL : Z := 0xa4020.
  Definition ra2 : Z := 0xa4120.
End OPAddr.
Import OPAddr.

Definition FUEL_op : nat := 600%nat.

Definition vVIDX : sv := SVar 14. Definition vVALS : sv := SVar 33. Definition vDEF : sv := SVar 34.
Definition vPRES : sv := SVar 35. Definition vALo : sv := SVar 36.

Definition Wp : sv := ltac2:(tb__ "0|0|
SeS94S10S95SaS33A1S43A3SaSa2Sa0Z2S33A2Z1A2A1A3").

Definition Cb : sv := ltac2:(tb__ "0|0|
SeS94S10S95SaS33A1S43A3SaSa2S33Z1A2A1A3").

Definition O_Fo (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13SdPaA1SaN80A1SaZ0A1Vcells;S11A5").
Definition O_Wo : sobj := ltac2:(tb__ "0|0|
S13S21Z80A1S23SaZ0A1S3SbA1S11A5").
Definition O_vec4 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S13S20SaZ0M0A1SaZ20A1S0SbS1fG0Vd;A2S0SbS1fZ8Vc;A2S0SbS1fZ10Vk;A2S0SbS1fZ18SaZ4A1A2S3SbA1A3A3A3A3S11A5").
Definition O_alo : sobj := ltac2:(tb__ "0|2|
S13S3bSaZ0M0A1M1SaZ30A1S0SbS1fG0SaSc0A1A2S0SbS1fZ8SaSc1A1A2S0SbS1fZ10G1A2S0SbS1fZ18SaSc2A1A2S0SbS1fZ20G1A2S0SbS1fZ28S31A2S3SbA1A3A3A3A3A3A3S11A5").
Definition O_vals : sobj := ltac2:(tb__ "0|0|
S13S38SaZ0A1SaSa0Z4S33A2A1S3SbA1S11A5").
Definition O_deflt : sobj := ltac2:(tb__ "0|0|
S13S37SaZ0A1SaSa0Z4S33A2A1S3SbA1S11A5").

Definition op_facts : list sprop := ltac2:(tb__ "0|b|
S5S9S0S9S15PaM0Z4M1A2S0S9ScSdG0A1M2SaS27A1M3A2S0S9ScSdP1eA1M4SeS94S21Z80A1M5S23A3A2S0S9ScG4S21Z120A1A2S0S9ScG4S21Zc0A1A2S0S9ScG4G5A2S0S9ScG4G2A2S0S9S16S97SaN10a0A1S23A3S0S9S16S97S23SaSa4Sa1Z2M6Z26A2A1A1A3S0S9S15PcZ3M7A2S0S9ScSaZ1000A1M8S20A2S0S9ScSeS94S20SaZ20A1A3G4A2S0S9ScS20G3A2S0S9S15P24G7A2S0S9ScG8S3bA2S0S9ScSeS94S3bSaZ30A1A3G4A2S0S9ScS3bG3A2S0S9S15P21G6A2S0S9ScG8S38A2S0S9ScSeS94S38SaSa0G1S33A2A1M9A3G4A2S0S9ScS38G3A2S0S9S15P22G6A2S0S9ScG8S37A2S0S9ScSeS94S37G9A3G4A2S0S9ScS37G3A2S0S9ScS6aSaZ1A1A2S0S9ScS43SaSa1G6Z1bA2A1A2S0S9ScS22S6cA2S0S9ScSaZ7fff7f800000A1MaG4A2S0S9ScG4SaZ7fffff800000A1A2S0S9ScGaG2A2S3S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Sb0S25S22S24PfA4A3").
Definition X_op (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4S8S8A2M0S1S8S8S20SaZ20A1A4S0G0S1S8S8S3bSaZ30A1A4S0G0S1S8S8S38SaSa0Z4S33A2A1M1A4S0G0S1S8S8S37G1A4S0G0S1S8S8Vd;Sb1Vk;A1A4S3G0A1A3A3A3A3A3").
Definition canon_op (fc : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfS72Vfc;A1S0SfS73S0SfS77Vd;Vc;Vk;A3S0SfS74S0SfS76S0SfS75S0SfSb3Vd;Vk;A2S3SfA1A3A3A3A3A3A3A3SaeA3").
Definition Pre_op : axst := ltac2:(tb__ "0|1|
SabS14SbbS9cS9eS0S4S2S8A2M0S1S2S8UbSaS33A1A4S3G0A1A3A2S9bS12S6S8A1S3fS3SbA1S25S22S24A4S40S9aS7A9S3eS25S24A2A2").
Definition tv0 : list (sv * sv) := tv_vec vDt vK.
Definition bd_op (k : sv) : list bitem := bd_cnt Wp k.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1eS8fS3S4S4S8S19A2S8A2A1S52S24A1A3").

Definition cutpcs_op : list Z := ltac2:(tb__ "0|0|
S0S19Sb5S0S19Sb8S0S19Sb7S3S19A1A3A3A3").
Definition optAo (x : option axst) : axst := match x with Some s => s | None => Pre_op end.
Definition leafO_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SbcS1bVk;SadS59S8cVS;Vpc;A4S4fA4").

Definition F_cells_src (src : sv) : list cell := ltac2:(tb__ "0|0|
S0SbS1fN80Vsrc;A2S0SbS1fN78S6aA2S0SbS1fN70S3bA2S0SbS1fN68SdP2fA1A2S0SbS1fN60SdP2eA1A2S0SbS1fN58SdP2dA1A2S0SbS1fN50SdP2cA1A2S0SbS1fN48SdP2bA1A2S0SbS1fN40SdP2aA1A2S0SbS1fN38SdP29A1A2S0SbS1fN30SdP28A1A2S0SbS1fN28SdP27A1A2S0SbS1fN20SdP26A1A2S0SbS1fN18SdP1dA1A2S0SbS1fN10SdP1cA1A2S0SbS1fN8SdPbA1A2S3SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_cells : list cell := F_cells_src vVALS.

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pD : sv := SVar 240. Definition pC : sv := SVar 241. Definition pK : sv := SVar 242.
Definition gV : positive := 250%positive.
Definition HNEXT : positive := 260%positive.
Definition shv (k : Z) : sv := ltac2:(tb__ "0|0|
SeS94SdS55A1SaSa3SacVk;A2A1A3").
Definition gV_facts : list sprop := ltac2:(tb__ "0|2|
S0S9S17SeS98SdS55A1M0SaZ3A1A3M1S20A2S0S9ScG0SaSa2Sa1Z2Z3dA2Z1A2A1A2S0S9ScG1S20A2S0S9ScS20G1A2S3S9A1A3A3A3A3").

Definition body_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|3|
S9cSbdS2S8S3aSbeU0M0U20A2A4S5S4S2S8A2M1S0G1S1S2S8G0SdP14A1A4S0G1S1S2S8U2S21Z80A1A4S0G1S1S2S8U3SdP17A1A4S0G1S1S2S8U4SdP18A1A4S0G1S1S2S8U8SeS94S20SaZ8A1A3A4S0G1S1S2S8U9SaS33A1A4S0G1S1S2S8U12SeS99S37SaZffffffffffffffffA1A3A4S0G1S1S2S8U13S20A4S0G1S1S2S8U14SeS94SdS55A1SaSacA1A3A4S0G1S1S2S8U15S37A4S0G1S1S2S8U16S69Z3A1A4S0G1S1S2S8U17S43A4S0G1S1S2S8U18SeS94S20SaZ18A1A3A4S0G1S1S2S8U19SafA4S0G1S1S2S8U1aS69Z1M2A1A4S0G1S1S2S8U1bSaSa2Sa2Sa1Z2Z40A2G2A2S33A2A1A4S3G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition cBnd : sprop := ltac2:(tb__ "0|0|
ScS32SaSa3Sa0S33Sa1Z2Z1bA2A2S33A2A1A2").
Definition OS (pc : Z) (regs : list (nat * sv)) (d c k : sv) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
SabS14Vpc;S53Vregs;A1S9bS12S6S8A1S3fS5aVd;Vc;Vk;A4S5S9Vfacts;S5S9S0S9S54S3S9A1A3S5S9S56S5S9Sb0Vd;Vc;Vk;Pf0A4S40A3A3A3A3Vnx;S7A9S3eVd;Vk;A2A2").

Definition inL : sprop := ltac2:(tb__ "0|0|
ScSeS94S32SaZ1A1A3S10S95SaS33A1S43A3A2").
Definition C_L : axst := ltac2:(tb__ "0|1|
S45Sb8S0S4S2S8A2M0S1S2S8UbS32A4S3G0A1A3S35S32S34S0S9S4bS3S9A1A3S39A7").

Definition inJ : sprop := SPUle pC Cb.
Definition C_J2 : axst := ltac2:(tb__ "0|5|
SabS14Sb7S9cS53S0S4S2S8A2M0S1S2S8UbS32A4S3G0A1M1A3A1S0G0S1S2S8U12M2S3aG2A1A4S0G0S1S2S8U14M3S3aG3A1A4S0G0S1S2S8U16M4S3aG4A1A4G1A3A3A3A2S9bS12S6S8A1S3fS5aS35S32S34A4S5S9S0S9S4aS0S9S54S3S9A1A3A3S5S9S56S5S9Sb0S35S32S34Pf0A4S40A3A3A3S39S7A9S3eS35S34A2A2").
Definition ndC : ndesc := ltac2:(tb__ "0|0|
S1eSb2S35S34A2S3S4S4S8S19A2S8A2A1S52S34A1A3").

Definition E_vrL0 : axst := Eval vm_compute in leafO_at C_L vr_entry 0.
Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0Sa6SaaU1M0SaN40M1A1A2S0Sa6Sa7G0G1A2S3Sa6A1A3A3").
Definition E_vrL : axst := Eval vm_compute in optAo (apply_axforms E_vrL0 xf_vcall).
Definition s_vr (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S1aS8A2M0S1S1aS8P13SeS94S23SaZ40A1A3A4S0G0S1S1aS8P3bS60A4S9fPaS1cVE;A1S1cS26A1A3A3A3").
Definition optRo (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_vrL : list sobj := Eval vm_compute in optRo (entails_frA E_vrL Pre_vr (s_vr E_vrL)).
Definition PD_vrN : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S1bS1dA2M0S1S1bS1dS2aS2cA4S0G0S1S1bS1dS28S1eS2dS3S4S4S8S19A2S8A2A1M1S3SbfA1A3A4S0G0S1S1bS1dS29S1eS2eG1S2bS30S2fA2A3A4S3G0A1A3A3A3").
Definition Xk_op : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4S8S8A2M0S1S8S8S20SaZ20A1A4S0G0S1S8S8S3bSaZ30A1A4S0G0S1S8S8S38SaSa0Z4S33A2A1M1A4S0G0S1S8S8S37G1A4S3G0A1A3A3A3A3").

Definition T_keepL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_keep Xk_op.
Definition T_failL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_fail Xk_op.
Definition T_grownL0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrL (s_vr E_vrL) R_vrL P_grown Xk_op.

Definition xf_vback : list axform := ltac2:(tb__ "0|1|
S0Sa6Sa7U1M0Z40A2S0Sa6Sa9S0S2U7S0S2G0S0S2U0S0S2U2S0S2U3S0S2U8S0S2U9S0S2U4S0S2U5S0S2U6S3S2A1A3A3A3A3A3A3A3A3A3A3A1S0Sa6Sa8G0A1S3Sa6A1A3A3A3").
Definition T_keepL : axst := Eval vm_compute in optAo (apply_axforms T_keepL0 xf_vback).
Definition T_failL : axst := Eval vm_compute in optAo (apply_axforms T_failL0 xf_vback).
Definition T_grownL : axst := Eval vm_compute in optAo (apply_axforms T_grownL0 xf_vback).

Definition slotL : sprop := ltac2:(tb__ "0|0|
ScSeS94S32SaS33A1A3S34A2").
Definition TA_L : axst := ltac2:(tb__ "0|1|
S45Sb4S0S4S2S8A2M0S1S2S8U1SaSb9A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S35S32S34S0S9S4bS0S9S42S3S9A1A3A3S39A7").
Definition TF_L : axst := ltac2:(tb__ "0|1|
S45Sb4S0S4S2S8A2M0S1S2S8U1SaSb9A1A4S0G0S1S2S8UaSaZ0A1A4S3G0A1A3A3S35S32S34S3S9A1S39A7").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S1eSb2S35S34A2S3S4S4S8S19A2S8A2A1S3SbfA1A3").

Definition pR : sv := SVar 243.

Definition dstB : sv := ltac2:(tb__ "0|0|
SeS94S10S95S32SaZ4A1A3S35A3").
Definition notB (p : sv) : sv := SAlu ALU_XOR p (SLit 18446744073709551615).
Definition slot4 : sprop := ltac2:(tb__ "0|1|
ScSeS94S10S95S32SaZ4M0A1A3SaSa0G0S33A2A1A3Sb1S34A1A2").
Definition R_facts : list sprop := ltac2:(tb__ "0|0|
S0S9S18S4dSaSa0Z4S33A2A1A2S3S9A1A3").
Definition K_cp1 : axst := ltac2:(tb__ "0|1|
S45Za4080S0S4S2S8A2M0S1S2S8UcS49A4S0G0S1S2S8UdSaSa0Z4S33A2A1A4S0G0S1S2S8UeS4dA4S0G0S1S2S8UfS58S49A1A4S3G0A1A3A3A3A3S35S32S34S5S9S0S9S4bS0S9S42S0S9S4eS3S9A1A3A3A3S5eA3S39A7").

Definition dnzB : sprop := SPUle (SLit 4096) pD.
Definition TA_Ls : axst := ltac2:(tb__ "0|1|
S45Sb4S0S4S2S8A2M0S1S2S8U1SaSb9A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S35S32S34S0S9S4bS0S9S42S0S9S4eS0S9S47S3S9A1A3A3A3A3S39A7").

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

Definition OS2 (pc : Z) (src : sv) (regs : list (nat * sv)) (d c k : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|4|
SabS14Vpc;S9cS53Vregs;A1S0S4S2S8A2M0S1S2S8U12M1S3aG1A1A4S0G0S1S2S8U14M2S3aG2A1A4S0G0S1S2S8U16M3S3aG3A1A4S3G0A1A3A3A3A2S9bS12S6S8A1S3fS70Vsrc;A1Vd;Vc;Vk;A4S5S9Vfacts;S5S9S0S9S54S3S9A1A3S5S9S56S5S9Sb0Vd;Vc;Vk;Pf0A4S40A3A3A3A3S39S7A9S3eVd;Vk;A2A2").
Definition TA_2 (src : sv) : axst := ltac2:(tb__ "0|1|
S48Sb4Vsrc;S0S4S2S8A2M0S1S2S8U1SaSb6A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S35S32S34S0S9S4aS0S9S42S3S9A1A3A3A7").
Definition TA_2s (src : sv) : axst := ltac2:(tb__ "0|1|
S48Sb4Vsrc;S0S4S2S8A2M0S1S2S8U1SaSb6A1A4S0G0S1S2S8UaSaZ1A1A4S3G0A1A3A3S35S32S34S0S9S4aS0S9S42S0S9S4eS0S9S47S3S9A1A3A3A3A3A7").
Definition pSRC : sv := SVar 244.
Definition TF_2 : axst := ltac2:(tb__ "0|1|
S48Sb4S8dS0S4S2S8A2M0S1S2S8U1SaSb6A1A4S0G0S1S2S8UaSaZ0A1A4S3G0A1A3A3S35S32S34S3S9A1A7").
Definition K_cp2 (src : sv) : axst := ltac2:(tb__ "0|1|
S48Za4198Vsrc;S0S4S2S8A2M0S1S2S8U1SaSb6A1A4S0G0S1S2S8U6Vsrc;A4S0G0S1S2S8UcS49A4S0G0S1S2S8UdSaSa0Z4S33A2A1A4S0G0S1S2S8UeS4dA4S0G0S1S2S8UfS58Vsrc;A1A4S0G0S1S2S8U10S58S49A1A4S3G0A1A3A3A3A3A3A3A3S35S32S34S5S9S0S9S4aS0S9S42S0S9S4eS3S9A1A3A3A3S5eA3A7").

Definition P_op1 : axst := ltac2:(tb__ "0|5|
SabS14SbaS9cS9dS9aA1S0S4S2S8A2M0S1S2S8UaSaZ1A1A4S3G0A1A3A2S9bS12S6S8A1S3fS3SbA1SdP8cM1A1M2SdP8dA1M3SdP8eA1M4A4S5S9S0S9ScG3S60A2S3S9A1A3S5S9Sb0G2G3G4G1A4S40A3A3P8fS7A9S3eG2G4A2A2").
Definition P_op0 : axst := ltac2:(tb__ "0|5|
SabS14SbaS9cS9dS9aA1S0S4S2S8A2M0S1S2S8UaSaZ0A1A4S3G0A1A3A2S9bS12S6S8A1S3fS3SbA1SdP8cM1A1M2SdP8dA1M3SdP8eA1M4A4S5S9Sb0G2G3G4G1A4S40A3P8fS7A9S3eG2G4A2A2").
Definition tvQ : list (sv * sv) := tv_vec (SVar 140) (SVar 142).
Definition nd1 : ndesc := ltac2:(tb__ "0|0|
S1eS90S3S4S4S8S19A2S8A2A1S52SdP8eA1A1A3").
Definition nd0' : ndesc := ND tvQ [] [].
Definition PD_op : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S1bS1dA2M0S1S1bS1dS5dS66A4S0G0S1S1bS1dS5cS65A4S3G0A1A3A3").

Definition X_Lin0 : axst := Eval vm_compute in leafO_at Pre_op op_L 0.
Definition X_Lin1 : axst := Eval vm_compute in leafO_at Pre_op op_L 1.
Definition cutpcs_all : list Z := ltac2:(tb__ "0|0|
S0S19Sb5S0S19Sb8S0S19Sb7S0S19Za4080S0S19Za4198S3S19A1A3A3A3A3A3").
Definition leafK_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SbcS1bVk;SadS59S8bVS;Vpc;A4S4fA4").

Definition VB (c : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
SeS94S10S95SaZ20A1SeS96SaSa3S27Z1000A2A1Vc;A3A3SaVph;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsO : list edescA := ltac2:(tb__ "0|9|
S0S4S4S1bS1dA2M0S4S19S8A2M1A2M2S1G0G1S1S1bS1dS4fS57A4S1S19S8Z64S3cA4A4S0G2S1G0G1S1S1bS1dS44S36A4S1S19S8Z32M3S46S32Z14A2A4A4S0G2S1G0G1S1S1bS1dS50S36A4S1S19S8G3S46S32Z12A2A4A4S0G2S1G0G1S1S1bS1dS5fS67A4S1S19S8Z2dS3cA4A4S0G2S1G0G1S1S1bS1dS71S36A4S1S19S8G3SeS94S46S32Z1A2SeS96SaSa0Z4S33A2M4A1S4dA3M5A3A4A4S0G2S1G0G1S1S1bS1dS6bS36A4S1S19S8Z28S3cA4A4S0G2S1G0G1S1S1bS1dS3dS38A1S36A4S1S19S8Z1eM6SaSa3ZaG4A2A1A4M7A4S0G2S1G0G1S1S1bS1dS3dS37A1S36A4G7A4S0G2S1G0G1S1S1bS1dS51S67A4S1S19S8G6S3cA4A4S0G2S1G0G1S1S1bS1dS5bS38A1S36A4S1S19S8G6G5A4M8A4S0G2S1G0G1S1S1bS1dS5bS37A1S36A4G8A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3").

Definition X_back0 : axst := Eval vm_compute in leafK_at K_cp1 op_L 0.
Definition X_back1 : axst := Eval vm_compute in leafK_at K_cp1 op_L 1.
Definition exitsO : list edescA := ltac2:(tb__ "0|9|
S0S4S4S1bS1dA2M0S4S19S8A2M1A2M2S1G0G1S1S1bS1dS61S57A4S1S19S8Z5aS3cA4M3A4S0G2S1G0G1S1S1bS1dS62S57A4G3A4S0G2S1G0G1S1S1bS1dS6fS36A4S1S19S8Z32M4S46S32Z13A2A4A4S0G2S1G0G1S1S1bS1dS63S36A4S1S19S8G4S46S32Z0M5A2A4M6A4S0G2S1G0G1S1S1bS1dS64S36A4G6A4S0G2S1G0G1S1S1bS1dS6eS36A4S1S19S8Z23S3cA4M7A4S0G2S1G0G1S1S1bS1dS6dS36A4G7A4S0G2S1G0G1S1S1bS1dS5dS66A4S1S19S8G5S3cA4M8A4S0G2S1G0G1S1S1bS1dS5cS65A4G8A4S3G2A1A3A3A3A3A3A3A3A3A3").

Definition isub (E : axst) (P : axst) : wsub := ltac2:(tb__ "0|0|
Sc3S8eVE;A1S26VP;VE;A4").
Definition vDgL : sv := Eval vm_compute in wsub_get (isub E_vrL P_grown) 140%positive.
Definition vKgL : sv := Eval vm_compute in wsub_get (isub E_vrL P_grown) 141%positive.
Definition vDg2v : sv := Eval vm_compute in wsub_get (isub E_2v P_grown) 140%positive.
Definition vKg2v : sv := Eval vm_compute in wsub_get (isub E_2v P_grown) 141%positive.
Definition vDg2d : sv := Eval vm_compute in wsub_get (isub E_2d P_grown) 140%positive.
Definition vKg2d : sv := Eval vm_compute in wsub_get (isub E_2d P_grown) 141%positive.

Definition slot4_at (k : sv) : sprop := ltac2:(tb__ "0|1|
ScSeS94S10S95S32SaZ4M0A1A3SaSa0G0S33A2A1A3Sb1Vk;A1A2").
Definition T_keepLs : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S34A1S0S9S47S3S9A1A3A3S85A2").
Definition T_grownLs : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S93A1S3S9A1A3S7fA2").
Definition T_keep2vs : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S34A1S0S9S47S3S9A1A3A3S83A2").
Definition T_grown2vs : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S92A1S3S9A1A3S7dA2").
Definition T_keep2ds : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S34A1S0S9S47S3S9A1A3A3S81A2").
Definition T_grown2ds : axst := ltac2:(tb__ "0|0|
Sa5S0S9S41S91A1S3S9A1A3S7bA2").
Definition s_keepL : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS86A1S1cS50A1A3").
Definition s_grownL : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS80A1S1cS50A1A3").
Definition s_failL : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS7aA1S1cS5fA1A3").
Definition s_keep2v : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS84A1S1cS3dS38A1A1A3").
Definition s_grown2v : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS7eA1S1cS3dS38A1A1A3").
Definition s_fail2v : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS79A1S1cS51A1A3").
Definition s_keep2d : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS82A1S1cS3dS37A1A1A3").
Definition s_grown2d : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS7cA1S1cS3dS37A1A1A3").
Definition s_fail2d : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS78A1S1cS51A1A3").

Definition inL_at (c : sv) : sprop := ltac2:(tb__ "0|0|
ScSeS94Vc;SaZ1A1A3S10S95SaS33A1S43A3A2").
Definition X_Lin0f : axst := ltac2:(tb__ "0|0|
Sa5S0S9S4cS22A1S3S9A1A3S61A2").
Definition X_Lin1f : axst := ltac2:(tb__ "0|0|
Sa5S0S9S4cS22A1S3S9A1A3S62A2").
Definition pCM : sv := ltac2:(tb__ "0|0|
SeS94S32SaS33A1A3").
Definition X_back0f : axst := ltac2:(tb__ "0|0|
Sa5S0S9S4cS68A1S3S9A1A3S63A2").
Definition X_back1f : axst := ltac2:(tb__ "0|0|
Sa5S0S9S4cS68A1S3S9A1A3S64A2").
Definition s_Lin0 : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS87A1S1cS44A1A3").
Definition s_Lin1 : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS88A1S1cS44A1A3").
Definition s_back0 : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS89A1S1cS44A1A3").
Definition s_back1 : wsub := ltac2:(tb__ "0|0|
S9fS9aS1cS8aA1S1cS44A1A3").
