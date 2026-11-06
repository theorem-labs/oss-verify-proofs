(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el Lib_handle_f_s3.

(* [comment removed for export] *)
Module Lib_build_line_index_rom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "list"; "option"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "sobj"; "SPBranch"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPAlign"; "mkSS"; "SPNot"; "valuation"; "SMd"; "SPEq"; "reg_sv"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom"; "c8"; "vDp"; "spm"; "vC"; "vK"; "vDt"; "KLG"; "PHI"; "two47"; "B32"; "Pre_vr"; "tv0"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom"; "pD"; "pK"; "pJ"; "vLEN"; "pC"; "vOUT"; "X_bli"; "pI"; "kb16"; "vALC"; "VL"; "vBUF"; "ndB"; "nd_pre"; "pG"; "XL0n"; "bli_facts"; "canon"; "vecL_facts"; "hx"; "tvB"; "z0"; "LS"; "PROGL"; "P_ret_S"; "Pre_blr"; "shOf"; "C_LI"; "E_ms0"; "FEo"; "FUEL_blr"; "F_cells"; "HNEXT"; "K_ok_S0"; "P_retL_S"; "bdL"; "cutpcs_blr"; "loop_regs"; "ndPE"; "ndPL"; "ok_facts"; "pNX"; "ra_vr"; "slot_facts"; "C_LI_S"; "E_vr"; "E_vr_S"; "E_vrx"; "K_ms"; "K_ok"; "K_ok_S"; "K_st"; "K_st_S"; "O_D"; "O_F"; "O_al"; "O_txt"; "O_vec16"; "P_retL0"; "P_retL1"; "Pre_blr_S"; "Pre_ms"; "T_fail"; "T_grown"; "T_keep"; "V_XB"; "V_XL"; "Vs"; "XL0"; "XR0a"; "XR0b"; "X_st"; "bdS"; "g8"; "loop_facts"; "ndF"; "ndS"; "rvR"; "slot_obj"; "st_facts"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_EQ"; "BC_GE"; "ALU_SUB"; "M_MUL"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "SHB"; "A_globals"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.BLRAddr"; "FR"; "bli_LI"; "bli_ST"; "bli_ret"; "bli_entry"; "memset_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "NF"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.VRRAddr"; "vr_entry"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Corelib.Init.Logic"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.RR.RRAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase CellTile ArrMat.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RV. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom. End RV.
Module RVP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_pf. End RVP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Module BLRAddr.
  Definition bli_entry : Z := 0x8f144.
  Definition bli_LI : Z := 0x8f260.
  Definition bli_rr : Z := 0x8f2b8.
  Definition bli_mr : Z := 0x8f304.
  Definition bli_ST : Z := 0x8f34c.
  Definition bli_ret : Z := 0x8f3f4.
  Definition memset_pc : Z := 0x5cce8.
  Definition FR : Z := 144.
End BLRAddr.
Import BLRAddr.

Definition FUEL_blr : nat := 500%nat.
Definition vBUF : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vOUT : sv := SVar 14. Definition vALC : sv := SVar 33.

Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S11PaA1SeSa0Sa2A1A1SeZ0A1Vcells;S15A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S16S25Sa2A1S24SeZ0A1S3S10A1S15A5").
Definition O_vec16 (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S16S3aSeZ0M0A1SeZ20A1S0S10S23G0Vd;A2S0S10S23Z8Vc;A2S0S10S23Z10M1Vk;A2S0S10S23Z18SeG1A1A2S3S10A1A3A3A3A3S15A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S16S3eSeZ0M0A1M1SeZ30A1S0S10S23G0SeSb6A1A2S0S10S23Z8SeSb7A1A2S0S10S23Z10G1A2S0S10S23Z18SeSb8A1A2S0S10S23Z20G1A2S0S10S23Z28S2fA2S3S10A1A3A3A3A3A3A3S15A5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S16S40SeZ0A1S38S3S10A1S15A5").

Definition vecL_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0SdS18Vdv;Z4A2S0SdSfVd;S11P1eA1M0A2S0SdSfS12S88Vd;S3dVk;A1M1A3G0A2S0SdSfVd;SeS2bA1A2S0SdSfVc;Vk;A2S0SdSfVk;SeS2cA1M2A2S0SdSfG1G2A2S3SdA1A3A3A3A3A3A3A3").
Definition bli_facts : list sprop := ltac2:(tb__ "0|b|
S0SdS18PaM0Z4M1A2S0SdSfS11G0A1M2SeS2bA1M3A2S0SdSfS11P1eA1M4S12S88S25Sa2A1M5S24A3A2S0SdSfG4S25S9fS9fSa2Z40A2Z1060A2A1A2S0SdSfG4G5A2S0SdSfG4G2A2S0SdS14S8bSeN10a0A1S24A3S0SdS14S8bS24SeSa0S9eZ2M6Z26A2A1A1A3S0SdS18PeZ3M7A2S0SdSfG2S3aA2S0SdSfS12S88S3aSeZ20A1A3G3A2S0SdSfS3aG3A2S0SdS18P21G7A2S0SdSfSeZ1000A1M8S3eA2S0SdSfS12S88S3eSeZ30A1A3G4A2S0SdSfS3eG3A2S0SdS18PcG1A2S0SdSfG8S40A2S0SdSfS12S88S40S38A3SeZ7fffff800000A1M9A2S0SdSfS40G9A2S0SdSfS38SeS9eG6Z1aA2A1A2S0SdSfSeZ7fff7f800000A1MaG4A2S0SdSfG4G9A2S0SdSfGaG2A2S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_bli (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS3aSeZ20A1A4S0G0S1ScScS3eSeZ30A1A4S0G0S1ScScS40S38A4S0G0S1ScScVd;S3dVk;A1A4S3G0A1A3A3A3A3").

Definition canon (fcells : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5S13S0S13S6bVfcells;A1S0S13S6aS0S13S6eVd;Vc;Vk;A3S0S13S6cS0S13S6dS3S13A1A3A3A3A3A3S96A3").
Definition Pre_blr_S : sstate := ltac2:(tb__ "0|0|
S19Sa6SacSa8S17S6ScA1S46S3S10A1S28S26S27A4S5SdS0SdSfS26SeZ0A1A2S3SdA1A3S5SdS47S28S26S27PfA4S45A3A3Sa9S7A9").
Definition Pre_blr : axst := ltac2:(tb__ "0|0|
S94S71S3bS28S27A2A2").

Definition cutpcs_blr : list Z := ltac2:(tb__ "0|0|
S0S20Sa3S0S20Sb1S0S20Sa7S0S20Sa4S3S20A1A3A3A3A3").
Definition optAb (x : option axst) : axst := match x with Some s => s | None => Pre_blr end.
Definition optSb (x : option sstate) : sstate := match x with Some s => s | None => Pre_blr_S end.
Definition leavesB (S : axst) : list axst := ltac2:(tb__ "0|1|
S9S8S32A1M0A1S8S30A1Lx;S34S98S53S59VS;SbA5G0SaeS32S30S33R1A4Lls;S3S30A1X9x2").
Definition leafB_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SafS30Vk;S97S53S59VS;Vpc;A4S4eA4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282.
Definition pI : sv := SVar 283. Definition pJ : sv := SVar 284. Definition pG : sv := SVar 288. Definition pNX : sv := SVar 290.
Definition HNEXT : positive := 300.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition FEo (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0SdS1dS7eVg;A1M0S3aA2S0SdSfVg;SeSa1S9eZ2Z3dA2Z1A2A1A2S0SdSfG0S3aA2S0SdSfS3aG0A2S3SdA1A3A3A3A3").
Definition shOf (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S12S88Vg;SeS9fS95Vk;A2A1A3").
Definition F_cells (g : sv) : list cell := ltac2:(tb__ "0|0|
S0S10S23N88S4fVg;Z3A2A2S0S10S23N78S12S88S3aSeZ18A1A3A2S0S10S23N80S4fVg;Z0A2A2S0S10S23N70S3eA2S0S10S23N68S11P2fA1A2S0S10S23N60S11P2eA1A2S0S10S23N58S11P2dA1A2S0S10S23N50S11P2cA1A2S0S10S23N48S11P2bA1A2S0S10S23N40S11P2aA1A2S0S10S23N38S11P29A1A2S0S10S23N30S11P28A1A2S0S10S23N28S11P27A1A2S0S10S23N20S11P26A1A2S0S10S23N18S11P1dA1A2S0S10S23N10S11P1cA1A2S0S10S23N8S11PbA1A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_regs (g i j : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
SaaSaeS2ScS48Sb0U0M0U20A2A4S5S4S2ScA2M1S0G1S1S2ScG0SeZ0A1A4S0G1S1S2ScU2S25Sa2A1A4S0G1S1S2ScU3S11P17A1A4S0G1S1S2ScU4S11P18A1A4S0G1S1S2ScU8S3aA4S0G1S1S2ScU9SeZdA1A4S0G1S1S2ScU12Vj;A4S0G1S1S2ScU13S40A4S0G1S1S2ScU14Vi;A4S0G1S1S2ScU15S12S88S3aSeZ8A1A3A4S0G1S1S2ScU18SeS95A1A4S0G1S1S2ScU19SeZaA1A4S0G1S1S2ScU1aS38A4S0G1S1S2ScU1bS4fVg;Z1A2A4S3G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition PROGL (p : sv) : bitem := ltac2:(tb__ "0|2|
S93Z60Z0M0S0S4S20S91A2M1S1S20S91Z1S92S38A1A4S0G1S1S20S91N1S92Vp;A1A4S3G1A1A3A3G0A4").
Definition bdL (i c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S90S2aS12S88Vc;SeZ1A1A3Vk;A2S0S90S29Vk;A1S0S90S4cVi;A1S3S90A1A3A3A3").
Definition loop_facts (i j c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SdSfS5eVi;A2S0SdSfVi;Vj;A2S0SdSfVc;Vi;A2S0SdS14S89Vi;S38A3S0SdSfVj;SeS9eZ2Z1aA2A1A2S3SdA1A3A3A3A3A3").
Definition LS (pc : Z) (g i j : sv) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S19Vpc;S5aVg;Vi;Vj;Vregs;A4Sa8S17S6ScA1S46S54Vg;A1Vd;Vc;Vk;A4S5SdVfacts;S5SdS7fVi;Vj;Vc;A3S5SdS52Vg;A1S5SdS47Vd;Vc;Vk;Vdv;A4S45A3A3A3A3S55S7A9").
Definition C_LI_S : sstate := ltac2:(tb__ "0|0|
S4bSa3S43S3cS37S3S4S2ScA2A1S35S39S36P118S0SdS14S89S37S38A3S3SdA1A3Aa").
Definition C_LI : axst := ltac2:(tb__ "0|0|
S94S61S3bS35S36A2A2").

Definition XL0 : list axst := Eval vm_compute in leavesA_at FUEL_blr cutpcs_blr Pre_blr bli_LI.
Definition XR0 : list axst := Eval vm_compute in leavesA_at FUEL_blr cutpcs_blr Pre_blr bli_ret.

Definition s_L0 (X : axst) : wsub := ltac2:(tb__ "0|0|
S0S4S21ScA2S1S21ScP122SeZ0A1A4SadSa9S31VX;A1S31S50A1A3A3").

Definition ra_vr : Z := 0x8f2b8.
Definition E_vr_S : sstate := ltac2:(tb__ "0|1|
S4bSb1S43S3cS37S0S4S2ScA2M0S1S2ScU1SeS5fA1A4S0G0S1S2ScUaS3aA4S0G0S1S2ScUbS12S88S39SeZ1A1A3A4S0G0S1S2ScUcS3eA4S3G0A1A3A3A3A3S35S39S36P118S0SdSfS37S38A2S3SdA1A3Aa").
Definition E_vr : axst := ltac2:(tb__ "0|0|
S94S63S3bS35S36A2A2").

Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0S99S9dU1M0SeN40M1A1A2S0S99S9aG0G1A2S3S99A1A3A3").
Definition E_vrx : axst := Eval vm_compute in optAb (apply_axforms E_vr xf_vcall).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S21ScA2S1S21ScP13S12S88S24SeZ40A1A3A4SadPaS31S64A1S31S2dA1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vrx Pre_vr s_v).
Definition PD_vrr : list pdescK := RVP.PDk_vrr.
Definition Xk_v : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS3aSeZ20A1A4S0G0S1ScScS3eSeZ30A1A4S0G0S1ScScS40S38A4S3G0A1A3A3A3").
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_grown Xk_v.

Definition xf_vback : list axform := ltac2:(tb__ "0|1|
S0S99S9aU1M0Z40A2S0S99S9cS0S2U6S0S2G0S0S2U0S0S2U2S0S2U3S0S2U7S0S2U4S0S2U5S3S2A1A3A3A3A3A3A3A3A3A1S0S99S9bG0A1S3S99A1A3A3A3").
Definition T_keep : axst := Eval vm_compute in optAb (apply_axforms T_keep0 xf_vback).
Definition T_fail : axst := Eval vm_compute in optAb (apply_axforms T_fail0 xf_vback).
Definition T_grown : axst := Eval vm_compute in optAb (apply_axforms T_grown0 xf_vback).

Definition slot_obj (d c : sv) : sobj := ltac2:(tb__ "0|0|
S16S12S88Vd;S3dVc;A1A3SeZ0A1SeZ10A1S3S10A1S15A5").
Definition slot_facts (c k : sv) : list sprop := ltac2:(tb__ "0|2|
S0SdSfS12S88S3dVc;A1M0SeZ10A1A3S3dVk;A1M1A2S0SdSfG0G1A2S3SdA1A3A3").
Definition ok_facts (d c k : sv) : list sprop := ltac2:(tb__ "0|0|
S5SdS0SdSfS12S88Vc;SeZ1A1A3Vk;A2S0SdSfSeSb4A1Vd;A2S0SdS1aS14S8aVd;SeZ0A1A3A1S3SdA1A3A3A3S60Vc;Vk;A2A3").
Definition K_ok_S0 : sstate := ltac2:(tb__ "0|1|
S4bSb2S43S3cS37S0S4S2ScA2M0S1S2ScU1SeS5fA1A4S0G0S1S2ScUaSeZ1A1A4S3G0A1A3A3S35S39S36P118S5SdS5dS35S39S36A3S0SdSfS37S38A2S3SdA1A3A3Aa").
Definition K_ok_S : sstate := ltac2:(tb__ "0|0|
Sb9S56S5S13S1fS56A1S0S13S83S35S39A2S3S13A1A3A3A2").
Definition K_ok : axst := ltac2:(tb__ "0|0|
S94S67S3bS35S36A2A2").
Definition T_keepF : axst := ltac2:(tb__ "0|0|
Sb3S5dS35S39S36A3S75A2").
Definition vDg : sv := SVar 340. Definition vKg : sv := SVar 341.
Definition T_grownF : axst := ltac2:(tb__ "0|0|
Sb3S60S39S85A2S74A2").
Definition T_keepC : axst := Eval vm_compute in carve_stateA T_keepF (SAlu ALU_ADD pD (kb16 pC)) (SLit 16).
Definition T_grownC : axst := Eval vm_compute in carve_stateA T_grownF (SAlu ALU_ADD vDg (kb16 pC)) (SLit 16).
Definition s_keep : wsub := Eval vm_compute in infer_sub NF (ax_S T_keepC) (ax_S K_ok).
Definition s_grown : wsub := Eval vm_compute in infer_sub NF (ax_S T_grownC) (ax_S K_ok).

Definition E_ms0 : axst := Eval vm_compute in leafB_at K_ok memset_pc 0.
Definition V_XB : positive := 53%positive.
Definition V_XL : positive := 54%positive.
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_m : wsub := ltac2:(tb__ "0|1|
S0S4S21ScA2M0S1S21ScS76S35A4S0G0S1S21ScS77S3dS36A1A4SadPaS31S51A1S31S72A1A3A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_ms0 Pre_ms s_m).
Definition T_ms0 : axst := Eval vm_compute in T_afterA Pre_ms E_ms0 s_m R_m L_ms.

Definition K_ms : axst := T_ms0.
Definition X_st : axst := Eval vm_compute in leafB_at K_ms bli_ST 0.
Definition sel_st : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U7S0S2U1S3S2A1A3A3A3A3A3A3A3A3").
Definition X_stS : axst := Eval vm_compute in optAb (apply_axforms X_st [AXSelect sel_st]).
Definition X_stA : axst := Eval vm_compute in drop_lastA X_stS (removelast (ss_objs (ax_S X_stS))).
Definition st_facts : list sprop := ltac2:(tb__ "0|1|
S0SdSfS5eS12S88S37SeZ1A1A3M0A2S0SdSfS39G0A2S0SdSfS39S38A2S0SdSfS3cS37A2S0SdSfS3cS38A2S0SdS14S89S3cS38A3S0SdSfS37S38A2S0SdSfS37SeS9eZ2Z1aA2A1A2S0SdSfSeSb4A1S35A2S0SdS1aS14S8aS35SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3").
Definition K_st_S : sstate := ltac2:(tb__ "0|4|
S19Sa4S5aS43S3cS37S0S4S2ScA2M0S1S2ScU1SeZ8f304A1A4S0G0S1S2ScUaM1S48G1A1A4S0G0S1S2ScUbM2S48G2A1A4S0G0S1S2ScU16S35A4S0G0S1S2ScU17M3S48G3A1A4S3G0A1A3A3A3A3A3A4Sa8S17S6ScA1S46S54S43A1S35S39S36A4S5SdS84S5SdS52S43A1S5SdS47S35S39S36P118A4S45A3A3A3S55S7A9").
Definition K_st : axst := ltac2:(tb__ "0|0|
S94S69S3bS35S36A2A2").
Definition s_st : wsub := Eval vm_compute in (281%positive, SAlu ALU_ADD pC (SLit 1)) :: (290%positive, SAlu ALU_ADD pJ (SLit 1)) :: infer_sub NF (ax_S X_stA) (ax_S K_st).

Definition bdS (i c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S90S2aVc;Vk;A2S0S90S29Vk;A1S0S90S4cVi;A1S3S90A1A3A3A3").

Definition P_ret_S (rv : Z) : sstate := ltac2:(tb__ "0|5|
S19Sa5SaaSabSa9A1S0S4S2ScA2M0S1S2ScUaSeVrv;A1A4S3G0A1A3A2Sa8S17S6ScA1S46S3S10A1S11P8cM1A1M2S11P8dA1M3S11P8eA1M4A4S5SdS0SdSfG3S38A2S3SdA1A3S5SdS47G2G3G4G1A4S45A3A3P90S7A9").
Definition P_ret1 : axst := ltac2:(tb__ "0|0|
S94S4dZ1A1S3bS11P8cA1S11P8eA1A2A2").
Definition P_ret0 : axst := ltac2:(tb__ "0|0|
S94S4dZ0A1S3bS11P8cA1S11P8eA1A2A2").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS11P8cA1S3dS11P8eA1A1A4S3G0A1A3").
Definition tvB (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScVd;S3dVk;A1A4S3G0A1A3").

Definition P_retL_S (rv : Z) : sstate := ltac2:(tb__ "0|1|
S19Sa5SaaSabP190A1S0S4S2ScA2M0S1S2ScUaSeVrv;A1A4S3G0A1A3A2Sa8S17S6ScA1S46S3S10A1S35S39S36A4S5SdS0SdSfS39S38A2S3SdA1A3S5SdS47S35S39S36P118A4S45A3A3P1b0S7A9").
Definition P_retL1 : axst := ltac2:(tb__ "0|0|
S94S57Z1A1S3bS35S36A2A2").
Definition P_retL0 : axst := ltac2:(tb__ "0|0|
S94S57Z0A1S3bS35S36A2A2").
Definition s_retL (rv : Z) : wsub := Eval vm_compute in infer_sub NF (ax_S (mkA (P_retL_S rv) (X_bli pD pK))) (ax_S (mkA (P_ret_S rv) (X_bli (SVar 140) (SVar 142)))).
Definition XR0a : axst := Eval vm_compute in nth 0 XR0 Pre_blr.
Definition XR0b : axst := Eval vm_compute in nth 1 XR0 Pre_blr.
Definition rvR (X : axst) : Z := ltac2:(tb__ "0|4|
ScS20Lx;S1eS31VX;A1ZaA2S20R1Lz;S21Z1M0Li;S8eScScG0Lb;La;M1Lop;M2G2S8fG1Lop;M3G3SaS22ScG0La;Lw;Lsgn;S21ScS20G0Lk;Li;Ll;Xcx8").
Definition s_retE (X : axst) : wsub := ltac2:(tb__ "0|0|
SadSa9S31VX;A1S31S94S4dS82VX;A1A1S3bS11P8cA1S11P8eA1A2A2A1A3").

Definition nd_pre : ndesc := ltac2:(tb__ "0|0|
S87S2eS3S4S4ScS20A2ScA2A1S58SeZ0A1S26S27A3A3").
Definition ndB : ndesc := ltac2:(tb__ "0|0|
S87S49S35S36A2S3S4S4ScS20A2ScA2A1S58S3cS39S36A3A3").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S87S49S35S36A2S3S4S4ScS20A2ScA2A1S7dS3cS39S36A3A3").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S87S49S35S36A2S3S4S4ScS20A2ScA2A1S0S90S4cS3cA1S3S90A1A3A3").
Definition ndP : ndesc := ND tvP [] [].
Definition ndPL : ndesc := ltac2:(tb__ "0|0|
S87S49S35S36A2S3S4S4ScS20A2ScA2A1S3S90A1A3").
Definition ndPE : ndesc := ND tv0 [] [].
Definition z0 : sv := SLit 0.

Definition VL (j : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
S12S88S1cS8dSeZ8A1S12S8cS12S88SeS9fS9eZ2Z1aA2Z10A2A1S38A3Vj;A3A3SeVph;A1A3").

Definition Vs : list (list positive) := ltac2:(tb__ "0|2|
S0S8S21A1M0S3S21A1M1S0G0S0S21P119S0S21P118S0S21P122S0S21P11aG1A3A3A3A3S3G0A1A3A3").
Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|2|
SaeS8S21A1M0S4G0S1bOF_;M1A2G0S1G0G1R1S1bSb5L_;A4LV;S78A4").
Definition XL0n (k : nat) : axst := ltac2:(tb__ "0|0|
SafS30Vk;S79S4eA4").
Definition cutsE : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S30S86A2M0S2A2M1S4S20ScA2M2A2M3S1G1G2S1G0S2S1S30S86S4eS42A4U0A4S1S20ScZ64S4aA4A4S0G3S1G1G2S1G0S2S1S30S86S50S41A4U1M4A4S1S20ScZ32M5S3fS37Z6A2A4A4S0G3S1G1G2S1G0S2S1S30S86S66S41A4G4A4S1S20ScG5S3fS37Z4A2A4A4S0G3S1G1G2S1G0S2S1S30S86S73S80A4G4A4S1S20ScZ2dS4aA4A4S0G3S1G1G2S1G0S2S1S30S86S65S41A4G4A4S1S20ScG5S3fS37Z2A2A4A4S0G3S1G1G2S1G0S2S1S30S86S68S81A4G4A4S1S20ScG5S3fS37Z0A2A4A4S3G3A1A3A3A3A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|9|
S0S4S4S4S30S86A2M0S2A2M1S4S20ScA2M2A2M3S1G1G2S1G0S2S1S30S86S44U0M4A1S42A4G4A4S1S20ScZ5aS4aA4M5A4S0G3S1G1G2S1G0S2S1S30S86S44U1M6A1S42A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S86S44U2A1S42A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S86S44U3A1S42A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S86S44U4A1S42A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S86S7aS5bA4G4A4S1S20ScZ0S4aA4M7A4S0G3S1G1G2S1G0S2S1S30S86S7bS5bA4G4A4G7A4S0G3S1G1G2S1G0S2S1S30S86S62S41A4G6A4S1S20ScZ32M8S3fS37Z5A2A4A4S0G3S1G1G2S1G0S2S1S30S86S51S41A4G6A4S1S20ScG8S3fS37Z3A2A4A4S0G3S1G1G2S1G0S2S1S30S86S7cS41A4G6A4S1S20ScG8S3fS37Z1A2A4A4S0G3S1G1G2S1G0S2S1S30S86S70S5cA4G6A4G7A4S0G3S1G1G2S1G0S2S1S30S86S6fS5cA4G6A4G7A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3").

Goal entails_frA E_vrx Pre_vr s_v = Some R_v /\ call_checkPA E_vrx Pre_vr s_v R_v (map (fun d => fst (fst d)) PD_vrr) = true
     /\ entails_frA E_ms0 Pre_ms s_m = Some R_m /\ call_checkPA E_ms0 Pre_ms s_m R_m [L_ms] = true
     /\ entailsA T_keepC K_ok s_keep = true /\ entailsA T_grownC K_ok s_grown = true
     /\ entailsA X_stA K_st s_st = true
     /\ entailsA P_retL1 P_ret1 (s_retL 1) = true /\ entailsA P_retL0 P_ret0 (s_retL 0) = true
     /\ entailsA XR0a (mkA (P_ret_S (rvR XR0a)) (X_bli (SVar 140) (SVar 142))) (s_retE XR0a) = true
     /\ entailsA XR0b (mkA (P_ret_S (rvR XR0b)) (X_bli (SVar 140) (SVar 142))) (s_retE XR0b) = true
     /\ length XL0 = 5%nat /\ length XR0 = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_build_line_index_rom.

(* [comment removed for export] *)
Module Lib_handle_f_epi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "nat"; "prod"; "pair"; "None"; "false"; "fst"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "SPUle"; "cell"; "DUnknown"; "FcsrFrm0"; "mkSS"; "ss_objs"; "SLit"; "SVar"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "qCUR"; "qERR"; "q_vfacts"; "qKco"; "qKfv"; "qKmi"; "qKmm"; "qKrp"; "qKsg"; "qKtr"; "qKts"; "q_base"; "NZ32"; "qA"; "qDco"; "qDfv"; "qDmi"; "qDmm"; "qDrp"; "qDsg"; "qDtr"; "qDts"; "q_acct"; "datasQ"; "qCfv"; "qCmi"; "qCmm"; "qCsg"; "tvQ"; "XQ"; "bd_face"; "regsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "EC2"; "PC"; "Pre_f5"; "q_baseR"; "E_f5f"; "E_f5o"; "F_mainE"; "NREL"; "P_fail"; "P_ok"; "XQR"; "XR"; "hf_retA"; "ilast"; "nd_fail"; "nd_ok"; "objs_rel"; "regsE2"; "sel_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "h_fregs"; "PROG"; "av_d"; "av_k"; "hF"; "h_xregs"; "tE"; "tI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vERR"; "O_al"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pHP"; "O_F"; "O_Wf"; "V496"; "V528"; "V560"; "V592"; "V720"; "V752e"; "V784e"; "V816"; "builderF"; "optAp"; "O_flag"; "O_frame"; "X_hf"; "cVF"; "hdr3"; "hf_facts"; "sel_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "shadow_reopen_stateA"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "hf_EPI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "@Stdlib.Lists.List"; "filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hf_retA : Z := 0x9f1b8.

Definition F_mainE : list cell := Eval vm_compute in
  List.filter (fun c => negb (existsb (fun o => sv_eqb (c_off c) (SLit o)) [-224; -160; -264; -192; -272; -240; -256; -232; -248; -216; -208; -144; -136])) F_cells.
Definition regsE2 : list (nat * sv) := ltac2:(tb__ "0|1|
S1S4S3SdA2M0S3bS0G0S5S3SdU12S15P164A1A4S2G0A1A3A3").
Definition EC2 (err : sv) (facts : list sprop) (sh : list sobj) : axst := ltac2:(tb__ "0|1|
S7bS12S85S5fS53A1S5aS11S6SdA1S1SbS0SbS66S0SbS72S75A1S0SbS71S2SbA1M0A3A3A3S1SbS7aS1SbS0SbS65S48A1G0A3S1SbS6fVerr;S64S6bS2aS29S1fA3S6cS2eS23A2S6dS30S25A2S67S2cS35S21A3S68S2bS34S20A3S69S2dS36S22A3S6aS2fS37S24A3S6eS31S26A2AaS1SbS0SbS63S0SbS58S1cA1S0SbS57S0SbS59G0A3A3A3A3S1SbS33Vsh;A3A3A3A3A3A3Vfacts;S56S7A9S39A2").
Definition C_Eo2 : axst := ltac2:(tb__ "0|0|
S42S62S1ScS32S1ScS1eS27A3A3S2SbA1A3").
Definition C_Ef2 : axst := ltac2:(tb__ "0|0|
S42S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS27A3A3S2SbA1A3").

Definition XEo42 : axst := ltac2:(tb__ "0|0|
S42S62S1ScS32S1ScS1eS27A3A3S0SbS80S55Z4Z5S2SfA1S10A5S2SbA1A3A3").
Definition XEf42 : axst := ltac2:(tb__ "0|0|
S42S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS27A3A3S0SbS80S55Z4Z5S2SfA1S10A5S2SbA1A3A3").

Goal map (fun L => leaf_matches1A NPH L C_Eo2) (leaves_at2 [T_dg] hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L C_Ef2) (leaves_at2 [JF_co; K; JF_mi] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEf42) (leaves_at2 [JF_fv; JF_mm; JF_sg] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEo42) (leaves_at2 [JR_sg] hf_EPI) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal lvs C_Eo2 = [(f5_pc, RsCut)] /\ lvs C_Ef2 = [(f5_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_f5o0 : axst := Eval vm_compute in leaf_at C_Eo2 f5_pc 0.
Definition E_f5f0 : axst := Eval vm_compute in leaf_at C_Ef2 f5_pc 0.
Definition Pre_f5 : axst := Pre_set_shadow AE_A 245.
Definition L_f5 : axst := L_set_shadow 245.

Definition XR (A : axst) : list (sv * sv) := ltac2:(tb__ "0|1|
S88S4SdSdA2M0G0SaS16S8SdSdR1A3S5eA2A1Lr;S3eVA;A1A3").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S82S9SbS13S3cVA;A1A1A2U1A2").
Definition f5_site (E0 : axst) : axst := ltac2:(tb__ "0|0|
S81VE0;S4dVE0;A1S55Z0Z40A5S3dS70S19R1S0S17S1bS4fR1A1S7cA2S2S17A1A3A2A1TE1;").
Definition E_f5o : axst := Eval vm_compute in f5_site E_f5o0.
Definition E_f5f : axst := Eval vm_compute in f5_site E_f5f0.
Definition s_f5o : wsub := ltac2:(tb__ "0|0|
S0S4S40SdA2S5S40SdPfS7dA4S7ePaS3cS47A1S3cS44A1A3A3").
Definition s_f5f : wsub := ltac2:(tb__ "0|0|
S0S4S40SdA2S5S40SdPfS7dA4S7ePaS3cS46A1S3cS44A1A3A3").
Definition R_f5o : list sobj := Eval vm_compute in optR (entails_frA E_f5o Pre_f5 s_f5o).
Definition R_f5f : list sobj := Eval vm_compute in optR (entails_frA E_f5f Pre_f5 s_f5f).
Goal entails_frA E_f5o Pre_f5 s_f5o = Some R_f5o /\ call_checkPA E_f5o Pre_f5 s_f5o R_f5o [L_f5] = true
  /\ entails_frA E_f5f Pre_f5 s_f5f = Some R_f5f /\ call_checkPA E_f5f Pre_f5 s_f5f R_f5f [L_f5] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
S0S17S1aU1M0A1S0S17S18S77VA;G0A2A1S2S17A1A3A3").
Definition T_f5o0 : axst := Eval vm_compute in T_afterA Pre_f5 E_f5o s_f5o R_f5o L_f5.
Definition T_f5f0 : axst := Eval vm_compute in T_afterA Pre_f5 E_f5f s_f5f R_f5f L_f5.
Definition T_f5o : axst := Eval vm_compute in flag_carve_stateA (optAp (apply_axforms T_f5o0 (xf_shback T_f5o0))) 170.
Definition T_f5f : axst := Eval vm_compute in flag_carve_stateA (optAp (apply_axforms T_f5f0 (xf_shback T_f5f0))) 170.
Goal lvs T_f5o = [(hf_REL, RsCut)] /\ lvs T_f5f = [(hf_REL, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_rlo : axst := Eval vm_compute in leaf_at T_f5o hf_REL 0.
Definition X_rlf : axst := Eval vm_compute in leaf_at T_f5f hf_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S1S3S0S3U0S0S3U1S0S3U2S2S3A1M0A3A3A3S1S3S84U5U1fA2S0S3U3S0S3U4S0S3U24S0S3U25G0A3A3A3A3A3A3").
Definition NREL : nat := 34%nat.
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S70S19VX;S0S17S18S54A1S2S17A1A3A2A1S3dS3fR1S86S3cR1A1M0S83SbS49S13G0A1A3A2A2TX1;").
Definition C_rlo : axst := Eval vm_compute in rel_state X_rlo.
Definition C_rlf : axst := Eval vm_compute in rel_state X_rlf.
Goal map (fun X => release_objs_ok 160 170 hG 3 (skipn NREL (ss_objs (ax_S (optAp (apply_axforms X [AXSelect sel_rel])))))) [X_rlo; X_rlf] = [true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rlo; C_rlf] = [NREL; NREL]
  /\ lvs C_rlo = [(hf_retA, RsSymJump)] /\ lvs C_rlf = [(hf_retA, RsSymJump)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition X_reto : axst := Eval vm_compute in leaf_at C_rlo hf_retA 0.
Definition X_retf : axst := Eval vm_compute in leaf_at C_rlf hf_retA 0.

Definition XQR : list (sv * sv) := ltac2:(tb__ "0|0|
S73S5cS2cS2bS2dS2fS2aS2eS30S31S5dS21S20S22S24S1fS23S25S26A12").
Definition objs_rel (err : sv) : list sobj := ltac2:(tb__ "0|1|
S1SbS0SbS66S2SbA1M0A3S1SbS7aS1SbS0SbS65S2SfA1A1G0A3S1SbS6fVerr;S64S6bS2aS29S1fA3S6cS2eS23A2S6dS30S25A2S67S2cS35S21A3S68S2bS34S20A3S69S2dS36S22A3S6aS2fS37S24A3S6eS31S26A2AaS1SbS0SbS63S0SbS58S1cA1S0SbS57S0SbS59G0A3A3A3A3S33A3A3A3A3A3").
Definition q_baseR : list sprop := ltac2:(tb__ "0|0|
S1ScS0ScSeS64S14Z1A1A2S0ScSeS61S1cA2S0ScSeS1cS60A2S2ScA1A3A3A3S76A3").
Definition PC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S7bS12S4eS87P190A1S5aS11S6SdA1S52Verr;A1Vfacts;S56S7A9S4cA2").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S43S62S1ScS32S1ScS1eS45A3A3A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S43S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS45A3A3A2").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S79S38S2S4S4SdS41A2SdA2A1S3aS1cS29S21S20S22S24S1fS23S25S26AaA3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S79S38S2S4S4SdS41A2SdA2A1S0S7fS5bS74S1cA2S2S7fA1A3A3").
Definition Posts_hf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S3dS78A2M0S5S3dS78S4aS50A4S0G0S5S3dS78S4bS51A4S2G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_handle_f_epi.

