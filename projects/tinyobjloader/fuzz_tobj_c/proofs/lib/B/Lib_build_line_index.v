(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "prod"; "app"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "mkObj"; "sobj"; "DUnknown"; "SPAlign"; "SPBranch"; "FcsrFrm0"; "mkSS"; "SMd"; "tfact"; "DArr"; "SPEq"; "SPNot"; "TF2le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr"; "c8"; "vDp"; "spm"; "vC"; "vK"; "vDt"; "tv0"; "two47"; "B32"; "KLG"; "PHI"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "flds"; "nd0"; "tvP"; "vKn"; "vUD"; "vW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_GE"; "BC_LTU"; "M_MUL"; "ALU_XOR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_build_line_index"; "vLEN"; "pJ"; "vOUT"; "pD"; "pK"; "pC"; "kb16"; "vALC"; "vBUF"; "ndB"; "VL"; "X_bli"; "pI"; "LS"; "bli_facts"; "canon"; "pG"; "shOf"; "vecL_facts"; "z0"; "PROGL"; "P_ret_S"; "Pre_bli"; "T_ms0"; "bdL"; "ndP"; "ok_facts"; "ra_vr"; "slot_facts"; "tvB"; "C_LI"; "C_LI_S"; "C_z"; "E_ms0"; "E_vr"; "E_vr_S"; "E_vrx"; "FEo"; "FUEL_bli"; "F_cells"; "HNEXT"; "K_ms"; "K_ok"; "K_ok_S"; "O_D"; "O_F"; "O_al"; "O_dat"; "O_txt"; "O_vec16"; "P_ret0"; "P_ret1"; "Pre_bli_S"; "T_fail"; "T_grown"; "T_keep"; "VZ"; "X_zx"; "cutpcs_bli"; "darrL"; "g8"; "hx"; "loop_facts"; "loop_regs"; "mid_obj"; "ndF"; "nd_pre"; "vIz"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "SHB"; "A_globals"; "leavesA_at"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_build_line_index.BLIAddr"; "FR"; "bli_LI"; "bli_entry"; "bli_mr"; "bli_ret"; "memset_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "NF"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.VRDAddr"; "vr_entry"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve_darr.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve_darr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRDAddr RA.ReallocAddr.

Module BLIAddr.
  Definition bli_entry : Z := 0x8ffe0.
  Definition bli_LI : Z := 0x90124.
  Definition bli_rr : Z := 0x90180.
  Definition bli_z : Z := 0x901dc.
  Definition bli_mr : Z := 0x90210.
  Definition bli_ret : Z := 0x90320.
  Definition memset_pc : Z := 0x901dc.
  Definition FR : Z := 128.
End BLIAddr.
Import BLIAddr.

Definition FUEL_bli : nat := 500%nat.
Definition vBUF : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vOUT : sv := SVar 14. Definition vALC : sv := SVar 33.

Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition darrL (c : sv) : odefault := ltac2:(tb__ "0|0|
S18Z10Vc;S2cS0S17S1bS6U0U1S40A4S2S17A1A3A4").
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
SfSdPaA1SaS94S96A1A1SaZ0A1Vcells;S11A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
SfS1eS96A1S1dSaZ0A1S2ScA1S11A5").
Definition O_vec16 (d c k : sv) : sobj := ltac2:(tb__ "0|2|
SfS42SaZ0M0A1SaZ20A1S0ScS1cG0Vd;A2S0ScS1cZ8Vc;A2S0ScS1cZ10M1Vk;A2S0ScS1cZ18SaG1A1A2S2ScA1A3A3A3A3S11A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
SfS47SaZ0M0A1M1SaZ30A1S0ScS1cG0SaSa7A1A2S0ScS1cZ8SaSa8A1A2S0ScS1cZ10G1A2S0ScS1cZ18SaSa9A1A2S0ScS1cZ20G1A2S0ScS1cZ28S30A2S2ScA1A3A3A3A3A3A3S11A5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
SfS48SaZ0A1S40S2ScA1S11A5").
Definition O_dat (d c k : sv) : sobj := ltac2:(tb__ "0|0|
SfVd;SaZ0A1S46Vk;A1S2ScA1S7bVc;A1A5").

Definition vecL_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S9S12Vdv;Z4A2S0S9SbVd;SdP1eA1M0A2S0S9SbSeS34Vd;S46Vk;A1M1A3G0A2S0S9SbVd;SaS23A1A2S0S9SbVc;Vk;A2S0S9SbVk;SaS24A1M2A2S0S9SbG1G2A2S2S9A1A3A3A3A3A3A3A3").
Definition bli_facts : list sprop := ltac2:(tb__ "0|b|
S0S9S12PaM0Z4M1A2S0S9SbSdG0A1M2SaS23A1M3A2S0S9SbSdP1eA1M4SeS34S1eS96A1M5S1dA3A2S0S9SbG4S1eS93S93S96Z40A2Z1060A2A1A2S0S9SbG4G5A2S0S9SbG4G2A2S0S9S13S36SaN10a0A1S1dA3S0S9S13S36S1dSaS94S92Z2M6Z26A2A1A1A3S0S9S12PeZ3M7A2S0S9SbG2S42A2S0S9SbSeS34S42SaZ20A1A3G3A2S0S9SbS42G3A2S0S9S12P21G7A2S0S9SbSaZ1000A1M8S47A2S0S9SbSeS34S47SaZ30A1A3G4A2S0S9SbS47G3A2S0S9S12PcG1A2S0S9SbG8S48A2S0S9SbSeS34S48S40A3SaZ7fffff800000A1M9A2S0S9SbS48G9A2S0S9SbS40SaS92G6Z1aA2A1A2S0S9SbSaZ7fff7f800000A1MaG4A2S0S9SbG4G9A2S0S9SbGaG2A2S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_bli (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S8S8A2M0S1S8S8S42SaZ20A1A4S0G0S1S8S8S47SaZ30A1A4S0G0S1S8S8S48S40A4S0G0S1S8S8Vd;S46Vk;A1A4S2G0A1A3A3A3A3").
Definition canon (fcells : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5S10S0S10S6dVfcells;A1S0S10S6cS0S10S71Vd;Vc;Vk;A3S0S10S6eS0S10S70S0S10S6fVd;Vc;Vk;A3S2S10A1A3A3A3A3A3A3S90A3").
Definition Pre_bli_S : sstate := ltac2:(tb__ "0|0|
S15S98Sa0S9cS14S7S8A1S4fS2ScA1S21S1fS20A4S5S9S0S9SbS1fSaZ0A1A2S2S9A1A3S5S9S52S21S1fS20PfA4S4eA3A3S9dS6A9").
Definition Pre_bli : axst := ltac2:(tb__ "0|0|
S8eS74S4bS21S20A2A2").

Definition cutpcs_bli : list Z := ltac2:(tb__ "0|0|
S0S32S97S0S32Sa1S0S32S9bS0S32S99S2S32A1A3A3A3A3").
Definition optAb (x : option axst) : axst := match x with Some s => s | None => Pre_bli end.
Definition optSb (x : option sstate) : sstate := match x with Some s => s | None => Pre_bli_S end.
Definition leafB_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa5S3bVk;S91S66S7aVS;Vpc;A4S56A4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282.
Definition pI : sv := SVar 283. Definition pJ : sv := SVar 284. Definition pG : sv := SVar 288.
Definition HNEXT : positive := 300.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition FEo (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0S9S19S7cVg;A1M0S42A2S0S9SbVg;SaS95S92Z2Z3dA2Z1A2A1A2S0S9SbG0S42A2S0S9SbS42G0A2S2S9A1A3A3A3A3").
Definition shOf (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
SeS34Vg;SaS93S8fVk;A2A1A3").
Definition F_cells (g : sv) : list cell := ltac2:(tb__ "0|0|
S0ScS1cN80S51Vg;Z3A2A2S0ScS1cN78S51Vg;Z0A2A2S0ScS1cN70S47A2S0ScS1cN68SdP2fA1A2S0ScS1cN60SdP2eA1A2S0ScS1cN58SdP2dA1A2S0ScS1cN50SdP2cA1A2S0ScS1cN48SdP2bA1A2S0ScS1cN40SdP2aA1A2S0ScS1cN38SdP29A1A2S0ScS1cN30SdP28A1A2S0ScS1cN28SdP27A1A2S0ScS1cN20SdP26A1A2S0ScS1cN18SdP1dA1A2S0ScS1cN10SdP1cA1A2S0ScS1cN8SdPbA1A2S2ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_regs (g i j : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
S9eSa4S3S8S7dSa6U0M0U20A2A4S5S4S3S8A2M1S0G1S1S3S8G0SaZ0A1A4S0G1S1S3S8U2S1eS96A1A4S0G1S1S3S8U3SdP17A1A4S0G1S1S3S8U4SdP18A1A4S0G1S1S3S8U8S40A4S0G1S1S3S8U9S48A4S0G1S1S3S8U12S42A4S0G1S1S3S8U13Vi;A4S0G1S1S3S8U14S51Vg;Z1A2A4S0G1S1S3S8U15SeS34S42SaZ8A1A3A4S0G1S1S3S8U16SeS34S42SaZ18A1A3A4S0G1S1S3S8U17SaS8fA1A4S0G1S1S3S8U18SeS39S48SaZffffffffffffffffA1A3A4S0G1S1S3S8U19Vj;A4S0G1S1S3S8U1aSaZaA1A4S0G1S1S3S8U1bSaZdA1A4S2G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition PROGL (p : sv) : bitem := ltac2:(tb__ "0|2|
S8dZ60Z0M0S0S4S32S8bA2M1S1S32S8bZ1S8cS40A1A4S0G1S1S32S8bN1S8cVp;A1A4S2G1A1A3A3G0A4").
Definition bdL (i c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8aS26SeS34Vc;SaZ1A1A3Vk;A2S0S8aS25Vk;A1S0S8aS54Vi;A1S2S8aA1A3A3A3").
Definition loop_facts (i j c : sv) : list sprop := ltac2:(tb__ "0|0|
S0S9SbVi;Vj;A2S0S9SbVc;Vi;A2S0S9S13S37Vi;S40A3S0S9SbVj;SaS92Z2Z1aA2A1A2S2S9A1A3A3A3A3").
Definition LS (pc : Z) (g i j : sv) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S15Vpc;S7fVg;Vi;Vj;Vregs;A4S9cS14S7S8A1S4fS67Vg;A1Vd;Vc;Vk;A4S5S9Vfacts;S5S9S7eVi;Vj;Vc;A3S5S9S65Vg;A1S5S9S52Vd;Vc;Vk;Vdv;A4S4eA3A3A3A3S68S6A9").
Definition C_LI_S : sstate := ltac2:(tb__ "0|0|
S4dS97S50S4cS41S2S4S3S8A2A1S43S45S44P118S0S9S13S37S41S40A3S2S9A1A3Aa").
Definition C_LI : axst := ltac2:(tb__ "0|0|
S8eS5fS4bS43S44A2A2").

Definition ra_vr : Z := 0x90180.
Definition E_vr_S : sstate := ltac2:(tb__ "0|1|
S4dSa1S50S4cS41S0S4S3S8A2M0S1S3S8U1SaS5bA1A4S0G0S1S3S8UaS42A4S0G0S1S3S8UbSeS34S45SaZ1A1A3A4S0G0S1S3S8UcS47A4S2G0A1A3A3A3A3S43S45S44P118S0S9SbS41S40A2S2S9A1A3Aa").
Definition E_vr : axst := ltac2:(tb__ "0|0|
S8eS63S4bS43S44A2A2").

Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0S85S89U1M0SaN40M1A1A2S0S85S86G0G1A2S2S85A1A3A3").
Definition E_vrx : axst := Eval vm_compute in optAb (apply_axforms E_vr xf_vcall).
Definition s_v : wsub := ltac2:(tb__ "0|1|
S0S4S33S8A2M0S1S33S8P13SeS34S1dSaZ40A1A3A4S0G0S1S33S8P35S40A4SaaPaS3cS64A1S3cS2aA1A3A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vrx Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S3bS3eA2M0S1S3bS3eS29S2dA4S0G0S1S3bS3eS27S3fS22S2S4S4S8S32A2S8A2A1M1S2S8aA1A3A4S0G0S1S3bS3eS28S3fS2eG1S2bS31S2fA2A3A4S2G0A1A3A3A3").
Definition Xk_v : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S8S8A2M0S1S8S8S42SaZ20A1A4S0G0S1S8S8S47SaZ30A1A4S0G0S1S8S8S48S40A4S2G0A1A3A3A3").
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_grown Xk_v.

Definition xf_vback : list axform := ltac2:(tb__ "0|1|
S0S85S86U1M0Z40A2S0S85S88S0S3U7S0S3G0S0S3U0S0S3U2S0S3U3S0S3U8S0S3U4S0S3U5S0S3U6S2S3A1A3A3A3A3A3A3A3A3A3A1S0S85S87G0A1S2S85A1A3A3A3").
Definition T_keep : axst := Eval vm_compute in optAb (apply_axforms T_keep0 xf_vback).
Definition T_fail : axst := Eval vm_compute in optAb (apply_axforms T_fail0 xf_vback).
Definition T_grown : axst := Eval vm_compute in optAb (apply_axforms T_grown0 xf_vback).

Definition slot_facts (c k : sv) : list sprop := ltac2:(tb__ "0|2|
S0S9SbSeS34S46Vc;A1M0SaZ10A1A3S46Vk;A1M1A2S0S9SbG0G1A2S2S9A1A3A3").
Definition ok_facts (d c k : sv) : list sprop := ltac2:(tb__ "0|0|
S5S9S0S9SbSeS34Vc;SaZ1A1A3Vk;A2S0S9SbSaSacA1Vd;A2S0S9S1aS13S3aVd;SaZ0A1A3A1S2S9A1A3A3A3S5cVc;Vk;A2A3").
Definition K_ok_S : sstate := ltac2:(tb__ "0|1|
S4dSa2S50S4cS41S0S4S3S8A2M0S1S3S8U1SaS5bA1A4S0G0S1S3S8UaSaZ1A1A4S2G0A1A3A3S43S45S44P118S5S9S5aS43S45S44A3S0S9SbS41S40A2S2S9A1A3A3Aa").
Definition K_ok : axst := ltac2:(tb__ "0|0|
S8eS6bS4bS43S44A2A2").
Definition T_keepF : axst := ltac2:(tb__ "0|0|
Sa3S5aS43S45S44A3S77A2").
Definition vDg : sv := SVar 340. Definition vKg : sv := SVar 341.
Definition T_grownF : axst := ltac2:(tb__ "0|0|
Sa3S5cS45S84A2S76A2").
Definition s_keep : wsub := Eval vm_compute in infer_sub NF (ax_S T_keepF) (ax_S K_ok).
Definition s_grown : wsub := Eval vm_compute in infer_sub NF (ax_S T_grownF) (ax_S K_ok).

Definition E_ms0 : axst := Eval vm_compute in leafB_at K_ok memset_pc 0.
Definition slot_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
SfSeS34Vd;S46S45A1A3SaZ0A1SaZ10A1S2ScA1S11A5").
Definition E_ms1 : axst := Eval vm_compute in ax_setS E_ms0 (optSb (arr_split_at (ax_S E_ms0) 5 (kb16 pC))).
Definition E_ms2 : axst := Eval vm_compute in optAb (apply_axforms E_ms1 [AXSplit 6 (SAlu ALU_ADD (kb16 pC) (SLit 16))]).
Definition E_ms : axst := Eval vm_compute in ax_setS E_ms2 (reshape_obj_at (ax_S E_ms2) 6 (slot_obj pD)).

Definition cutpcs_z : list Z := cutpcs_bli.
Definition C_z : axst := Eval vm_compute in bl_cut E_ms 13 (SLit 16) [11; 15; 16]%nat [].
Definition vIz : sv := Eval vm_compute in reg_sv (ax_S C_z) 13.

Definition X_zx : axst := Eval vm_compute in nth 0 (leavesA_at FUEL_bli cutpcs_z C_z bli_mr) Pre_bli.
Definition T_ms0 : axst := X_zx.

Definition mid_obj (d : sv) : sobj := ltac2:(tb__ "0|1|
SfVd;S46S45A1M0SeS34G0SaZ10A1A3S2ScA1S11A5").
Definition T_ms1 : axst := ltac2:(tb__ "0|0|
S3dS57SabS3cS57A1U6S80S43A1A3A2").
Definition xf_mback : list axform := [AXMerge 6].
Definition T_ms2 : axst := Eval vm_compute in optAb (apply_axforms T_ms1 xf_mback).
Definition K_ms : axst := Eval vm_compute in ax_setS T_ms2 (optSb (arr_merge_at (ax_S T_ms2) 5)).

Definition P_ret_S (rv : Z) : sstate := ltac2:(tb__ "0|5|
S15S9aS9eS9fS9dA1S0S4S3S8A2M0S1S3S8UaSaVrv;A1A4S2G0A1A3A2S9cS14S7S8A1S4fS2ScA1SdP8cM1A1M2SdP8dA1M3SdP8eA1M4A4S5S9S0S9SbG3S40A2S2S9A1A3S5S9S52G2G3G4G1A4S4eA3A3P90S6A9").
Definition P_ret1 : axst := ltac2:(tb__ "0|0|
S8eS55Z1A1S4bSdP8cA1SdP8eA1A2A2").
Definition P_ret0 : axst := ltac2:(tb__ "0|0|
S8eS55Z0A1S4bSdP8cA1SdP8eA1A2A2").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S8S8A2M0S1S8S8SdP8cA1S46SdP8eA1A1A4S2G0A1A3").
Definition tvB (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S8S8A2M0S1S8S8Vd;S46Vk;A1A4S2G0A1A3").

Definition nd_pre : ndesc := ltac2:(tb__ "0|0|
S3fS22S2S4S4S8S32A2S8A2A1S58SaZ0A1S1fS20A3A3").
Definition ndB : ndesc := ltac2:(tb__ "0|0|
S3fS5dS43S44A2S2S4S4S8S32A2S8A2A1S58S4cS45S44A3A3").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S3fS5dS43S44A2S2S4S4S8S32A2S8A2A1S0S8aS54S4cA1S2S8aA1A3A3").
Definition ndP : ndesc := ND tvP [] [].
Definition z0 : sv := SLit 0.

Definition VL (j : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
SeS34S16S38SaZ40A1SeS35SeS34SaS93S92Z2Z1aA2Z10A2A1S40A3Vj;A3A3SaVph;A1A3").

Definition VZ (j i : sv) : sv := ltac2:(tb__ "0|1|
SeS34S16S38SaZ40A1SeS35SeS34SaS93S92Z2Z1aM0A2Z10A2A1S40A3Vj;A3A3SeS35SaG0A1Vi;A3A3").
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S4S4S3bS3eA2M0S4S32S8A2M1A2M2S1G0G1S1S3bS3eS56S82A4S1S32S8Z64S53A4A4S0G2S1G0G1S1S3bS3eS5eS49A4S1S32S8Z32M3S4aS41Z3cA2A4A4S0G2S1G0G1S1S3bS3eS6aS49A4S1S32S8G3S4aS41Z28A2A4A4S0G2S1G0G1S1S3bS3eS75S81A4S1S32S8Z2dS53A4A4S0G2S1G0G1S1S3bS3eS60S49A4S1S32S8G3S78S41S83A2A4A4S0G2S1G0G1S1S3bS3eS69S49A4S1S32S8G3S4aS41Z1A2A4A4S2G2A1A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|5|
S0S4S4S3bS3eA2M0S4S32S8A2M1A2M2S1G0G1S1S3bS3eS62S49A4S1S32S8Z32M3S4aS41G3A2A4A4S0G2S1G0G1S1S3bS3eS61S49A4S1S32S8G3S4aS41Z1eA2A4A4S0G2S1G0G1S1S3bS3eS79S49A4S1S32S8G3S4aS41Z5A2A4A4S0G2S1G0G1S1S3bS3eS73S59A4S1S32S8Z0S53A4M4A4S0G2S1G0G1S1S3bS3eS72S59A4G4A4S2G2A1A3A3A3A3A3").

Goal entails_frA E_vrx Pre_vr s_v = Some R_v /\ call_checkPA E_vrx Pre_vr s_v R_v (map fst PD_vr) = true
     /\ entailsA T_keepF K_ok s_keep = true /\ entailsA T_grownF K_ok s_grown = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
