(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double eb.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ Lib_vec_push.

(* [comment removed for export] *)
Module Lib_intern_rest.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "length"; "list"; "option"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "SLit"; "SVar"; "SAlu"; "sobj"; "cell"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkObj"; "SPAlign"; "SPBranch"; "SPUlt"; "ss_objs"; "ss_regs"; "SPEq"; "ob_base"; "sv_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_GE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest"; "z0"; "c8"; "vC1"; "vN"; "vARi"; "vC2"; "vH"; "vK"; "vP"; "X_ir"; "tv_ir"; "vCAPl"; "vHDi"; "nd0"; "two40"; "ir_facts"; "vBld"; "vLn"; "vR"; "am_np"; "vDp"; "X_nohead"; "ir_state"; "ndO"; "pN"; "p_fit"; "C_loop"; "C_nul"; "C_slow"; "O_Fi"; "O_Wi"; "O_arI"; "P_b8"; "cle"; "ndL"; "ndMok"; "ndS"; "objs_ir0"; "vJ"; "vNn"; "vS"; "vU"; "E_m"; "FUEL_ir"; "F_cells"; "P_ok"; "Pre_ir"; "bd_m"; "cutpcs_ir"; "junk_regs"; "ndKc"; "objs_loop"; "p_new"; "slot_factsI"; "spm"; "vCAP"; "vNXl"; "vUc"; "vUg"; "CHi"; "C_K"; "C_m"; "C_open"; "C_tl"; "C_tm"; "C_tr"; "K0_facts"; "K_facts"; "O_hdrI"; "O_slotI"; "P_fail"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fitc"; "X_fitc3"; "X_fitn"; "X_fitn3"; "X_loop"; "X_nofit"; "X_nofit2"; "X_nul"; "X_open"; "X_ret"; "X_ret3"; "X_sretc"; "X_sretc3"; "X_sretn"; "X_sretn3"; "am_ir"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "cend"; "cin"; "find_idxb"; "ghK"; "loop_facts"; "loop_regs"; "ndF"; "ndK"; "ndM"; "nul_regs"; "objs_ir"; "ok_facts"; "optAi"; "slow_facts"; "slow_regs"; "tv_m"; "ug_facts"; "vNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "pB"; "vE"; "vL"; "vB"; "vI"; "O_txt"; "two26"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "POT"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest.IRAddr"; "ir_K"; "ir_cpy"; "ir_m"; "ir_nul"; "ir_ret"; "ir_slow"; "ir_tl"; "ir_tm"; "ir_tr"; "ir_entry"; "ir_open"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "NPOSTM"; "Pre_malloc";
"UStopLe"; "ulink"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "filter"; "removelast"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module IRAddr.
  Definition ir_entry : Z := 0x9cff8.
  Definition ir_tl : Z := 0x9d04c.
  Definition ir_tm : Z := 0x9d080.
  Definition ir_tr : Z := 0x9d0a0.
  Definition ir_m : Z := 0x9d0d8.
  Definition ir_open : Z := 0x9d11c.
  Definition ir_slow : Z := 0x9d154.
  Definition ir_fits : Z := 0x9d1e8.
  Definition ir_K : Z := 0x9d180.
  Definition ir_cpy : Z := 0x9d210.
  Definition ir_nul : Z := 0x9d300.
  Definition ir_ret : Z := 0x9d340.
  Definition ir_malloc : Z := 0x9d298.
End IRAddr.
Import IRAddr ScanDoubleAddr RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two40 := RA.two40. Definition vDp : sv := SVar 19.

Definition FUEL_ir : nat := 400%nat.
Definition vBld : sv := SVar 12. Definition vARi : sv := SVar 53. Definition vHDi : sv := SVar 54.
Definition O_Fi (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S11PaA1S10N50A1S10Z0A1Vcells;S17A5").
Definition O_Wi : sobj := ltac2:(tb__ "0|0|
S18S64Z50A1S42S10Z0A1S3S14A1S17A5").
Definition P_b8 : sobj := ltac2:(tb__ "0|1|
S18S3eS10Z8M0A1S10Z10A1S0S14S2fG0S32A2S3S14A1A3S17A5").
Definition O_arI (hd : sv) : sobj := ltac2:(tb__ "0|0|
S18S32S10Z0A1S10Z40A1Sd3Vhd;A1S17A5").
Definition ir_facts : list sprop := ltac2:(tb__ "0|8|
S0SeS19PaM0Z4M1A2S0SeSfS11G0A1M2S10Sb7A1M3A2S0SeSfS11P1eA1M4S12S27S64Z50A1M5S42A3A2S0SeSfG4G5A2S0SeSfG4G2A2S0SeS1aS29S10N1000A1S42A3S0SeS1aS29S42S10SdfS3cA1A1A3S0SeS19PcZ3A2S0SeSfS10Sd5A1S3eA2S0SeSfS12S27S3eS10Z518A1A3G4A2S0SeSfS3eG3A2S0SeS19P35G1A2S0SeSfS10Z1000A1S32A2S0SeSfS12S27S32S10Z40A1A3G4A2S0SeSfS32G3A2S0SeSfS3aG4A2S0SeSfSb4Sb1A2S0SeSfSb1Sb2A2S0SeSfSb2S10Sb6A1A2S0SeSfSb3G3A2S0SeSfS10Z1A1Sb3A2S0SeSfS12S27Sb3Sb2A3S10Z7fffff800000A1M6A2S0SeSfS10Z7fff7f800000A1M7G4A2S0SeSfG4G6A2S0SeSfG7G2A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_ir : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS3eS10Z518A1A4S0G0S1SdSdS32S10Z40A1A4S0G0S1SdSdSb3Sb2A4S3G0A1A3A3A3").
Definition objs_ir0 (hd : sv) : list sobj := ltac2:(tb__ "0|1|
S5S13S0S13S4bS3S14A1M0A1S0S13S4cS0S13S4eS0S13S4dVhd;A1S0S13Sb5G0A1S3S13A1A3A3A3A3A3Sb9A3").
Definition Pre_ir : axst := ltac2:(tb__ "0|1|
Sb8S16SceSacSafS0S4S2SdA2M0S1S2SdUbSb0Sb4A1A4S0G0S1S2SdUcSb0Sb1A1A4S3G0A1A3A3A2SabS15S6SdA1S53S3aA1S3dSaaS7A9S37A2").
Definition tv_ir : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS32S10Z40A1A4S3G0A1A3").
Definition am_ir : amode := AHead vHDi true.

Definition CHi : list bitem := ltac2:(tb__ "0|6|
S0Sa4Sa6Z1M0Z0M1S0S4S21Sa5A2M2S1S21Sa5Z2Sa7Sb1A1M3A4S0G2S1S21Sa5N2Sa7Sb4A1M4A4S3G2A1M5A3A3Z62A4S0Sa4Sa6G1G0S0G2S1S21Sa5Z4G3A4S0G2S1S21Sa5N4G4A4G5A3A3Z44A4S3Sa4A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S69S8aA4").

Definition cutpcs_ir : list Z := ltac2:(tb__ "0|0|
S0S21ScbS0S21SccS0S21ScdS0S21Sc7S0S21ScfS0S21ScaS0S21Sc5S0S21Sc6S0S21Sc8S0S21Sd4S3S21A1A3A3A3A3A3A3A3A3A3A3").
Definition optAi (x : option axst) : axst := match x with Some s => s | None => Pre_ir end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sd1S23Vk;SbbS59S5eVS;Vpc;A4S5cA4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
S8S25SaS9S25A1M0A1G0Lx;S26SbcS59S5eVS;ScA5G0R1Ll;S3S25A1Xax2A2").

Definition F_cells_ : unit := tt.
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S14S2fN8S11PbA1A2S0S14S2fN10S11P1cA1A2S0S14S2fN18S11P1dA1A2S0S14S2fN20S11P26A1A2S0S14S2fN28S11P27A1A2S0S14S2fN30S11P28A1A2S0S14S2fN38S11P29A1A2S0S14S2fN40S11P2aA1A2S0S14S2fN48S11P2bA1A2S3S14A1A3A3A3A3A3A3A3A3A3").
Definition objs_ir (hd : sv) : list sobj := ltac2:(tb__ "0|0|
S5S13S0S13S4bS5aA1S0S13S4cS0S13S4eS0S13S4dVhd;A1S0S13Sb5S3S14A1A1S3S13A1A3A3A3A3A3Sb9A3").

Definition cin (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfSb4Vc;A2S0SeS1bVc;Sb1A2S0SeS1bVc;Sb2A2S0SeSfVc;S10S3cA1A2S0SeS1aS2aSb0Vc;A1Sb0Sb1A1A3S3SeA1A3A3A3A3A3").
Definition vC1 : sv := SVar 132.
Definition vC2 : sv := SVar 133.
Definition ir_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
Sb8S16Vpc;SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S27S11PaA1S10N50A1A3A4S0G0S1S2SdU9SbaA4S0G0S1S2SdUaS3eA4S0G0S1S2SdUcSb0Sb1A1A4S3G0A1A3A3A3A3Vregs;A3A2SabS15S6SdA1S9cS3aA1S5SeVfacts;S3dA3Vnx;S7A9S37A2").

Definition C_tl : axst := ltac2:(tb__ "0|2|
S44ScbS0S4S2SdA2M0S1S2SdUbSb0S30A1M1A4S0G0S1S2SdUdG1A4S0G0S1S2SdUeS10Z20A1A4S0G0S1S2SdUfS10Z9A1A4S3G0A1A3A3A3A3S93S30A1P8cA4").

Definition cle (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfSb4Vc;A2S0SeSfVc;Sb1A2S0SeSfVc;S10S3cA1A2S3SeA1A3A3A3").
Definition cend (c1 c2 : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfVc1;Vc2;A2S0SeSfVc2;Sb1A2S0SeSfVc2;S10S3cA1A2S3SeA1A3A3A3").

Definition C_tm : axst := ltac2:(tb__ "0|1|
S44SccS0S4S2SdA2M0S1S2SdUbSb0S30A1A4S3G0A1A3S4fS30A1P8cA4").

Definition C_tr : axst := ltac2:(tb__ "0|3|
S44ScdS0S4S2SdA2M0S1S2SdUbSb0S30A1M1A4S0G0S1S2SdUcSb0S12S27S33S10Z1A1A3A1M2A4S0G0S1S2SdUdSb0S33A1A4S0G0S1S2SdUeS10Z20A1A4S0G0S1S2SdUfS10Z9A1A4S3G0A1A3A3A3A3A3S5SeS4fS30A1S0SeSfS30S33A2S0SeS1bS33Sb1A2S0SeS1bS33Sb2A2S0SeS1aS2aG1G2A3S3SeA1A3A3A3A3A3P8cA4").

Definition C_m : axst := ltac2:(tb__ "0|1|
S44Sc7S0S4S2SdA2M0S1S2SdUbSb0S30A1A4S0G0S1S2SdUcSb0S33A1A4S3G0A1A3A3S5SeS4fS30A1S92S30S33A2A3P8cA4").

Definition vN : sv := ltac2:(tb__ "0|0|
S12S27S12S28S33S30A3S10Z1A1A3").
Definition vLEN : sv := SAlu ALU_SUB vC2 vC1.

Definition X_open : axst := Eval vm_compute in leaf_at C_m ir_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHDi.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S2dS3aSa3S65S3S4SdSdA2A1A4").

Definition CHn : list bitem := ltac2:(tb__ "0|5|
S0Sa4Sa6Z1M0Z0M1S0S4S21Sa5A2M2S1S21Sa5Z2Sa7S31A1M3A4S3G2A1M4A3Z60A4S0Sa4Sa6G1G0S0G2S1S21Sa5Z4G3A4G4A3Z40A4S3Sa4A1A3A3").
Definition bd_open : list bitem := CHn ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leaf_at C_m ir_slow 0.

Definition X_nofit : axst := Eval vm_compute in leaf_at C_open ir_slow 0.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
SacS1dS24S43A1A1S0S4S2SdA2M0S1S2SdUdS11P66A1A4S0G0S1S2SdUeS11P67A1A4S0G0S1S2SdU11S11P68A1A4S0G0S1S2SdU5S11P69A1A4S0G0S1S2SdU6S11P6aA1A4S3G0A1A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHDi (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SeSfS10Z10001A1S12S27S68S31A3A2S0SeSfS68S10S3cA1A2S3SeA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
Sb8S16ScaSa0SabS15S6SdA1S1cS24S43A1A1S5SeSa2S9fA3P96S7A9S37A2").
Definition bd_slow : list bitem := POT vUg ++ CHn.
Definition am_np : amode := AHead vHDi false.

Definition X_K0 : axst := Eval vm_compute in leaf_at C_slow ir_K 0.
Definition vK : sv := SVar 146.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS10Z10000A1M0S35A2S0SeSfS12S27S31S10Z1A1M1A3S35A2S0SeSfS35S12S27S31G0A3A2S0SeSfS35S10Se0Z2Z1bA2A1A2S0SeSfG1SbeS35A1A2S3SeA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 147) (SLit 0).
Definition K0_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with SPBranch BC_LTU _ (SLit 65536) => false | SPNot (SPBranch BC_LTU _ (SLit 65536)) => false | _ => true end)
                                 (ss_facts (ax_S X_K0)).
Definition C_K : axst := ltac2:(tb__ "0|2|
Sb8S16Sc5SacS1dS24S78A1M0A1S0S4S2SdA2M1S1S2SdU15S35A4S3G1A1A3A2SabS15S6SdA1S1cG0A1S0SeS95S5SeS71S70A3A3P96S7A9S37A2").
Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leaf_at C_slow ir_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S4S22SdA2M0S1S22SdP93S10Z0A1A4S0G0S1S22SdP92S10Z10000A1A4S3G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S4S22SdA2M0S1S22SdP93S10Z0A1A4S0G0S1S22SdP92S12S27S31S10Z1A1A3A4S3G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5Sa4S0Sa4Sa6Z1M0Z0M1S0S4S21Sa5A2M2S1S21Sa5G0Sa7SbeS35A1A1A4S3G2A1A3G1A4S0Sa4Sa8G1G0SdeZ2Sa9A2A3S3Sa4A1A3A3SbfS31A1A3").

Definition E_m : axst := Eval vm_compute in leaf_at C_K malloc_pc 0.
Definition Pre_m : axst := ltac2:(tb__ "0|0|
Sd8Sd6S3SdaA1Sd9A3").
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S22SdA2S1S22SdPfS42A4SbdPaS24S58A1S24S75A1A3A3").
Definition optRi (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_m : list sobj := Eval vm_compute in optRi (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1SdSdS11S46A1SbeS35A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.
Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5Sa4S0Sa4Sa8Z0Z1Sa9A3S3Sa4A1A3SbfS31A1A3").
Definition tv_m : list (sv * sv) := blkN :: tv_ir.
Definition bd_m2 : list bitem := POT vN.

Definition vLn : sv := SVar 145. Definition vS : sv := SVar 148. Definition vJ : sv := SVar 149. Definition vR : sv := SVar 139.
Definition vNn : sv := SAlu ALU_ADD vLn (SLit 1).
Definition vH : sv := SVar 134.  Definition vNXl : sv := SVar 135.  Definition vCAPl : sv := SVar 136.
Definition vUc : sv := SVar 137. Definition vP : sv := SVar 138.
Definition O_hdrI (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S18Vhd;S10Z0M0A1S10Z18A1S0S14S2fG0Vnx;A2S0S14S2fZ8Vcap;A2S0S14S2fZ10Vu;A2S3S14A1A3A3A3S17A5").
Definition O_slotI (p n : sv) : sobj := ltac2:(tb__ "0|0|
S18Vp;S10Z0A1Vn;S3S14A1S17A5").
Definition am_loop : amode := ltac2:(tb__ "0|1|
S2dS34S66S39S0S4SdSdA2M0S1SdSdS36S55A4S3G0A1A3A4").
Definition junk_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SdA2M0S1S2SdU1S11P6fA1A4S0G0S1S2SdU5S11P69A1A4S0G0S1S2SdU6S11P6aA1A4S0G0S1S2SdU7S11P6bA1A4S0G0S1S2SdU10S11P74A1A4S0G0S1S2SdU11S11P75A1A4S0G0S1S2SdU13S11P77A1A4S0G0S1S2SdU14S11P78A1A4S0G0S1S2SdU15S11P79A1A4S0G0S1S2SdU16S11P7aA1A4S0G0S1S2SdU17S11P7bA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_regs : list (nat * sv) := ltac2:(tb__ "0|3|
S5S4S2SdA2M0S0G0S1S2SdU8S12S27S32S10Z30A1A3A4S0G0S1S2SdUaS36A4S0G0S1S2SdUbS12S27Sb3S56A3M1A4S0G0S1S2SdUcG1A4S0G0S1S2SdUdS12S27S36S54A3M2A4S0G0S1S2SdUeG2A4S0G0S1S2SdUfS40A4S0G0S1S2SdU12S3fA4S3G0A1A3A3A3A3A3A3A3A3S5fA3").

Definition slot_factsI : list sprop := ltac2:(tb__ "0|4|
S0SeSfS67S39A2S0SeSfS10Z10000A1S39A2S0SeSfS39S10Se1S3cZ21A2A1A2S0SeSfS12S27S34SbeS39A1A3M0S11P1eA1M1A2S0SeSfS34G1A2S0SeSfS10Z1000A1M2S34A2S0SeS19P86Z4A2S0SeSfS12S27S34S10Z20A1A3S36A2S0SeSfS12S27S36S55A3M3G0A2S0SeSfG2S36A2S0SeSfG3G1A2S0SeSfS36G1A2S0SeSfS3fS10S3cA1A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_facts : list sprop := ltac2:(tb__ "0|0|
S5SeS0SeSfS10Z1A1S40A2S0SeS1eS12S27S54S40A3S3fA2S0SeSfS54S3fA2S0SeSfS40S3fA2S0SeSfS12S27S56S40A3Sb2A2S0SeSfS56Sb2A2S3SeA1A3A3A3A3A3A3S63A3").
Definition objs_loop : list sobj := ltac2:(tb__ "0|1|
S5S13S0S13S4bS5aA1S0S13S4cS0S13S4eS0S13S4dS34A1S0S13Sb5S3S14A1A1S3S13A1M0A3A3A3A3A3S5S13Sb9S0S13S72S34S66S39S67A4S0S13S73S36S55A2G0A3A3A3A3").
Definition X_loop : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4SdSdA2S1SdSdS34SbeS39A1A4S37A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
Sb8S16Sc6SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S27S11PaA1S10N50A1A3A4S0G0S1S2SdU9SbaA4S3G0A1A3A3S97A3A2SabS15S6SdA1S61S5SeS96S3dA3P96S7A9S7fA2").
Definition bd_loop : list bitem := POT vUc.

Definition nul_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2SdA2M0S0G0S1S2SdU8S12S27S32S10Z30A1A3A4S0G0S1S2SdUaS36A4S0G0S1S2SdUbS11P7cA1A4S0G0S1S2SdUcS11P70A1A4S0G0S1S2SdUdS11P71A1A4S0G0S1S2SdUeS11P72A1A4S0G0S1S2SdUfS11P73A1A4S0G0S1S2SdU12S3fA4S3G0A1A3A3A3A3A3A3A3A3S5fA3").
Definition X_nul : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4SdSdA2S1SdSdS34SbeS39A1A4S37A3").
Definition C_nul : axst := ltac2:(tb__ "0|1|
Sb8S16Sc8SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S27S11PaA1S10N50A1A3A4S0G0S1S2SdU9SbaA4S3G0A1A3A3S9bA3A2SabS15S6SdA1S61S5SeS63S3dA3P96S7A9S82A2").

Definition X_fitc : axst := Eval vm_compute in leaf_at C_open ir_cpy 0.
Definition X_fitn : axst := Eval vm_compute in leaf_at C_open ir_nul 0.
Definition p_fit : sv := ltac2:(tb__ "0|0|
S12S27S12S27S3aS57A3S10Z20A1A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS10Z1000A1S47A2S0SeSfS47S11P1eA1M0A2S0SeSfS12S27S47S31A3M1S12S27S3aSbeS65A1A3A2S0SeSfG1G0A2S0SeSfS12S27S3aS10Z20A1A3S47A2S3SeA1A3A3A3A3A3").
Definition X_fitc3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fitc p_fit vN) (fit_facts ++ ss_facts (ax_S X_fitc)).
Definition X_fitn3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fitn p_fit vN) (fit_facts ++ ss_facts (ax_S X_fitn)).

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition sret_pipe (X : axst) : axst * axst := ltac2:(tb__ "0|2|
S94S13S13S20S1fR1A1S11S46A1A2Lo;S1cS24VX;A1A1M0U0M1A4S2S5S2SdcS2S2SbSdbR1R2A2A1Lj;Sd2G1S8S13G0A2A2A3S0S2R1S3S2A1A3A3S9S2A1S9eSc4VX;S0Sc1Sc2R1A1S0Sc1Sc3Sd0S8S2R1A2U1A2S10Z18A1A2S3Sc1A1A3A3A2A1S23Sc0R1SddS13S1cS24R1A1A1A2A2S23S1S23S23R2R1A4TX2;TX1;Tsel;TiN;").
Definition p_new : sv := ltac2:(tb__ "0|0|
S12S27S11S46A1S10Z20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS12S27S62S31A3M0S12S27S11S46A1SbeS35A1A3A2S0SeSfG0S11P1eA1M1A2S0SeSfS62G1A2S3SeA1A3A3A3").
Definition X_sretc : axst := Eval vm_compute in leaf_at T_mok ir_cpy 0.
Definition X_sretn : axst := Eval vm_compute in leaf_at T_mok ir_nul 0.
Definition X_sretc1 : axst := Eval vm_compute in fst (sret_pipe X_sretc).
Definition X_sretc2 : axst := Eval vm_compute in snd (sret_pipe X_sretc).
Definition X_sretc3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sretc2 p_new vN) (new_facts ++ ss_facts (ax_S X_sretc2)).
Definition X_sretn1 : axst := Eval vm_compute in fst (sret_pipe X_sretn).
Definition X_sretn2 : axst := Eval vm_compute in snd (sret_pipe X_sretn).
Definition X_sretn3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sretn2 p_new vN) (new_facts ++ ss_facts (ax_S X_sretn2)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
SfS10Z10001A1S12S27S57S31A3A2").
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).

Definition X_ret : axst := Eval vm_compute in leaf_at C_nul ir_ret 0.
Definition X_ret2 : axst := Eval vm_compute in drop_lastA X_ret (removelast (ss_objs (ax_S X_ret))).
Definition X_ret3 : axst := Eval vm_compute in drop_lastA X_ret2 (removelast (ss_objs (ax_S X_ret2))).

Definition P_fail : axst := ltac2:(tb__ "0|1|
Sb8S16Sc9SacSaeSaaA1S0S4S2SdA2M0S1S2SdUaS10Z0A1A4S3G0A1A3A2SabS15S6SdA1S53S3aA1S3dSd7S7A9S37A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|4|
S0SeSfS10Z1000A1M0S11P8cA1M1A2S0SeSfG1S11P1eA1M2A2S0SeSfG0S11P8dA1M3A2S0SeSfG3G2A2S3SeA1A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
Sb8S16Sc9SacSaeSaaA1S0S4S2SdA2M0S1S2SdUaS11P8cA1A4S3G0A1A3A2SabS15S6SdA1S53S11P8dA1A1S5SeS9dS3dA3P8eS7A9S37A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fitc : wsub := ltac2:(tb__ "0|0|
SbdSaaS24S7cA1S24S48A1A3").
Definition s_fitn : wsub := ltac2:(tb__ "0|0|
SbdSaaS24S7eA1S24S49A1A3").
Definition s_sretc : wsub := ltac2:(tb__ "0|0|
SbdSaaS24S87A1S24S48A1A3").
Definition s_sretn : wsub := ltac2:(tb__ "0|0|
SbdSaaS24S89A1S24S49A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S4S22SdA2S1S22SdP6cS57A4SbdSaaS24S81A1S24S4aA1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S4S22SdA2S1S22SdP6cS10Z10000A1A4SbdSaaS24S43A1S24S4aA1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
SbdSaaS24S85A1S24S5bA1A3").

Definition ndO : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S90S8dA4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S91S41A4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S8eS41A4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S5dS41A4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S2cSa1S3S4S4SdS21A2SdA2A1S5dS41A4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S8fS8bA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S3Sa4A1S41A4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S2cS38S3S4S4SdS21A2SdA2A1S3Sa4A1S8cA4").
Definition z0 : sv := SLit 0.
Definition cutsI : list edescA := ltac2:(tb__ "0|4|
S0S4S4S23S2bA2M0S4S21SdA2M1A2M2S1G0G1S1S23S2bS5cS3bA4S1S21SdZ64S2eA4A4S0G2S1G0G1S1S23S2bS6dS3bA4S1S21SdZ61S12S28Sb1S30A3A4A4S0G2S1G0G1S1S23S2bS6eS3bA4S1S21SdZ5fS2eA4A4S0G2S1G0G1S1S23S2bS6fS3bA4S1S21SdZ5dS33A4A4S0G2S1G0G1S1S23S2bS6bS3bA4S1S21SdZ5cS2eA4A4S0G2S1G0G1S1S23S2bS6cS45A4S1S21SdZ5aS2eA4A4S0G2S1G0G1S1S23S2bS4aS52A4S1S21SdZ50S2eA4A4S0G2S1G0G1S1S23S2bS6aS60A4S1S21SdZ4bS2eA4A4S0G2S1G0G1S1S23S2bS76S9aA4S1S21SdZ41S2eA4M3A4S0G2S1G0G1S1S23S2bS77S51A4G3A4S0G2S1G0G1S1S23S2bS48S50A4S1S21SdZ32S40A4A4S0G2S1G0G1S1S23S2bS49S50A4S1S21SdZ2dS2eA4A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsI : list edescA := ltac2:(tb__ "0|8|
S0S4S4S23S2bA2M0S4S21SdA2M1A2M2S1G0G1S1S23S2bS83S3bA4S1S21SdZ5bS2eA4M3A4S0G2S1G0G1S1S23S2bS43S3bA4G3A4S0G2S1G0G1S1S23S2bS7bS45A4S1S21SdZ55S2eA4M4A4S0G2S1G0G1S1S23S2bS7dS45A4G4A4S0G2S1G0G1S1S23S2bS80S45A4G4A4S0G2S1G0G1S1S23S2bS79S52A4S1S21SdZ4eS2eA4M5A4S0G2S1G0G1S1S23S2bS7aS52A4G5A4S0G2S1G0G1S1S23S2bS58S60A4S1S21SdZ46S2eA4A4S0G2S1G0G1S1S23S2bS86S51A4S1S21SdZ3cS2eA4M6A4S0G2S1G0G1S1S23S2bS88S51A4G6A4S0G2S1G0G1S1S23S2bS84S50A4S1S21SdZ28S2eA4A4S0G2S1G0G1S1S23S2bS74S98A4S1S21SdZ0S2eA4M7A4S0G2S1G0G1S1S23S2bS5bS99A4G7A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

End Lib_intern_rest.

(* [comment removed for export] *)
Module DrvJRe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "entailsA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "Some"; "option"; "orb"; "pair"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "ss_facts"; "sprop"; "SVar"; "sv"; "agree_below"; "eval"; "holds"; "rm"; "rw"; "sobj"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "nd_tv"; "JA"; "JAi"; "am_subst"; "fr_sub_eqb"; "am_eqb"; "amode"; "keptFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "V_TOP"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "w_cfg"; "w_tr"; "assn"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "to_nat"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.DrvJRe.PureCallV"; "post_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bud_le"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "import_sub"; "wsub_bound"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Code DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Reorigin.
Variable AInv : ltac2:(tb__ "0|0|
S3aSfS8S25Q40A1A1S1dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Variable NP : positive.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S8S9S9S1fS1fA2S1fA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis H24 : (24 < NP)%positive.
Hypothesis H30 : (V_TOP < NP)%positive.

Lemma rw_rho_sub : ltac2:(tb__ "0|0|
SfS28S20S0S25Q40A1S19S26R3R2A2R1A2S16R3S27R2R1A2A2A3Fv;Fs;Frho;").
Proof. intros. reflexivity. Qed.

Lemma JAi_reorigin : ltac2:(tb__ "0|3|
SfSfOF_;M0G0S28S20S8S12A1S2aS2aS3aS1fSfSfS8S25Q40A1A1S8S1eA1S1dS0S14S27RcP18M1A2S13G1A1A3S0S14S27RdS38A2S13S38A1A3S44VNP;RdA2S0S6S2dReRcA2S7A3S0S6S51R10S2fRdA1S2fRcA1A3S7A3S0S6S33R11S2eReA1S2eRdA1A3S7A3S0S6S53R10S52R12S2cReA1A2S2cRfA1A3S7A3S0S35S32R13S2bRfA1A2S2bR10A1A3S15R13RdRcA3S45S12S17RdA1R13A3R17S26ReR16A2A1S31VAInv;VCST;VXGL;VNP;VKc;R1aR19VFB;VFF;VBX;VPA;R14R12R11R10ReRdRcA12S31VAInv;VCST;VXGL;VNP;VKc;S26R10R18A2M2R19VFB;VFF;VBX;VPA;R14R13R12G2RfReRdA12F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fndj;Fndi;Ffacts;Fn;Fs;FP0f';FP0f;Frho0;").
Proof using ALA H24 H30.
  intros rho0 P0f P0f' s n facts ndi ndj Ai kc rho rho' tp tr md Hs24 Hs30 H2 H3 H5 H6 H7 Ham Hag HF HP0'' HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [apply agree_vals_refl|].
  split; [exact Hk|].
  split; [eapply (law_vars _ _ _ ALA); [exact HM|]; apply functional_extensionality; exact Hrm|].
  split.
  {
    unfold TPA, T0 in HT |- *. rewrite !rw_rho_sub, Hs24. change Contract.V_TOP with V_TOP. rewrite Hs30. cbn [eval].
    destruct Hav' as [Hv _]. rewrite <- (Hv 24%positive ltac:(lia)), <- (Hv V_TOP ltac:(lia)).
    destruct Hav as [Hv0 _]. rewrite <- (Hv0 24%positive H24), <- (Hv0 V_TOP H30). exact HT. }
  split; [exact HB|]. split; [exact HFF|].
  split; [split; [|split]|].
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - split; [eapply fr_sub_eqb_sound; [exact H6|]; eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR]|].
    split; [apply keptFA_refl|].
    split; [exact HP0''|].
    split; [eapply XA_subst; [exact M1 |]; rewrite Ham; eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA]|].
    assert (HCNT : cntS rho (nd_tv ndi) <= cntS (rho_sub rho' s) (nd_tv ndj)) by (rewrite (cntS_map _ _ _ _ M1), (cntS_agree n rho rho' _ Hav' Hbt); lia).
    split; [|exact (JA_tail_le _ _ _ rho (rho_sub rho' s) _ _ HCNT HPA)].
    rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer; [exact HF | exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
Qed.

Lemma SPA_reorigin_JA : ltac2:(tb__ "0|3|
SfSfOF_;M0G0S2S2S28S2aS2aSfS8S25Q40A1A1S3dS0S6S5R8R7R6A3S7A3S0S14S27R7P18M1A2S13G1A1A3S0S14S27R8S38A2S13S38A1A3S0S6S41VNP;S10S1RbA1A1A2S7A3S0S6S2dS10S1RcA1A1R9A2S7A3S0S6S51RbS2fRaA1S2fR9A1A3S7A3S0S6S33RcS2eRbA1S2eRaA1A3S7A3S0S6S53S11S1RfA1A1S52RdS2cRbA1A2S2cRcA1A3S7A3S0S6S34S32ReS2bRcA1A2S2bRdA1A2S7A3S3aS1fS45S12S17ReA1S11S1R13A1A1A3R16R17A1S57VNP;R18R10A3S36VCST;VXGL;R19VFB;VFF;S18R19A1S18R11A1A7VKc;S3fR10A1S48S3eR10A1A1A2S31VAInv;VCST;VXGL;VNP;VKc;R1bR1aVFB;VFF;VBX;VPA;R15R7R6R13R12S3fR11A1S48S3eR11A1A1A12R1aS26R14R17A2A1F_;F_;F_;F_;F_;F_;Fkc;FAi;S21S1cS30VAInv;VCST;VXGL;VNP;VKc;R15R14VFB;VFF;VBX;VPA;RfAcR12RdRcRbA6S21S1cS30VAInv;VCST;VXGL;VNP;VKc;S26ReR11A2M2R14VFB;VFF;VBX;VPA;RfAcR12G2RdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;FP0f';FP0f;Frho0;").
Proof using ALA H24 H30.
  intros rho0 P0f P0f' L T s ndi ndj rho tp w He Hs24 Hs30 Hnp Hnb Htv Hfr Hbd Ham HP0' [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ, HP0' |- *.
  destruct HJ as (Ai & kc & HJ). exists Ai, kc.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  eapply (JAi_reorigin rho0 P0f P0f' s (ss_next (ax_S L)) (ss_facts (ax_S L)));
    [exact Hs24 | exact Hs30 | exact Hnp | exact Hnb | exact Htv | exact Hfr | exact Hbd | exact Ham | apply agree_below_refl | exact HF | | exact HJ].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA).
  exact (HP0' Ai kc HF HP0 Hav HK Hk HJ).
Qed.
End Reorigin.

Section PureCallV.
Variable AInv : ltac2:(tb__ "0|0|
S3aSfS8S25Q40A1A1S1dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Variable NP : positive.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S8S9S9S1fS1fA2S1fA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Let JAK (Kc : KcA) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S30VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Vnd;Ac").

Definition post_val (s : wsub) (Pre Cl L : sstate) (rho' rhoL : valuation) : Prop := ltac2:(tb__ "0|2|
S20S0S6ScScSeS42R1S10VPre;A1M0A2A1S59Vs;R1A2A2S42R1S10VCl;A1M1A2A2S7A3S56S43R2A1S43S10VL;A1A1A2S0S25Q40A1S19VrhoL;R3A2S16Vrho';S27S58Vs;G0VL;G1A4R3A2A2A3F_;F_;Fv;").

Theorem pure_callJ_v : ltac2:(tb__ "0|4|
S3dOF_;S37S37S2S2S28S8S1aA1M0S8S3A1SfS8S25Q40A1A1M1S2aS22S22S40S39RcA1SfG1S3cS1cR11S21S1cR6RdR2R1A5S23S1cR5S10S1RdA1A1R2R1RaA6A4Ftp1;Frho1;S0SbG0A1S4eRdRcRbA3SaG0RaA2A3S0S6S4dReRdRcRbS46S3S2S4RaA4A5S7A3S0S6S41VNP;S10S1RfA1A1A2S7A3S0S6S2dS10S1R10A1A1R9A2S7A3S0S6S55S12S1bS10S1R11A1M2A1A1S11G2A1A3S7A3S8S1eA1M3S47S1dS24S1cR10RfR15SdG3S49R3S4aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS26S29R12R14S50R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;SfG3S1dRdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S3SfSfG3S1dS54S3R5R15A3S15S10S1R1aA1A1R15R5A3R12R5R15R4R3A4S4bR1aS1R1bA1S1R1cA1S1S4R8A1A1R7R6A6S3cS1cR20S21S1cVJAK;R1eR16A2S4cS11S1R1dA1A1S4fR1bR1cS4R9A1R1dR1aA5A2R8R17A5R13A4F_;F_;F_;F_;Fmd';Ftr';FrhoL;Frho';FL;S3cS1cR18S21S1cVJAK;R17ReA2R15R10RfA5RbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;Fok;").
Proof using ALA.
  intros ok Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply triple_factsA. intros HF.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (HIN tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' rhoL tr' md' HinL HAG Hk' (proj2 (proj2 HLK)) n HgQ). split.
  - apply smatchA_add_facts; [exact HSP | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
  - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ').
Qed.

Theorem pure_callJ_v_ex : ltac2:(tb__ "0|4|
S37S37S2S2S28S8S1aA1M0S8S3A1SfS8S25Q40A1A1M1S2aS22S22S3dOF_;S39RcA1SfG1S3bS1cS21S1cR6RdR2R1A5S23S1cR5S10S1RdA1A1R2R1RaA6A3Ftp1;Frho1;S0SbG0A1S4eRdRcRbA3SaG0RaA2A3S0S6S4dReRdRcRbS46S3S2S4RaA4A5S7A3S0S6S41VNP;S10S1RfA1A1A2S7A3S0S6S2dS10S1R10A1A1R9A2S7A3S0S6S55S12S1bS10S1R11A1M2A1A1S11G2A1A3S7A3S8S1eA1M3S47S1dS24S1cR10RfR15SdG3S49R3S4aR2R1A2A4A5VJAK;R18RfR11R10R4R2A6RfS26S29R12R14S50R3R11R4A3A3R15A2R11R5R3A4F_;F_;Fmd;Fms;Ftr;SfG3S1dRdR3R10R2R1A4VJAK;R18R10R12R11R3R2A6F_;Fmd';Ftr';FrhoL;S3SfSfG3S1dS54S3R5R15A3S15S10S1R1aA1A1R15R5A3R12R5R15R4R3A4S4bR1aS1R1bA1S1R1cA1S1S4R8A1A1R7R6A6S3bS1cS21S1cVJAK;R1eR16A2S4cS11S1R1dA1A1S4fR1bR1cS4R9A1R1dR1aA5A2R8R17A5R13A3F_;F_;F_;F_;Fmd';Ftr';FrhoL;Frho';FL;S3bS1cS21S1cVJAK;R17ReA2R15R10RfA5RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FJp';FJp;Fnd;Ftp;Frho;FPosts;FR;Fs;FPre;FCl;FKc';FKc;").
Proof using ALA.
  intros Kc Kc' Cl Pre s R Posts rho tp nd Jp Jp' Q HKc' Hsum He Hchk Hnf Hnb Hfb HIN HOUT Hcont. apply Pos.leb_le in Hnf.
  apply etriple_factsA. intros HF.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (HIN tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' rhoL tr' md' HinL HAG Hk' (proj2 (proj2 HLK)) (tr', mkCfg ms' md')) as (w'' & Hsteps' & HQ).
  { split.
    - apply smatchA_add_facts; [exact HSP | |].
      + apply Forall_forall. intros q Hq.
        apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
        * exact (proj1 (forallb_forall _ _) Hfb q Hq).
        * exact (proj1 (Forall_forall _ _) HF q Hq).
      + apply forallb_forall. intros q Hq.
        eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
        unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
    - destruct (HOUT rhoL tr' md' Hk') as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NP Kc' rho0 P0f FB FF BX PA HKc' ALA (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ'). }
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.
End PureCallV.
End DrvJRe.

(* [comment removed for export] *)
Module Lib_arena_dup.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "app"; "nat"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup"; "vSZ"; "vH"; "vCAPl"; "vP"; "z0"; "c8"; "vK"; "tv0"; "X_ad"; "p_fit"; "vHD"; "vSRC"; "O_F"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "vI"; "vLS"; "vU"; "X_nohead"; "ndO"; "vUc"; "C_loop"; "C_slow"; "nd0"; "ndL"; "ndS"; "pN"; "vAR"; "vNXl"; "E_m"; "F_cells"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "base_fit"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "slow_facts"; "spm"; "ug_facts"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "cutpcs_ad"; "ghK"; "loop_facts"; "loop_regs"; "ndF"; "ndK"; "ndM"; "ok_facts"; "pad_fit"; "s3_sh"; "slow_regs"; "tv_m"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "leavesA_at"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0xa8000.
  Definition ad_open : Z := 0xa8058.
  Definition ad_slow : Z := 0xa80b0.
  Definition ad_K : Z := 0xa80dc.
  Definition ad_loop : Z := 0xa818c.
  Definition ad_xit : Z := 0xa81cc.
  Definition ad_ret : Z := 0xa8164.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S29SdZ0A1S31S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1eS2S10A1S14A5").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S4SbSa3S0SbScSdZ1A1S1eA2S0SbScS1eS31A2S0SbScS31SdS97Z2Z20A2A1A2S0SbScSdZ1000A1S29A2S0SbScSfS1cS29S31A3SaP1eA1M0A2S0SbScS29G0A2S2SbA1A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S3cSdZ40A1A4S0G0S1S9S9S29S31A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|0|
S12Sa0S91S8dS11S6S9A1S4SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS28A1S0SeS2dS2SeA1A3A3A3A3S93A3S2eS8fS7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S3cSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S85S87Z1M0Z0M1S0S3S1aS86A2M2S1S1aS86Z2S88S1eA1M3A4S2G2A1M4A3Z60A4S0S85S87G1G0S0G2S1S1aS86Z4G3A4G4A3Z40A4S2S85A1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa1S0S1aS9eS0S1aS9bS0S1aSa4S0S1aS9cS0S1aS9fS2S1aA1A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa2S80Vk;S94S53S6fVS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S84S28S7dS4dS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S8eS17S81S33A1A1S0S3S5S9A2M0S1S5S9UaSaP65A1A4S0G0S1S5S9UeSaP66A1A4S0G0S1S5S9UfSaP67A1A4S0G0S1S5S9U10SaP68A1A4S0G0S1S5S9U11SaP69A1A4S0G0S1S5S9U5SaP6aA1A4S0G0S1S5S9U6SaP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SbScSdZ10001A1SfS1cS4eSfS1cS1eSdZ10A1A3A3A2S0SbScS4eSdS97Z2Z28A2A1A2S2SbA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S92S12S9eS79S8dS11S6S9A1S16S81S33A1A1S4SbS4cS4aA3P6dS7A9S26A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SbScSdZ10000A1M0S24A2S0SbScSfS1cS1eSdZ10M1A1A3S24A2S0SbScS24SfS1cS1eG0A3A2S0SbScS24SdS99S97Z2Z20A2G1A2A1A2S0SbScSdZ1A1S8bS24A1A2S2SbA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S92S12S9bS8eS17S81S5aA1M0A1S0S3S5S9A2M1S1S5S9U14S24A4S2G1A1A3A2S8dS11S6S9A1S16G0A1S0SbS70S4SbS54S4SbS4cS4aA3A3A3P70S7A9S26A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1eSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S4S85S0S85S87Z1M0Z0M1S0S3S1aS86A2M2S1S1aS86G0S88S8bS24A1A1A4S2G2A1A3G1A4S0S85S89G1G0S9aZ2S8aA2A3S2S85A1A3A3S8cS1eA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS7cA4S96PaS81S3eA1S81S57A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SaS3bA1S8bS24A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S4S85S0S85S89Z0Z1S8aA3S2S85A1A3S8cS1eA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S84S1fS3dS20S0S3S9S9A2M0S1S9S9S21S1eA4S2G0A1A3A4").
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S10S23N40SaP2aA1A2S0S10S23N38SaP29A1A2S0S10S23N30SaP28A1A2S0S10S23N28SaP27A1A2S0S10S23N20SaP26A1A2S0S10S23N18SaP1dA1A2S0S10S23N10SaP1cA1A2S0S10S23N8SaPbA1A2S2S10A1A3A3A3A3A3A3A3A3").
Definition s3_sh : sv := Eval vm_compute in nth 19 (ss_regs (ax_S X_nohead)) (SLit 0).
Definition loop_regs : list sv := ltac2:(tb__ "0|2|
S0S9SaP6bA1S0S9SaP6cA1S0S9S4bZ40A1S0S9SaP17A1S0S9SaP18A1S0S9SaP6dA1S0S9SaP6eA1S0S9SaP6fA1S0S9SfS1cS3cSdZ30A1A3S0S9S95S0S9S21S0S9SfS1cS29S30A3M0S0S9SfS1dS1eS30A3S0S9G0S0S9SfS1cS21S30A3M1S0S9G1S0S9SaP70A1S0S9SaP71A1S0S9S1eS0S9S78S0S9SaP72A1S0S9SaP73A1S0S9SaP74A1S0S9SaP2bA1S0S9SaP2cA1S0S9SaP2dA1S0S9SaP2eA1S0S9SaP2fA1S0S9SaP75A1S0S9SaP76A1S0S9SaP77A1S0S9SaP78A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SbS19S30S1eA2S0SbScS35S20A2S0SbScSdZ10000A1S20A2S0SbScS20SdS98S97Z2Z28A2Z21A2A1A2S0SbScSfS1cS1fS8bS20A1A3M0SaP1eA1M1A2S0SbScS1fG1A2S0SbScSdZ1000A1M2S1fA2S0SbS13P65Z4M3A2S0SbScSfS1cS1fSdZ20A1A3S21A2S0SbScSfS1cS21S1eA3M4G0A2S0SbScG2S21A2S0SbScG4G1A2S0SbScS21G1A2S0SbS13P69G3A2S2SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S92S12S9cS72S8dS11S6S9A1S4SeS0SeS2aS3fA1S0SeS2bS0SeS2cS1fA1S0SeS2dS2SeA1M0A3A3A3A3S4SeS93S0SeS40S1fS3dS20S35A4S0SeS41S21A1G0A3A3A3A3S4SbS71S4SbS46S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S1fS8bS20A1A4S26A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS28SdZ20A1A3S32A3").
Definition pad_fit : sv := SAlu ALU_SUB p_fit base_fit.
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS32S1eA3S77A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SbScS44S27A2S0SbScS27SfS1cS44SdZfA1M0A3A2S0SbScSdZ1000A1S27A2S0SbScS27SaP1eA1M1A2S0SbScSfS1cS27S1eA3M2SfS1cS28S8bS4dA1A3A2S0SbScG2G1A2S0SbScSfS1cS28SdZ20A1A3S27A2S0SbScS7bSfS1cS32SfS1cS1eG0A3A3A2S2SbA1A3A3A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
ScSdZ10001A1SfS1cS32SfS1cS1eSdZ10A1A3A3A2").
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition iN : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_sret : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iN)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iN].
Definition X_sret1 : axst := Eval vm_compute in optAp (apply_axforms X_sret [AXSelect sel_sret; AXSplit (length sel_sret - 1) (SLit 24)]).
Definition iH : nat := Eval vm_compute in (length (ss_objs (ax_S X_sret1)) - 2)%nat.
Definition jU : nat := Eval vm_compute in
  find_idxb (fun c => sv_eqb (c_off c) (SLit 16)) (ob_cells (nth iH (ss_objs (ax_S X_sret1)) O_src)) 0%nat.
Definition optSC (x : option (sstate * cell)) : sstate * cell := ltac2:(tb__ "0|2|
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S56S23Z0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSaS3bA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SbScSfS1cS49S1eA3M0SfS1cSaS3bA1S8bS24A1A3A2S0SbScG0SaP1eA1M1A2S0SbScS49G1A2S2SbA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SaP6bA1S0S9SaP6cA1S0S9S4bZ40A1S0S9SaP17A1S0S9SaP18A1S0S9SaP6dA1S0S9SaP6eA1S0S9SaP6fA1S0S9SaP70A1S0S9SaP71A1S0S9S21S0S9SaP7aA1S0S9SaP7bA1S0S9SaP7cA1S0S9SaP7dA1S0S9SaP7eA1S0S9SaP7fA1S0S9SaP80A1S0S9SaP81A1S0S9SaP82A1S0S9SaP72A1S0S9SaP73A1S0S9SaP74A1S0S9SaP2bA1S0S9SaP2cA1S0S9SaP2dA1S0S9SaP2eA1S0S9SaP2fA1S0S9SaP75A1S0S9SaP76A1S0S9SaP77A1S0S9SaP78A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SbScS35S20A2S0SbScSdZ10000A1S20A2S0SbScS20SdS98S97Z2Z28A2Z21A2A1A2S0SbScSfS1cS1fS8bS20A1A3SaP1eA1M0A2S0SbScS1fG0A2S0SbScSdZ1000A1M1S1fA2S0SbS13P65Z4M2A2S0SbScG1S21A2S0SbScSfS1cS21S1eA3G0A2S0SbScS21G0A2S0SbS13P69G2A2S2SbA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S92S12S9fS7fS8dS11S6S9A1S4SeS0SeS2aS3fA1S0SeS2bS0SeS2cS1fA1S0SeS2dS2SeA1M0A3A3A3A3S4SeS93S0SeS40S1fS3dS20S35A4S0SeS41S21A1G0A3A3A3A3S4SbS7eS4SbS46S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S1fS8bS20A1A4S26A3A2").

Definition X_ret : axst := Eval vm_compute in leafA_at C_exit ad_ret 0.
Definition iS : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) vP) (ss_objs (ax_S X_ret)) 0%nat.
Definition iHd : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) vH &&& sv_eqb (ob_hi o) (SLit 24)) (ss_objs (ax_S X_ret)) 0%nat.
Definition sel_ret : list nat := Eval vm_compute in
  (List.filter (fun j => negb (Nat.eqb j iS || Nat.eqb j iHd)) (seq 0 (length (ss_objs (ax_S X_ret))))) ++ [iHd; iS].
Definition X_ret1 : axst := Eval vm_compute in optAp (apply_axforms X_ret [AXSelect sel_ret]).
Definition objsR : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_ret1))).
Definition ohR : sobj := Eval vm_compute in nth (length objsR) (ss_objs (ax_S X_ret1)) O_src.
Definition osR : sobj := Eval vm_compute in nth (S (length objsR)) (ss_objs (ax_S X_ret1)) O_src.
Definition X_ret2 : axst := Eval vm_compute in drop_lastA X_ret1 (objsR ++ [ohR]).
Definition X_ret3 : axst := Eval vm_compute in drop_lastA X_ret2 objsR.

Definition P_fail : axst := ltac2:(tb__ "0|1|
S92S12S9dS8eS90S8fA1S0S3S5S9A2M0S1S5S9UaSdZ0A1A4S2G0A1A3A2S8dS11S6S9A1S4SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS28A1S0SeS2dS2SeA1A3A3A3A3S93A3S2eSa5S7A9S26A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SbScSdZ1000A1M0SaP8cM1A1M2A2S0SbScSfS1cG2S1eA3SaP1eA1M3A2S0SbS13G1Z4A2S0SbScG0SaP8dA1M4A2S0SbScG4G3A2S2SbA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S92S12S9dS8eS90S8fA1S0S3S5S9A2M0S1S5S9UaSaP8cA1A4S2G0A1A3A2S8dS11S6S9A1S4SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cSaP8dA1A1S0SeS2dS2SeA1A3A3A3A3S93A3S4SbS76S2eA3P8eS7A9S26A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S96P64S81S5eA1S81S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S96P64S81S66A1S81S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS32A4S96P64S81S60A1S81S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S96P64S81S33A1S81S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S96P64S81S64A1S81S42A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S4fS67A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S6dS6aA4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S6eS2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S6bS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S45S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S83S7aS2S3S3S9S1aA2S9A2A1S45S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S6cS68A4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S2S85A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S83S25S2S3S3S9S1aA2S9A2A1S2S85A1S69A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S80S82A2M0S3S1aS9A2M1A2M2S1G0G1S1S80S82S43S38A4S1S1aS9Z64S22A4A4S0G2S1G0G1S1S80S82S52S34A4S1S1aS9Z5aS22A4A4S0G2S1G0G1S1S80S82S37S3aA4S1S1aS9Z50S22A4A4S0G2S1G0G1S1S80S82S50S47A4S1S1aS9Z4bS22A4A4S0G2S1G0G1S1S80S82S58S75A4S1S1aS9Z41S22A4M3A4S0G2S1G0G1S1S80S82S59S48A4G3A4S0G2S1G0G1S1S80S82S36S39A4S1S1aS9Z32SfS1dS1eS30A3A4A4S0G2S1G0G1S1S80S82S51S39A4S1S1aS9Z2dS22A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S80S82A2M0S3S1aS9A2M1A2M2S1G0G1S1S80S82S62S38A4S1S1aS9Z5fS22A4M3A4S0G2S1G0G1S1S80S82S33S38A4G3A4S0G2S1G0G1S1S80S82S61S34A4S1S1aS9Z55S22A4M4A4S0G2S1G0G1S1S80S82S5dS34A4G4A4S0G2S1G0G1S1S80S82S5fS34A4G4A4S0G2S1G0G1S1S80S82S5bS3aA4S1S1aS9Z4eS22A4M5A4S0G2S1G0G1S1S80S82S5cS3aA4G5A4S0G2S1G0G1S1S80S82S3eS47A4S1S1aS9Z46S22A4A4S0G2S1G0G1S1S80S82S65S48A4S1S1aS9Z3cS22A4A4S0G2S1G0G1S1S80S82S63S39A4S1S1aS9Z28S22A4A4S0G2S1G0G1S1S80S82S55S73A4S1S1aS9Z0S22A4M6A4S0G2S1G0G1S1S80S82S42S74A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_arena_dup.

(* [comment removed for export] *)
Module Lib_arena_alloc_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "cons"; "nil"; "app"; "Some"; "option"; "None"; "fst"; "length"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "valuation"; "SLit"; "sprop_eqb"; "SPUle"; "sv"; "SVar"; "SAlu"; "holds"; "ss_facts"; "ss_objs"; "SPBranch"; "ss_next"; "DUnknown"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BIc"; "KU"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "sub"; "mul"; "lt"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "AK0"; "JA"; "JLA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc"; "vCAP"; "vHD"; "s_m"; "E_m"; "R_m"; "X_fit"; "nd0"; "vAR"; "vU"; "P_fail"; "P_ok"; "SZ"; "X_sret1"; "X_sret2"; "ndF"; "ndK"; "ndO"; "p_fit"; "vDp"; "Pre_aa"; "Pre_m"; "X_nofit1"; "X_open"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndS"; "sel_sret"; "spm"; "C_open"; "FUEL_aa"; "O_W"; "T_mnull"; "T_mok0"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_sret3"; "cutpcs_aa"; "fit_facts"; "ndMok"; "need_fit"; "nofit_fact"; "p_new"; "pad_fit"; "tv0"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_alloc_pf"; "P0_aa"; "objsN"; "ohN"; "ohF"; "otN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_alloc_pf.Sum"; "Posts_aa"; "JL"; "basez"; "baseF"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA";
"ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "e32"; "drop_lastA"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_alloc_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import AAAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0SbS48S7S87S6aS74P64S64S65A7ScA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S4Sb7S61S4cA2S69A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S4Sb2S5fS4eS4dS4fS94S90S10S92A1S91A3A5S6cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S4Sb2S5fS4eS4dS4fS95S90S10S92A1S91A3A5S6dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S4Sb1S60SfS19S78S23S5S60A1A1A3A2S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_W.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0SaS1aA1S24S5S50A1A1M0S11S1aS3eS1aG0A2SfS1aS8dS10S1aA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S4Sb1Sb4S50S5cS1cS56A1A3S11S19S75S23S5S50A1A1A3A2S6eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S13S4A1SafS62SfSacSadS67A1SfSacSaeSbbS16S17S67A2U1A2S1cZ18A1A2S10SacA1A3A3A2S12S4S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ohN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 2) (ss_objs (ax_S X_sret1)) O_W.
Definition otN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 1) (ss_objs (ax_S X_sret1)) O_W.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1))).
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0SaS1aA1S24S5S57A1A1S11S1aS11S1aS8bSfS1aS8cS10S1aA1M0A3A3SfS1aS8eG0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S4Sb6S57S11S1aS8bSfS1aS8cS10S1aA1A3A3A2S58A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0SaS1aA1S24S5S58A1A1S11S1aS8bSfS1aS8cS10S1aA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S4Sb4S58S79S1cS56A1A3S73A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition bd_m2 : list bitem := ltac2:(tb__ "0|2|
SfS2fS30Z1M0Z0M1Zf0A3SfS2fS30G1G0S35S33S45Z160A2S36Z2S31A2A2A3S10S2fA1A3A3").

Definition P0_aa (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := True.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Sb0S1bSaS3fQ40A1A1Sa2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S9bS7VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S18SbaVCST;R1A2S1S32Z0R2A2S37R2Sb9A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S18SbaVXGL;R1A2S1S32Z0R2A2S37R2Sb9A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SaSeSeS18S18A2S18A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S47VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42Vnd;Aa").
Definition Posts_aa : list (axst * jpostA) := ltac2:(tb__ "0|1|
SfSeS4S7eA2M0SdS4S7eS54Sa5S59A1A4SfG0SdS4S7eS55Sa5S5aA1A4S10G0A1A3A3").

Definition PD_aa : list (axst * ndesc) := ltac2:(tb__ "0|1|
SfSeS4S41A2M0SdS4S41S54S59A4SfG0SdS4S41S55S5aA4S10G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;S87VKc;Vrho0;S8aVFB;VFF;A2VFB;VFF;VBX;S42Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
SeS4S41A2SbfFn;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;S87VKc;Vrho0;S8aVFB;VFF;A2VFB;VFF;VBX;S42Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S7fS7S87Vrho0;Vtp0;Sa4A5").

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|5|
S1S0SbS3cS19S1dS1eS20PaA1M0S1cS7dA1M1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS20P1eA1M2S21S88S68Z40M3A1M4S5dA3A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eG2G4A2A1VF;A3ScA3S1S0SbS3cS19S1dS25S89S1cN1000A1S5dA3A1VF;A3ScA3S1S0SbS3cS19S1dS25S89S5dS1cS38S7cA1A1A3A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ1000A1S52A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS21S88S52S1cG3A1A3G2A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS52G1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS4cG2A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eG2G0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ7fff7f800000A1G2A2A1VF;A3ScA3S0SbS3cS19S1dS1eG2S1cZ7fffff800000A1A2A1VF;A3ScA3A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_win : forall a, fst (obj_range rho O_W) <= a < snd (obj_range rho O_W) -> bv_unsigned (rw rho V_TOP) <= a < uval rho (SVar 10) - 64;
  bz_ar : 4096 <= uval rho vAR /\ uval rho vAR + 64 <= bv_unsigned (rw rho V_TOP);
  bz_hd : uval rho vHD <= bv_unsigned (rw rho V_TOP);

  bz_top : 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S1bS18S1S32Z0R1A2S32R1S2eR2S20PaA1M0A2A2A2S0S18S2eR3S68R2A1A2S35S2eR3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S1bSaS19A1Sa8S19S22R2A1R1A3Sa7R2A1Sa6R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2. zf HT1. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8. pose proof (holds_mem _ _ _ HF B9) as H9.
  pose proof (holds_mem _ _ _ HF B10) as H10.
  zf H1. zf H2. zf H3. zf H6. zf H7. zf H8. zf H9. zf H10.
  apply (proj1 (holds_bge _ _ _)) in H4. apply (proj1 (holds_bge _ _ _)) in H5.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold two47, RA.two47, two40, RA.two40 in *.
  rewrite !uval_lit in H1, H6, H8, HT1, HT2 by lia.
  change (uval rho (SLit (-4096))) with (bv_unsigned (eval rho (SLit (-4096)))) in H4. rewrite U_lit in H4. change ((-4096) mod M64v) with 18446744073709547520 in H4.
  change (uval rho (SLit (- 2 ^ 40))) with (bv_unsigned (eval rho (SLit (- 2 ^ 40)))) in H5. rewrite U_lit in H5.
  change ((- 2 ^ 40) mod M64v) with 18446742974197923840 in H5.
  rewrite uval_add_small in H7 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H7 by lia.
  rewrite uval_spm in H3 by lia.

  pose proof (uval_range rho vDp) as RD.
  destruct (Zsigned_spec (uval rho vDp)) as [[L1 E1]|[L1 E1]]; rewrite E1 in H4, H5;
    [destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in H4; lia|].
  destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in H4; [lia|].
  destruct (Zsigned_spec 18446742974197923840) as [[? E3]|[? E3]]; rewrite E3 in H5; [lia|].
  assert (EA : uval rho (SAlu ALU_ADD (spm 64) vDp) = uval rho (SVar 10) - 64 + (uval rho vDp - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho (spm 64))) with (uval rho (spm 64)). change (bv_unsigned (eval rho vDp)) with (uval rho vDp).
    rewrite uval_spm by lia. unfold M64v.
    replace (uval rho (SVar 10) - 64 + uval rho vDp) with ((uval rho (SVar 10) - 64 + (uval rho vDp - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite EA in H2.
  constructor; try lia.
  intros a Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_W in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. change (bv_unsigned (eval rho (spm 64))) with (uval rho (spm 64)) in Hr. rewrite uval_spm in Hr by lia.
  unfold soff in Hr. rewrite bv_signed_U in Hr. change (bv_unsigned (eval rho vDp)) with (uval rho vDp) in Hr. rewrite E1 in Hr. lia.
Qed.

Lemma objs_ok_gen : ltac2:(tb__ "0|5|
S1bSaS1aA1Sa6R2A1S1aS3dS1aR1R3A3S2S1S0S1fS28R2A1M0S20PaA1A3S1S0S1fS2bR2A1M1S1cN40A1A3S1S0S1fS2aR2A1M2S1cZ0A1M3A3S0S2cS29R2A1S27A3M4A2A2A2S2S0S1aR2S6bA3S2S1S0S1fG0S52A3S1S0S1fG1G3A3S1S0S1fG2S1cZ40A1A3G4A2A2A2S2S0S1aR2S8A3S0S1aR2S9A3A2A2A2A2F_;Fo;S0S18Sc0Vrho0;A1S40Q40S2dR4S98A2A2A3Sb8VCST;Vrho0;VFB;VFF;R5S7bS10SeSeS1fS18A2S1fA2A1R4A8F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ Hcls ET o a Ho Hr. destruct BZ as [Bsp Bwin Bar Bhd Btop].
  destruct (Hcls o Ho) as [(Hb & Hl & Hh & Hd)|[->|[(Hb & Hl & Hh & Hd)|[->| ->]]]].
  - left. left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in Hb, Hl, Hh, Hd. subst.
    apply range_lit' in Hr; [|lia|lia]. lia.
  - left. left. pose proof (Bwin a Hr). lia.
  - left. right; right; left. exists (uval rho vAR), 64. split.
    + apply In_FBx. right. exists (vAR, SLit 64). split; [left; reflexivity|]. split; [unfold tnz; cbn [fst]; unfold uval in Bar; lia|].
      unfold tvv. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
    + destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in Hb, Hl, Hh, Hd. subst. apply range_lit' in Hr; [|lia|lia]. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_got in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold GOT_LO, GOT_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_rtc in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold RTC_LO, RTC_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S18SaS3fQ40A1A1S83F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3aS4S1bSaS3fQ40A1A1S83Sa8S19S22R3A1S23S5R4A1A1A3VTR;S39S7R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S83S83S84S3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3aS3aS4S4S9fSaS1aA1M0SaSeS4S7eA2M1A1SaSeS1fS1fA2M2A1S83S1bSaS3fQ40A1A1M3G2S3dG2R1R5A3S3dG2R2S6RbA1A3F_;Fr;S0S13G0A1S82RaR9R8A3S12G0R7A2A3S0SbS81RbRaR9R8Sa9G1S4S15S4S7eA2R7A4A5ScA3S1bG3VTR;S39S7RfRdR2R1A5S7fS7S26S5RdA1A1R2R1RaA5A2Ftp1;Frho1;SaSa3A1M4Sa1Sa2S3bS7R9R8R10SdG4SaaR3SabR2R1A2A4A5R13RaR9R4R2A4R13S9eS9dRbRfS8fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S7eG4Sa1Sa2S1bG3G4Sa1Sa2S3dG1SdS4S7eRaR9A4R14A3S3bS7R12R11R19SdG4SaaR9SabR8R7A2A4A5R1cR13R12RaR8A4SbdS26S5R1aA1A1S9eS9dR14R18S8fR9R13RaA3A3R19A2R8A3S3bS7R9R8ReSdG4SaaR7SabR6R5A2A4A5ReS9eS9dR16R1aS8fRbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sc1R17S8fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1bSbeR18S8fRdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S39S7S80R11S9eS9dR19R1dS8fReR18RfA3A3R1eA2R18RdRcA5Sc2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S39S7R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sb0S1bSaS3fQ40A1A1VTR;S39S7S93VAInv;S10S92A1M0S91R3VKc;S20PcA1A6S97S90G0S91A3R2R1A5S7fS7S87R2R1S96S90VAInv;VCST;VXGL;G0S91R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S41SeS18S1fA2M0S1bSaS3fQ40A1A1M1S18G1S3dSeSeS4S41A2M2G0A2SdG2G0SdS4S41R7R6A4R5A4S64A3S1S32Z0S44SdG2G0SdS4S41R8R7A4R6A4R5A2M3A2S37G3R3A2A2VTR;S39S7VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S41S1bSaS3fQ40A1A1M0S18G0S3dSeS4S7eA2SdS4S7eR6Sa5R5A1A4Sa4A3VTR;S39S7VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Lemma X_X_open : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z5bS34Z2Z40A2A2R2A2VTR;S39S7VJAv;S51A1S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      + apply objs_ok_gen; [eapply basez_of; [exact HF | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]| |exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. rewrite uval_lit in Ha by lia.
        pose proof (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [right; left; reflexivity | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z51S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S51A1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [do 2 right; left; reflexivity | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ E0) (AHead vHD false)) ndS);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HBX); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hw].
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S59A1S54R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5aA1S55R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S1bSb3VAInv;VCST;VXGL;S87Vrho0;S8aVFB;VFF;A2VFB;VFF;S4eS4dS4fR1S66S14S18A1Sb0Sa1S1S1S32Z1S2eR3Sa0S4dPcA2A2M0A2S37G0S34Z2Z27A2A2A2S9cS10S92A1S91S9eS9dR3S4fR1A3S4dA2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndS] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun _ => false) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. discriminate Hb.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun _ => false) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. discriminate Hb.
    + exact I.
  - change (wsub_get s_m 12) with (SLit 65568). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z42S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S66A1S4eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndS bd_m (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [do 3 right; left; reflexivity | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [do 4 right; left; reflexivity | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fit_arith : ltac2:(tb__ "0|9|
S1bS32S2eR1S4cA2Z7fffff800000A2S32S2eR2S53A2S2eR2S4bA2A2S32S2eR3S4bA2S35S34Z2Z28A2Z21A2A2S1S0S18S2eR4S63A2M0S33S33S2eR4S4cA2M1Z20M2A2S2eR4S53A2M3A2A3S1S1S32G0S2eR4S5cA2M4A2S32G4S33G0ZfM5A2M6A2A2S1S0S18S2eR4S7aA2M7S35G4G0A2A3S1S0S18S2eR4S77A2S33S33G3Z48M8A2G7A2A3S1S0S18S2eR4S21S88S63S1cG5A1A3A2G6A3S1S0S18S2eR4S21S88S5cS1cS56A1A3A2S33G4G8A2A3S0S18S2eR4S21S88S4cSb5S4bA1A3A2S33G1S33S2eR4S4bA2G2A2A2A3A2A2A2A2A2A2F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc. unfold SZ.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split]].
  - unfold need_fit, SZ.
    assert (E1 : uval rho (SAlu ALU_ADD vU (SLit 72)) = uval rho vU + 72) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite E1; lia). rewrite E1. lia.
  - unfold SZ. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0SbS3cS19S1dS1eS4cS20P1eA1M0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS53S4bA2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS4bS1cS35S34Z2Z28A2Z21A2A1A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ10000A1S4bA2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS21S88S4cSb5S4bA1A3G0A2A1VF;A3ScA3S1S0SbS3cS19S1dS1eS1cZ1000A1S4cA2A1VF;A3ScA3S0SbS3cS19S1dS1eG0S1cZ7fffff800000A1A2A1VF;A3ScA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|4|
S1bSaS19A1Sa8S19S22R2A1R1A3SbcR2A1S1S32S2eR4S4cA2M0Z7fffff800000M1A2S1S32S2eR4S53A2S2eR4S4bA2M2A2S1S32G2S35S34Z2Z28A2Z21A2A2S1S32Z10000G2A2S1S32S33G0S33G2Z20A2A2S2eR4S20P1eA1A2M3A2S1S32Z1000G0A2S32G3G1A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3) as (_ & _ & _ & _ & _ & _ & E7). rewrite E7 in H5. lia.
Qed.

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5bA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & _).
  assert (HO : existsb (sprop_eqb (SPBranch BC_LTU (SLit 18446744073709551543) pad_fit)) (ss_facts (ax_S X_nofitO)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HO) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0.
  rewrite uval_lit in H0 by lia. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0S32S36Z51S34Z2Z40A2A2R2A2VTR;S39S7VJAv;S5bA1S6fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & _).
  assert (HN : existsb (sprop_eqb (SPNot (SPBranch BC_GEU vCAP need_fit))) (ss_facts (ax_S X_nofit)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HN) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.

  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65449 mod M64v) with 65449.
      assert (EU : eval rho1 vU = eval rho vU) by (unfold rho1; apply eval_absorb). rewrite EU. change (bv_unsigned (eval rho vU)) with (uval rho vU). lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [do 2 right; left; reflexivity | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S5bA1S50R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & E15 & E72 & EHC).
  assert (HY : existsb (sprop_eqb (SPBranch BC_GEU vCAP need_fit)) (ss_facts (ax_S X_fit)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (holds_mem _ _ _ HF HY) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.
  eapply TR_pre; [|apply (X_P_ok (rho_sub rho s_fit) tp b tp0)].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_fit3 P_ok s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, SLit SZ)])) ndK);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit))); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit (SLit SZ) X_fit rho tp w);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact Hw].
    + intros r HFr. destruct (openz r _ HFr ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3) as (EB' & EP' & EPAD' & EN' & _).
      pose proof (holds_mem _ _ _ HFr HY) as H1. zf H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. rewrite EN' in H1.
      unfold SZ. rewrite uval_lit by lia. pose proof (uval_range r vU). lia.
    + intros Ai rho1 tp1 md1 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      * intros o a Ho Hr.
        rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_gen rho (removelast (ss_objs (ax_S X_fit))) (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD. lia.
      * intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha.
        -- assert (E32 : uval rho (e32 vCAP) = uval rho vCAP + 32)
             by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
           change (SAlu ALU_ADD (SVar 102) (SLit 32)) with (e32 vCAP) in Ha. change (SVar 15) with vHD in Ha.
           rewrite E32 in Ha. pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. pose proof (basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD).
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC; rewrite ?uval_lit by lia; lia.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
S1bSaS3fQ40A1A1M0S18G0VTR;S39S7VJAv;S76A1S62R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD (SLit 65536) (SLit 72)
                  X_sret1 objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
                   ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H1).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD (SLit 65536) p_new (SLit SZ) X_sret2 rho1 tp _);
        [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact H2].
      - intros r HFr.
        assert (HE : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
        assert (HE' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
        pose proof (holds_mem _ _ _ HFr HE) as HE1. zf HE1. pose proof (holds_mem _ _ _ HFr HE') as HE2. zf HE2.
        repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
        rewrite uval_lit in HE2 by lia.
        rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
        pose proof (uval_range r (SVar pN)) as RP. unfold p_new, SZ.
        rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite !uval_lit by lia. lia.
      - intros Ai rho2 tp2 md2 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 HavS eq_refl) as ET. split.
        + intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
          * destruct (objs_ok_gen rho1 objsN (basez_of rho1 _ HF' ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
          * right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia].
            unfold pN. lia.
        + intros r a Hr Ha.
          assert (HX : In r [(SVar 12, SLit 64); (SVar pN, SLit 65568)]) by exact Hr. clear Hr.
          pose proof (basez_of rho1 _ HF' ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]].
          destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha.
          * rewrite uval_lit in Ha by lia. unfold vAR in *. lia.
          * assert (HE' : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
            assert (HE'' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
            pose proof (holds_mem _ _ _ HF1 HE') as HE1. zf HE1. pose proof (holds_mem _ _ _ HF1 HE'') as HE2. zf HE2.
            repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
            rewrite uval_lit in HE2 by lia.
            rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
            rewrite uval_lit in Ha by lia. pose proof (uval_range rho1 (SVar pN)). lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_sret3 P_ok s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)])) ndK);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S41SeS18S1fA2M0S1bSaS3fQ40A1A1M1G1S3dSeSeS4S41A2M2G0A2SdG2G0SdS4S41R6R5A4R4A4S65A3VTR;S39S7VJAv;R6A1R7R4R3A5VFAM;S44SdG2G0SdS4S41R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_nofit. meas.
  - apply X_X_fit.
  - apply X_E_m. meas.
  - apply X_X_sret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S4aS7VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S99S7S90VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum : ltac2:(tb__ "0|0|
SaS3fQ40A1A1S86S7Vok;S39S7S43VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42S51AaS5eVrho0;R1A5S7fS7S87Vrho0;R1Sa4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_aa FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_aa P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9aS7S90VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum_ex : ltac2:(tb__ "0|0|
SaS3fQ40A1A1S85S7S39S7S43VAInv;VCST;VXGL;VKc;S8aVFB;VFF;A2VFB;VFF;VBX;S42S51AaS5eVrho0;R1A5S7fS7S87Vrho0;R1Sa4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_aa FB FF) FB FF BX PTrue rho0 tp0 nd Posts_aa P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_arena_alloc_pf.

(* [comment removed for export] *)
Module Lib_vec_push_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_push"; "E_vr"; "s_v"; "vKg"; "R_v"; "T_grown"; "T_keep"; "Xk_v"; "xf_vback"; "E_msg"; "E_msk"; "L_ms"; "Pre_ms"; "T_fail0"; "T_grown0"; "T_keep0"; "s_m"; "slot_facts"; "vC1"; "vDg"; "xf_mback"; "xf_mcall"; "E_msg0"; "E_msg1"; "E_msk0"; "E_msk1"; "E_vr0"; "FUEL_vp"; "R_mg"; "R_mk"; "T_fail"; "T_grownF"; "T_keepF"; "T_mg"; "T_mg0"; "T_mg1"; "T_mk"; "T_mk0"; "T_mk1"; "cutpcs_vp"; "cutsP"; "exitsP"; "hse_fact"; "xf_vcall"; "@Corelib.Init.Datatypes"; "Some"; "option"; "list"; "app"; "prod"; "cons"; "nil"; "bool"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "Pre_vr"; "bdP"; "tv0"; "vK"; "P_grown"; "P_keep"; "P_fail"; "vW"; "kbytes"; "tvP"; "vDt"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve Lib_vec_push.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.
Import VPAddr.

Lemma ejcertP_ok : ltac2:(tb__ "0|0|
S2S35S51S4fS50S1dS29P64S2aS2bA7S37A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S1cS2dA2S2eS0S3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S2S0S4aS38S3S4S6S3dS9A6S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S2S0S4aS38S3S4S6S3eS9A6SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S2S0S4aS38S3S4S6S3cS9A6S10A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S11SaA2S2eS0S8A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47SfSaA2S2eS0S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S10SaA2S2eS0S7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepF_eq : ltac2:(tb__ "0|0|
S2S0S4bS8S31S45S31S45S13S3bA1S33S45S2cS34S45A1A3A3S46S1S8A1A1A3A2S22A3"). Proof. reflexivity. Qed.
Lemma T_grownF_eq : ltac2:(tb__ "0|0|
S2S0S4bS7S31S45S13S5A1S46S1S7A1A1A3A2S21A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S2S30S32S44S44A2A1S49S48S4S38S3dS3A4S3aA2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S2S30S4dA1S4cS48S4S38S3dS3A4S39S3fS3bA2A2S39S14S3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S2S30S32S44S44A2A1S49S48S4S38S3eS3A4S3aA2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|1|
S2S30S32S44S44A2M0A1S49S48S4S38S3cS3A4S41A2S33G0S36S44S44S15S40S5A1A4S34G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S2S30S4dA1S4cS48S4S38S3cS3A4S39S3fS43A2A2S39S14S5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_msk1_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S1aS17A2S2eS0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_msg1_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S18S17A2S2eS0S19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk0_eq : ltac2:(tb__ "0|0|
S2S0S4eSeScS12ScS42S3bA3S1fSdA5S27A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg0_eq : ltac2:(tb__ "0|0|
S2S0S4eSeSbS12SbS15S5A3S1eSdA5S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S28S16A2S2eS0S26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg_eq : ltac2:(tb__ "0|0|
S2S2fS0A1S47S25S16A2S2eS0S23A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_vec_push_eqs.

(* [comment removed for export] *)
Module Lib_vec_push_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "sprop_eqb"; "valuation"; "ss_facts"; "SLit"; "sobj"; "ss_next"; "SVar"; "holds"; "SAlu"; "mkObj"; "DUnknown"; "rw"; "cell"; "obj_wf"; "ss_objs"; "DZero"; "ob_cells"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "pair"; "cons"; "nil"; "Some"; "option"; "None"; "fst"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "ND"; "JA_pre"; "emeasA"; "JA"; "JLA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "kbytes"; "bdP"; "vE"; "B32"; "vC"; "vK"; "vDt"; "spm"; "vV"; "O_vec"; "Pre_vr"; "nd0"; "tv0"; "two47"; "vDn"; "vKn"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_push"; "vC1"; "s_m"; "ndp0"; "Pre_ms"; "L_ms"; "Pre_vp"; "R_v"; "cutsP"; "mid_obj"; "ndpG"; "slot_obj"; "vAp"; "E_msg0"; "E_msk0"; "E_vr"; "E_vr0"; "O_Wp"; "O_alp"; "PD_vr"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "Xk_v"; "exitsP"; "s_v"; "slot_facts"; "vDg"; "vKg"; "xf_mback"; "xf_mcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_vec_push_pf"; "P0_vp"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BXok_d"; "bd_below"; "bd_wpos"; "bxt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_vec_push_pf.Sum"; "basePF"; "JLp"; "Posts_vp"; "basePz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "site_okA"; "T_afterA"; "call_checkTA"; "payA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_memset_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "PostsC"; "robjs_okF"; "xrs_okF"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_push.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_push OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_vec_push_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.
Import VPAddr.

Definition P0_vp (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S27S31Q40M0S16Vr;P11A2A2Z0M1A3A1S2S0S27S31G0S16Vr;PfA2A2G1A3A1F_;S1S91VFF;S31G0S16Vr;PcA2A2Z20A3S91VFF;S31G0S16Vr;PdA2A2Z30A3A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S92ScS1fS30Q40A1A1S8dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S27Sa2VCST;R1A2S1S71Z0R2A2S74R2S9cA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S27Sa2VXGL;R1A2S1S71Z0R2A2S74R2S9cA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1fS1eS1eS27S27A2S27A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JLp (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S3dVAInv;VCST;VXGL;VKc;S70VFB;VFF;A2VFB;VFF;VBX;S38Vnd;Aa").
Definition Posts_vp : list (axst * jpostA) := ltac2:(tb__ "0|1|
S21S1eS4S32A2M0S20S4S32S67S87S54A1A4S21G0S20S4S32S65S87S39S4dS22S1eS1eS8S27A2S8A2A1S22S77A1A3A1A4S21G0S20S4S32S66S87S5bS4fS50A2A1A4S22G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3cVAInv;VCST;VXGL;S2fVKc;Vrho0;S70VFB;VFF;A2VFB;VFF;VBX;S38Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S1eS4S37A2Sa3Fn;") := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;S2fVKc;Vrho0;S70VFB;VFF;A2VFB;VFF;VBX;S38Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S33S28S2fVrho0;Vtp0;S88A5").

Definition basePF (F : list sprop) : Prop := ltac2:(tb__ "0|4|
S1S0S1cS29S9SbSaS11P1eA1M0S48Z30A1A2A1VF;A3S1dA3S1S0S1cS29S9SbSaG0S11PaA1M1A2A1VF;A3S1dA3S1S0S1cS29S9SbSaG1SeS4eA1A2A1VF;A3S1dA3S1S0S1cS29S9SbSaSeZ1A1S43A2A1VF;A3S1dA3S1S0S1cS29S9SbSaS43SeZ1000A1A2A1VF;A3S1dA3S1S0S1cS29S9SbSaS45S46A2A1VF;A3S1dA3S1S0S1cS29S9SbSaS46SeS44A1M2A2A1VF;A3S1dA3S1S0S1cS29S9SbSaS13S85S47S41S46A1M3A3G0A2A1VF;A3S1dA3S1S0S1cS29S9SbSaS47G0A2A1VF;A3S1dA3S1S0S1cS29S9SbSaG3G2A2A1VF;A3S1dA3S1S0S1cS29S9SbSaSeZ7fff7f800000A1G0A2A1VF;A3S1dA3S0S1cS29S9SbSaG0SeZ7fffff800000A1A2A1VF;A3S1dA3A2A2A2A2A2A2A2A2A2A2A2").
Record basePz (rho : valuation) : Prop := BPZ {
  pz_sp : bv_unsigned (rw rho V_TOP) + 48 <= uval rho (SVar 10) <= 2 ^ 47;
  pz_e : 1 <= uval rho vE <= 4096;
  pz_ck : uval rho vC <= uval rho vK <= B32;
  pz_ec : uval rho (kbytes vC) = uval rho vE * uval rho vC;
  pz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK;
  pz_dk : uval rho vDt + uval rho (kbytes vK) <= bv_unsigned (rw rho V_TOP);

  pz_top : 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
ScS27S1S71Z0R1A2S71R1S76R2S11PaA1M0A2A2A2S0S27S76R3S48R2A1A2S75S76R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basePz_of : ltac2:(tb__ "0|0|
ScS1fS9A1S7cS9S12R2A1R1A3S86R2A1S89R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8. pose proof (holds_mem _ _ _ HF B9) as H9. pose proof (holds_mem _ _ _ HF B10) as H10.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf HT1. zf HT2. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold two47, RA.two47, B32 in *.
  rewrite !uval_lit in H3, H4, H5, H7, H10, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia. pose proof (uval_range rho vC). pose proof (uval_range rho vDt).
  assert (EC : uval rho (kbytes vC) = uval rho vE * uval rho vC) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite uval_add_small in H8 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma P0p_now : ltac2:(tb__ "0|1|
ScS8fS2fVrho0;R1A3S70VFB;VFF;Vrho0;A3S1S2S0S27S76R3S46A2Z0M0A3A1S2S0S27S76R4S47A2G0A3A1F_;S1S91VFF;S76R3S49A2Z20A3S91VFF;S76R3S5dA2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C). unfold uval, vK, vDt, vV, vAp. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 13%positive eq_refl).
  auto.
Qed.

Lemma HIN_v : ltac2:(tb__ "0|2|
ScS7fS7cS9S12R2A1SdS5S60A1A1A3S70VFB;VFF;Vrho0;A3S8fS2fVrho0;R4A3S1Sa9VCST;Vrho0;VFB;VFF;R5S22S1eS8S8A2A1M0S22S1eS1eS8S27A2S8A2A1M1S58A8S1SaaVCST;VXGL;Vrho0;VFB;VFF;R5G0G1S68A9S95Sa4VFB;R5G0A3Sa7VFF;R5G1A3S8bS8aR5S58R4A3S6aA2A3A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (P0p_now rho Hav HP0) as (HKD & HV & HA).
  assert (BZ : basePz rho) by (eapply basePz_of; [exact HF | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]). destruct BZ.
  pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. cbn in Ho. destruct Ho as [<-|[]]. left. apply range_lit' in Hr; [|lia|lia]. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; rewrite uval_lit in Ha by lia; left.
    + eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with vK. change (wsub_get s_v 15) with vDt. change (wsub_get s_v 12) with vV. change (wsub_get s_v 14) with vAp.
    split; [exact HKD|]. split.
    + destruct HV as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|a|
S4S1fSfA1M0S8S8ScS0G0R4S21SfS4aR3S45R2S43A4S21SfS63S21SfS14R3SeZ0M1A1M2S41S45A1M3S22S17A1M4S15A5S21SfS14R3S13S85G3S43A3S41R2A1G4S15A5S21SfS14S11PaA1SeN30A1G2S1bS7eSfU4R4S62A4A1S15A5S22SfA1A3A3A3A3A3A3S0S1fS1eS8S8A2M5A1S6R6A1S21G5S20S8S8S49SeZ20A1A4M6S21G5S20S8S8S5dSeZ30A1A4M7S21G5G6S21G5G7S21G5S20S8S8R4S41R3A1A4S22G5A1M8A3A3A3A3A3A3S86SdS5R7A1A1A1S0S1cS29S9SbSaS52R5A2A1SdS5R8A1A1A3S1dA3S0S1cS29S9SbSaS13S85R7S41R6A1A3S11P1eA1M9A2A1SdS5R9A1A1A3S1dA3S0S1cS29S9SbSaR7SeS44A1A2A1SdS5RaA1A1A3S1dA3S0S1cS29S9SbSaR9G9A2A1SdS5RbA1A1A3S1dA3ScS7cS9S12R1A1SdS5RdA1A1A3S8fS2fVrho0;R2A3S70VFB;VFF;Vrho0;A3S2S0S27S76R4ReA2G1A3A1F_;F_;F_;Frho;S98VAInv;VCST;VXGL;S2fVrho0;S70VFB;VFF;A2VFB;VFF;RdS53RdRbRaA3RcR9S39S21G5S20S8S8RbS41RaA1A4G8A3S22S1eS1eS8S27A2S8A2A1S42S52RaA2A3S25S27A1S92S7fS3Lms;LAi;AfF_;F_;F_;F_;F_;F_;F_;F_;Frho;Fk;Fd;FR;FE;").
Proof.
  intros E R d k rho HR HX HB HCk Hdk Hk32 Hdac Hd Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. destruct (P0p_now rho Hav HP0) as (HKD & HV & HA).
  pose proof (basePz_of rho _ HF HB) as [Bsp Be Bck EC EK Bdk Btop]. apply T_ok_rw in HTK as [HTK HTR].
  pose proof (holds_mem _ _ _ HF HCk) as F1. pose proof (holds_mem _ _ _ HF Hdk) as F2. pose proof (holds_mem _ _ _ HF Hk32) as F3. pose proof (holds_mem _ _ _ HF Hdac) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in F2, F4. unfold B32 in *. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vC) as RC. pose proof (uval_range rho d) as Rd.
  unfold vC1 in F1. rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (EKk : uval rho (kbytes k) = uval rho vE * uval rho k) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite uval_add_small in F2 by (rewrite EKk; nia).
  specialize (Hd rho HF Hav HP0).
  assert (ECk : uval rho vE * uval rho vC + uval rho vE <= uval rho vE * uval rho k).
  { replace (uval rho vE * uval rho vC + uval rho vE) with (uval rho vE * (uval rho vC + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }

  cbn [nd_tv] in HN. assert (Hnz : tnz rho (d, kbytes k)) by (unfold tnz; cbn [fst]; unfold uval in Hd; exact Hd).
  destruct (proj1 (Forall_forall _ _) HN (d, kbytes k) ltac:(left; reflexivity) Hnz) as (_ & HinL & _). unfold tvv in HinL. cbn [fst snd] in HinL.
  change (bv_unsigned (eval rho d)) with (uval rho d) in HinL. change (bv_unsigned (eval rho (kbytes k))) with (uval rho (kbytes k)) in HinL.
  assert (INBLK : forall a, uval rho d <= a < uval rho d + uval rho (kbytes k) -> cmaddrA CST Ai None a).
  { intros a Ha. right; right; left. exists (uval rho d), (uval rho (kbytes k)). split; [exact HinL|]. split; [discriminate | lia]. }
  split; [|split; [|exact I]].
  - intros o a Ho Hr. rewrite HR in Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
    + unfold O_alp in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
    + apply INBLK. unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho (kbytes vC)) in Hr by (rewrite EC; lia). rewrite EC in Hr. rewrite EKk. unfold uval in *. lia.
    + apply INBLK. unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      rewrite (soff_smallu rho (kbytes k)) in Hr by (rewrite EKk; lia).
      rewrite (soff_smallu rho (SAlu ALU_ADD (kbytes vC) vE)) in Hr by (rewrite uval_add_small by (rewrite EC; lia); rewrite EC; lia).
      rewrite uval_add_small in Hr by (rewrite EC; lia). rewrite EC, EKk in Hr. rewrite EKk. unfold uval in *. lia.
    + left. apply range_lit' in Hr; [|lia|lia]. lia.
  - intros r a Hr Ha. rewrite HX in Hr. cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; left.
    + rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
    + rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
    + rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
    + rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
    + apply INBLK. exact Ha.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|0|
ScS1fS9A1S8S7cS9S12R3A1R2A3S86R3A1S0S1cS29S9SbSaS52R3A2A1R4A3S1dA3S0S1cS29S9SbSaR4SeS44A1A2A1R5A3S1dA3S7cS9S12R7A1S6bR5A1A3F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF HB H1 H2. pose proof (basePz_of rho _ HF HB) as [Bsp Be Bck EC EK Bdk Btop].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in F2 by lia.
  pose proof (uval_range rho vC) as RC.
  unfold vC1 in F1. rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (EKk : uval rho (kbytes k) = uval rho vE * uval rho k) by (unfold kbytes; apply uval_mul_small; nia).
  assert (ECk : uval rho vE * uval rho vC + uval rho vE <= uval rho vE * uval rho k).
  { replace (uval rho vE * uval rho vC + uval rho vE) with (uval rho vE * (uval rho vC + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  unfold slot_facts. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite EC, EKk. nia.
  - rewrite uval_add_small by (rewrite EC; nia). rewrite EC, EKk. nia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
ScOF_;S1fS9A1S1fS77A1S0S1cS7aR1A1S1dA3S9bS2fVrho0;R4R3SeZ0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S27S1fS30Q40A1A1S80F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2dS4ScS1fS30Q40A1A1S80S7cS9S12R3A1SdS5R4A1A1A3VTR;S2cS28R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S80S80S80S83R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2dS2dS4S4S8cS1fSfA1M0S1fS1eS4S32A2M1A1S1fS1eS8S8A2M2A1S80ScS1fS30Q40A1A1M3G2S2aG2R1R5A3S2aG2R2S6RbA1A3F_;Fr;S0S24G0A1S35RaR9R8A3S23G0R7A2A3S0S1cS34RbRaR9R8S7dG1S4S26S4S32A2R7A4A5S1dA3ScG3VTR;S2cS28RfRdR2R1A5S33S28S10S5RdA1A1R2R1RaA5A2Ftp1;Frho1;S1fS8eA1M4S7fS8dS2eS28R9R8R10S20G4S93R3S94R2R1A2A4A5R13RaR9R4R2A4R13S8bS8aRbRfS84R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S32G4S7fS8dScG3G4S7fS8dS2aG1S20S4S32RaR9A4R14A3S2eS28R12R11R19S20G4S93R9S94R8R7A2A4A5R1cR13R12RaR8A4S8fS10S5R1aA1A1S8bS8aR14R18S84R9R13RaA3A3R19A2R8A3S2eS28R9R8ReS20G4S93R7S94R6R5A2A4A5ReS8bS8aR16R1aS84RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sa5R17S84RcR16RdA3R1bR1cR1dR10R1eR19RbA9ScS90R18S84RdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S2cS28S36R11S8bS8aR19R1dS84ReR18RfA3A3R1eA2R18RdRcA5Sa6R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2cS28R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S92ScS1fS30Q40A1A1VTR;S2cS28S9fVAInv;R3VKc;A3S55R2R1A5S33S28S2fR2R1S21S1eS4S32A2M0S20S4S32S56S9eVAInv;VCST;VXGL;R3VKc;A5A4S22G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
S1fS1eS27S27A2M0A1S1fS1eG0S27A2A1S7bScS1fS30Q40A1A1S78Z3R3A2VTR;S2cS28S3aVAInv;VCST;VXGL;VKc;S95R6R5A2R6R5R4S38S4cAaS4bR3R2A5S33S28S2fR3R2Sa8VAInv;VCST;VXGL;VKc;S95S38S64R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S37S1eS27S8A2M0ScS1fS30Q40A1A1M1S27G1S2aS1eS1eS4S37A2M2G0A2S20G2G0S20S4S37R7R6A4R5A4S59A3S1S71Z0S3bS20G2G0S20S4S37R8R7A4R6A4R5A2M3A2S74G3R3A2A2VTR;S2cS28VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S37ScS1fS30Q40A1A1M0S27G0S2aS1eS4S32A2S20S4S32R6S87R5A1A4S88A3VTR;S2cS28VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsP exitsP Posts_vp PD_vr]; do n right; left; reflexivity.

Lemma X_E_vr : ltac2:(tb__ "0|1|
ScS1fS30Q40A1A1M0S27G0S71S72Z5aS73Z2Z40A2A2R2A2VTR;S2cS28VJAv;S54A1S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndp0) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_vr nd0 PD_vr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [] tv0 [] (bdP vC1 vK) [] ANone (FAM b tp0)).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_v rho ms HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am nd0 ndN ndG ND am_subst app].
    +   rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_keepF ndp0 (80, z0)); [innth 1 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep0 T_keep tp' w T_keep_eq Hw) as Hw1.
      rewrite <- T_keepF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ vK HF2); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
      *
        assert (TNZ : tnz rho' (vDt, kbytes vK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & _ & _ & _ & HP0' & _). destruct HP0' as [HKD _]. destruct Hav' as [Hrw _].
          factz HF2 (SPUle vC1 vK) F1. factz HF2 (SPUle vC vK) F0. factz HF2 (SPUle vK (SLit B32)) F2.
          unfold B32 in F2. rewrite uval_lit in F2 by lia. unfold vC1 in F1. pose proof (uval_range rho' vC) as RC.
          rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
          unfold tnz. cbn [fst]. change (eval rho' vDt) with (rw rho' 15%positive).
          change (uval rho' vK) with (bv_unsigned (rw rho' 17%positive)) in F1.
          rewrite <- (Hrw 15%positive) by reflexivity. apply HKD. rewrite (Hrw 17%positive) by reflexivity. lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vDt, kbytes vK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, hse_fact. cbn [fst snd]. do 5 right. left. reflexivity.
    +   rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER T_fail (ND tv0 [] []) (80, z0)); [innth 2 | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_vback rho' T_fail0 T_fail tp' w T_fail_eq Hw).
    +   rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_grownF (ndpG vDg vKg) (80, z0)); [innth 3 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown0 T_grown tp' w T_grown_eq Hw) as Hw1.
      rewrite <- T_grownF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
      apply (slot_holds rho' _ vKg HF2); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.

Lemma X_E_m : ltac2:(tb__ "0|f|
S4S4S4S4S4S4S1fSfA1M0S8S8ScS1fS30Q40A1A1M1S27G1S0S24S4A1M2S97RdS6fA2S23S4RcA2A3S0S4S7RdS96S5RdA1U4M3S5cR7A1A3A2RcA3S0S24SfA1M4S2bSfS19S5ReA1A1G3A3S23SfS14R8S41S45A1M5S13S85G5S43A3S22S17A1M6S15A5A2A3S0S1cS18S10S5RfA1A1S5cR9A1A2S1dA3S86SdS5R10A1A1A1S0S1cS29S9SbSaRbS11P1eA1M7A2A1SdS5R11A1A1A3S1dA3S0S1cS29S9SbSaS52RbA2A1SdS5R12A1A1A3S1dA3S0S1cS29S9SbSaRcSeS44A1M8A2A1SdS5R13A1A1A3S1dA3S0S24G0A1S35R13S55S53R13ReRdA3A3S23G0RfA2A3S0S1cS34R14S55S53R14RfReA3R10S21S4S56S22S4A1A3A5S1dA3S0S1cS9aS2fS53R15R10RfA3A2S1dA3S0S1cSabS2fS10S5R16A1A1A2S1dA3S0S1cS3eS10S5R17A1A1S39S21S1eS8S8A2M9S20S8S8R12S41R11A1A4S22G9A1MaA3S22S1eS1eS8S27A2S8A2A1MbS42S52R11A2A3A2S1dA3S0S1cS79S10S5R18A1A1S42S52R12A2A2S1dA3S98VAInv;VCST;VXGL;S2fVrho0;S70VFB;VFF;A2VFB;VFF;R19S53R19R14R13A3R15R12S39S21G9S20S8S8R14S41R13A1A4GaA3GbS42S52R13A2A3S25S27A1S92S7fS3Lms;LAi;AfS0S4S99S55R1aS53R1aR15R14A3R16S56A5R19A3S0G4S2bSfS19S5R1aA1A1U1McA3S23SfS14S13S85R16G5A3SeZ0A1S43G6S1aA5A2A3S0S4S7R1bS96S5R1bA1GcS5aR17A1A3A2R1aA3S0S1cS18S10S5R1cA1A1S5aR18A1A2S1dA3S86SdS5R1dA1A1A1S0S1cS29S9SbSaR1aG7A2A1SdS5R1eA1A1A3S1dA3S0S1cS29S9SbSaS52R1aA2A1SdS5R1fA1A1A3S1dA3S0S1cS29S9SbSaR1bG8A2A1SdS5R20A1A1A3S1dA3S0G2S97R20S6eA2S23S4R1fA2A3S2aS1eS1eS4S37A2MdS1eS27S8A2MeA2S20GdGeS20S4S37R20S39S21G9S20S8S8R1eS41R1dA1A4GaA3GbS42S52R1dA2A3A4S20S27S8Z3cS51A4A4S59A3S71S72Z46S73Z2Z40A2A2R1bA2VTR;S2cS28VJAv;S39S21G9S20S8S8R20S41R1fA1A4GaA3GbS42S52R1fA2A3A1R27R1eR1dA5VFAM;R1cR1bA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fd;FR;FTm;FTm1;FTm0;FE;FE1;FE0;").
Proof.
  intros E0 E1 E Tm0 Tm1 Tm R d k rho tp b tp0 HE1 HE Hp4 Hwf HB1 Hd1 Hc1 Hk1 He Hchk Htp Hnf Hnb Hbr HSITE HTm0 Hq1 HTm1 Hwf2 HB2 Hd2 Hc2 Hk2 HTm HinM Hb.

  assert (RNG : forall r F, Forall (holds r) F -> basePF F -> existsb (sprop_eqb (SPUle d (SVar 30))) F = true ->
            existsb (sprop_eqb (SPUle vC1 k)) F = true -> existsb (sprop_eqb (SPUle k (SLit B32))) F = true ->
            uval r (SAlu ALU_ADD d (kbytes vC)) = uval r d + uval r (kbytes vC)
            /\ soff r (kbytes vC) = uval r (kbytes vC) /\ soff r (SAlu ALU_ADD (kbytes vC) vE) = uval r (kbytes vC) + uval r vE /\ soff r vE = uval r vE).
  { intros r F HF HB Hd Hc Hk. pose proof (basePz_of r _ HF HB) as [Bsp Be Bck EC EK Bdk Btop].
    pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hc) as F2. pose proof (holds_mem _ _ _ HF Hk) as F3. zf F1. zf F2. zf F3.
    repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. change (uval r (SVar 30)) with (bv_unsigned (rw r V_TOP)) in F1. unfold B32 in *.
    rewrite uval_lit in F3 by lia. pose proof (uval_range r vC) as RC. pose proof (uval_range r d) as Rd.
    unfold vC1 in F2. rewrite uval_add_small in F2 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F2 by lia.
    assert (A1 : uval r (SAlu ALU_ADD (kbytes vC) vE) = uval r (kbytes vC) + uval r vE) by (apply uval_add_small; rewrite EC; nia).
    split; [apply uval_add_small; rewrite EC; nia|]. split; [apply soff_smallu; rewrite EC; nia|]. split; [|apply soff_smallu; lia].
    rewrite <- A1. apply soff_smallu. rewrite A1, EC. nia. }
  eapply TR_pre with (P := SPA segs (JAv (ND [(d, kbytes k)] [] (bdP vC1 k))) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mcall rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE.
    apply (SPA_reshape segs _ rho E1 4 _ _ tp w Hp4); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw1].
    intros HF. destruct (RNG rho _ HF HB1 Hd1 Hc1 Hk1) as (A1 & A2 & A3 & A4).
    unfold slot_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by lia. rewrite A2, A3, A4.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (kbytes vC)))) with (uval rho (SAlu ALU_ADD d (kbytes vC))). rewrite A1. unfold uval. lia. }
  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E (s_m E d k) R rho tp (ND [(d, kbytes k)] [] (bdP vC1 k)) (bdP vC1 k) (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnf.
  - exact Hnb.
  - exact Hbr.
  - cbn [nd_bd]. apply payA_same. reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact HSITE.
  - intros Ai tr ms md Hsm HM HX. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E memset_pc (s_m E d k) R rho tp tr ms md Hsm HM HX He).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr]. rewrite HTm0.
    eapply TR_pre; [|apply (REENTER Tm (ND [(d, kbytes k)] [] (bdP vC1 k)) (60, z0)); [exact HinM | meas]].
    intros w Hw.
    assert (Hw1 : SPA segs (JAv (ND [(d, kbytes k)] [] (bdP vC1 k))) Tm1 rho' tp' w).
    { rewrite <- HTm1. apply (SPA_reshape segs _ rho' Tm0 1 _ _ tp' w Hq1); [reflexivity | reflexivity | reflexivity | exact Hwf2 | | exact Hw].
      intros HF. destruct (RNG rho' _ HF HB2 Hd2 Hc2 Hk2) as (A1 & A2 & A3 & A4).
      unfold mid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by lia. rewrite A2, A3, A4.
      change (bv_unsigned (eval rho' (SAlu ALU_ADD d (kbytes vC)))) with (uval rho' (SAlu ALU_ADD d (kbytes vC))). rewrite A1. unfold uval. lia. }
    exact (SPA_axforms segs _ xf_mback rho' Tm1 Tm tp' w HTm Hw1).
Qed.

Lemma X_E_msk : ltac2:(tb__ "0|1|
ScS1fS30Q40A1A1M0S27G0S71S72Z46S73Z2Z40A2A2R2A2VTR;S2cS28VJAv;S54A1S5fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndp0, tv0.
  apply (X_E_m E_msk0 E_msk1 E_msk T_mk0 T_mk1 T_mk R_mk vDt vK rho tp b tp0 E_msk1_eq eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply (site_m E_msk R_mk vDt vK rho); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros r HF Hav HP0. destruct (P0p_now r Hav HP0) as (HKD & _). apply HKD.
    factz HF (SPUle vC1 vK) HCK. unfold vC1 in HCK. pose proof (uval_range r vC).
    destruct (Z.eq_dec (uval r vK) 0) as [E0|]; [|assumption]. exfalso. rewrite E0 in HCK.
    rewrite uval_add_small in HCK by (rewrite uval_lit by lia; factz HF (SPUle vC vK) HCK2; lia). rewrite uval_lit in HCK by lia. lia.
  - exact T_mk0_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_mk_eq.
  - innth 4.
  - exact Hb.
Qed.
Lemma X_E_msg : ltac2:(tb__ "0|1|
ScS1fS30Q40A1A1M0S27G0S71S72Z46S73Z2Z40A2A2R2A2VTR;S2cS28VJAv;S5bS6cS6dA2A1S5eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndpG.
  apply (X_E_m E_msg0 E_msg1 E_msg T_mg0 T_mg1 T_mg R_mg vDg vKg rho tp b tp0 E_msg1_eq eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply (site_m E_msg R_mg vDg vKg rho); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
      | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros r HF Hav HP0. factz HF (SPNot (SPBranch BC_EQ vDg (SLit 0))) HD. rewrite uval_lit in HD by lia. exact HD.
  - exact T_mg0_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_mg_eq.
  - innth 5.
  - exact Hb.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S37S1eS27S8A2M0ScS1fS30Q40A1A1M1G1S2aS1eS1eS4S37A2M2G0A2S20G2G0S20S4S37R6R5A4R4A4S69A3VTR;S2cS28VJAv;R6A1R7R4R3A5VFAM;S3bS20G2G0S20S4S37R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsP] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <-.
  - apply X_E_vr. meas.
  - apply X_E_msk. meas.
  - apply X_E_msg. meas.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S40S28VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sa0S28S9dVAInv;VCST;VXGL;A5").

Theorem vec_push_sum : ltac2:(tb__ "0|0|
S1fS30Q40A1A1S82S28Vok;S2cS28S3aVAInv;VCST;VXGL;VKc;S70VFB;VFF;A2VFB;VFF;VBX;S38S54AaS57Vrho0;R1A5S33S28S2fVrho0;R1S88A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc ALA FUEL_vp cutpcs_vp 100
                (map edropA cutsP) (map edropA exitsP) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertP_ok))
         with (ndT := ndp0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsP)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue ok (map edropA cutsP) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vp FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vp P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sa1S28S9dVAInv;VCST;VXGL;A5").

Theorem vec_push_sum_ex : ltac2:(tb__ "0|0|
S1fS30Q40A1A1S81S28S2cS28S3aVAInv;VCST;VXGL;VKc;S70VFB;VFF;A2VFB;VFF;VBX;S38S54AaS57Vrho0;R1A5S33S28S2fVrho0;R1S88A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc ALA FUEL_vp cutpcs_vp 100 cutsP exitsP (Q tp0) ejcertP_ok)
         with (ndT := ndp0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue) cutsP) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue cutsP T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vp FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vp P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_push_pf.

