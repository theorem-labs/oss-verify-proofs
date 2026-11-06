(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2"; "vSZ"; "vH"; "vCAPl"; "z0"; "vP"; "vSRC"; "vK"; "tv0"; "p_fit"; "X_ad"; "vHD"; "O_F"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "vLS"; "vU"; "X_nohead"; "ndO"; "ra_an"; "vUc"; "C_loop"; "C_slow"; "base_fit"; "nd0"; "ndL"; "ndS"; "pN"; "vI"; "vNXl"; "E_m"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "slow_facts"; "ug_facts"; "vAR"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "c8"; "cutpcs_ad"; "ghK"; "loop_facts"; "loop_regs"; "nP"; "ndF"; "ndK"; "ndM"; "nsrc"; "ok_facts"; "pad_fit"; "slow_regs"; "tv_m"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_retF"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0x908e0.
  Definition ad_open : Z := 0x9b978.
  Definition ad_slow : Z := 0x9b9fc.
  Definition ad_K : Z := 0x9ba28.
  Definition ad_loop : Z := 0x908fc.
  Definition ad_xit : Z := 0x9093c.
  Definition ad_ret : Z := 0x90978.
  Definition ad_retF : Z := 0x9095c.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S24SdZ0A1S30S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1fS2S10A1S14A5").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S5SaSa5S0SaScSdZ1A1S1fA2S0SaScS1fS30A2S0SaScS30SdS98Z2Z20A2A1A2S0SaScSdZ1000A1S24A2S0SaScSfS1cS24S30A3SbP1eA1M0A2S0SaScS24G0A2S2SaA1A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S0G0S1S9S9S24S30A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|1|
S12Sa2S8fS92S0S3S4S9A2M0S1S4S9UbS1fA4S0G0S1S4S9UcSdZ10A1A4S0G0S1S4S9U1bS24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eS90S7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87Z2S89S1fA1M3A4S2G2A1M4A3Z60A4S0S86S88G1G0S0G2S1S1aS87Z4G3A4G4A3Z40A4S2S86A1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa3S0S1aSa0S0S1aS9cS0S1aSa6S0S1aS9dS0S1aSa1S0S1aS9eS0S1aS9fS2S1aA1A3A3A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa4S81Vk;S96S52S6fVS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S85S29S7eS4cS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S8fS17S82S32A1A1S0S3S4S9A2M0S1S4S9UbSbP65A1A4S0G0S1S4S9UdSbP66A1A4S0G0S1S4S9UeSbP67A1A4S0G0S1S4S9UfSbP68A1A4S0G0S1S4S9U10SbP69A1A4S0G0S1S4S9U11SbP6aA1A4S0G0S1S4S9U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScSdZ10001A1SfS1cS4dSfS1cS1fSdZ10A1A3A3A2S0SaScS4dSdS98Z2Z28A2A1A2S2SaA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S93S12Sa0S7aS8eS11S6S9A1S16S82S32A1A1S5SaS4aS49A3P6dS7A9S28A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSdZ10000A1M0S25A2S0SaScSfS1cS1fSdZ10M1A1A3S25A2S0SaScS25SfS1cS1fG0A3A2S0SaScS25SdS9aS98Z2Z20A2G1A2A1A2S0SaScSdZ1A1S8cS25A1A2S2SaA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S93S12S9cS8fS17S82S59A1M0A1S0S3S4S9A2M1S1S4S9U14S25A4S2G1A1A3A2S8eS11S6S9A1S16G0A1S0SaS70S5SaS53S5SaS4aS49A3A3A3P70S7A9S28A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1fSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5S86S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87G0S89S8cS25A1A1A4S2G2A1A3G1A4S0S86S8aG1G0S9bZ2S8bA2A3S2S86A1A3A3S8dS1fA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS7dA4S97PaS82S3fA1S82S56A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SbS3cA1S8cS25A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5S86S0S86S8aZ0Z1S8bA3S2S86A1A3S8dS1fA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S85S20S3eS21S0S3S9S9A2M0S1S9S9S23S1fA4S2G0A1A3A4").
Definition ra_an : Z := 0x908e4.
Definition nsrc : sv := ltac2:(tb__ "0|0|
SfS1eS24SdZffffffffffffffffA1A3").
Definition nP : sv := SAlu ALU_XOR vP (SLit 18446744073709551615).
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9S3dS0S9S77S0S9S73S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9SbP29A1S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9S24S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SaS19S3dS1fA2S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3M0SbP1eA1M1A2S0SaScS20G1A2S0SaScSdZ1000A1M2S20A2S0SaS13P65Z4M3A2S0SaScSfS1cS20SdZ20A1A3S23A2S0SaScSfS1cS23S1fA3M4G0A2S0SaScG2S23A2S0SaScG4G1A2S0SaScS23G1A2S0SaS13P69G3A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S93S12S9dS72S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS71S5SaS45S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS29SdZ20A1A3S31A3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS1dS27S38A3").
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS79S1fA3S31A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS38S27A2S0SaScS27SfS1cS38SdZfA1M0A3A2S0SaScSdZ1000A1S27A2S0SaScS27SbP1eA1M1A2S0SaScSfS1cS27S1fA3M2SfS1cS29S8cS4cA1A3A2S0SaScG2G1A2S0SaScSfS1cS29SdZ20A1A3S27A2S0SaScS7cSfS1cS31SfS1cS1fG0A3A3A2S2SaA1A3A3A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
ScSdZ10001A1SfS1cS31SfS1cS1fSdZ10A1A3A3A2").
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
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S55S6eZ0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSbS3cA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSfS1cS48S1fA3M0SfS1cSbS3cA1S8cS25A1A3A2S0SaScG0SbP1eA1M1A2S0SaScS48G1A2S2SaA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9SbP7cA1S0S9SbP7dA1S0S9SbP7eA1S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9SbP29A1S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9S24S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3SbP1eA1M0A2S0SaScS20G0A2S0SaScSdZ1000A1M1S20A2S0SaS13P65Z4M2A2S0SaScG1S23A2S0SaScSfS1cS23S1fA3G0A2S0SaScS23G0A2S0SaS13P69G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S93S12Sa1S80S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS7fS5SaS45S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").

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
S93S12S9fS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSdZ0A1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U1bS24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eSa7S7A9S28A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SaScSdZ1000A1M0SbP8cM1A1M2A2S0SaScSfS1cG2S1fA3SbP1eA1M3A2S0SaS13G1Z4A2S0SaScG0SbP8dA1M4A2S0SaScG4G3A2S2SaA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S93S12S9eS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSbP8cA1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U1bS24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cSbP8dA1A1S0SeS2dS2SeA1A3A3A3A3S94A3S5SaS78S2eA3P8eS7A9S28A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S97P64S82S5dA1S82S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S97P64S82S65A1S82S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS31A4S97P64S82S5fA1S82S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S97P64S82S32A1S82S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S97P64S82S63A1S82S42A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S4eS66A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6cS69A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6dS2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6aS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S84S7bS2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6bS67A4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S68A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S43S39A4S1S1aS9Z64S22A4A4S0G2S1G0G1S1S81S83S51S33A4S1S1aS9Z5aS22A4A4S0G2S1G0G1S1S81S83S37S3bA4S1S1aS9Z50S22A4A4S0G2S1G0G1S1S81S83S4fS46A4S1S1aS9Z4bS22A4A4S0G2S1G0G1S1S81S83S57S76A4S1S1aS9Z41S22A4M3A4S0G2S1G0G1S1S81S83S58S47A4G3A4S0G2S1G0G1S1S81S83S36S3aA4S1S1aS9Z32SfS1dS1fS3dA3A4A4S0G2S1G0G1S1S81S83S50S3aA4S1S1aS9Z2dS22A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S61S39A4S1S1aS9Z5fS22A4M3A4S0G2S1G0G1S1S81S83S32S39A4G3A4S0G2S1G0G1S1S81S83S60S33A4S1S1aS9Z55S22A4M4A4S0G2S1G0G1S1S81S83S5cS33A4G4A4S0G2S1G0G1S1S81S83S5eS33A4G4A4S0G2S1G0G1S1S81S83S5aS3bA4S1S1aS9Z4eS22A4M5A4S0G2S1G0G1S1S81S83S5bS3bA4G5A4S0G2S1G0G1S1S81S83S3fS46A4S1S1aS9Z46S22A4A4S0G2S1G0G1S1S81S83S64S47A4S1S1aS9Z3cS22A4A4S0G2S1G0G1S1S81S83S62S3aA4S1S1aS9Z28S22A4A4S0G2S1G0G1S1S81S83S54S74A4S1S1aS9Z0S22A4M6A4S0G2S1G0G1S1S81S83S42S75A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_finalize_shape_dup2.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3"; "vSZ"; "vH"; "vCAPl"; "z0"; "vP"; "vSRC"; "vK"; "tv0"; "p_fit"; "X_ad"; "vHD"; "O_F"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "vLS"; "vU"; "X_nohead"; "ndO"; "ra_an"; "vUc"; "C_loop"; "C_slow"; "base_fit"; "nd0"; "ndL"; "ndS"; "pN"; "vI"; "vNXl"; "E_m"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "slow_facts"; "ug_facts"; "vAR"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "c8"; "cutpcs_ad"; "ghK"; "loop_facts"; "loop_regs"; "nP"; "ndF"; "ndK"; "ndM"; "nsrc"; "ok_facts"; "pad_fit"; "slow_regs"; "tv_m"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_retF"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0x90a64.
  Definition ad_open : Z := 0x9b978.
  Definition ad_slow : Z := 0x9b9fc.
  Definition ad_K : Z := 0x9ba28.
  Definition ad_loop : Z := 0x90a80.
  Definition ad_xit : Z := 0x90ac0.
  Definition ad_ret : Z := 0x90b04.
  Definition ad_retF : Z := 0x90ae0.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S24SdZ0A1S30S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1fS2S10A1S14A5").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S5SaSa5S0SaScSdZ1A1S1fA2S0SaScS1fS30A2S0SaScS30SdS98Z2Z20A2A1A2S0SaScSdZ1000A1S24A2S0SaScSfS1cS24S30A3SbP1eA1M0A2S0SaScS24G0A2S2SaA1A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S0G0S1S9S9S24S30A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|1|
S12Sa2S8fS92S0S3S4S9A2M0S1S4S9UbS1fA4S0G0S1S4S9UcSdZ10A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eS90S7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87Z2S89S1fA1M3A4S2G2A1M4A3Z60A4S0S86S88G1G0S0G2S1S1aS87Z4G3A4G4A3Z40A4S2S86A1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa3S0S1aSa0S0S1aS9cS0S1aSa6S0S1aS9dS0S1aSa1S0S1aS9eS0S1aS9fS2S1aA1A3A3A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa4S81Vk;S96S52S6fVS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S85S29S7eS4cS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S8fS17S82S32A1A1S0S3S4S9A2M0S1S4S9UbSbP65A1A4S0G0S1S4S9UdSbP66A1A4S0G0S1S4S9UeSbP67A1A4S0G0S1S4S9UfSbP68A1A4S0G0S1S4S9U10SbP69A1A4S0G0S1S4S9U11SbP6aA1A4S0G0S1S4S9U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScSdZ10001A1SfS1cS4dSfS1cS1fSdZ10A1A3A3A2S0SaScS4dSdS98Z2Z28A2A1A2S2SaA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S93S12Sa0S7aS8eS11S6S9A1S16S82S32A1A1S5SaS4aS49A3P6dS7A9S28A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSdZ10000A1M0S25A2S0SaScSfS1cS1fSdZ10M1A1A3S25A2S0SaScS25SfS1cS1fG0A3A2S0SaScS25SdS9aS98Z2Z20A2G1A2A1A2S0SaScSdZ1A1S8cS25A1A2S2SaA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S93S12S9cS8fS17S82S59A1M0A1S0S3S4S9A2M1S1S4S9U14S25A4S2G1A1A3A2S8eS11S6S9A1S16G0A1S0SaS70S5SaS53S5SaS4aS49A3A3A3P70S7A9S28A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1fSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5S86S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87G0S89S8cS25A1A1A4S2G2A1A3G1A4S0S86S8aG1G0S9bZ2S8bA2A3S2S86A1A3A3S8dS1fA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS7dA4S97PaS82S3fA1S82S56A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SbS3cA1S8cS25A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5S86S0S86S8aZ0Z1S8bA3S2S86A1A3S8dS1fA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S85S20S3eS21S0S3S9S9A2M0S1S9S9S23S1fA4S2G0A1A3A4").
Definition ra_an : Z := 0x90a68.
Definition nsrc : sv := ltac2:(tb__ "0|0|
SfS1eS24SdZffffffffffffffffA1A3").
Definition nP : sv := SAlu ALU_XOR vP (SLit 18446744073709551615).
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9S3dS0S9S77S0S9S73S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SaS19S3dS1fA2S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3M0SbP1eA1M1A2S0SaScS20G1A2S0SaScSdZ1000A1M2S20A2S0SaS13P65Z4M3A2S0SaScSfS1cS20SdZ20A1A3S23A2S0SaScSfS1cS23S1fA3M4G0A2S0SaScG2S23A2S0SaScG4G1A2S0SaScS23G1A2S0SaS13P69G3A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S93S12S9dS72S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS71S5SaS45S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS29SdZ20A1A3S31A3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS1dS27S38A3").
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS79S1fA3S31A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS38S27A2S0SaScS27SfS1cS38SdZfA1M0A3A2S0SaScSdZ1000A1S27A2S0SaScS27SbP1eA1M1A2S0SaScSfS1cS27S1fA3M2SfS1cS29S8cS4cA1A3A2S0SaScG2G1A2S0SaScSfS1cS29SdZ20A1A3S27A2S0SaScS7cSfS1cS31SfS1cS1fG0A3A3A2S2SaA1A3A3A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
ScSdZ10001A1SfS1cS31SfS1cS1fSdZ10A1A3A3A2").
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
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S55S6eZ0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSbS3cA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSfS1cS48S1fA3M0SfS1cSbS3cA1S8cS25A1A3A2S0SaScG0SbP1eA1M1A2S0SaScS48G1A2S2SaA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9SbP7cA1S0S9SbP7dA1S0S9SbP7eA1S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3SbP1eA1M0A2S0SaScS20G0A2S0SaScSdZ1000A1M1S20A2S0SaS13P65Z4M2A2S0SaScG1S23A2S0SaScSfS1cS23S1fA3G0A2S0SaScS23G0A2S0SaS13P69G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S93S12Sa1S80S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS7fS5SaS45S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").

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
S93S12S9fS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSdZ0A1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eSa7S7A9S28A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SaScSdZ1000A1M0SbP8cM1A1M2A2S0SaScSfS1cG2S1fA3SbP1eA1M3A2S0SaS13G1Z4A2S0SaScG0SbP8dA1M4A2S0SaScG4G3A2S2SaA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S93S12S9eS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSbP8cA1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cSbP8dA1A1S0SeS2dS2SeA1A3A3A3A3S94A3S5SaS78S2eA3P8eS7A9S28A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S97P64S82S5dA1S82S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S97P64S82S65A1S82S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS31A4S97P64S82S5fA1S82S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S97P64S82S32A1S82S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S97P64S82S63A1S82S42A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S4eS66A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6cS69A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6dS2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6aS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S84S7bS2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6bS67A4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S68A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S43S39A4S1S1aS9Z64S22A4A4S0G2S1G0G1S1S81S83S51S33A4S1S1aS9Z5aS22A4A4S0G2S1G0G1S1S81S83S37S3bA4S1S1aS9Z50S22A4A4S0G2S1G0G1S1S81S83S4fS46A4S1S1aS9Z4bS22A4A4S0G2S1G0G1S1S81S83S57S76A4S1S1aS9Z41S22A4M3A4S0G2S1G0G1S1S81S83S58S47A4G3A4S0G2S1G0G1S1S81S83S36S3aA4S1S1aS9Z32SfS1dS1fS3dA3A4A4S0G2S1G0G1S1S81S83S50S3aA4S1S1aS9Z2dS22A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S61S39A4S1S1aS9Z5fS22A4M3A4S0G2S1G0G1S1S81S83S32S39A4G3A4S0G2S1G0G1S1S81S83S60S33A4S1S1aS9Z55S22A4M4A4S0G2S1G0G1S1S81S83S5cS33A4G4A4S0G2S1G0G1S1S81S83S5eS33A4G4A4S0G2S1G0G1S1S81S83S5aS3bA4S1S1aS9Z4eS22A4M5A4S0G2S1G0G1S1S81S83S5bS3bA4G5A4S0G2S1G0G1S1S81S83S3fS46A4S1S1aS9Z46S22A4A4S0G2S1G0G1S1S81S83S64S47A4S1S1aS9Z3cS22A4A4S0G2S1G0G1S1S81S83S62S3aA4S1S1aS9Z28S22A4A4S0G2S1G0G1S1S81S83S54S74A4S1S1aS9Z0S22A4M6A4S0G2S1G0G1S1S81S83S42S75A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_finalize_shape_dup3.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4"; "vSZ"; "vH"; "vCAPl"; "z0"; "vP"; "vSRC"; "vK"; "tv0"; "p_fit"; "X_ad"; "vHD"; "O_F"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "vLS"; "vU"; "X_nohead"; "ndO"; "ra_an"; "vUc"; "C_loop"; "C_slow"; "base_fit"; "nd0"; "ndL"; "ndS"; "pN"; "vI"; "vNXl"; "E_m"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "slow_facts"; "ug_facts"; "vAR"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "c8"; "cutpcs_ad"; "ghK"; "loop_facts"; "loop_regs"; "nP"; "ndF"; "ndK"; "ndM"; "nsrc"; "ok_facts"; "pad_fit"; "slow_regs"; "tv_m"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_retF"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0x90bf4.
  Definition ad_open : Z := 0x9b978.
  Definition ad_slow : Z := 0x9b9fc.
  Definition ad_K : Z := 0x9ba28.
  Definition ad_loop : Z := 0x90c10.
  Definition ad_xit : Z := 0x90c50.
  Definition ad_ret : Z := 0x90c94.
  Definition ad_retF : Z := 0x90c70.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S24SdZ0A1S30S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1fS2S10A1S14A5").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S5SaSa5S0SaScSdZ1A1S1fA2S0SaScS1fS30A2S0SaScS30SdS98Z2Z20A2A1A2S0SaScSdZ1000A1S24A2S0SaScSfS1cS24S30A3SbP1eA1M0A2S0SaScS24G0A2S2SaA1A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S0G0S1S9S9S24S30A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|1|
S12Sa2S8fS92S0S3S4S9A2M0S1S4S9UbS1fA4S0G0S1S4S9UcSdZ10A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eS90S7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87Z2S89S1fA1M3A4S2G2A1M4A3Z60A4S0S86S88G1G0S0G2S1S1aS87Z4G3A4G4A3Z40A4S2S86A1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa3S0S1aSa0S0S1aS9cS0S1aSa6S0S1aS9dS0S1aSa1S0S1aS9eS0S1aS9fS2S1aA1A3A3A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa4S81Vk;S96S52S6fVS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S85S29S7eS4cS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S8fS17S82S32A1A1S0S3S4S9A2M0S1S4S9UbSbP65A1A4S0G0S1S4S9UdSbP66A1A4S0G0S1S4S9UeSbP67A1A4S0G0S1S4S9UfSbP68A1A4S0G0S1S4S9U10SbP69A1A4S0G0S1S4S9U11SbP6aA1A4S0G0S1S4S9U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScSdZ10001A1SfS1cS4dSfS1cS1fSdZ10A1A3A3A2S0SaScS4dSdS98Z2Z28A2A1A2S2SaA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S93S12Sa0S7aS8eS11S6S9A1S16S82S32A1A1S5SaS4aS49A3P6dS7A9S28A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSdZ10000A1M0S25A2S0SaScSfS1cS1fSdZ10M1A1A3S25A2S0SaScS25SfS1cS1fG0A3A2S0SaScS25SdS9aS98Z2Z20A2G1A2A1A2S0SaScSdZ1A1S8cS25A1A2S2SaA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S93S12S9cS8fS17S82S59A1M0A1S0S3S4S9A2M1S1S4S9U14S25A4S2G1A1A3A2S8eS11S6S9A1S16G0A1S0SaS70S5SaS53S5SaS4aS49A3A3A3P70S7A9S28A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1fSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5S86S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87G0S89S8cS25A1A1A4S2G2A1A3G1A4S0S86S8aG1G0S9bZ2S8bA2A3S2S86A1A3A3S8dS1fA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS7dA4S97PaS82S3fA1S82S56A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SbS3cA1S8cS25A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5S86S0S86S8aZ0Z1S8bA3S2S86A1A3S8dS1fA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S85S20S3eS21S0S3S9S9A2M0S1S9S9S23S1fA4S2G0A1A3A4").
Definition ra_an : Z := 0x90bf8.
Definition nsrc : sv := ltac2:(tb__ "0|0|
SfS1eS24SdZffffffffffffffffA1A3").
Definition nP : sv := SAlu ALU_XOR vP (SLit 18446744073709551615).
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9S3dS0S9S77S0S9S73S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SaS19S3dS1fA2S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3M0SbP1eA1M1A2S0SaScS20G1A2S0SaScSdZ1000A1M2S20A2S0SaS13P65Z4M3A2S0SaScSfS1cS20SdZ20A1A3S23A2S0SaScSfS1cS23S1fA3M4G0A2S0SaScG2S23A2S0SaScG4G1A2S0SaScS23G1A2S0SaS13P69G3A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S93S12S9dS72S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS71S5SaS45S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS29SdZ20A1A3S31A3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS1dS27S38A3").
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS79S1fA3S31A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS38S27A2S0SaScS27SfS1cS38SdZfA1M0A3A2S0SaScSdZ1000A1S27A2S0SaScS27SbP1eA1M1A2S0SaScSfS1cS27S1fA3M2SfS1cS29S8cS4cA1A3A2S0SaScG2G1A2S0SaScSfS1cS29SdZ20A1A3S27A2S0SaScS7cSfS1cS31SfS1cS1fG0A3A3A2S2SaA1A3A3A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
ScSdZ10001A1SfS1cS31SfS1cS1fSdZ10A1A3A3A2").
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
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S55S6eZ0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSbS3cA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSfS1cS48S1fA3M0SfS1cSbS3cA1S8cS25A1A3A2S0SaScG0SbP1eA1M1A2S0SaScS48G1A2S2SaA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9SbP7cA1S0S9SbP7dA1S0S9SbP7eA1S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3SbP1eA1M0A2S0SaScS20G0A2S0SaScSdZ1000A1M1S20A2S0SaS13P65Z4M2A2S0SaScG1S23A2S0SaScSfS1cS23S1fA3G0A2S0SaScS23G0A2S0SaS13P69G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S93S12Sa1S80S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS7fS5SaS45S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").

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
S93S12S9fS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSdZ0A1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eSa7S7A9S28A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SaScSdZ1000A1M0SbP8cM1A1M2A2S0SaScSfS1cG2S1fA3SbP1eA1M3A2S0SaS13G1Z4A2S0SaScG0SbP8dA1M4A2S0SaScG4G3A2S2SaA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S93S12S9eS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSbP8cA1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cSbP8dA1A1S0SeS2dS2SeA1A3A3A3A3S94A3S5SaS78S2eA3P8eS7A9S28A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S97P64S82S5dA1S82S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S97P64S82S65A1S82S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS31A4S97P64S82S5fA1S82S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S97P64S82S32A1S82S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S97P64S82S63A1S82S42A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S4eS66A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6cS69A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6dS2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6aS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S84S7bS2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6bS67A4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S68A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S43S39A4S1S1aS9Z64S22A4A4S0G2S1G0G1S1S81S83S51S33A4S1S1aS9Z5aS22A4A4S0G2S1G0G1S1S81S83S37S3bA4S1S1aS9Z50S22A4A4S0G2S1G0G1S1S81S83S4fS46A4S1S1aS9Z4bS22A4A4S0G2S1G0G1S1S81S83S57S76A4S1S1aS9Z41S22A4M3A4S0G2S1G0G1S1S81S83S58S47A4G3A4S0G2S1G0G1S1S81S83S36S3aA4S1S1aS9Z32SfS1dS1fS3dA3A4A4S0G2S1G0G1S1S81S83S50S3aA4S1S1aS9Z2dS22A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S61S39A4S1S1aS9Z5fS22A4M3A4S0G2S1G0G1S1S81S83S32S39A4G3A4S0G2S1G0G1S1S81S83S60S33A4S1S1aS9Z55S22A4M4A4S0G2S1G0G1S1S81S83S5cS33A4G4A4S0G2S1G0G1S1S81S83S5eS33A4G4A4S0G2S1G0G1S1S81S83S5aS3bA4S1S1aS9Z4eS22A4M5A4S0G2S1G0G1S1S81S83S5bS3bA4G5A4S0G2S1G0G1S1S81S83S3fS46A4S1S1aS9Z46S22A4A4S0G2S1G0G1S1S81S83S64S47A4S1S1aS9Z3cS22A4A4S0G2S1G0G1S1S81S83S62S3aA4S1S1aS9Z28S22A4A4S0G2S1G0G1S1S81S83S54S74A4S1S1aS9Z0S22A4M6A4S0G2S1G0G1S1S81S83S42S75A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_finalize_shape_dup4.

(* [comment removed for export] *)
Module Lib_vec_finalize_dup.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup"; "vSZ"; "vH"; "vCAPl"; "z0"; "vP"; "vK"; "tv0"; "p_fit"; "vSRC"; "X_ad"; "vHD"; "O_F"; "O_F2"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "c8"; "vLS"; "vU"; "X_nohead"; "ndO"; "vUc"; "C_loop"; "C_slow"; "F2_cells"; "base_fit"; "nd0"; "ndL"; "ndS"; "pN"; "sp_entry"; "vI"; "vNXl"; "E_m"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "ra_an"; "slow_facts"; "ug_facts"; "vAR"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "cutpcs_ad"; "f2_fact"; "ghK"; "loop_facts"; "loop_regs"; "nP"; "ndF"; "ndK"; "ndM"; "nsrc"; "ok_facts"; "pad_fit"; "slow_regs"; "tv_m"; "two47"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "NPOSTM"; "Pre_malloc"; "UStopLe"; "ulink"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0x91760.
  Definition ad_open : Z := 0x9b978.
  Definition ad_slow : Z := 0x9b9fc.
  Definition ad_K : Z := 0x9ba28.
  Definition ad_loop : Z := 0x9177c.
  Definition ad_xit : Z := 0x917bc.
  Definition ad_ret : Z := 0x9171c.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S26SdZ0A1S31S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1eS2S10A1S14A5").

Definition O_F2 (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S15SaPaA1SdZ0A1SdZ20A1Vcells;S14A5").
Definition sp_entry : sv := SAlu ALU_ADD (SVar 10) (SLit 32).
Definition f2_fact : sprop := ltac2:(tb__ "0|0|
ScS3eSdS7fA1A2").
Definition F2_cells : list cell := ltac2:(tb__ "0|0|
S0S10S30Z0SaP26A1A2S0S10S30Z8SaP1dA1A2S0S10S30Z10SaP1cA1A2S0S10S30Z18SaPbA1A2S2S10A1A3A3A3A3").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S5SbSa8S0SbScSdZ1A1S1eA2S0SbScS1eS31A2S0SbScS31SdS9cZ2Z20A2A1A2S0SbScSdZ1000A1S26A2S0SbScSfS1cS26S31A3SaP1eA1M0A2S0SbScS26G0A2S0SbS72S2SbA1A3A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4eSdZ40A1A4S0G0S1S9S9S26S31A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|1|
S12Sa5S93S96S0S3S4S9A2M0S1S4S9U8S1eA4S0G0S1S4S9U9S99A4S0G0S1S4S9UbS1eA4S0G0S1S4S9UcSdZ10A1A4S0G0S1S4S9U12S26A4S2G0A1A3A3A3A3A3A2S92S11S6S9A1S5SeS0SeS29S2S10A1A1S0SeS2bS0SeS2cS28A1S0SeS2dS0SeS2aS38A1S2SeA1A3A3A3A3A3S98A3S2eS94S7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4eSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S8aS8cZ1M0Z0M1S0S3S1aS8bA2M2S1S1aS8bZ2S8dS1eA1M3A4S2G2A1M4A3Z60A4S0S8aS8cG1G0S0G2S1S1aS8bZ4G3A4G4A3Z40A4S2S8aA1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa6S0S1aSa3S0S1aSa0S0S1aSa9S0S1aSa1S0S1aSa4S2S1aA1A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa7S85Vk;S9aS55S71VS;Vpc;A4S45A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S89S28S82S4fS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S93S17S86S33A1A1S0S3S4S9A2M0S1S4S9UbSaP65A1A4S0G0S1S4S9UdSaP66A1A4S0G0S1S4S9UeSaP67A1A4S0G0S1S4S9UfSaP68A1A4S0G0S1S4S9U10SaP69A1A4S0G0S1S4S9U11SaP6aA1A4S0G0S1S4S9U5SaP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SbScSdZ10001A1SfS1cS50SfS1cS1eSdZ10A1A3A3A2S0SbScS50SdS9cZ2Z28A2A1A2S2SbA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S97S12Sa3S7dS92S11S6S9A1S16S86S33A1A1S5SbS4dS4cA3P6dS7A9S27A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SbScSdZ10000A1M0S23A2S0SbScSfS1cS1eSdZ10M1A1A3S23A2S0SbScS23SfS1cS1eG0A3A2S0SbScS23SdS9eS9cZ2Z20A2G1A2A1A2S0SbScSdZ1A1S90S23A1A2S2SbA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S97S12Sa0S93S17S86S5cA1M0A1S0S3S4S9A2M1S1S4S9U14S23A4S2G1A1A3A2S92S11S6S9A1S16G0A1S0SbS73S5SbS56S5SbS4dS4cA3A3A3P70S7A9S27A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1eSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5S8aS0S8aS8cZ1M0Z0M1S0S3S1aS8bA2M2S1S1aS8bG0S8dS90S23A1A1A4S2G2A1A3G1A4S0S8aS8eG1G0S9fZ2S8fA2A3S2S8aA1A3A3S91S1eA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := ltac2:(tb__ "0|0|
SacSaaS2SaeA1SadA3").
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS81A4S9bPaS86S41A1S86S59A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SaS3dA1S90S23A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5S8aS0S8aS8eZ0Z1S8fA3S2S8aA1A3S91S1eA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S89S1fS40S20S0S3S9S9A2M0S1S9S9S22S1eA4S2G0A1A3A4").
Definition ra_an : Z := 0x91764.
Definition nsrc : sv := SAlu ALU_XOR vSRC (SLit 18446744073709551615).
Definition nP : sv := SAlu ALU_XOR vP (SLit 18446744073709551615).
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0S9SaP6bA1S0S9SdS4bA1S0S9SaPaA1S0S9SaP17A1S0S9SaP18A1S0S9SaP6dA1S0S9SaP6eA1S0S9SaP6fA1S0S9S1eS0S9S99S0S9S22S0S9SaP70A1S0S9SaP71A1S0S9S3fS0S9S7aS0S9S76S0S9SaP72A1S0S9SaP73A1S0S9S26S0S9SaP27A1S0S9SaP28A1S0S9SaP29A1S0S9SaP2aA1S0S9SaP2bA1S0S9SaP2cA1S0S9SaP2dA1S0S9SaP2eA1S0S9SaP2fA1S0S9SaP74A1S0S9SaP75A1S0S9SaP76A1S0S9SaP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SbS19S3fS1eA2S0SbScS35S20A2S0SbScSdZ10000A1S20A2S0SbScS20SdS9dS9cZ2Z28A2Z21A2A1A2S0SbScSfS1cS1fS90S20A1A3M0SaP1eA1M1A2S0SbScS1fG1A2S0SbScSdZ1000A1M2S1fA2S0SbS13P65Z4M3A2S0SbScSfS1cS1fSdZ20A1A3S22A2S0SbScSfS1cS22S1eA3M4G0A2S0SbScG2S22A2S0SbScG4G1A2S0SbScS22G1A2S0SbS13P69G3A2S2SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S97S12Sa1S75S92S11S6S9A1S5SeS0SeS29S2S10A1A1S0SeS2bS0SeS2cS1fA1S0SeS2dS0SeS2aS38A1S2SeA1M0A3A3A3A3A3S5SeS98S0SeS42S1fS40S20S35A4S0SeS43S22A1G0A3A3A3A3S5SbS74S5SbS47S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S1fS90S20A1A4S27A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS28SdZ20A1A3S32A3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS1dS25S39A3").
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS7cS1eA3S32A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SbScS39S25A2S0SbScS25SfS1cS39SdZfA1M0A3A2S0SbScSdZ1000A1S25A2S0SbScS25SaP1eA1M1A2S0SbScSfS1cS25S1eA3M2SfS1cS28S90S4fA1A3A2S0SbScG2G1A2S0SbScSfS1cS28SdZ20A1A3S25A2S0SbScS80SfS1cS32SfS1cS1eG0A3A3A2S2SbA1A3A3A3A3A3A3A3A3").
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
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S58S30Z0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSaS3dA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SbScSfS1cS4aS1eA3M0SfS1cSaS3dA1S90S23A1A3A2S0SbScG0SaP1eA1M1A2S0SbScS4aG1A2S2SbA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SaP6bA1S0S9SdS4bA1S0S9SaPaA1S0S9SaP17A1S0S9SaP18A1S0S9SaP6dA1S0S9SaP6eA1S0S9SaP6fA1S0S9SaP7aA1S0S9SaP7bA1S0S9S22S0S9SaP70A1S0S9SaP71A1S0S9SaP7cA1S0S9SaP7dA1S0S9SaP7eA1S0S9SaP72A1S0S9SaP73A1S0S9SaP7fA1S0S9SaP27A1S0S9SaP28A1S0S9SaP29A1S0S9SaP2aA1S0S9SaP2bA1S0S9SaP2cA1S0S9SaP2dA1S0S9SaP2eA1S0S9SaP2fA1S0S9SaP74A1S0S9SaP75A1S0S9SaP76A1S0S9SaP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SbScS35S20A2S0SbScSdZ10000A1S20A2S0SbScS20SdS9dS9cZ2Z28A2Z21A2A1A2S0SbScSfS1cS1fS90S20A1A3SaP1eA1M0A2S0SbScS1fG0A2S0SbScSdZ1000A1M1S1fA2S0SbS13P65Z4M2A2S0SbScG1S22A2S0SbScSfS1cS22S1eA3G0A2S0SbScS22G0A2S0SbS13P69G2A2S2SbA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S97S12Sa4S84S92S11S6S9A1S5SeS0SeS29S2S10A1A1S0SeS2bS0SeS2cS1fA1S0SeS2dS0SeS2aS38A1S2SeA1M0A3A3A3A3A3S5SeS98S0SeS42S1fS40S20S35A4S0SeS43S22A1G0A3A3A3A3S5SbS83S5SbS47S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S1fS90S20A1A4S27A3A2").

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

Definition P_fail : axst := ltac2:(tb__ "0|2|
S97S12Sa2S93S95S94A1S0S3S4S9A2M0S1S4S9U2S3eA4S0G0S1S4S9UaSdZ0A1A4S2G0A1A3A3A2S92S11S6S9A1S5SeS0SeS29S2S10A1M1A1S0SeS2bS0SeS2cS28A1S0SeS2dS0SeS2aG1A1S2SeA1A3A3A3A3A3S98A3S2eSabS7A9S27A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SbScSdZ1000A1M0SaP8cM1A1M2A2S0SbScSfS1cG2S1eA3SaP1eA1M3A2S0SbS13G1Z4A2S0SbScG0SaP8dA1M4A2S0SbScG4G3A2S2SbA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|2|
S97S12Sa2S93S95S94A1S0S3S4S9A2M0S1S4S9U2S3eA4S0G0S1S4S9UaSaP8cA1A4S2G0A1A3A3A2S92S11S6S9A1S5SeS0SeS29S2S10A1M1A1S0SeS2bS0SeS2cSaP8dA1A1S0SeS2dS0SeS2aG1A1S2SeA1A3A3A3A3A3S98A3S5SbS7bS2eA3P8eS7A9S27A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S9bP64S86S60A1S86S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S9bP64S86S68A1S86S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS32A4S9bP64S86S62A1S86S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S9bP64S86S33A1S86S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S9bP64S86S66A1S86S44A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S51S69A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S6fS6cA4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S70S2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S6dS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S46S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S88S7eS2S3S3S9S1aA2S9A2A1S46S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S6eS6aA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S2S8aA1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S88S24S2S3S3S9S1aA2S9A2A1S2S8aA1S6bA4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S85S87A2M0S3S1aS9A2M1A2M2S1G0G1S1S85S87S45S3aA4S1S1aS9Z64S21A4A4S0G2S1G0G1S1S85S87S54S34A4S1S1aS9Z5aS21A4A4S0G2S1G0G1S1S85S87S37S3cA4S1S1aS9Z50S21A4A4S0G2S1G0G1S1S85S87S52S48A4S1S1aS9Z4bS21A4A4S0G2S1G0G1S1S85S87S5aS79A4S1S1aS9Z41S21A4M3A4S0G2S1G0G1S1S85S87S5bS49A4G3A4S0G2S1G0G1S1S85S87S36S3bA4S1S1aS9Z32SfS1dS1eS3fA3A4A4S0G2S1G0G1S1S85S87S53S3bA4S1S1aS9Z2dS21A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S85S87A2M0S3S1aS9A2M1A2M2S1G0G1S1S85S87S64S3aA4S1S1aS9Z5fS21A4M3A4S0G2S1G0G1S1S85S87S33S3aA4G3A4S0G2S1G0G1S1S85S87S63S34A4S1S1aS9Z55S21A4M4A4S0G2S1G0G1S1S85S87S5fS34A4G4A4S0G2S1G0G1S1S85S87S61S34A4G4A4S0G2S1G0G1S1S85S87S5dS3cA4S1S1aS9Z4eS21A4M5A4S0G2S1G0G1S1S85S87S5eS3cA4G5A4S0G2S1G0G1S1S85S87S41S48A4S1S1aS9Z46S21A4A4S0G2S1G0G1S1S85S87S67S49A4S1S1aS9Z3cS21A4A4S0G2S1G0G1S1S85S87S65S3bA4S1S1aS9Z28S21A4A4S0G2S1G0G1S1S85S87S57S77A4S1S1aS9Z0S21A4M6A4S0G2S1G0G1S1S85S87S44S78A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_vec_finalize_dup.

(* [comment removed for export] *)
Module Lib_finalize_shape_name_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "valuation"; "SLit"; "sprop_eqb"; "SPUle"; "sv"; "SVar"; "SAlu"; "ss_objs"; "holds"; "ss_facts"; "SPBranch"; "ss_next"; "DUnknown"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "pair"; "prod"; "app"; "Some"; "option"; "None"; "fst"; "length"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "sub"; "lt"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "AK0"; "JA"; "JLA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name"; "vCAP"; "vHD"; "s_m"; "E_m"; "R_m"; "X_fit"; "nd0"; "objsR"; "vAR"; "vU"; "P_fail"; "P_ok"; "SZ"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret2"; "ndF"; "ndKc"; "ohR"; "p_fit"; "vDp"; "Pre_aa"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndO"; "ndS"; "sel_sret"; "spm"; "C_open"; "FUEL_aa"; "O_W"; "T_mnull"; "T_mok0"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nohead"; "X_ret3"; "X_sret3"; "cutpcs_aa"; "fit_facts"; "ndK"; "ndMok"; "need_fit"; "nofit_fact"; "osR"; "p_new"; "pad_fit"; "sel_ret"; "tv0"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_name_pf"; "P0_aa"; "objsN"; "ohN"; "ohF"; "otN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_name_pf.Sum"; "Posts_aa"; "JL"; "basez"; "baseF"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_name_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import AAAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0S20S48S1cS8fS6fS79P64S68S69A7S21A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S4SbbS64S4cA2S6eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S4SbfS62S4eS4dS4fS9cS98S23S9aA1S99A3A5S71A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S4SbfS62S4eS4dS4fS9dS98S23S9aA1S99A3A5S72A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S4SbeS63S22S8S7eS12S5S63A1A1A3A2S75A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_W.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S1fS7A1S10S5S50A1A1M0S26S7S3eS7G0A2S22S7S95S23S7A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S4SbeSb9S50S5fSaS57A1A3S26S8S7aS12S5S50A1A1A3A2S73A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S28S4A1SabS66S22Sa9SaaS6cA1S22Sa9SacSc3S2bS2cS6cA2U1A2SaZ18A1A2S23Sa9A1A3A3A2S27S4S5aA2A3"). Proof. vm_compute. reflexivity. Qed.

Definition ohN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 2) (ss_objs (ax_S X_sret1)) O_W.
Definition otN : sobj := Eval vm_compute in nth (length (ss_objs (ax_S X_sret1)) - 1) (ss_objs (ax_S X_sret1)) O_W.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1))).
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S1fS7A1S10S5S5aA1A1S26S7S26S7S93S22S7S94S23S7A1M0A3A3S22S7S96G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S4Sb8S5aS26S7S93S22S7S94S23S7A1A3A3A2S5bA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S1fS7A1S10S5S5bA1A1S26S7S93S22S7S94S23S7A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S4Sb9S5bS80SaS57A1A3S78A3"). Proof. vm_compute. reflexivity. Qed.

Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S28S4A1SabS65S22Sa9SaaS82A1S23Sa9A1A3A2S27S4S58A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S1fS7A1S10S5S58A1A1S26S7S26S7S52S22S7S5eS23S7A1M0A3A3S22S7S7fG0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S4Sb8S58S26S7S52S22S7S5eS23S7A1A3A3A2S59A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S1fS7A1S10S5S59A1A1S26S7S52S22S7S5eS23S7A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S4Sb8S59S52A2S77A3"). Proof. vm_compute. reflexivity. Qed.
Definition bd_m2 : list bitem := ltac2:(tb__ "0|2|
S22S36S37Z1M0Z0M1Z62A3S22S36S37G1G0S32S2fS45Z44A2S31Z2S38A2A2A3S23S36A1A3A3").

Definition P0_aa (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := True.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
SbdS9S1fS3fQ40A1A1SaeOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa3S1cVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2dSc2VCST;R1A2S1S2eZ0R2A2S33R2Sc1A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2dSc2VXGL;R1A2S1S2eZ0R2A2S33R2Sc1A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1fS25S25S2dS2dA2S2dA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S47VAInv;VCST;VXGL;VKc;S92VFB;VFF;A2VFB;VFF;VBX;S42Vnd;Aa").
Definition Posts_aa : list (axst * jpostA) := ltac2:(tb__ "0|1|
S22S25S4S86A2M0S24S4S86S55Sb1S5cA1A4S22G0S24S4S86S56Sb1S5dA1A4S23G0A1A3A3").

Definition PD_aa : list (axst * ndesc) := ltac2:(tb__ "0|1|
S22S25S4S41A2M0S24S4S41S55S5cA4S22G0S24S4S41S56S5dA4S23G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;S8fVKc;Vrho0;S92VFB;VFF;A2VFB;VFF;VBX;S42Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S25S4S41A2Sc7Fn;") := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;S8fVKc;Vrho0;S92VFB;VFF;A2VFB;VFF;VBX;S42Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S87S1cS8fVrho0;Vtp0;Sb0A5").

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|5|
S1S0S20S3cS8SbScSePaA1M0SaS85A1M1A2A1VF;A3S21A3S1S0S20S3cS8SbScSeP1eA1M2SfS90S6dZ40M3A1M4S60A3A2A1VF;A3S21A3S1S0S20S3cS8SbScG2G4A2A1VF;A3S21A3S1S0S20S3cS8SbS13S91SaN1000A1S60A3A1VF;A3S21A3S1S0S20S3cS8SbS13S91S60SaS34S84A1A1A3A1VF;A3S21A3S1S0S20S3cS8SbScSaZ1000A1S53A2A1VF;A3S21A3S1S0S20S3cS8SbScSfS90S53SaG3A1A3G2A2A1VF;A3S21A3S1S0S20S3cS8SbScS53G1A2A1VF;A3S21A3S1S0S20S3cS8SbScS4cG2A2A1VF;A3S21A3S1S0S20S3cS8SbScG2G0A2A1VF;A3S21A3S1S0S20S3cS8SbScSaZ7fff7f800000A1G2A2A1VF;A3S21A3S0S20S3cS8SbScG2SaZ7fffff800000A1A2A1VF;A3S21A3A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_win : forall a, fst (obj_range rho O_W) <= a < snd (obj_range rho O_W) -> bv_unsigned (rw rho V_TOP) <= a < uval rho (SVar 10) - 64;
  bz_ar : 4096 <= uval rho vAR /\ uval rho vAR + 64 <= bv_unsigned (rw rho V_TOP);
  bz_hd : uval rho vHD <= bv_unsigned (rw rho V_TOP);

  bz_top : 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S9S2dS1S2eZ0R1A2S2eR1S35R2SePaA1M0A2A2A2S0S2dS35R3S6dR2A1A2S32S35R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S9S1fS8A1Sb4S8S11R2A1R1A3Sb3R2A1Sb2R4A1F_;F_;FF;Frho;").
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
S9S1fS7A1Sb2R2A1S7S3dS7R1R3A3S2S1S0SdS16R2A1M0SePaA1A3S1S0SdS19R2A1M1SaN40A1A3S1S0SdS18R2A1M2SaZ0A1M3A3S0S1aS17R2A1S15A3M4A2A2A2S2S0S7R2S70A3S2S1S0SdG0S53A3S1S0SdG1G3A3S1S0SdG2SaZ40A1A3G4A2A2A2S2S0S7R2S1dA3S0S7R2S1eA3A2A2A2A2F_;Fo;S0S2dSc8Vrho0;A1S40Q40S1bR4Sa0A2A2A3SbcVCST;Vrho0;VFB;VFF;R5S83S23S25S25SdS2dA2SdA2A1R4A8F_;F_;F_;Fobjs;Frho;").
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
S2dS1fS3fQ40A1A1S8bF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3aS4S9S1fS3fQ40A1A1S8bSb4S8S11R3A1S12S5R4A1A1A3VTR;S39S1cR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S8bS8bS8bS8cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S8bS8bS8cS3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3aS3aS4S4Sa7S1fS7A1M0S1fS25S4S86A2M1A1S1fS25SdSdA2M2A1S8bS9S1fS3fQ40A1A1M3G2S3dG2R1R5A3S3dG2R2S6RbA1A3F_;Fr;S0S28G0A1S8aRaR9R8A3S27G0R7A2A3S0S20S89RbRaR9R8Sb5G1S4S2aS4S86A2R7A4A5S21A3S9G3VTR;S39S1cRfRdR2R1A5S87S1cS14S5RdA1A1R2R1RaA5A2Ftp1;Frho1;S1fSafA1M4SadSaeS3bS1cR9R8R10S24G4Sb6R3Sb7R2R1A2A4A5R13RaR9R4R2A4R13Sa6Sa5RbRfS97R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S86G4SadSaeS9G3G4SadSaeS3dG1S24S4S86RaR9A4R14A3S3bS1cR12R11R19S24G4Sb6R9Sb7R8R7A2A4A5R1cR13R12RaR8A4Sc5S14S5R1aA1A1Sa6Sa5R14R18S97R9R13RaA3A3R19A2R8A3S3bS1cR9R8ReS24G4Sb6R7Sb7R6R5A2A4A5ReSa6Sa5R16R1aS97RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sc9R17S97RcR16RdA3R1bR1cR1dR10R1eR19RbA9S9Sc6R18S97RdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S39S1cS88R11Sa6Sa5R19R1dS97ReR18RfA3A3R1eA2R18RdRcA5ScaR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S39S1cR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
SbdS9S1fS3fQ40A1A1VTR;S39S1cS9bVAInv;S23S9aA1M0S99R3VKc;SePcA1A6S9fS98G0S99A3R2R1A5S87S1cS8fR2R1S9eS98VAInv;VCST;VXGL;G0S99R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S41S25S2dSdA2M0S9S1fS3fQ40A1A1M1S2dG1S3dS25S25S4S41A2M2G0A2S24G2G0S24S4S41R7R6A4R5A4S68A3S1S2eZ0S44S24G2G0S24S4S41R8R7A4R6A4R5A2M3A2S33G3R3A2A2VTR;S39S1cVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S41S9S1fS3fQ40A1A1M0S2dG0S3dS25S4S86A2S24S4S86R6Sb1R5A1A4Sb0A3VTR;S39S1cVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Lemma X_X_open : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z5bS30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S51A1S64R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      + apply objs_ok_gen; [eapply basez_of; [exact HF | repeat split; vm_compute; reflexivity]| |exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. rewrite uval_lit in Ha by lia.
        pose proof (basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [right; left; reflexivity | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z51S30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S51A1S76R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [do 2 right; left; reflexivity | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ E0) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0VTR;S39S1cVJAv;S5cA1S55R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0VTR;S39S1cVJAv;S5dA1S56R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S9Sc0VAInv;VCST;VXGL;S8fVrho0;S92VFB;VFF;A2VFB;VFF;S4eS4dS4fR1S6bS29S2dA1SbdSadS1S1S2eZ1S35R3Sa8S4dPcA2A2M0A2S33G0S30Z2Z27A2A2A2Sa4S23S9aA1S99Sa6Sa5R3S4fR1A3S4dA2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndS] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun _ => false) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. discriminate Hb.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun _ => false) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros r a Hr Hb Ha. discriminate Hb.
    + exact I.
  - change (wsub_get s_m 12) with (SLit 65568). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z42S30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S6bA1S4eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndS bd_m (FAM b tp0) CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [do 3 right; left; reflexivity | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndS]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [do 4 right; left; reflexivity | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma fit_arith : ltac2:(tb__ "0|8|
S9S2eS35R1S4cA2Z7fffff800000A2S2eS35R2S54A2S35R2S4bA2A2S2eS35R3S4bA2S32S30Z2Z28A2Z21A2A2S1S0S2dS35R4S67A2M0S2fS2fS35R4S4cA2M1Z20M2A2S35R4S54A2M3A2A3S1S1S2eG0S35R4S5fA2M4A2S2eG4S2fG0Z0A2A2A2S1S0S2dS35R4S81A2M5S32G4G0A2A3S1S0S2dS35R4S7dA2S2fS2fG3Z1M6A2G5A2A3S1S0S2dS35R4SfS90S67SaZfM7A1A3A2S2fG0G7A2A3S1S0S2dS35R4SfS90S5fSaS57A1A3A2S2fG4G6A2A3S0S2dS35R4SfS90S4cSbaS4bA1A3A2S2fG1S2fS35R4S4bA2G2A2A2A3A2A2A2A2A2A2F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc. unfold SZ.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (Ep0 : p_fit = base_fit) by reflexivity.
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 0) by (rewrite Ep0; lia).
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split]].
  - unfold need_fit. rewrite EPAD, Ep0. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - unfold SZ. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S20S3cS8SbScS4cSeP1eA1M0A2A1VF;A3S21A3S1S0S20S3cS8SbScS54S4bA2A1VF;A3S21A3S1S0S20S3cS8SbScS4bSaS32S30Z2Z28A2Z21A2A1A2A1VF;A3S21A3S1S0S20S3cS8SbScSaZ10000A1S4bA2A1VF;A3S21A3S1S0S20S3cS8SbScSfS90S4cSbaS4bA1A3G0A2A1VF;A3S21A3S1S0S20S3cS8SbScSaZ1000A1S4cA2A1VF;A3S21A3S0S20S3cS8SbScG0SaZ7fffff800000A1A2A1VF;A3S21A3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|4|
S9S1fS8A1Sb4S8S11R2A1R1A3Sc4R2A1S1S2eS35R4S4cA2M0Z7fffff800000M1A2S1S2eS35R4S54A2S35R4S4bA2M2A2S1S2eG2S32S30Z2Z28A2Z21A2A2S1S2eZ10000G2A2S1S2eS2fG0S2fG2Z20A2A2S35R4SeP1eA1A2M3A2S1S2eZ1000G0A2S2eG3G1A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3) as (_ & _ & _ & _ & _ & _ & E7). rewrite E7 in H5. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z51S30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S6aA1S74R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & _).
  assert (HN : existsb (sprop_eqb (SPNot (SPBranch BC_GEU vCAP need_fit))) (ss_facts (ax_S X_nofit)) = true) by (vm_compute; reflexivity).
  pose proof (holds_mem _ _ _ HF HN) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.

  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65536 mod M64v) with 65536.
      assert (EU : eval rho1 vU = eval rho vU) by (unfold rho1; apply eval_absorb). rewrite EU. change (bv_unsigned (eval rho vU)) with (uval rho vU). lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [do 2 right; left; reflexivity | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z33S30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S6aA1S50R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  destruct (openz rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3) as (EB & EP & EPAD & EN & E15 & E72 & EHC).
  assert (HY : existsb (sprop_eqb (SPBranch BC_GEU vCAP need_fit)) (ss_facts (ax_S X_fit)) = true) by (vm_compute; reflexivity).
  pose proof (holds_mem _ _ _ HF HY) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EN in H0.
  eapply TR_pre; [|apply (REENTER C_nul ndK (50, z0) (rho_sub rho s_fit)); [do 6 right; left; reflexivity | meas]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_fit3 C_nul s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, SLit SZ)])) ndK);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit (SLit SZ) X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
    + intros r HFr. destruct (openz r _ HFr ltac:(repeat split; vm_compute; reflexivity)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3) as (EB' & EP' & EPAD' & EN' & _).
      pose proof (holds_mem _ _ _ HFr HY) as H1. zf H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. rewrite EN' in H1.
      unfold SZ. rewrite uval_lit by lia. pose proof (uval_range r vU). lia.
    + intros Ai rho1 tp1 md1 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho HavS eq_refl) as ET. split.
      * intros o a Ho Hr.
        rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_gen rho (removelast (ss_objs (ax_S X_fit))) (basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD. lia.
      * intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha.
        -- assert (E32 : uval rho (e32 vCAP) = uval rho vCAP + 32)
             by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
           change (SAlu ALU_ADD (SVar 102) (SLit 32)) with (e32 vCAP) in Ha. change (SVar 15) with vHD in Ha.
           rewrite E32 in Ha. pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. pose proof (basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]]. unfold vAR in *. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD).
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC; rewrite ?uval_lit by lia; lia.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0S2eS31Z33S30Z2Z40A2A2R2A2VTR;S39S1cVJAv;S7cA1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) C_nul rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD (SLit 65536) (SLit 1)
                  X_sret1 objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD (SLit 65536) p_new (SLit SZ) X_sret2 rho1 tp _);
        [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
      - intros r HFr.
        assert (HE : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (vm_compute; reflexivity).
        assert (HE' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (vm_compute; reflexivity).
        pose proof (holds_mem _ _ _ HFr HE) as HE1. zf HE1. pose proof (holds_mem _ _ _ HFr HE') as HE2. zf HE2.
        repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
        rewrite uval_lit in HE2 by lia.
        rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
        pose proof (uval_range r (SVar pN)) as RP. unfold p_new, SZ.
        rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite !uval_lit by lia. lia.
      - intros Ai rho2 tp2 md2 HF' _ HavS _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 HavS eq_refl) as ET. split.
        + intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
          * destruct (objs_ok_gen rho1 objsN (basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity))
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
          * right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia].
            unfold pN. lia.
        + intros r a Hr Ha.
          assert (HX : In r [(SVar 12, SLit 64); (SVar pN, SLit 65568)]) by exact Hr. clear Hr.
          pose proof (basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
          destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha.
          * rewrite uval_lit in Ha by lia. unfold vAR in *. lia.
          * assert (HE' : existsb (sprop_eqb (SPUle (SAlu ALU_ADD (SVar pN) (SLit 65568)) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (vm_compute; reflexivity).
            assert (HE'' : existsb (sprop_eqb (SPUle (SVar pN) (SLit 140737479966720))) (ss_facts (ax_S X_sret2)) = true) by (vm_compute; reflexivity).
            pose proof (holds_mem _ _ _ HF1 HE') as HE1. zf HE1. pose proof (holds_mem _ _ _ HF1 HE'') as HE2. zf HE2.
            repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in HE2.
            rewrite uval_lit in HE2 by lia.
            rewrite uval_add_small in HE1 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in HE1 by lia.
            rewrite uval_lit in Ha by lia. pose proof (uval_range rho1 (SVar pN)). lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_sret3 C_nul s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD (SLit 65536) [(p_new, SLit SZ)])) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER C_nul ndK (50, z0)); [do 6 right; left; reflexivity | meas].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
S9S1fS3fQ40A1A1M0S2dG0VTR;S39S1cVJAv;S7bA1S65R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndKc) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_ret X_ret1 tp _ X_ret1_eq Hw) as H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_ok (SVar 141) (SVar 142) (SVar 143) (SVar 140) (SLit SZ)
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_ok [] (SVar 141) (SVar 142) (SVar 143) (SVar 144)
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead (SVar 141) true)) ndKc);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S41S25S2dSdA2M0S9S1fS3fQ40A1A1M1G1S3dS25S25S4S41A2M2G0A2S24G2G0S24S4S41R6R5A4R4A4S69A3VTR;S39S1cVJAv;R6A1R7R4R3A5VFAM;S44S24G2G0S24S4S41R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofit. meas.
  - apply X_X_fit. meas.
  - apply X_E_m. meas.
  - apply X_X_sret. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S4aS1cVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sa1S1cS98VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum : ltac2:(tb__ "0|0|
S1fS3fQ40A1A1S8eS1cVok;S39S1cS43VAInv;VCST;VXGL;VKc;S92VFB;VFF;A2VFB;VFF;VBX;S42S51AaS61Vrho0;R1A5S87S1cS8fVrho0;R1Sb0A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
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
Sa2S1cS98VAInv;VCST;VXGL;A5").

Theorem arena_alloc_sum_ex : ltac2:(tb__ "0|0|
S1fS3fQ40A1A1S8dS1cS39S1cS43VAInv;VCST;VXGL;VKc;S92VFB;VFF;A2VFB;VFF;VBX;S42S51AaS61Vrho0;R1A5S87S1cS8fVrho0;R1Sb0A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue HKc ALA FUEL_aa cutpcs_aa 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_aa FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_aa FB FF) FB FF BX PTrue rho0 tp0 nd Posts_aa P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_finalize_shape_name_pf.

(* [comment removed for export] *)
Module Lib_intern_rest.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "length"; "list"; "option"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "SLit"; "SVar"; "SAlu"; "sobj"; "cell"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkObj"; "SPAlign"; "SPUlt"; "ss_objs"; "SPBranch"; "ss_regs"; "ob_base"; "sv_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest"; "z0"; "vC1"; "c8"; "vN"; "vP"; "vC2"; "vH"; "vHDi"; "vK"; "X_ir"; "tv_ir"; "vCAPl"; "nd0"; "two40"; "vARi"; "ir_facts"; "vBld"; "vLn"; "am_np"; "vCu"; "vDp"; "X_nohead"; "ir_state"; "ndO"; "pN"; "p_fit"; "C_loop"; "C_nul"; "C_slow"; "O_Fi"; "O_Wi"; "O_arI"; "O_cu"; "P_b8"; "cle"; "nX"; "ndL"; "ndMok"; "ndS"; "objs_ir0"; "vJ"; "vNn"; "vS"; "vU"; "E_m"; "FUEL_ir"; "F_cells"; "P_ok"; "Pre_ir"; "bd_m"; "cutpcs_ir"; "junk_regs"; "ndKc"; "objs_loop"; "p_new"; "slot_factsI"; "spm"; "vCAP"; "vNXl"; "vUc"; "vUg"; "CHi"; "C_K"; "C_m"; "C_open"; "C_tl"; "C_tm"; "C_tr"; "K0_facts"; "K_facts"; "O_hdrI"; "O_slotI"; "P_fail"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fitc"; "X_fitc3"; "X_fitn"; "X_fitn3"; "X_loop"; "X_nofit"; "X_nofit2"; "X_nul"; "X_open"; "X_ret"; "X_ret3"; "X_sretc"; "X_sretc3"; "X_sretn"; "X_sretn3"; "am_ir"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "cend"; "cin"; "find_idxb"; "ghK"; "loop_facts"; "loop_regs"; "ndF"; "ndK"; "ndM"; "nul_regs"; "objs_ir"; "ok_facts"; "optAi"; "slow_facts"; "slow_regs"; "tv_m"; "ug_facts"; "vNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "pB"; "vE"; "vL"; "vI"; "vB"; "O_txt"; "two26"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest.IRAddr"; "ir_K"; "ir_cpy"; "ir_m"; "ir_nul"; "ir_ret"; "ir_slow"; "ir_tl"; "ir_tm"; "ir_tr"; "ir_entry"; "ir_open"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "NPOSTM"; "Pre_malloc"; "UStopLe";
"ulink"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "filter"; "removelast"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module IRAddr.
  Definition ir_entry : Z := 0x9b2bc.
  Definition ir_tl : Z := 0x9b334.
  Definition ir_tm : Z := 0x9b36c.
  Definition ir_tr : Z := 0x9b390.
  Definition ir_m : Z := 0x9b3cc.
  Definition ir_open : Z := 0x9b978.
  Definition ir_slow : Z := 0x9b9fc.
  Definition ir_fits : Z := 0x9b3fc.
  Definition ir_K : Z := 0x9ba28.
  Definition ir_cpy : Z := 0x9b414.
  Definition ir_nul : Z := 0x9b478.
  Definition ir_ret : Z := 0x9b4ac.
  Definition ir_malloc : Z := 0x9b91c.
End IRAddr.
Import IRAddr ScanDoubleAddr RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two40 := RA.two40. Definition vDp : sv := SVar 19.

Definition FUEL_ir : nat := 400%nat.
Definition vBld : sv := SVar 12. Definition vARi : sv := SVar 53. Definition vHDi : sv := SVar 54.
Definition O_Fi (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S11PaA1S10N70A1S10Z0A1Vcells;S17A5").
Definition O_Wi : sobj := ltac2:(tb__ "0|0|
S18S64Z70A1S40S10Z0A1S3S14A1S17A5").

Definition vCu : sv := SVar 13.
Definition O_cu : sobj := ltac2:(tb__ "0|1|
S18S3fS10Z0M0A1S10Z10A1S0S14S2eG0Sb0Sb3A1A2S0S14S2eZ8Sb0Sb1A1A2S3S14A1A3A3S17A5").
Definition P_b8 : sobj := ltac2:(tb__ "0|1|
S18S3cS10Z8M0A1S10Z10A1S0S14S2eG0S3aA2S3S14A1A3S17A5").
Definition O_arI (hd : sv) : sobj := ltac2:(tb__ "0|0|
S18S3aS10Z0A1S10Z40A1Sd3Vhd;A1S17A5").
Definition ir_facts : list sprop := ltac2:(tb__ "0|9|
S0SeS19PaM0Z4M1A2S0SeSfS11G0A1M2S10Sb7A1M3A2S0SeSfS11P1eA1M4S12S26S64Z70A1M5S40A3A2S0SeSfG4G5A2S0SeSfG4G2A2S0SeS1cS28S10N1000A1S40A3S0SeS1cS28S40S10SdfS39A1A1A3S0SeS19PcZ3M6A2S0SeSfS10Sd5A1S3cA2S0SeSfS12S26S3cS10Z518A1A3G4A2S0SeSfS3cG3A2S0SeS19P35G1A2S0SeSfS10Z1000A1S3aA2S0SeSfS12S26S3aS10Z40A1A3G4A2S0SeSfS3aG3A2S0SeSfS33G4A2S0SeSfSb3Sb1A2S0SeSfSb1Sb2A2S0SeSfSb2S10Sb6A1A2S0SeSfSb4G3A2S0SeSfS10Z1A1Sb4A2S0SeSfS12S26Sb4Sb2A3S10Z7fffff800000A1M7A2S0SeSfS10Z7fff7f800000A1M8G4A2S0SeSfG4G7A2S0SeSfG8G2A2S0SeS19PdG6A2S0SeSfG4S3fA2S0SeSfS12S26S3fS10Z10A1A3G3A2S0SeSfS3fG3A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_ir : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS3cS10Z518A1A4S0G0S1SdSdS3aS10Z40A1A4S0G0S1SdSdSb4Sb2A4S0G0S1SdSdS3fS10Z10A1A4S3G0A1A3A3A3A3").
Definition objs_ir0 (hd : sv) : list sobj := ltac2:(tb__ "0|1|
S5S13S0S13S49S3S14A1M0A1S0S13S4aS0S13S4dS0S13S4bVhd;A1S0S13Sb5G0A1S0S13S4cS3S13A1A3A3A3A3A3A3Sb9A3").
Definition Pre_ir : axst := ltac2:(tb__ "0|0|
Sb8S16SceSafSabS15S6SdA1S53S33A1S3bSaaS7A9S35A2").
Definition tv_ir : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS3aS10Z40A1A4S3G0A1A3").
Definition am_ir : amode := AHead vHDi true.

Definition CHi : list bitem := ltac2:(tb__ "0|6|
S0Sa4Sa6Z1M0Z0M1S0S4S20Sa5A2M2S1S20Sa5Z2Sa7Sb1A1M3A4S0G2S1S20Sa5N2Sa7Sb3A1M4A4S3G2A1M5A3A3Z62A4S0Sa4Sa6G1G0S0G2S1S20Sa5Z4G3A4S0G2S1S20Sa5N4G4A4G5A3A3Z44A4S3Sa4A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S69S8aA4").

Definition cutpcs_ir : list Z := ltac2:(tb__ "0|0|
S0S20ScbS0S20SccS0S20ScdS0S20Sc7S0S20ScfS0S20ScaS0S20Sc5S0S20Sc6S0S20Sc8S0S20Sd4S3S20A1A3A3A3A3A3A3A3A3A3A3").
Definition optAi (x : option axst) : axst := match x with Some s => s | None => Pre_ir end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sd1S22Vk;SbbS59S5eVS;Vpc;A4S5cA4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
S8S24SaS9S24A1M0A1G0Lx;S25SbcS59S5eVS;ScA5G0R1Ll;S3S24A1Xax2A2").

Definition F_cells_ : unit := tt.
Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S14S2eN8S11PbA1A2S0S14S2eN10S11P1cA1A2S0S14S2eN18S11P1dA1A2S0S14S2eN20S11P26A1A2S0S14S2eN28S11P27A1A2S3S14A1A3A3A3A3A3").
Definition objs_ir (hd : sv) : list sobj := ltac2:(tb__ "0|0|
S5S13S0S13S49S5aA1S0S13S4aS0S13S4dS0S13S4bVhd;A1S0S13Sb5S3S14A1A1S0S13S4cS3S13A1A3A3A3A3A3A3Sb9A3").

Definition cin (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfSb3Vc;A2S0SeS1aVc;Sb1A2S0SeS1aVc;Sb2A2S0SeSfVc;S10S39A1A2S3SeA1A3A3A3A3").
Definition vC1 : sv := SVar 132.
Definition vC2 : sv := SVar 133.
Definition ir_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
Sb8S16Vpc;SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S26S11PaA1S10N30A1A3A4S0G0S1S2SdU8SbaA4S0G0S1S2SdUaS3cA4S0G0S1S2SdU12Sb0Sb1A1A4S3G0A1A3A3A3A3Vregs;A3A2SabS15S6SdA1S9cS33A1S5SeVfacts;S3bA3Vnx;S7A9S35A2").

Definition C_tl : axst := ltac2:(tb__ "0|2|
S42ScbS0S4S2SdA2M0S1S2SdU9Sb0S2dA1M1A4S0G0S1S2SdUbG1A4S0G0S1S2SdUcS10Z9A1A4S0G0S1S2SdUdS10Z20A1A4S3G0A1A3A3A3A3S93S2dA1P8cA4").

Definition cle (c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfSb3Vc;A2S0SeSfVc;Sb1A2S0SeSfVc;S10S39A1A2S3SeA1A3A3A3").
Definition cend (c1 c2 : sv) : list sprop := ltac2:(tb__ "0|0|
S0SeSfVc1;Vc2;A2S0SeSfVc2;Sb1A2S0SeSfVc2;S10S39A1A2S3SeA1A3A3A3").

Definition C_tm : axst := ltac2:(tb__ "0|1|
S42SccS0S4S2SdA2M0S1S2SdU9Sb0S2dA1A4S3G0A1A3S4eS2dA1P8cA4").

Definition C_tr : axst := ltac2:(tb__ "0|2|
S42ScdS0S4S2SdA2M0S1S2SdU9Sb0S2dA1A4S0G0S1S2SdU12Sb0S12S26S31S10Z1A1M1A3A1A4S0G0S1S2SdUbSb0S31A1A4S0G0S1S2SdUcG1A4S0G0S1S2SdUdS10Z20A1A4S0G0S1S2SdUeS10Z9A1A4S3G0A1A3A3A3A3A3A3S5SeS4eS2dA1S0SeSfS2dS31A2S0SeS1aS31Sb1A2S0SeS1aS31Sb2A2S3SeA1A3A3A3A3P8cA4").

Definition C_m : axst := ltac2:(tb__ "0|1|
S42Sc7S0S4S2SdA2M0S1S2SdU9Sb0S2dA1A4S0G0S1S2SdU12Sb0S31A1A4S3G0A1A3A3S5SeS4eS2dA1S92S2dS31A2A3P8cA4").

Definition vN : sv := ltac2:(tb__ "0|0|
S12S26S12S27S31S2dA3S10Z1A1A3").
Definition vLEN : sv := SAlu ALU_SUB vC2 vC1.

Definition X_open : axst := Eval vm_compute in leaf_at C_m ir_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHDi.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S2bS33Sa3S65S3S4SdSdA2A1A4").

Definition CHn : list bitem := ltac2:(tb__ "0|5|
S0Sa4Sa6Z1M0Z0M1S0S4S20Sa5A2M2S1S20Sa5Z2Sa7S2fA1M3A4S3G2A1M4A3Z60A4S0Sa4Sa6G1G0S0G2S1S20Sa5Z4G3A4G4A3Z40A4S3Sa4A1A3A3").
Definition bd_open : list bitem := CHn ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leaf_at C_m ir_slow 0.

Definition X_nofit : axst := Eval vm_compute in leaf_at C_open ir_slow 0.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
SacS1dS23S41A1A1S0S4S2SdA2M0S1S2SdUbS11P65A1A4S0G0S1S2SdUdS11P66A1A4S0G0S1S2SdUeS11P67A1A4S0G0S1S2SdUfS11P68A1A4S0G0S1S2SdU10S11P76A1A4S0G0S1S2SdU11S11P77A1A4S0G0S1S2SdU5S11P69A1A4S3G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHDi (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SeSfS10Z10001A1S12S26S68S2fA3A2S0SeSfS68S10S39A1A2S3SeA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
Sb8S16ScaSa0SabS15S6SdA1S1bS23S41A1A1S5SeSa2S9fA3P96S7A9S35A2").
Definition bd_slow : list bitem := POT vUg ++ CHn.
Definition am_np : amode := AHead vHDi false.

Definition X_K0 : axst := Eval vm_compute in leaf_at C_slow ir_K 0.
Definition vK : sv := SVar 146.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS10Z10000A1M0S34A2S0SeSfS12S26S2fS10Z1A1M1A3S34A2S0SeSfS34S12S26S2fG0A3A2S0SeSfS34S10Se0Z2Z1bA2A1A2S0SeSfG1SbeS34A1A2S3SeA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 147) (SLit 0).
Definition K0_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with SPBranch BC_LTU _ (SLit 65536) => false | SPNot (SPBranch BC_LTU _ (SLit 65536)) => false | _ => true end)
                                 (ss_facts (ax_S X_K0)).
Definition C_K : axst := ltac2:(tb__ "0|2|
Sb8S16Sc5SacS1dS23S78A1M0A1S0S4S2SdA2M1S1S2SdU14S34A4S3G1A1A3A2SabS15S6SdA1S1bG0A1S0SeS95S5SeS71S70A3A3P96S7A9S35A2").
Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leaf_at C_slow ir_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S4S21SdA2M0S1S21SdP93S10Z0A1A4S0G0S1S21SdP92S10Z10000A1A4S3G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S4S21SdA2M0S1S21SdP93S10Z0A1A4S0G0S1S21SdP92S12S26S2fS10Z1A1A3A4S3G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5Sa4S0Sa4Sa6Z1M0Z0M1S0S4S20Sa5A2M2S1S20Sa5G0Sa7SbeS34A1A1A4S3G2A1A3G1A4S0Sa4Sa8G1G0SdeZ2Sa9A2A3S3Sa4A1A3A3SbfS2fA1A3").

Definition E_m : axst := Eval vm_compute in leaf_at C_K malloc_pc 0.
Definition Pre_m : axst := ltac2:(tb__ "0|0|
Sd8Sd6S3SdaA1Sd9A3").
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S21SdA2S1S21SdPfS40A4SbdPaS23S58A1S23S75A1A3A3").
Definition optRi (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_m : list sobj := Eval vm_compute in optRi (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1SdSdS11S44A1SbeS34A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.
Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5Sa4S0Sa4Sa8Z0Z1Sa9A3S3Sa4A1A3SbfS2fA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv_ir.
Definition bd_m2 : list bitem := POT vN.

Definition vLn : sv := SVar 145. Definition vS : sv := SVar 148. Definition vJ : sv := SVar 149. Definition vR : sv := SVar 139.
Definition vNn : sv := SAlu ALU_ADD vLn (SLit 1).
Definition vH : sv := SVar 134.  Definition vNXl : sv := SVar 135.  Definition vCAPl : sv := SVar 136.
Definition vUc : sv := SVar 137. Definition vP : sv := SVar 138.
Definition O_hdrI (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S18Vhd;S10Z0M0A1S10Z18A1S0S14S2eG0Vnx;A2S0S14S2eZ8Vcap;A2S0S14S2eZ10Vu;A2S3S14A1A3A3A3S17A5").
Definition O_slotI (p n : sv) : sobj := ltac2:(tb__ "0|0|
S18Vp;S10Z0A1Vn;S3S14A1S17A5").
Definition am_loop : amode := ltac2:(tb__ "0|1|
S2bS32S66S37S0S4SdSdA2M0S1SdSdS30S55A4S3G0A1A3A4").
Definition junk_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SdA2M0S1S2SdU1S11P6fA1A4S0G0S1S2SdU5S11P69A1A4S0G0S1S2SdU6S11P6aA1A4S0G0S1S2SdU7S11P6bA1A4S0G0S1S2SdU10S11P74A1A4S0G0S1S2SdU11S11P75A1A4S0G0S1S2SdU12S11P76A1A4S3G0A1A3A3A3A3A3A3A3").
Definition nX (x : sv) : sv := SAlu ALU_XOR x (SLit 18446744073709551615).
Definition loop_regs : list (nat * sv) := ltac2:(tb__ "0|2|
S5S4S2SdA2M0S0G0S1S2SdU8SbaA4S0G0S1S2SdU9Sb0S56A1M1A4S0G0S1S2SdUaS30A4S0G0S1S2SdUbS11P7cA1A4S0G0S1S2SdUcS11P70A1A4S0G0S1S2SdUdS4fS30A1A4S0G0S1S2SdUeS54A4S0G0S1S2SdUfS4fG1A1A4S0G0S1S2SdU13S3dA4S3G0A1A3A3A3A3A3A3A3A3A3S5fA3").

Definition slot_factsI : list sprop := ltac2:(tb__ "0|4|
S0SeSfS67S37A2S0SeSfS10Z10000A1S37A2S0SeSfS37S10Se1S39Z21A2A1A2S0SeSfS12S26S32SbeS37A1A3M0S11P1eA1M1A2S0SeSfS32G1A2S0SeSfS10Z1000A1M2S32A2S0SeS19P86Z4A2S0SeSfS12S26S32S10Z20A1A3S30A2S0SeSfS12S26S30S55A3M3G0A2S0SeSfG2S30A2S0SeSfG3G1A2S0SeSfS30G1A2S0SeSfS3dS10S39A1A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_facts : list sprop := ltac2:(tb__ "0|0|
S5SeS0SeS1aS54S3dA2S0SeSfS12S26S56S3dA3Sb2A2S0SeSfS56Sb2A2S3SeA1A3A3A3S63A3").
Definition objs_loop : list sobj := ltac2:(tb__ "0|1|
S5S13S0S13S49S5aA1S0S13S4aS0S13S4dS0S13S4bS32A1S0S13Sb5S3S14A1A1S0S13S4cS3S13A1M0A3A3A3A3A3A3S5S13Sb9S0S13S72S32S66S37S67A4S0S13S73S30S55A2G0A3A3A3A3").
Definition X_loop : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4SdSdA2S1SdSdS32SbeS37A1A4S35A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
Sb8S16Sc6SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S26S11PaA1S10N30A1A3A4S3G0A1A3S97A3A2SabS15S6SdA1S61S5SeS96S3bA3P96S7A9S7fA2").
Definition bd_loop : list bitem := POT vUc.

Definition nul_regs : list (nat * sv) := ltac2:(tb__ "0|1|
S5S4S2SdA2M0S0G0S1S2SdU8SbaA4S0G0S1S2SdU9S11P6dA1A4S0G0S1S2SdUaS30A4S0G0S1S2SdUbS11P7cA1A4S0G0S1S2SdUcS11P70A1A4S0G0S1S2SdUdS4fS30A1A4S0G0S1S2SdUeS11P72A1A4S0G0S1S2SdUfS11P73A1A4S0G0S1S2SdU13S3dA4S3G0A1A3A3A3A3A3A3A3A3A3S5fA3").
Definition X_nul : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4SdSdA2S1SdSdS32SbeS37A1A4S35A3").
Definition C_nul : axst := ltac2:(tb__ "0|1|
Sb8S16Sc8SacSadSaaA1S5S4S2SdA2M0S0G0S1S2SdU2S12S26S11PaA1S10N30A1A3A4S3G0A1A3S9bA3A2SabS15S6SdA1S61S5SeS63S3bA3P96S7A9S82A2").

Definition X_fitc : axst := Eval vm_compute in leaf_at C_open ir_cpy 0.
Definition X_fitn : axst := Eval vm_compute in leaf_at C_open ir_nul 0.
Definition p_fit : sv := ltac2:(tb__ "0|0|
S12S26S12S26S33S10Z20A1A3S57A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS10Z1000A1S45A2S0SeSfS45S11P1eA1M0A2S0SeSfS12S26S45S2fA3M1S12S26S33SbeS65A1A3A2S0SeSfG1G0A2S0SeSfS12S26S33S10Z20A1A3S45A2S3SeA1A3A3A3A3A3").
Definition X_fitc3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fitc p_fit vN) (fit_facts ++ ss_facts (ax_S X_fitc)).
Definition X_fitn3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fitn p_fit vN) (fit_facts ++ ss_facts (ax_S X_fitn)).

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition sret_pipe (X : axst) : axst * axst := ltac2:(tb__ "0|2|
S94S13S13S1fS1eR1A1S11S44A1A2Lo;S1bS23VX;A1A1M0U0M1A4S2S5S2SdcS2S2SbSdbR1R2A2A1Lj;Sd2G1S8S13G0A2A2A3S0S2R1S3S2A1A3A3S9S2A1S9eSc4VX;S0Sc1Sc2R1A1S0Sc1Sc3Sd0S8S2R1A2U1A2S10Z18A1A2S3Sc1A1A3A3A2A1S22Sc0R1SddS13S1bS23R1A1A1A2A2S22S1S22S22R2R1A4TX2;TX1;Tsel;TiN;").
Definition p_new : sv := ltac2:(tb__ "0|0|
S12S26S11S44A1S10Z20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SeSfS12S26S62S2fA3M0S12S26S11S44A1SbeS34A1A3A2S0SeSfG0S11P1eA1M1A2S0SeSfS62G1A2S3SeA1A3A3A3").
Definition X_sretc : axst := Eval vm_compute in leaf_at T_mok ir_cpy 0.
Definition X_sretn : axst := Eval vm_compute in leaf_at T_mok ir_nul 0.
Definition X_sretc1 : axst := Eval vm_compute in fst (sret_pipe X_sretc).
Definition X_sretc2 : axst := Eval vm_compute in snd (sret_pipe X_sretc).
Definition X_sretc3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sretc2 p_new vN) (new_facts ++ ss_facts (ax_S X_sretc2)).
Definition X_sretn1 : axst := Eval vm_compute in fst (sret_pipe X_sretn).
Definition X_sretn2 : axst := Eval vm_compute in snd (sret_pipe X_sretn).
Definition X_sretn3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sretn2 p_new vN) (new_facts ++ ss_facts (ax_S X_sretn2)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
SfS10Z10001A1S12S26S57S2fA3A2").
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).

Definition X_ret : axst := Eval vm_compute in leaf_at C_nul ir_ret 0.
Definition X_ret2 : axst := Eval vm_compute in drop_lastA X_ret (removelast (ss_objs (ax_S X_ret))).
Definition X_ret3 : axst := Eval vm_compute in drop_lastA X_ret2 (removelast (ss_objs (ax_S X_ret2))).

Definition P_fail : axst := ltac2:(tb__ "0|1|
Sb8S16Sc9SacSaeSaaA1S0S4S2SdA2M0S1S2SdUaS10Z0A1A4S3G0A1A3A2SabS15S6SdA1S53S33A1S3bSd7S7A9S35A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|4|
S0SeSfS10Z1000A1M0S11P8cA1M1A2S0SeSfG1S11P1eA1M2A2S0SeSfG0S11P8dA1M3A2S0SeSfG3G2A2S3SeA1A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
Sb8S16Sc9SacSaeSaaA1S0S4S2SdA2M0S1S2SdUaS11P8cA1A4S3G0A1A3A2SabS15S6SdA1S53S11P8dA1A1S5SeS9dS3bA3P8eS7A9S35A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fitc : wsub := ltac2:(tb__ "0|0|
SbdSaaS23S7cA1S23S46A1A3").
Definition s_fitn : wsub := ltac2:(tb__ "0|0|
SbdSaaS23S7eA1S23S47A1A3").
Definition s_sretc : wsub := ltac2:(tb__ "0|0|
SbdSaaS23S87A1S23S46A1A3").
Definition s_sretn : wsub := ltac2:(tb__ "0|0|
SbdSaaS23S89A1S23S47A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|1|
S0S4S21SdA2M0S1S21SdP6cS57A4S0G0S1S21SdP65S12S26S33S10Z10A1A3A4SbdSaaS23S81A1S23S48A1A3A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|1|
S0S4S21SdA2M0S1S21SdP6cS10Z10000A1A4S0G0S1S21SdP65S2fA4SbdSaaS23S41A1S23S48A1A3A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
SbdSaaS23S85A1S23S5bA1A3").

Definition ndO : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S90S8dA4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S91S3eA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S8eS3eA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S5dS3eA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S2aSa1S3S4S4SdS20A2SdA2A1S5dS3eA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S8fS8bA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S3Sa4A1S3eA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S2aS36S3S4S4SdS20A2SdA2A1S3Sa4A1S8cA4").
Definition z0 : sv := SLit 0.
Definition cutsI : list edescA := ltac2:(tb__ "0|4|
S0S4S4S22S29A2M0S4S20SdA2M1A2M2S1G0G1S1S22S29S5cS38A4S1S20SdZ64S2cA4A4S0G2S1G0G1S1S22S29S6dS38A4S1S20SdZ61S12S27Sb1S2dA3A4A4S0G2S1G0G1S1S22S29S6eS38A4S1S20SdZ5fS2cA4A4S0G2S1G0G1S1S22S29S6fS38A4S1S20SdZ5dS31A4A4S0G2S1G0G1S1S22S29S6bS38A4S1S20SdZ5cS2cA4A4S0G2S1G0G1S1S22S29S6cS43A4S1S20SdZ5aS2cA4A4S0G2S1G0G1S1S22S29S48S52A4S1S20SdZ50S2cA4A4S0G2S1G0G1S1S22S29S6aS60A4S1S20SdZ4bS2cA4A4S0G2S1G0G1S1S22S29S76S9aA4S1S20SdZ41S2cA4M3A4S0G2S1G0G1S1S22S29S77S51A4G3A4S0G2S1G0G1S1S22S29S46S50A4S1S20SdZ32S12S27S3dS54A3A4A4S0G2S1G0G1S1S22S29S47S50A4S1S20SdZ2dS2cA4A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsI : list edescA := ltac2:(tb__ "0|8|
S0S4S4S22S29A2M0S4S20SdA2M1A2M2S1G0G1S1S22S29S83S38A4S1S20SdZ5bS2cA4M3A4S0G2S1G0G1S1S22S29S41S38A4G3A4S0G2S1G0G1S1S22S29S7bS43A4S1S20SdZ55S2cA4M4A4S0G2S1G0G1S1S22S29S7dS43A4G4A4S0G2S1G0G1S1S22S29S80S43A4G4A4S0G2S1G0G1S1S22S29S79S52A4S1S20SdZ4eS2cA4M5A4S0G2S1G0G1S1S22S29S7aS52A4G5A4S0G2S1G0G1S1S22S29S58S60A4S1S20SdZ46S2cA4A4S0G2S1G0G1S1S22S29S86S51A4S1S20SdZ3cS2cA4M6A4S0G2S1G0G1S1S22S29S88S51A4G6A4S0G2S1G0G1S1S22S29S84S50A4S1S20SdZ28S2cA4A4S0G2S1G0G1S1S22S29S74S98A4S1S20SdZ0S2cA4M7A4S0G2S1G0G1S1S22S29S5bS99A4G7A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

End Lib_intern_rest.

