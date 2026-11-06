(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_push.

(* [comment removed for export] *)
Module Lib_arena_alloc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SPUle"; "cell"; "sobj"; "SAlu"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPAlign"; "mkSS"; "SPBranch"; "ss_objs"; "ss_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AK0"; "AOpen"; "AV0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc"; "c8"; "z0"; "SZ"; "tv0"; "vAR"; "vHD"; "p_fit"; "vDp"; "X_nohead"; "am_np"; "ndO"; "C_slow"; "O_F"; "O_W"; "O_ar"; "P_ok"; "X_aa"; "aa_facts"; "nd0"; "E_m"; "Pre_aa"; "base_fit"; "bd_m"; "ndMok"; "ndS"; "pN"; "spm"; "vCAP"; "vU"; "AL"; "CH"; "C_open"; "FUEL_aa"; "O_hdr"; "O_slot"; "P_fail"; "Pre_m"; "T_mnull"; "T_mok"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_sret"; "X_sret3"; "ahd"; "am_ok"; "am_open"; "ar_cells"; "bd_ok"; "bd_open"; "bd_slow"; "cutpcs_aa"; "gh0"; "ndF"; "ndK"; "ndM"; "ok_facts"; "pad_fit"; "pre_regs_aa"; "slow_facts"; "slow_regs"; "tv_m"; "two40"; "two47"; "vNX"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.AAAddr"; "aa_ret"; "aa_slow"; "aa_entry"; "aa_open"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "opp"; "pow"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.RA.ReallocAddr"; "malloc_pc"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma HTOP_ok : InitState.segs_top segs <= IMG_HI.
Proof. vm_compute. discriminate. Qed.

Module AAAddr.
  Definition aa_entry : Z := 0x9b91c.
  Definition aa_open : Z := 0x9b978.
  Definition aa_slow : Z := 0x9b9fc.
  Definition aa_join : Z := 0x9bb44.
  Definition aa_ret : Z := 0x9bb68.
End AAAddr.
Import AAAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_aa : nat := 400%nat.
Definition SZ : Z := 72. Definition AL : Z := 16.
Definition vAR : sv := SVar 12. Definition vHD : sv := SVar 15. Definition vDp : sv := SVar 19.

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11SbPaA1S9N40A1S9Z0A1Vcells;S10A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S3dZ40A1S2aS9Z0A1S2SdA1S10A5").
Definition ar_cells (hd : sv) : list cell := ltac2:(tb__ "0|2|
S0SdS23Z0M0S9S7fA1A2S0SdS23Z8S9S80A1A2S0SdS23Z10S9G0A1M1A2S0SdS23Z18S9S81A1A2S0SdS23Z20G1A2S0SdS23Z28S67A2S0SdS23Z30Vhd;A2S0SdS23Z38S9Z10000A1A2S2SdA1A3A3A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S11S27S9Z0A1S9Z40A1S55Vhd;A1S10A5").
Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S11Vhd;S9Z0M0A1S9Z18A1S0SdS23G0Vnx;A2S0SdS23Z8Vcap;A2S0SdS23Z10Vu;A2S2SdA1A3A3A3S10A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S11Vp;S9Z0A1S9S25A1S2SdA1S10A5").

Definition aa_facts : list sprop := ltac2:(tb__ "0|8|
S0SaS13PaM0Z4M1A2S0SaScSbG0A1M2S9S65A1M3A2S0SaScSbP1eA1M4SfS21S3dZ40M5A1M6S2aA3A2S0SaScG4G6A2S0SaScG4G2A2S0SaS15S22S9N1000A1S2aA3S0SaS15S22S2aS9S7bS64A1A1A3S0SaS13PcG1A2S0SaScS9Z1000A1S27A2S0SaScSfS21S27S9G5A1A3G4A2S0SaScS27G3A2S0SaScS28G4A2S0SaScS9Z7fff7f800000A1M7G4A2S0SaScG4S9Z7fffff800000A1A2S0SaScG7G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_aa : list sv := ltac2:(tb__ "0|1|
S6dS70S0S3S4S8A2M0S1S4S8UbS9S25A1A4S0G0S1S4S8UcS9S40A1A4S2G0A1A3A3A2").
Definition X_aa : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S9Z40A1A4S2G0A1A3").
Definition Pre_aa_S : sstate := ltac2:(tb__ "0|0|
S14S77S60S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31S28A1S2SeA1A3A3A3S71A3S34S6eS7A9").
Definition Pre_aa : axst := mkA Pre_aa_S X_aa.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S9Z40A1A4S2G0A1A3").
Definition CH : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1Zf0A3S0S68S69G1G0Z160A3S2S68A1A3A3").

Definition cutpcs_aa : list Z := ltac2:(tb__ "0|0|
S0S18S78S0S18S76S0S18S7eS2S18A1A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S7dS1aVk;S73S43S59VS;Vpc;A4S37A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_aa aa_open 0.
Definition nO : positive := ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.

Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S1fS28S66S3eS2S3S8S8A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_aa aa_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open aa_slow 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open aa_slow 1.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open aa_ret 0.

Definition E0 : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1S20A3S0S68S69G1G0S1eA3S2S68A1A3A3").
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S6dS17S1bS2bA1A1S0S3S4S8A2M0S1S4S8UbSbP65A1A4S0G0S1S4S8UdSbP66A1A4S0G0S1S4S8UeSbP67A1A4S0G0S1S4S8UfSbP68A1A4S0G0S1S4S8U10SbP69A1A4S0G0S1S4S8U11SbP6aA1A4S0G0S1S4S8U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").

Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).

Definition gh0 : sprop := SPEq (SVar 108) (SLit 0).
Definition C_slow : axst := ltac2:(tb__ "0|0|
S72S14S76S62S6cS12S5S8A1S16S1bS2bA1A1S0SaS5aS61A3P6dS7A9S33A2").
Definition bd_slow : list bitem := CH ++ E0.
Definition am_np : amode := AHead vHD false.

Definition E_m : axst := Eval vm_compute in leafA_at C_slow malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8PfS2aA4S6bPaS1bS36A1S1bS47A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S8S8SbS3cA1S9Z10020A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1Zf0A3S0S68S69G1G0S79S7aS1eZ160A2S6aA2A3S2S68A1A3A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok aa_ret 0.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_aa end.

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition iN : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_sret : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iN)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iN].
Definition X_sret1 : axst := Eval vm_compute in optAp (apply_axforms X_sret [AXSelect sel_sret; AXSplit (length sel_sret - 1) (SLit 24)]).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1 (removelast (ss_objs (ax_S X_sret1))).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS21SbS3cA1S9Z20A1A3").
Definition X_sret3 : axst := Eval vm_compute in carve_stateA X_sret2 p_new (SLit SZ).
Definition new_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS9Z18A1S9Z20A1A2S2SaA1A3").

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition u_fit : sv := Eval vm_compute in
  match find (fun o => sv_eqb (ob_base o) vHD) (ss_objs (ax_S X_fit)) with
  | Some o => match find (fun c => sv_eqb (c_off c) (SLit 16)) (ob_cells o) with Some c => c_val c | None => SLit 0 end
  | None => SLit 0 end.
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS21SfS21S28S9Z20A1A3S3fA3").
Definition pad_fit : sv := SAlu ALU_SUB p_fit base_fit.
Definition need_fit : sv := ltac2:(tb__ "0|0|
SfS21SfS21S5fS9S25A1A3S3fA3").

Definition nofit_fact : sprop := SPUle (SLit 65449) vU.
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).
Definition fit_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS38S29A2S0SaScS29SfS21S38S9ZfA1A3A2S0SaScS9Z1000A1S29A2S0SaScS29SbP1eA1A2S0SaScSfS21S29S9S25A1A3SfS21S28S74S3eA1A3A2S2SaA1A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition P_fail : axst := ltac2:(tb__ "0|1|
S72S14S75S6dS6fS6eA1S0S3S4S8A2M0S1S4S8UaS9Z0A1A4S2G0A1A3A2S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31S28A1S2SeA1A3A3A3S71A3S34S82S7A9S33A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|8|
S0SaScSbP90A1SbP8fA1M0A2S0SaScS9Z10000A1G0A2S0SaScG0S9S79S7cZ2Z28A2Z21A2A1A2S0SaScSfS21SbP8dM1A1M2S74G0A1A3M3SbP1eA1M4A2S0SaScG2G4A2S0SaScS9Z1000A1G2A2S0SaS13G1Z4M5A2S0SaScSfS21G2S9Z18A1A3SbP8cM6A1M7A2S0SaScSfS21G7S9S25A1A3G3A2S0SaS13G6G5A2S2SaA1A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|4|
S72S14S75S6dS6fS6eA1S0S3S4S8A2M0S1S4S8UaSbP8cA1M1A4S2G0A1A3A2S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31SbP8dA1M2A1S0SeS44G2SbP8eA1SbP8fA1M3SbP90A1A4S0SeS45G1A1S2SeA1A3A3A3A3A3S71A3S6SaS5eS34A3P91S7A9S0S3S8S8A2S1S8S8G2S74G3A1A4S33A3A2").
Definition am_ok : amode := ltac2:(tb__ "0|1|
S1fSbP8dA1SbP8eA1SbP8fA1S0S3S8S8A2M0S1S8S8SbP8cA1S9S25A1A4S2G0A1A3A4").
Definition bd_ok : list bitem := POT (SVar 144).

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S6bP64S1bS4bA1S1bS32A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S6bP64S1bS51A1S1bS32A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S6bP64S1bS4dA1S1bS2eA1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S6bP64S1bS2bA1S1bS2eA1A3A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S41S52A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S57S54A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S58S2cA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S39S2cA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S1dS63S2S3S3S8S18A2S8A2A1S39S2cA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S2S68A1S2cA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S56S53A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS37S35A4S1S18S8Z64S24A4A4S0G2S1G0G1S1S1aS1cS42S2dA4S1S18S8Z5aS24A4A4S0G2S1G0G1S1S1aS1cS2eS3bA4S1S18S8Z50S24A4A4S0G2S1G0G1S1S1aS1cS48S5dA4S1S18S8Z41S24A4M3A4S0G2S1G0G1S1S1aS1cS49S3aA4G3A4S2G2A1A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS4fS35A4S1S18S8Z5fS24A4M3A4S0G2S1G0G1S1S1aS1cS2bS35A4G3A4S0G2S1G0G1S1S1aS1cS4eS2dA4S1S18S8Z55S24A4M4A4S0G2S1G0G1S1S1aS1cS4cS2dA4G4A4S0G2S1G0G1S1S1aS1cS4aS2dA4G4A4S0G2S1G0G1S1S1aS1cS36S3bA4S1S18S8Z46S24A4A4S0G2S1G0G1S1S1aS1cS50S3aA4S1S18S8Z3cS24A4A4S0G2S1G0G1S1S1aS1cS46S5bA4S1S18S8Z0S24A4M5A4S0G2S1G0G1S1S1aS1cS32S5cA4G5A4S2G2A1A3A3A3A3A3A3A3A3A3").
End Lib_arena_alloc.

(* [comment removed for export] *)
Module Lib_finalize_shape_name.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SPUle"; "sobj"; "cell"; "SAlu"; "FcsrFrm0"; "mkSS"; "DUnknown"; "mkObj"; "SPAlign"; "SPBranch"; "ss_objs"; "ss_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AK0"; "AOpen"; "AV0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name"; "z0"; "c8"; "tv0"; "vHD"; "p_fit"; "vAR"; "O_F"; "O_W"; "O_ar"; "SZ"; "X_aa"; "aa_facts"; "vDp"; "X_nohead"; "am_np"; "C_nul"; "C_slow"; "base_fit"; "nd0"; "ndO"; "E_m"; "P_ok"; "Pre_aa"; "bd_m"; "fail_regs"; "ndF"; "ndK"; "ndMok"; "ndS"; "ok_regs"; "pN"; "spm"; "vCAP"; "AL"; "CH"; "C_open"; "C_rf"; "FUEL_aa"; "O_hdr"; "O_slot"; "P_fail"; "Pre_m"; "T_mnull"; "T_mok"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_ok"; "am_okc"; "am_open"; "ar_cells"; "bd_ok"; "bd_open"; "bd_slow"; "cutpcs_aa"; "gh0"; "ndKc"; "ndM"; "ok_facts"; "okc_facts"; "pre_regs_aa"; "slow_facts"; "slow_regs"; "tv_m"; "two40"; "two47"; "vNX"; "vU"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name.AAAddr"; "aa_ret"; "aa_slow"; "nm_fail"; "nm_ok"; "aa_entry"; "aa_open"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "opp"; "pow"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_finalize_shape_name.RA.ReallocAddr"; "malloc_pc"; "thunk_alloc"; "thunk_calloc"; "thunk_free"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma HTOP_ok : InitState.segs_top segs <= IMG_HI.
Proof. vm_compute. discriminate. Qed.

Module AAAddr.
  Definition aa_entry : Z := 0x905f0.
  Definition aa_open : Z := 0x9b978.
  Definition aa_slow : Z := 0x9b9fc.
  Definition aa_ret : Z := 0x905f4.
  Definition nm_ok : Z := 0x9060c.
  Definition nm_fail : Z := 0x907a0.
End AAAddr.
Import AAAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_aa : nat := 400%nat.
Definition SZ : Z := 1. Definition AL : Z := 1.
Definition vAR : sv := SVar 12. Definition vHD : sv := SVar 15. Definition vDp : sv := SVar 19.

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13SbPaA1S9N40A1S9Z0A1Vcells;S12A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S13S40Z40A1S2dS9Z0A1S2SeA1S12A5").
Definition ar_cells (hd : sv) : list cell := ltac2:(tb__ "0|2|
S0SeS22Z0M0S9S8bA1A2S0SeS22Z8S9S8cA1A2S0SeS22Z10S9G0A1M1A2S0SeS22Z18S9S8dA1A2S0SeS22Z20G1A2S0SeS22Z28S6cA2S0SeS22Z30Vhd;A2S0SeS22Z38S9Z10000A1A2S2SeA1A3A3A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S13S26S9Z0A1S9Z40A1S5aVhd;A1S12A5").
Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S13Vhd;S9Z0M0A1S9Z18A1S0SeS22G0Vnx;A2S0SeS22Z8Vcap;A2S0SeS22Z10Vu;A2S2SeA1A3A3A3S12A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S13Vp;S9Z0A1S9S2aA1S2SeA1S12A5").

Definition aa_facts : list sprop := ltac2:(tb__ "0|8|
S0SaS14PaM0Z4M1A2S0SaScSbG0A1M2S9S69A1M3A2S0SaScSbP1eA1M4SfS6dS40Z40M5A1M6S2dA3A2S0SaScG4G6A2S0SaScG4G2A2S0SaS15S6eS9N1000A1S2dA3S0SaS15S6eS2dS9S87S68A1A1A3S0SaS14PcG1A2S0SaScS9Z1000A1S26A2S0SaScSfS6dS26S9G5A1A3G4A2S0SaScS26G3A2S0SaScS24G4A2S0SaScS9Z7fff7f800000A1M7G4A2S0SaScG4S9Z7fffff800000A1A2S0SaScG7G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_aa : list sv := ltac2:(tb__ "0|1|
S75S78S0S3S4S8A2M0S1S4S8UbS9S2aA1A4S0G0S1S4S8UcS9S42A1A4S0G0S1S4S8U18S7bA4S2G0A1A3A3A3A2").
Definition X_aa : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S26S9Z40A1A4S2G0A1A3").
Definition Pre_aa_S : sstate := ltac2:(tb__ "0|0|
S11S81S64S74S10S6S8A1S5SdS0SdS27S2SeA1A1S0SdS28S0SdS29S24A1S2SdA1A3A3A3S79A3S2cS76S7A9").
Definition Pre_aa : axst := mkA Pre_aa_S X_aa.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S26S9Z40A1A4S2G0A1A3").
Definition CH : list bitem := ltac2:(tb__ "0|2|
S0S70S71Z1M0Z0M1Z62A3S0S70S71G1G0Z44A3S2S70A1A3A3").

Definition cutpcs_aa : list Z := ltac2:(tb__ "0|0|
S0S18S82S0S18S7eS0S18S8aS0S18S7dS0S18S80S0S18S7fS2S18A1A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S89S1aVk;S7cS46S5eVS;Vpc;A4S37A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_aa aa_open 0.
Definition nO : positive := ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.

Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S1fS24S6aS41S2S3S8S8A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_aa aa_slow 0.

Definition X_nofit : axst := Eval vm_compute in leafA_at C_open aa_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open aa_ret 0.

Definition E0 : list bitem := ltac2:(tb__ "0|2|
S0S70S71Z1M0Z0M1S20A3S0S70S71G1G0S1eA3S2S70A1A3A3").
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S75S17S1bS2eA1A1S0S3S4S8A2M0S1S4S8UbSbP65A1A4S0G0S1S4S8UdSbP66A1A4S0G0S1S4S8UeSbP67A1A4S0G0S1S4S8UfSbP68A1A4S0G0S1S4S8U10SbP69A1A4S0G0S1S4S8U11SbP6aA1A4S0G0S1S4S8U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").

Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).

Definition gh0 : sprop := SPEq (SVar 108) (SLit 0).
Definition C_slow : axst := ltac2:(tb__ "0|0|
S7aS11S7eS66S74S10S6S8A1S16S1bS2eA1A1S0SaS5fS65A3P6dS7A9S2bA2").
Definition bd_slow : list bitem := CH ++ E0.
Definition am_np : amode := AHead vHD false.

Definition E_m : axst := Eval vm_compute in leafA_at C_slow malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8PfS2dA4S73PaS1bS35A1S1bS4aA1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S8S8SbS3fA1S9Z10020A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|2|
S0S70S71Z1M0Z0M1Z62A3S0S70S71G1G0S85S86S1eZ44A2S72A2A3S2S70A1A3A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok aa_ret 0.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_aa end.

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition iN : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_sret : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iN)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iN].
Definition X_sret1 : axst := Eval vm_compute in optAp (apply_axforms X_sret [AXSelect sel_sret; AXSplit (length sel_sret - 1) (SLit 24)]).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1 (removelast (ss_objs (ax_S X_sret1))).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS6dSbS3fA1S9Z20A1A3").
Definition X_sret3 : axst := Eval vm_compute in carve_stateA X_sret2 p_new (SLit SZ).
Definition new_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS9Z18A1S9Z20A1A2S2SaA1A3").

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition u_fit : sv := Eval vm_compute in
  match find (fun o => sv_eqb (ob_base o) vHD) (ss_objs (ax_S X_fit)) with
  | Some o => match find (fun c => sv_eqb (c_off c) (SLit 16)) (ob_cells o) with Some c => c_val c | None => SLit 0 end
  | None => SLit 0 end.
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS6dSfS6dS24S9Z20A1A3S6bA3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS6fS25S32A3").
Definition need_fit : sv := SAlu ALU_ADD vU (SLit 1).

Definition nofit_fact : sprop := SPUle (SLit 65536) vU.
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).
Definition fit_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS32S25A2S0SaScS25SfS6dS32S9ZfA1A3A2S0SaScS9Z1000A1S25A2S0SaScS25SbP1eA1A2S0SaScSfS6dS25S9S2aA1A3SfS6dS24S83S41A1A3A2S2SaA1A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition fail_regs : list sv := ltac2:(tb__ "0|1|
S75S77S76A1S0S3S4S8A2M0S1S4S8UaS9Z0A1A4S0G0S1S4S8U1S9S7dA1A4S0G0S1S4S8U18S7bA4S2G0A1A3A3A3A2").
Definition C_rf : axst := ltac2:(tb__ "0|0|
S7aS11S7dS39S74S10S6S8A1S5SdS0SdS27S2SeA1A1S0SdS28S0SdS29S24A1S2SdA1A3A3A3S79A3S2cS84S7A9S2bA2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S7aS11S7fS39S74S10S6S8A1S5SdS0SdS27S2SeA1A1S0SdS28S0SdS29S24A1S2SdA1A3A3A3S79A3S2cS84S7A9S2bA2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|8|
S0SaScSbP90A1SbP8fA1M0A2S0SaScS9Z10000A1G0A2S0SaScG0S9S85S88Z2Z28A2Z21A2A1A2S0SaScSfS6dSbP8dM1A1M2S83G0A1A3M3SbP1eA1M4A2S0SaScG2G4A2S0SaScS9Z1000A1M5G2A2S0SaS14G1Z4A2S0SaScSfS6dG2S9Z18A1A3SbP8cA1M6A2S0SaScSfS6dG6S9S2aA1A3M7G3A2S0SaScG5G6A2S0SaScG6G4A2S0SaScG7G4A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ok_regs : list sv := ltac2:(tb__ "0|1|
S75S77S76A1S0S3S4S8A2M0S1S4S8UaSbP8cA1A4S0G0S1S4S8U1S9S7dA1A4S0G0S1S4S8U18S7bA4S2G0A1A3A3A3A2").
Definition C_nul : axst := ltac2:(tb__ "0|2|
S7aS11S7dS3eS74S10S6S8A1S5SdS0SdS27S2SeA1A1S0SdS28S0SdS29SbP8dA1M0A1S0SdS47G0SbP8eA1SbP8fA1M1SbP90A1A4S0SdS48SbP8cA1A1S2SdA1A3A3A3A3A3S79A3S5SaS62S2cA3P91S7A9S0S3S8S8A2S1S8S8G0S83G1A1A4S2bA3A2").
Definition am_ok : amode := ltac2:(tb__ "0|1|
S1fSbP8dA1SbP8eA1SbP8fA1S0S3S8S8A2M0S1S8S8SbP8cA1S9S2aA1A4S2G0A1A3A4").
Definition bd_ok : list bitem := POT (SVar 144).

Definition okc_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScS9Z1000A1M0SbP8cA1A2S0SaScG0SbP8dA1M1A2S0SaScG1SbP1eA1A2S2SaA1A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S7aS11S80S3eS74S10S6S8A1S5SdS0SdS27S2SeA1A1S0SdS28S0SdS29SbP8dA1A1S2SdA1A3A3A3S79A3S5SaS63S2cA3P91S7A9S2bA2").
Definition am_okc : amode := AHead (SVar 141) true.

Definition X_ret : axst := Eval vm_compute in leafA_at C_nul nm_ok 0.
Definition iS : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar 140)) (ss_objs (ax_S X_ret)) 0%nat.
Definition iHd : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar 141) &&& sv_eqb (ob_hi o) (SLit 24)) (ss_objs (ax_S X_ret)) 0%nat.
Definition sel_ret : list nat := Eval vm_compute in
  (List.filter (fun j => negb (Nat.eqb j iS || Nat.eqb j iHd)) (seq 0 (length (ss_objs (ax_S X_ret))))) ++ [iHd; iS].
Definition X_ret1 : axst := Eval vm_compute in optAp (apply_axforms X_ret [AXSelect sel_ret]).
Definition objsR : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_ret1))).
Definition ohR : sobj := Eval vm_compute in nth (length objsR) (ss_objs (ax_S X_ret1)) O_W.
Definition osR : sobj := Eval vm_compute in nth (S (length objsR)) (ss_objs (ax_S X_ret1)) O_W.
Definition X_ret2 : axst := Eval vm_compute in drop_lastA X_ret1 (objsR ++ [ohR]).
Definition X_ret3 : axst := Eval vm_compute in drop_lastA X_ret2 objsR.
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S73P64S1bS53A1S1bS36A1A3").

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S73P64S1bS4eA1S1bS30A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S73P64S1bS55A1S1bS30A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S73P64S1bS50A1S1bS31A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S73P64S1bS2eA1S1bS31A1A3A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S43S56A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S5cS59A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S5dS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S38S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S1dS67S2S3S3S8S18A2S8A2A1S38S2fA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S2S70A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S5bS57A4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S1dS23S2S3S3S8S18A2S8A2A1S2S70A1S58A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS37S33A4S1S18S8Z64S21A4A4S0G2S1G0G1S1S1aS1cS44S34A4S1S18S8Z5aS21A4A4S0G2S1G0G1S1S1aS1cS31S3dA4S1S18S8Z50S21A4A4S0G2S1G0G1S1S1aS1cS4bS61A4S1S18S8Z41S21A4M3A4S0G2S1G0G1S1S1aS1cS4cS3cA4G3A4S0G2S1G0G1S1S1aS1cS45S3aA4S1S18S8ZaS21A4A4S0G2S1G0G1S1S1aS1cS30S3bA4S1S18S8Z32S21A4A4S2G2A1A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS51S33A4S1S18S8Z5fS21A4M3A4S0G2S1G0G1S1S1aS1cS2eS33A4G3A4S0G2S1G0G1S1S1aS1cS4fS34A4S1S18S8Z55S21A4M4A4S0G2S1G0G1S1S1aS1cS4dS34A4G4A4S0G2S1G0G1S1S1aS1cS35S3dA4S1S18S8Z46S21A4A4S0G2S1G0G1S1S1aS1cS54S3cA4S1S18S8Z3cS21A4A4S0G2S1G0G1S1S1aS1cS52S3bA4S1S18S8Z28S21A4A4S0G2S1G0G1S1S1aS1cS49S3aA4S1S18S8Z0S21A4M5A4S0G2S1G0G1S1S1aS1cS36S60A4G5A4S2G2A1A3A3A3A3A3A3A3A3A3").
End Lib_finalize_shape_name.

(* [comment removed for export] *)
Module Lib_vec_reserve_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "SLit"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "nil"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "E_r15f"; "E_rW1f"; "E_c8"; "E_cW0"; "Pre_c"; "Xk_r"; "inj"; "kbytes"; "s_c"; "s_r"; "vW"; "xf_rback"; "E_r15x"; "E_rW1x"; "R_c8"; "R_cW0"; "R_r15"; "R_rW1"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW0"; "XW1"; "kn15"; "tvf0"; "xf_rcall"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW0"; "NW1"; "T_c8n0"; "T_c8ok"; "T_c8ok0"; "T_c8ok2"; "T_cW0n0"; "T_cW0ok"; "T_cW0ok0"; "T_cW0ok2"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.RA"; "Pre_ra"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "tv_factsA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_calloc_null"; "L_calloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S2SdS4bS53S54S32S43P64S44S45A7SeA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_r15x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S30S2fA2S8S0S1dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_rW1x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S31S2fA2S8S0S1eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_r15f_eq : ltac2:(tb__ "0|0|
S2S0SfS1dS9S4S2eS5S1S1dA1A1A3A2S11A3"). Proof. reflexivity. Qed.
Lemma E_rW1f_eq : ltac2:(tb__ "0|0|
S2S0SfS1eS9S4S2eS5S1S1eA1A1A3A2S12A3"). Proof. reflexivity. Qed.
Lemma T_r15f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S47S16A6S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S48S16A6S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S47S16A6S26A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S48S16A6S27A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S23S1cA2S8S0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S26S1cA2S8S0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S24S1cA2S8S0S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S27S1cA2S8S0S28A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S2dA1A4A1S25A2S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S1bA1A4A1S28A2S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S51S4eSbS50A1S4fA3A5S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S52S4eSbS50A1S4fA3A5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS51S4eSbS50A1S4fA3A5S37A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS52S4eSbS50A1S4fA3A5S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S1bA1A4A1S3eA2S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S7Z8A1A1A4A1S3aA2S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N15_eq : ltac2:(tb__ "0|0|
S2S0SfS29S9S4S17S2dA1S5S1S29A1A1A3A2S33A3"). Proof. reflexivity. Qed.
Lemma NW1_eq : ltac2:(tb__ "0|0|
S2S0SfS2cS9S4S17S1bA1S5S1S2cA1A1A3A2S36A3"). Proof. reflexivity. Qed.
Lemma NW0_eq : ltac2:(tb__ "0|0|
S2S0SfS2bS9S4S17S1bA1S5S1S2bA1A1A3A2S35A3"). Proof. reflexivity. Qed.
Lemma N8_eq : ltac2:(tb__ "0|0|
S2S0SfS2aS9S4S17S7Z8A1A1S5S1S2aA1A1A3A2S34A3"). Proof. reflexivity. Qed.
End Lib_vec_reserve_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserve_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "zlog15"; "KU"; "bitem"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bd_subst"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "sobj"; "SLit"; "sprop_eqb"; "ss_next"; "SVar"; "SPUle"; "holds"; "SPBranch"; "SPNot"; "mkObj"; "rw"; "DUnknown"; "ob_cells"; "sprop_below"; "eval"; "ss_objs"; "DZero"; "cell"; "obj_range"; "obj_wf"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "xr_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "nil"; "cons"; "app"; "Some"; "None"; "option"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vK"; "vW"; "kbytes"; "bdP"; "nd0"; "s_r"; "vDt"; "vE"; "cutsE"; "vAl"; "E_c8'"; "E_cW0'"; "O_data"; "Pre_c"; "Xk_r"; "inj"; "kn15"; "s_c"; "vV"; "O_W"; "O_vec"; "tv0"; "vC"; "B32"; "PD_ra"; "z0"; "E_r15f"; "E_rW1f"; "Pre_vr"; "R_c8"; "R_cW0"; "X15"; "X8"; "XW0"; "XW1"; "X_vr"; "ndG"; "ndN"; "spm"; "tvf0"; "B_EW"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "O_alv"; "P_fail"; "P_grown"; "P_keep"; "exitsE"; "tvP"; "two47"; "two48"; "vKn"; "xf_rback"; "xf_rcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "tv_factsA"; "JA_pre"; "ND"; "emeasA"; "ffinA"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf.Sum"; "baseF"; "basez"; "s_rbd"; "JL"; "Posts_vr"; "injF"; "injz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "import_subA"; "J_ofPA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.RA"; "Pre_ra"; "P0_ra"; "tv0"; "P_fail"; "P_ok"; "bd0"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "csz"; "payA"; "site_okA"; "T_afterA"; "call_checkTA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "ulink"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "FBx"; "T0"; "T_ok"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "robjs_okF"; "xrs_okF"; "FFx"; "PostsC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Lemma uval_kn15 : ltac2:(tb__ "0|1|
S12S3eS3R1S46A2S5dA2S0S2fS3R2S56A2S41S3R2S46A2M0S44G0Z2A2A2A3F_;Frho;").
Proof.
  intros rho HK. unfold kn15. pose proof (uval_range rho vK).
  assert (E1 : uval rho (SAlu ALU_SRL vK (SLit 1)) = uval rho vK / 2).
  { unfold uval. rewrite U_srl_lit. change (2 ^ (1 mod 64)) with 2. reflexivity. }
  unfold B32 in HK. rewrite uval_add_small; rewrite E1; [lia|]. pose proof (Z.div_le_upper_bound (uval rho vK) 2). lia.
Qed.

Definition P0_vr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S2fS83Q40M0S1fVr;P11A2A2Z0M1A3A1S2S0S2fS83G0S1fVr;PfA2A2G1A3A1F_;S1S9dVFF;S83G0S1fVr;PcA2A2Z20A3S9dVFF;S83G0S1fVr;PeA2A2Z30A3A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
ScdS12S33S82Q40A1A1Sd3OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
ScaS45VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2fSefVCST;R1A2S1S3eZ0R2A2S42R2SeeA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2fSefVXGL;R1A2S1S3eZ0R2A2S42R2SeeA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S33S34S34S2fS2fA2S2fA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S92VAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aVnd;Aa").
Definition Posts_vr : list (axst * jpostA) := ltac2:(tb__ "0|2|
S37S34S2aSa2A2M0S35S2aSa2S76S99S4aA1A4S37G0S35S2aSa2S74S99S8dS5bS36S34S34S11S2fA2S11A2A1M1S36S6A1A3A1A4S37G0S35S2aSa2S75S99S8dS78G1S49S47S7bA2A3A1A4S36G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S91VAInv;VCST;VXGL;S7eVKc;Vrho0;S95VFB;VFF;A2VFB;VFF;VBX;S8aVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S34S2aS89A2SdcFn;") := ltac2:(tb__ "0|0|
S93VAInv;VCST;VXGL;S7eVKc;Vrho0;S95VFB;VFF;A2VFB;VFF;VBX;S8aAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sa3S45S7eVrho0;Vtp0;S9aA5").

Lemma range_data : ltac2:(tb__ "0|2|
S12S11S11S2fS42S3R4S48R2A1A2S40Z2Z3fA2A2S1S3eS3cS2fS2fS27R5S52R4S48R3A1A2A2M0A3R2A2S42R2S3dS2fS2fG0A3A2A2S1S3eS3R6R5A2M1R3A2S42R3S41G1S3R6S48R4A1A2A2A2A2F_;F_;Fa;Fk;Fd;Frho;").
Proof.
  intros rho d k a Hk Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_data in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho (kbytes k) Hk) in Hr. unfold uval in *. lia.
Qed.

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|3|
S1S0S31S84S13S17S1aS19P1eA1M0S6cZ40A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aG0S19PaA1M1A2A1VF;A3S32A3S1S0S31S84S13S17S1aG1S16S79A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS16Z1A1S4dA2A1VF;A3S32A3S1S0S31S84S13S17S1aS4dS16Z1000A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS47S16S7aA1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS46S16S5dA1M2A2A1VF;A3S32A3S1S0S31S84S13S17S1aS48S47A1S16S6eA1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS48S46A1G2A2A1VF;A3S32A3S1S0S31S84S13S17S1aS16Z7fff7f800000A1G0A2A1VF;A3S32A3S0S31S84S13S17S1aG0S16Z7fffff800000A1A2A1VF;A3S32A3A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_e : 1 <= uval rho vE <= 4096;
  bz_w : uval rho vW <= 2 ^ 48;
  bz_k : uval rho vK <= B32;
  bz_ew : uval rho (kbytes vW) = uval rho vE * uval rho vW /\ uval rho (kbytes vW) <= B_EW;
  bz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK /\ uval rho (kbytes vK) <= B32;

  bz_top : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S12S2fS1S3eZ0R1A2S3eR1S3R2S19PaA1M0A2A2A2S0S2fS3R3S6cR2A1A2S43S3R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S12S33S13A1Sa8S13S1bR2A1R1A3S96R2A1S97R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B1') as H1'. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2.
  zf H1. zf H1'. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf HT1. zf HT2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold aceil, two47, RA.two47, two48, B_EW, B32 in *.
  rewrite !uval_lit in H2, H3, H4, H5, H6, H7, H8, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia.
  assert (EW : uval rho (kbytes vW) = uval rho vE * uval rho vW) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  constructor; unfold aceil, B_EW, B32; lia.
Qed.

Lemma robjs_r : ltac2:(tb__ "0|1|
S12S33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0A1S21S87S15S59R1A3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S97R3A1S0S2fSe1Vrho0;A1S83Q40S1fR4Sc7A2A2A3S9dVFF;S3R5S58A2Z20A3Se7VCST;Vrho0;VFB;VFF;R6S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1R5A8F_;F_;F_;F_;FR;Frho;").
Proof.
  intros rho R -> BZ ET HV o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
Qed.
Lemma xrs_r : ltac2:(tb__ "0|0|
S12S9dVFF;S3R1S58A2Z20A3S9dVFF;S3R2S4fA2Z30A3Se8VCST;VXGL;Vrho0;VFB;VFF;R3S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1S54A9F_;F_;Frho;").
Proof.
  intros rho HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S12Sd7S7eVrho0;R1A3S95VFB;VFF;Vrho0;A3S1S2S0S2fS3R3S46A2Z0M0A3A1S2S0S2fS3R4S4cA2G0A3A1F_;S1S9dVFF;S3R3S58A2Z20A3S9dVFF;S3R3S4fA2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C). unfold uval, vK, vDt, vV, vAl. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 14%positive eq_refl).
  auto.
Qed.

Lemma HIN_r : ltac2:(tb__ "0|3|
S2aS33S15A1M0S12SccS0G0R3S37S15S1eS19PaA1S16N40A1S16Z0A1S21S87S15S59R3A3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S96S14S2bR5A1A1A1S0S11SaaS4bR6A1PcA2S4fA3Sa8S13S1bR5A1S14S2bR7A1A1A3S95VFB;VFF;Vrho0;A3Sd7S7eVrho0;R7A3S1Se7VCST;Vrho0;VFB;VFF;R8S36S34S11S11A2A1M1S36S34S34S11S2fA2S11A2A1M2R9A8S1Se8VCST;VXGL;Vrho0;VFB;VFF;R8G1G2S54A9SafSe0VFB;R8G1A3Se9VFF;R8G2A3SacSabR8R9R7A3S4bRaA1A2A3A2A2F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR HB Hs12 HF HP0 Hav. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF HB) as BZ. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [exact (robjs_r rho R HR BZ ET HV)|]. split; [exact (xrs_r rho HV HA)|].
  unfold RA.P0_ra. rewrite rw_call', Hs12. destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl.
  split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma robjs_c : ltac2:(tb__ "0|2|
S12ScdS33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0M1A1S21S87S15S59R1A3A1S20A5S37S15S5aS4cS5cS46S4dA4S37S15S73S37S15S52S4cS48S46A1A2S36S15A1A3A3A3A3A3S97R4A1Se2R5ScfSceR4A1A1A2S0S2fS3R6S46A2G1A3S8fVFF;R6A2S9dVFF;S3R8S58A2Z20A3S9dVFF;S3R9S4fA2Z30A3SbbVCST;R9S3aS2fA1RaR8A5F_;F_;F_;F_;F_;F_;F_;FR;FAi;Frho;").
Proof.
  intros rho Ai R -> BZ HTK HK0 HFF HV HA o a Ho Hr. cbn in Ho. apply T_ok_rw in HTK. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - unfold O_alv in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _]. apply range_data in Hr; [|rewrite EK, HK0; lia]. rewrite EK, HK0 in Hr. lia.
Qed.
Lemma xrs_c : ltac2:(tb__ "0|1|
S12ScdS33S34S11S11A2A1M0S0G0R1S69S4cS46A2A3S97R4A1S0S2fS3R5S46A2Z0A3S8fVFF;R5A2S9dVFF;S3R7S58A2Z20A3S9dVFF;S3R8S4fA2Z30A3SbcVCST;VXGL;R8S3aS2fA1R9R7A6F_;F_;F_;F_;F_;F_;FX;FAi;Frho;").
Proof.
  intros rho Ai X -> BZ HK0 HFF HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _]. rewrite EK, HK0 in Ha. lia.
Qed.

Lemma baseF_E_cW0' : ltac2:(tb__ "0|0|
S96S14S2bS51A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_c8' : ltac2:(tb__ "0|0|
S96S14S2bS50A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_r15f : ltac2:(tb__ "0|0|
S96S14S2bS60A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_rW1f : ltac2:(tb__ "0|0|
S96S14S2bS61A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X15 : ltac2:(tb__ "0|0|
S96S14S2bS65A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW1 : ltac2:(tb__ "0|0|
S96S14S2bS68A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW0 : ltac2:(tb__ "0|0|
S96S14S2bS67A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X8 : ltac2:(tb__ "0|0|
S96S14S2bS66A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma site_cW0 : ltac2:(tb__ "0|2|
S12Sb8VAInv;VCST;VXGL;S7eVrho0;S95VFB;VFF;A2VFB;VFF;S51S57S51A1M0S64R1S4aS3aS2fA1ScdSccS1S1S3eZ1S3R3Sb6G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SaaG0PcA2A2S3R3SaaG0PdA2A2A2G1A3Sc0S36SbfA1SbdSacSabR3S64R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_cW0') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  factz HF (SPBranch BC_GEU vW (SLit 8)) HW8. rewrite uval_lit in HW8 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). change (wsub_get (s_c E_cW0') 12) with vW. change (wsub_get (s_c E_cW0') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. rewrite uval_mul_comm. fold (kbytes vW). rewrite EW. unfold B_EW in BEW.
  split; [nia|]. split; [lia | exact I].
Qed.
Lemma site_c8 : ltac2:(tb__ "0|2|
S12Sb8VAInv;VCST;VXGL;S7eVrho0;S95VFB;VFF;A2VFB;VFF;S50S57S50A1M0S63R1S4aS3aS2fA1ScdSccS1S1S3eZ1S3R3Sb6G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SaaG0PcA2A2S3R3SaaG0PdA2A2A2G1A3Sc0S36SbfA1SbdSacSabR3S63R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_c8') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). change (wsub_get (s_c E_c8') 12) with (SLit 8). change (wsub_get (s_c E_c8') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. rewrite uval_mul_lit by lia. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact I].
Qed.

Definition s_rbd (kn : sv) : list bitem := ltac2:(tb__ "0|2|
S38S6S37S6ScZ1M0Z0M1S48Vkn;A1A3S37S6SbG1S3fZ2S5A2G0A3S36S6A1A3A3S49S47Vkn;A2A3").

Lemma sums_bdP : ltac2:(tb__ "0|1|
S12S11S11S1S0S2fS9S49R2R1A2M0R3A2S41S43S3fZ6S3R3S48R2A1A2A2S3fZ4S3R3S48R1A1A2A2A2S3fZ20S3R3S4dA2A2A2A3S0S2fS8G0R3A2S3fS3fZ2S5A2S43SeS4S3R3R1A2A1A2A2A3A2Fk;Fw;Frho;").
Proof. intros. unfold bdP, PHI, KLG. cbn [bsumV bsumK]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma sums_s_rbd : ltac2:(tb__ "0|2|
S12S11S1S0S2fS9S98R1A1M0R2A2S41S3R2S48R1A1A2S9S49S47R1A2M1R2A2A2A3S0S2fS8G0R2A2S41S3fZ2S5A2S8G1R2A2A2A3A2Fkn;Frho;").
Proof. intros. unfold s_rbd, BIs, BIc. cbn [bsumV bsumK app]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma bd_nn_bdP : ltac2:(tb__ "0|1|
S12S11S11S3eS3fZ4S3R3S48R1A1A2A2S41S3fZ6S3R3S48R2A1A2A2S3fZ20M0S3R3S4dA2A2A2A2S3eS3R4R2A2S40Z2G0A2A2S7S49R4R3A2R5A2F_;F_;Fk;Fw;Frho;").
Proof.
  intros rho w k H1 H2. unfold bd_nn, bdP, PHI, KLG. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c]; [lia|].
  pose proof (zlog15_ZK _ H2). lia.
Qed.
Lemma bd_nn_s_rbd : ltac2:(tb__ "0|0|
S12S11S7S49S47R1A2R2A2S7S98R2A1R3A2F_;Fkn;Frho;").
Proof.
  intros rho kn H. unfold s_rbd. apply bd_nn_app. split; [|exact H]. unfold bd_nn, BIs, BIc. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c].
  - pose proof (uval_range rho (kbytes kn)). lia.
  - lia.
Qed.

Record injz (rho : valuation) (kn : sv) : Prop := IJ {
  ij_b : 4 * uval rho (kbytes vK) <= 3 * uval rho (kbytes kn);
  ij_a : 4 * uval rho (kbytes kn) <= 6 * uval rho (kbytes vW) + 32 * uval rho vE;
  ij_c : 1 <= uval rho (kbytes kn) <= B32;
  ij_e : uval rho (kbytes kn) = uval rho vE * uval rho kn }.
Definition injF (kn : sv) (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S0S31S86S13S13S84S13S17R1A1VF;A3Lf;S55Vkn;A1A3S32A3").
Lemma injz_of : ltac2:(tb__ "0|0|
S12S11S33S13A1Sa8S13S1bR3A1R1A3S97R4A1S9bR4R3A2S3eS3R6R5A2S40Z2Z31A2A2S9cR7R6A2F_;F_;F_;F_;FF;Fkn;Frho;").
Proof.
  intros rho kn F HF BZ H Hkn. unfold injF, inj in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  pose proof (uval_range rho kn) as Rkn.
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite !uval_lit in F3, F4 by lia.
  rewrite !uval_mul_lit in F1 by (rewrite ?EKn; lia). rewrite uval_add_small in F2 by (rewrite !uval_mul_lit by lia; lia).
  rewrite !uval_mul_lit in F2 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma grow15 : ltac2:(tb__ "0|0|
S12S97R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S47A2A2S42S3R4S47A2S3R4S56A2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S56A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2 |- *.
  pose proof (uval_range rho vK). pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma growW1 : ltac2:(tb__ "0|0|
S12S97R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S47A2A2S3eS3R4S56A2S3R4S47A2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S47A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2.
  pose proof (uval_range rho vK).
  destruct (Z_lt_ge_dec (uval rho vK) 2).
  - assert (E1 : uval rho vK = 1) by lia. rewrite E1, zlog15_1. pose proof (zlog15_ge1 (uval rho vW) ltac:(lia)). lia.
  - pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). pose proof (zlog15_mono (uval rho vK + uval rho vK / 2) (uval rho vW) ltac:(lia)). lia.
Qed.
Lemma grow0 : ltac2:(tb__ "0|0|
S12S11S0S2fS3R2S46A2Z0A3S3eZ8S3R3R2A2A2S3eS41S4S3R4S46A2A1Z1A2S4S3R4R3A2A1A2F_;F_;Fkn;Frho;").
Proof. intros rho kn -> H. rewrite zlog15_0. pose proof (zlog15_ge1 (uval rho kn) ltac:(lia)). lia. Qed.

Lemma pay_r : ltac2:(tb__ "0|3|
S2aS11S96S14S2bR2A1A1A1S9bR2S14S2bR3A1A1A2S12Sa8S13S1bR1A1S14S2bR5A1A1M0A3S97R2A1S1S3eS3R3R6A2M1S40Z2Z31A2A2S3eS41S4S3R3S46A2A1Z1A2S4G1A1A2A2F_;F_;Frho;Sb7S7eVrho0;S95VFB;VFF;A2G0S16Z0M2A1G2S49S47S46A2S98R4A1A8F_;F_;F_;Fkn;FE;").
Proof.
  intros E kn HB HI HG. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as [Hkn HL]. pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|apply bd_nn_s_rbd; exact NN]].
  - rewrite uval_lit by lia. destruct (sums_s_rbd rho kn) as [-> _]. destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. lia.
  - destruct (sums_s_rbd rho kn) as [_ ->]. destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_r15 : ltac2:(tb__ "0|1|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS60A1A1S16Z0M0A1G0S49S47S46A2S98S56A1A8").
Proof.
  apply pay_r; [exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (grow15 rho BZ HK0 HKW HWn)].
  destruct BZ as [Bsp Be Bw Bk _ _ _]. rewrite (uval_kn15 rho Bk). pose proof (uval_range rho vK). lia.
Qed.
Lemma pay_rW1 : ltac2:(tb__ "0|1|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS61A1A1S16Z0M0A1G0S49S47S46A2S98S47A1A8").
Proof.
  apply pay_r; [exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (growW1 rho BZ HK0 HKW HWn)]. destruct BZ; lia.
Qed.

Lemma pay_c : ltac2:(tb__ "0|2|
S2aS11S11S96S14S2bR3A1A1A1S9bR3S14S2bR4A1A1A2S12Sa8S13S1bR1A1S14S2bR6A1A1M0A3S97R2A1S1S3eS3R3R7A2M1S40Z2Z31A2A2S1S0S2fS3R3S46A2Z0A3S1S3eZ8G1A2S0S2fS3R3R6A2S3R3S48R7A1A2A3A2A2A2F_;F_;Frho;Sb7S7eVrho0;S95VFB;VFF;A2G0R4S5S49S47S46A2S49S47R5A2A8F_;F_;F_;Fcst;Fkn;FE;").
Proof.
  intros E kn cst HB HI HG. split; [reflexivity|]. split; [unfold KU; lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as (Hkn & HK0 & H8 & ->). pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  pose proof (grow0 rho kn HK0 H8) as HL.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|exact NN]].
  - destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. rewrite EK, HK0. lia.
  - destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_cW0 : ltac2:(tb__ "0|0|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS51A1A1Sb6S57S51A1A1S5S49S47S46A2S49S47S47A2A8").
Proof.
  apply pay_c; [exact baseF_E_cW0' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia.
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). rewrite uval_mul_comm. fold (kbytes vW).
  destruct BZ; repeat split; lia.
Qed.
Lemma pay_c8 : ltac2:(tb__ "0|0|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS50A1A1Sb6S57S50A1A1S5S49S47S46A2S49S47S16Z8A1A2A8").
Proof.
  apply pay_c; [exact baseF_E_c8' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). rewrite uval_mul_comm. fold (kbytes (SLit 8)).
  rewrite uval_lit by lia. destruct BZ; repeat split; lia.
Qed.

Lemma inj_holds : ltac2:(tb__ "0|4|
S12S11S97R2A1S3eS3R3R2A2S40Z2Z31A2A2S3eS3fZ4M0S3fS3R4S4dA2M1S3R4S46A2A2A2S3fZ3S3fG1S3R4R3A2A2A2A2S3eS3fG0S3fS3R5S4dA2M2S3R5R4A2A2A2S41S3fZ6S3fG2S3R5S47A2A2A2S3fZ20G2A2A2A2S1S3eZ1S3fS3R6S4dA2S3R6R5A2A2M3A2S3eG3S5dA2A2Sa8S13S1bR7A1S55R6A1A3F_;F_;F_;F_;F_;Fkn;Frho;").
Proof.
  intros rho kn BZ Hkn H1 H2 H3. destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  assert (Hkn32 : uval rho kn <= 4294967295) by nia.
  pose proof (uval_range rho kn).
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  unfold inj, B32. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite !uval_mul_lit by (rewrite ?EK, ?EKn; lia). rewrite EK, EKn. lia.
  - rewrite uval_add_small by (rewrite !uval_mul_lit by (rewrite ?EW; lia); rewrite EW; lia).
    rewrite !uval_mul_lit by (rewrite ?EW, ?EKn; lia). rewrite EW, EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. exact Hkn32.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2fS33S82Q40A1A1S9eF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S80S2aS12S33S82Q40A1A1S9eSa8S13S1bR3A1S14S2bR4A1A1A3VTR;S7fS45R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9eS9eS9eS9fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S9eS9eS9fS2R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S80S80S2aS2aSadS33S15A1M0S33S34S2aSa2A2M1A1S33S34S11S11A2M2A1S9eS12S33S82Q40A1A1M3G2S85G2R1R5A3S85G2R2S2cRbA1A3F_;Fr;S0S3bG0A1Sa5RaR9R8A3S39G0R7A2A3S0S31Sa4RbRaR9R8Sa9G1S2aS3cS2aSa2A2R7A4A5S32A3S12G3VTR;S7fS45RfRdR2R1A5Sa3S45S18S2bRdA1A1R2R1RaA5A2Ftp1;Frho1;S33Sd4A1M4SccSd3S81S45R9R8R10S35G4Sd5R3Sd6R2R1A2A4A5R13RaR9R4R2A4R13SacSabRbRfSd0R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2aSa2G4SccSd3S12G3G4SccSd3S85G1S35S2aSa2RaR9A4R14A3S81S45R12R11R19S35G4Sd5R9Sd6R8R7A2A4A5R1cR13R12RaR8A4Sd7S18S2bR1aA1A1SacSabR14R18Sd0R9R13RaA3A3R19A2R8A3S81S45R9R8ReS35G4Sd5R7Sd6R6R5A2A4A5ReSacSabR16R1aSd0RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf2R17Sd0RcR16RdA3R1bR1cR1dR10R1eR19RbA9S12Sd9R18Sd0RdR17ReA3R1cR1dS2bR1eA1S2bR1fA1S2bR11A1R1RcA9VTR;S7fS45Sa7R11SacSabR19R1dSd0ReR18RfA3A3R1eA2R18RdRcA5Sf3R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S7fS45R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CCALLOC : ltac2:(tb__ "0|1|
ScdS12S33S82Q40A1A1VTR;S7fS45Sc1VAInv;S36SbfA1M0SbdR3VKc;ScbA6Sc5SbeG0SbdA3R2R1A5Sa3S45S7eR2R1Sc4SbeVAInv;VCST;VXGL;G0SbdR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CREALLOC : ltac2:(tb__ "0|1|
S33S34S2fS2fA2M0A1S33S34G0S2fA2A1S10S12S33S82Q40A1A1SdZ2R3A2VTR;S7fS45S8cVAInv;VCST;VXGL;VKc;SafR6R5A2R6R5R4S8aSb4Sb0Sb3A2AaSaeR3R2A5Sa3S45S7eR3R2SeaVAInv;VCST;VXGL;VKc;SafS8aS5eR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S2aS89S34S2fS11A2M0S12S33S82Q40A1A1M1S2fG1S85S34S34S2aS89A2M2G0A2S35G2G0S35S2aS89R7R6A4R5A4S4eA3S1S3eZ0S8eS35G2G0S35S2aS89R8R7A4R6A4R5A2M3A2S42G3R3A2A2VTR;S7fS45VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2aS89S12S33S82Q40A1A1M0S2fG0S85S34S2aSa2A2S35S2aSa2R6S99R5A1A4S9aA3VTR;S7fS45VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_vr PD_ra]; do n right; left; reflexivity.

Lemma X_N : ltac2:(tb__ "0|4|
S2aS2aS11S2fS12S33S82Q40A1A1M0S2fG0S0S2aSddR8S38S13S55R6A1S14S2bR8A1A1A3A2R7A3S85S34S34S2aS89A2M1S34S2fS11A2M2A2S35G1G2S35S2aS89R8S4aA4S35S2fS11R6S5fA4A4S4eA3S3eS3fS41R7Z1A2S40Z2Z40A2A2R4A2S3eZ0R8A2S0S31S86S13S22S18S2bRcA1M3A1A1S38S13S55RaA1S14G3A1A3A3S32A3S12Sa8S13S1bR1A1S14S2bReA1A1A3Sa8S13S1bR2A1S55RdA1A3F_;Frho;VTR;S7fS45VJAv;S4aA1ReRaR9A5VFAM;R8R7A2A2F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fr;Fkn;FNs;FXs;").
Proof.
  intros Xs Ns kn r rho tp b tp0 HN Hin Hb Hr Hbelow Hinj.
  eapply TR_pre; [|apply (REENTER Ns nd0 (r, z0)); [exact Hin | meas]].
  intros w Hw. rewrite <- HN. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |].
  intros tr md _ HF. apply Forall_app. split; [exact (Hinj _ HF) | exact HF].
Qed.

Lemma X_X15 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S65R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X15 N15 kn15 80 rho tp b tp0 N15_eq); [innth 1 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X15) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r kn15 BZ); rewrite ?(uval_kn15 r Bk); unfold B32; try nia.
Qed.
Lemma X_XW1 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S68R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW1 NW1 vW 80 rho tp b tp0 NW1_eq); [innth 2 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW1) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_XW0 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S67R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW0 NW0 vW 80 rho tp b tp0 NW0_eq); [innth 3 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW0) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_X8 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X8 N8 (SLit 8) 80 rho tp b tp0 N8_eq); [innth 4 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X8) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPNot (SPBranch BC_GEU vW (SLit 8))) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  pose proof (uval_range r vW).
  apply (inj_holds r (SLit 8) BZ); rewrite ?uval_lit by lia; unfold B32; try nia.
Qed.

Lemma C_calloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S82Q40A1A1S9eS0S31S84S13S17S1cSd2S46S16Z0A1M0A3A1S14S2bR4A1A1A3S32A3S0S31S84S13S17S1cSd1S4cG0A3A1S14S2bR5A1A1A3S32A3VTR;S7fS45VJAv;S4aA1R6R5R4A5R3A2F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  destruct (P0_now rho Hav HP0) as (HKD & _ & _).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1, F2 by lia. exact (HKD F1 F2).
Qed.
Lemma C_realloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S82Q40A1A1S9eS0S31S84S13S17S1dS1cSd2S46S16Z0A1M0A3A1A1S14S2bR4A1A1A3S32A3S0S31S84S13S17S1dS1cSd1S4cG0A3A1A1S14S2bR5A1A1A3S32A3S96S14S2bR6A1A1A1VTR;S7fS45VJAv;S4aA1R7R6R5A5R4A2F_;F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2 HB. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & (HN & _ & _) & _).
  pose proof (basez_of rho _ HF HB) as [_ _ _ _ _ [EK _] _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (tnz_of_fact rho vDt (kbytes vK) F2) as Hnz. zf F1.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1 by lia.
  cbn [nd_tv nd0] in HN. destruct (proj1 (Forall_forall _ _) HN (vDt, kbytes vK) ltac:(left; reflexivity) Hnz) as (Hpos & _).
  unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho (kbytes vK))) with (uval rho (kbytes vK)) in Hpos.
  rewrite EK, F1 in Hpos. lia.
Qed.

Lemma X_E_r : ltac2:(tb__ "0|10|
S2aS2aS2aS2aS2aS2aS2aS2aS33S15A1M0S11S30S12S33S82Q40A1A1M1S2fG1S0S3bS2aA1M2Se4RfS7dA2S39S2aReA2A3S0S2aSddRfS38S13S6dS14S2bRfA1A1A3A2ReA3S0S31S84S13S17S1dS1cSd1S4cS16Z0M3A1M4A3A1A1S14S2bR10A1A1A3S32A3S0G0RaS37S15S1eS19PaA1S16N40A1G4S21S87S15S59RaA3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S96S14S2bR11A1A1A1S0S11SaaS4bR12A1PcA2S4fA3S0S31SedS54S2cR13A1A2S32A3S0S3bG0A1Sa5R14SaeS4bR14A1A3S39G0ReA2A3S0S31Sa4R15SaeS4bR15A1RfSa9S34S2aS89A2M5S2aS3cS2aS89A2S5eA4A5S32A3S0S31SbaS7eS4bR16A1A2S32A3S0S31SdaS4bR17A1S7eA2S32A3S0S31Sf0S7eS18S2bR18A1A1A2S32A3S0S31S90S18S2bR19A1A1S8dS38S34S11S11A2M6S36G6A1M7S5bA3S36S34S34S11S2fA2S11A2A1S49S47S46A2M8A3A2S32A3S0S31SaS18S2bR1aA1A1S49S47R13A2A2S32A3S0S31Se3S4bR1bA1S5bSb0A3S32A3Sb7S7eVrho0;S95VFB;VFF;A2S14S2bR1cA1A1G4G3G8S38S6SfS4bR1cA1Sb3A2S49S47R15A2A3A8S0S31S86SecSebSaeS7eS4bR1dA1S18S2bR1dA1A1A4S5eA3S32A3S0S2aSe6SaeR1eS4bR1eA1R18Sb1S54A6R1dA3S0G2Se4R1eS7cA2S39S2aR1dA2A3M9S0S2aSe6SaeR20S4bR20A1R1aSb2S54A6R1dA3G9S0S2aSdbS8bS35S11S11S19R1aA1S48R1bA1A4A1R1eA2R1dA3S0S33G6A1MaSdfSa6S4bR23A1SaeSb2R23A4Sb5A2S37G6S35S11S11S19R1bA1S48R1cA1A4G7A3A3S0GaSdfSa6S4bR24A1SaeSb1R24A4Sb0A2S5bA3S0S31S84S13S17S1dS1cSd1S19R1dA1G4A3A1A1S14S2bR21A1A1A3S32A3S0S31S86S13S22S18S2bR22A1MbA1A1S38S13S8bS35S11S11S19R1eA1S48R1fA1A4A1S14GbA1A3A3S32A3S0S31S86S13S22S18S2bR28A1McA1A1S38S13S6dS14GcA1A3A3S32A3S85S34G5S34S2fS11A2MdA2MeS35G5GdS35S2aS89R26S6bR21A1A4S35S2fS11Z3cS5fA4MfA4S4eA3S85GeS35G5GdS35S2aS89R24S6aS19R21A1R22A2A4GfA4S4eA3S3eS3fZ46S40Z2Z40A2A2R1fA2VTR;S7fS45VJAv;S4aA1R2dR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FpN;Fkn;FR;FTok;FTokB;FTok0;FTf;FTf0;FEf;FEx;FE;").
Proof.
  intros E Ex Ef Tf0 Tf Tok0 TokB Tok R kn pN rho tp b tp0 HEx HEf HD HR HB Hs12 HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass HPAY Hpd HTf0 HTf HTok0 HTokB HTok Htvok Htvf HpN Hbelow HbelowE HinF HinOK Hb.

  eapply TR_pre with (P := SPA segs (JAv nd0) Ef rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_rcall rho E Ex tp w HEx Hw) as Hw1.
    rewrite <- HEf. apply (SPA_refacts_JA segs); [exact Hw1 | exact HbelowE | ].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF HD). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX RA.P0_ra PTrue (fun _ H => H) (fun _ _ _ H => H) RA.Pre_ra (RA.ndR RA.tv0 RA.bd0) PD_ra NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CREALLOC eq_refl
           Ef (s_r Ef) R Xk_r rho tp [] tv0 [] (bdP vW vK) (bdP vW kn) ANone (FAM b tp0) HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl HPAY Hpd).
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD' HZ HFR HM HT HTK. apply (HIN_r Ef R rho ms HR HB Hs12 HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_ra In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am RA.ndR ND am_subst app].
    + rewrite HTf0, Htvf. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tf (ndN kn) (60, z0)); [exact HinF | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_rback rho' Tf0 Tf tp' w HTf Hw).
    + rewrite HTok0, Htvok. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tok (ndG (SVar pN) kn) (60, z0)); [exact HinOK | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_rback rho' Tok0 TokB tp' w HTokB Hw) as Hw1.
      rewrite <- HTok. unfold ax_add_facts.
      change (ax_setS TokB (add_facts (tv_factsA (SVar pN, kbytes kn)) (ax_S TokB))) with (ax_with_facts TokB (tv_factsA (SVar pN, kbytes kn) ++ ss_facts (ax_S TokB))).
      apply (SPA_refacts_JA segs); [exact Hw1 | exact Hbelow |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
      eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
      apply tnz_of_fact. exact (holds_mem _ _ _ HF2 HpN).
Qed.
Lemma X_E_r15 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S71R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_r15 E_r15x E_r15f T_r15f0 T_r15f T_r15ok0 T_r15okB T_r15ok R_r15 kn15 141%positive rho tp b tp0 E_r15x_eq E_r15f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_r15f.
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
  - pose proof pay_r15 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes kn15); BIc 0 (2 * KU) 1] ++ bdP vW kn15) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_r15f0_eq.
  - exact T_r15f_eq.
  - exact T_r15ok0_eq.
  - exact T_r15okB_eq.
  - exact T_r15ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 5.
  - innth 6.
  - exact Hb.
Qed.
Lemma X_E_rW1 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_rW1 E_rW1x E_rW1f T_rW1f0 T_rW1f T_rW1ok0 T_rW1okB T_rW1ok R_rW1 vW 141%positive rho tp b tp0 E_rW1x_eq E_rW1f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_rW1f.
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
  - pose proof pay_rW1 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes vW); BIc 0 (2 * KU) 1] ++ bdP vW vW) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_rW1f0_eq.
  - exact T_rW1f_eq.
  - exact T_rW1ok0_eq.
  - exact T_rW1okB_eq.
  - exact T_rW1ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 7.
  - innth 8.
  - exact Hb.
Qed.

Lemma X_E_c : ltac2:(tb__ "0|19|
S2aS2aS2aS2aS2aSadS33S15A1M0S11S11S12S33S82Q40A1M1A1M2S2fG2S0SadR8S57RdA1A3S0S3bG0A1Sa5ReS53R9A3S39G0R8A2A3S0S31Sa4RfS53RaR9S37S2aSc2SbeS36SbfA1M3SbdA3M4S37S2aSc3SbeG3SbdA3M5S36S2aA1A3A3A5S32A3S0S31SbaS7eRbA2S32A3S0S31Sf0S7eS18S2bR11A1A1A2S32A3S0S31S90S18S2bR12A1A1S4aA2S32A3S0S31SaS18S2bR13A1A1S49S47RcA2A2S32A3S0S31S29S18S2bR14A1A1Sb6RfA1A2S32A3S0S11SaaSa6R10S53G5R15A4Sc6A2S19Sd8S18S2bR15A1A1UaM6A2A1A3S0S11S19Sd8S18S2bR16A1A1G6A2A1S19P70A1M7A3Sb7S7eVrho0;S95VFB;VFF;A2M8S14S2bR17A1A1Sb6R12A1S5S49S47S46A2S49S47R10A2A8Sb8VAInv;VCST;VXGL;S7eVrho0;G8VFB;VFF;R18R13R12RfS4aS3aS2fA1ScdSccS1S1S3eZ1S3R11Sb6R15A1A2M9A2S42G9S40Z2MaZ27A2A2A2S1S0S2fS3fS3R11SaaR15PcA2A2S3R11SaaR15PdA2A2A2G9A3Sc0G3SbdSacSabR11R14R1A3R15A2A3A2A2Lms;LAi;AfS0S2aSb9S53R19R14R13G4A5R18A3S0S2aSb9S53R1aR15R14G5A5R18A3S12S0G1S23R1R14A2S23R1S48R15A1A2A3Fr;S0S11Sb6R17A1R14A3S0S3bS15A1MbS88S15S24S2bR1bA1A1U1McA3S39S15S1eG7S16Z0A1MdR15S36S26A1S25A5A2A3S0S33S34S11S11A2MeA1S2cR1cA1S38GeS69S4cS46A2MfS37GeS35S11S11G7R16A4S36GeA1M10A3A3A3S0S2aSdeS2dR1dSf1S2bR1dA1GcS52G7S48R18A1M11A2A3A2S38GeGfS37GeS35S11S11G7G11A4G10A3A3A2R1cA3S0S31S28S18S2bR1eA1A1S52G7S48R19A1A2A2S32A3S0S31S86GeS2eS18S2bR1fA1M12A1A1S38GeGfS37GeS35S11S11G7S48R1aA1A4G10A3A3A3S32A3S0GbS88S15S24G12A1U7M13A3S39S15S52S4cS48S46A1A2A2A3S0S31S84S13S17S1dS1cSd2S46GdA3A1A1S14S2bR20A1A1A3S32A3S96S14S2bR21A1A1A1S0S2aSdbS8bS35S11S11G7S48R1eA1A4A1S2dR22Se5S2bR22A1G13A2A2A2R21A3S0S31S84S13S17S1dS1cSd1G7GdA3A1A1S14S2bR23A1A1A3S32A3S0S31S86S13S22S18S2bR24A1M14A1A1S38S13S8bS35S11S11G7S48R20A1A4A1S14G14A1A3A3S32A3S85S34S34S2aS89A2M15S34S2fS11A2M16A2M17S35G15G16S35S2aS89R27S6bR21A1A4S35S2fS11Z3cS5fA4M18A4S4eA3S85G17S35G15G16S35S2aS89R25S6aG7R22A2A4G18A4S4eA3S3eS3fZ46S40GaZ40A2A2R1fA2VTR;S7fS45VJAv;S4aA1R2bR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fcst;Fkn;FR;Fs;FTok;FTokA;FTok0;FTn;FE;").
Proof.
  intros E Tn Tok0 TokA Tok s R kn cst rho tp b tp0 Hs He Hchk Htp Hnf Hnb Hbr Hcsz Hres H112 HPAY HSITE
         HTn HTok0 Hev Hcst Hblk HX HTokA Hwf HXb Hold HK0 HB HTok Hp0 Hbelow HinN HinOK Hb.
  subst s. unfold Pre_c in *.
  apply (calloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E (s_c E) R rho tp nd0 (bdP vW kn) (FAM b tp0) CCALLOC He Hchk Htp Hnf Hnb Hbr Hcsz Hres HPAY (fun _ _ _ _ => I) HSITE).
  -   intros rho' tp'. rewrite HTn. cbn [nd_tv nd_fr nd0]. apply (REENTER Tn (ndN kn) (60, z0)); [exact HinN | meas].
  -   intros rho' tp'. rewrite HTok0, H112, Hcst. cbn [nd_tv nd_fr nd0].
    eapply TR_pre; [|apply (REENTER Tok (ndG (SVar 112) kn) (60, z0)); [exact HinOK | meas]].
    intros w Hw.

    apply (SPA_JA_tv_ext segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ((SVar 112, cst) :: tv0) ((SVar 112, kbytes kn) :: tv0)) in Hw.
    2: { intros _. split; [cbn [map]; unfold tvv; cbn [fst snd]; rewrite (Hev rho'); reflexivity|].
         intros [|k] t t' Ht Ht'; cbn [nth_error] in Ht, Ht'; [injection Ht as <-; injection Ht' as <-; unfold tnz; cbn [fst]; tauto|].
         rewrite Ht in Ht'. injection Ht' as <-. tauto. }
    apply (SPA_JA_drop_tv segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue _ [] (bdP vW kn) 1) in Hw.
    2: {
         intros HF0 t Ht. unfold tv0 in Ht. cbn [nth_error] in Ht. injection Ht as <-. right.
         assert (EF : ss_facts (ax_S TokA) = ss_facts (ax_S Tok0)) by (rewrite <- HTokA; reflexivity).
         pose proof HB as HB0. pose proof HK0 as HK00. rewrite EF in HB0, HK00.
         pose proof (basez_of rho' _ HF0 HB0) as [_ _ _ _ _ [EK _] _].
         pose proof (holds_mem _ _ _ HF0 HK00) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
         rewrite uval_lit in F0 by lia. unfold tvv. cbn [snd]. change (bv_unsigned (eval rho' (kbytes vK))) with (uval rho' (kbytes vK)). rewrite EK, F0. lia. }
    cbn [remove_nth] in Hw.
    change (ND [(SVar 112, kbytes kn)] [] (bdP vW kn)) with (ndG (SVar 112) kn) in Hw.

    assert (Hw1 : SPA segs (JAv (ndG (SVar 112) kn)) TokA rho' tp' w).
    { rewrite <- HTokA. apply (SPA_x_requiv segs).
      - cbn [ax_X ax_setS]. rewrite HX. unfold X_vr. repeat constructor; cbn [fst snd]; try reflexivity. symmetry. apply Hev.
      - cbn [ax_S ax_setS]. unfold reshape_obj_at. cbn [ss_next set_objs]. exact HXb.
      - apply (SPA_reshape segs _ rho' Tok0 1 _ _ tp' w Hblk); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw].
        intros _. unfold obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi]. unfold soff. rewrite (Hev rho'). split; reflexivity. }
    assert (Hw3 : SPA segs (JAv (ndG (SVar 112) kn)) (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) rho' tp' w).
    { apply (SPA_drop_empty segs _ rho' TokA 7 _ tp' w Hold); [|exact Hw1].
      intros HF. pose proof (basez_of rho' _ HF HB) as [_ _ _ _ _ [EK _] _].
      pose proof (holds_mem _ _ _ HF HK0) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
      rewrite uval_lit in F0 by lia.
      unfold obj_hi_of, obj_lo_of, O_data. cbn [ob_lo ob_hi]. rewrite soff_lit_small by lia.
      rewrite (soff_smallu rho' (kbytes vK)) by (rewrite EK, F0; lia). rewrite EK, F0. lia. }
    rewrite <- HTok. unfold ax_add_facts.
    change (ax_setS (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (add_facts (tv_factsA (SVar 112, kbytes kn)) (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7)))))
      with (ax_with_facts (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (tv_factsA (SVar 112, kbytes kn) ++ ss_facts (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7))))).
    apply (SPA_refacts_JA segs); [exact Hw3 | exact Hbelow |].
    intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF2 Hp0).
Qed.
Lemma X_E_cW0 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_cW0 T_cW0n0 T_cW0ok0 T_cW0okA T_cW0ok (s_c E_cW0) R_cW0 vW (SMd M_MUL vW vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_cW0.
  - exact (site_cW0 rho).
  - exact T_cW0n0_eq.
  - exact T_cW0ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_cW0ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 9.
  - innth 10.
  - exact Hb.
Qed.
Lemma X_E_c8 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S6fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_c8 T_c8n0 T_c8ok0 T_c8okA T_c8ok (s_c E_c8) R_c8 (SLit 8) (SMd M_MUL (SLit 8) vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_c8.
  - exact (site_c8 rho).
  - exact T_c8n0_eq.
  - exact T_c8ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_c8ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 11.
  - innth 12.
  - exact Hb.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2aS89S34S2fS11A2M0S12S33S82Q40A1A1M1G1S85S34S34S2aS89A2M2G0A2S35G2G0S35S2aS89R6R5A4R4A4S77A3VTR;S7fS45VJAv;R6A1R7R4R3A5VFAM;S8eS35G2G0S35S2aS89R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X15. meas.
  - apply X_XW1. meas.
  - apply X_XW0. meas.
  - apply X_X8. meas.
  - apply X_E_r15. meas.
  - apply X_E_rW1. meas.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_E_cW0. meas.
  - apply X_E_c8. meas.
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S94S45VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc8S45SbeVAInv;VCST;VXGL;A5").

Theorem vec_reserve_sum : ltac2:(tb__ "0|0|
S33S82Q40A1A1Sa1S45Vok;S7fS45S8cVAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aS4aAaS62Vrho0;R1A5Sa3S45S7eVrho0;R1S9aA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc9S45SbeVAInv;VCST;VXGL;A5").

Theorem vec_reserve_sum_ex : ltac2:(tb__ "0|0|
S33S82Q40A1A1Sa0S45S7fS45S8cVAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aS4aAaS62Vrho0;R1A5Sa3S45S7eVrho0;R1S9aA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_reserve_pf.

(* [comment removed for export] *)
Module Lib_vec_push_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_push"; "E_vr"; "s_v"; "R_v"; "T_grown"; "T_keep"; "Xk_v"; "vKg"; "xf_vback"; "T_fail0"; "T_grown0"; "T_keep0"; "slot_facts"; "vC1"; "E_vr0"; "FUEL_vp"; "T_fail"; "T_grownF"; "T_keepF"; "cutpcs_vp"; "cutsP"; "exitsP"; "hse_fact"; "vDg"; "xf_vcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "Pre_vr"; "bdP"; "tv0"; "P_grown"; "P_keep"; "vK"; "P_fail"; "vW"; "kbytes"; "tvP"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "app"; "prod"; "cons"; "nil"; "bool"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve Lib_vec_push.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.
Import VPAddr.

Lemma ejcertP_ok : ltac2:(tb__ "0|0|
S0S30S3cS3aS3bS11S15P64S16S17A7S32A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S0S2bS1A1S34S10S1aA2S2aS1S3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S1S36S1bS3S4S5S1fS8A6SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S1S36S1bS3S4S5S21S8A6SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S1S36S1bS3S4S5S1eS8A6ScA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S2bS1A1S34SdSaA2S2aS1S7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail_eq : ltac2:(tb__ "0|0|
S0S2bS1A1S34SbSaA2S2aS1S12A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S2bS1A1S34ScSaA2S2aS1S6A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepF_eq : ltac2:(tb__ "0|0|
S0S1S37S7S2cS27S2cS27SeS20A1S2eS27S18S2fS27A1A3A3S28S2S7A1A1A3A2S14A3"). Proof. reflexivity. Qed.
Lemma T_grownF_eq : ltac2:(tb__ "0|0|
S0S1S37S6S2cS27SeS9A1S28S2S6A1A1A3A2S13A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S0S29S2dS26S26A2A1S35S33S4S1bS1fS3A4S1dA2S1dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0S29S39A1S38S33S4S1bS1fS3A4S1cS22S20A2A2S1cSfS20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S0S29S2dS26S26A2A1S35S33S4S1bS21S3A4S1dA2S1dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|1|
S0S29S2dS26S26A2M0A1S35S33S4S1bS1eS3A4S24A2S2eG0S31S26S26S19S23S9A1A4S2fG0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0S29S39A1S38S33S4S1bS1eS3A4S1cS22S25A2A2S1cSfS9A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

End Lib_vec_push_eqs.

