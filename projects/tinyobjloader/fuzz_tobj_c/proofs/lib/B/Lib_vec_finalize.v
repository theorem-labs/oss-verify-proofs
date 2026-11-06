(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "false"; "None"; "option"; "true"; "app"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "sobj"; "DUnknown"; "mkObj"; "SAlu"; "FcsrFrm0"; "SPAlign"; "SVar"; "mkSS"; "SPBranch"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AHead"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_finalize"; "vARv"; "vD"; "vV"; "vHDv"; "vL"; "z0"; "nd0"; "X_vf"; "eC"; "objs_vf"; "tv_vf"; "vE"; "vf_facts"; "E_call"; "FUEL_vf"; "Pre_vf"; "cutpcs_vf"; "nd_zero"; "CHv"; "C_go"; "O_Fv"; "O_Wv"; "O_arv"; "O_data"; "O_vec"; "P_fail"; "P_ok"; "P_zero"; "P_zero2"; "X_go"; "am_vf"; "nd_fail"; "nd_ok"; "vC"; "vHDn"; "vKv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup"; "vDp"; "c8"; "sp_entry"; "spm"; "O_F2"; "Pre_ad"; "f2_fact"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_finalize.VFAddr"; "vf_entry"; "vf_go"; "vf_ret"; "vf_ret2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.
Module Lib_arena_dup. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup. End Lib_arena_dup.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VFAddr.
  Definition vf_entry : Z := 0x916a0.
  Definition vf_go : Z := 0x9173c.
  Definition vf_ret : Z := 0x91738.
  Definition vf_ret2 : Z := 0x9171c.
End VFAddr.
Import VFAddr ADAddr.

Definition FUEL_vf : nat := 100%nat.
Definition vV : sv := SVar 12. Definition vARv : sv := SVar 13.
Definition vD : sv := SVar 15. Definition vC : sv := SVar 16. Definition vL : sv := SVar 17. Definition vE : sv := SVar 18.
Definition vHDv : sv := SVar 53. Definition vKv : sv := SVar 54.
Definition eC : sv := SMd M_MUL vE vC.
Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S17PaA1SeN40A1SeZ0A1Vcells;S12A5").
Definition O_Wv : sobj := ltac2:(tb__ "0|0|
S13S4aZ40A1S47SeZ0A1S2S10A1S12A5").
Definition O_vec : sobj := ltac2:(tb__ "0|1|
S13S25SeZ0M0A1SeZ20A1S0S10S48G0S24A2S0S10S48Z8S44A2S0S10S48Z10S46A2S0S10S48Z18S2eA2S2S10A1A3A3A3A3S12A5").
Definition O_arv (hd : sv) : sobj := ltac2:(tb__ "0|0|
S13S23SeZ0A1SeZ40A1S64Vhd;A1S12A5").
Definition O_data : sobj := ltac2:(tb__ "0|0|
S13S24SeZ0A1S27S2S10A1S12A5").
Definition vf_facts : list sprop := ltac2:(tb__ "0|a|
S0SdS16PaM0Z4M1A2S0SdSfS17G0A1M2SeS4fA1M3A2S0SdSfS17P1eA1M4S14S54S4aZ40M5A1M6S47A3A2S0SdSfG4G6A2S0SdSfG4G2A2S0SdS19S55SeN1000A1S47A3S0SdS19S55S47SeS67S4eA1A1A3S0SdS16PdG1A2S0SdSfSeZ1000A1M7S23A2S0SdSfS14S54S23SeG5A1A3G4A2S0SdSfS23G3A2S0SdSfS26G4A2S0SdS16PcZ3A2S0SdSfG7S25A2S0SdSfS14S54S25SeZ20M8A1A3G4A2S0SdSfS25G3A2S0SdSfSeZ1A1S2eA2S0SdSfS2eG7A2S0SdSfS2bS27A2S0SdSfS27SeS68Z2G8A2A1A2S0SdSfS14S54S24S27A3G4A2S0SdSfS24G4A2S0SdS4dS0SdSfSeZ7fff7f800000A1M9G4A2S0SdSfG4SeZ7fffff800000A1A2S0SdSfG9G2A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_vf : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS25SeZ20A1A4S0G0S1ScScS23SeZ40A1A4S0G0S1ScScS24S27A4S2G0A1A3A3A3").
Definition objs_vf (hd : sv) : list sobj := ltac2:(tb__ "0|1|
S9S11S0S11S37S2S10A1M0A1S0S11S38S0S11S3bS0S11S39Vhd;A1S0S11S3aS0S11S4bG0A1S2S11A1A3A3A3A3A3A3S57A3").
Definition Pre_vf : axst := ltac2:(tb__ "0|1|
S56S18S60S5cS5eS0S3S4ScA2M0S1S4ScU2S49A4S2G0A1A3A2S5bS15S6ScA1S2cS26A1S2fS5aS5A9S2aA2").

Definition CHv : list bitem := ltac2:(tb__ "0|5|
S0S50S52Z1M0Z0M1S0S3S1aS51A2M2S1S1aS51Z2S53S2bA1M3A4S2G2A1M4A3Z60A4S0S50S52G1G0S0G2S1S1aS51Z4G3A4G4A3Z40A4S2S50A1A3A3").
Definition tv_vf : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS23SeZ40A1A4S2G0A1A3").
Definition am_vf : amode := AHead vHDv true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S21S2dS2S3S3ScS1aA2ScA2A1S35S41A4").

Definition cutpcs_vf : list Z := ltac2:(tb__ "0|0|
S0S1aS61S0S1aS65S2S1aA1A3A3").
Definition optAv (x : option axst) : axst := match x with Some s => s | None => Pre_vf end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S5fS1cVk;S58S31S33VS;Vpc;A4S32A4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SaS1dS7SbS1dA1M0A1G0Lx;S1fS59S31S33VS;S8A5G0R1Ll;S2S1dA1X7x2A2").

Definition X_go : axst := Eval vm_compute in leaf_at Pre_vf vf_go 0.
Definition go_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfSeZ1000A1S24A2S0SdSfSeZ1A1S2bA2S2SdA1A3A3").
Definition C_go : axst := ax_add_facts go_facts X_go.

Definition E_call : axst := Eval vm_compute in leaf_at C_go ad_entry 0.
Definition s_call : wsub := ltac2:(tb__ "0|0|
S0S3S1bScA2S1S1bScP13S47A4S66PaS1eS30A1S1eS4cA1A3A3").
Definition optRv (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_call : list sobj := Eval vm_compute in optRv (entails_frA E_call Pre_ad s_call).

Definition Xk_call : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS25SeZ20A1A4S2G0A1A3").

Definition P_fail : axst := Eval vm_compute in T_afterA3 Pre_ad E_call s_call R_call Lib_arena_dup.P_fail Xk_call.
Definition P_ok : axst := Eval vm_compute in T_afterA3 Pre_ad E_call s_call R_call Lib_arena_dup.P_ok Xk_call.

Definition P_zero : axst := ltac2:(tb__ "0|1|
S56S18S62S5cS5dS5aA1S0S3S4ScA2M0S1S4ScU2S49A4S0G0S1S4ScUaSeZ0A1A4S2G0A1A3A3A2S5bS15S6ScA1S2cS26A1S2fP84S5A9S2aA2").
Definition P_zero2 : axst := ltac2:(tb__ "0|1|
S56S18S63S5cS5dS5aA1S0S3S4ScA2M0S1S4ScU2S49A4S0G0S1S4ScUaSeZ0A1A4S2G0A1A3A3A2S5bS15S6ScA1S2cS26A1S2fP84S5A9S2aA2").
Goal [leaf_matches1A NF (leaf_at Pre_vf vf_ret 0) P_zero; leaf_matches1A NF (leaf_at Pre_vf vf_ret2 0) P_zero2] = [true; true]
  /\ entails_frA E_call Pre_ad s_call = Some R_call /\ call_checkPA E_call Pre_ad s_call R_call [Lib_arena_dup.P_fail; Lib_arena_dup.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vHDn : sv := SVar 142.
Definition nd_zero : ndesc := nd0.
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S21S2dS2S3S3ScS1aA2ScA2A1S2S50A1S22S26S5A2A4").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S21S2dS2S3S3ScS1aA2ScA2A1S2S50A1S22S45S8A2A4").
Definition z0 : sv := SLit 0.
Definition cutsV : list edescA := ltac2:(tb__ "0|3|
S0S3S3S1cS20A2M0S3S1aScA2M1A2M2S1G0G1S1S1cS20S32S29A4S1S1aScZ64S28A4A4S0G2S1G0G1S1S1cS20S36S29A4S1S1aScZ50S28A4A4S2G2A1A3A3").
Definition exitsV : list edescA := ltac2:(tb__ "0|4|
S0S3S3S1cS20A2M0S3S1aScA2M1A2M2S1G0G1S1S1cS20S40S29A4S1S1aScZ5aS28A4A4S0G2S1G0G1S1S1cS20S30S29A4S1S1aScZ46S28A4A4S0G2S1G0G1S1S1cS20S3eS34A4S1S1aScZ0S28A4M3A4S0G2S1G0G1S1S1cS20S3cS42A4G3A4S0G2S1G0G1S1S1cS20S3dS43A4G3A4S0G2S1G0G1S1S1cS20S3fS34A4G3A4S2G2A1A3A3A3A3A3A3").
Goal ejcertA segs NF FUEL_vf cutpcs_vf 100 cutsV exitsV = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
