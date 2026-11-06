(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "false"; "None"; "nat"; "option"; "true"; "app"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "sobj"; "DUnknown"; "mkObj"; "SAlu"; "SPAlign"; "SVar"; "FcsrFrm0"; "SPBranch"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AHead"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize"; "vARv"; "vD"; "vV"; "vL"; "z0"; "nd0"; "vHDv"; "eC"; "tv_vf"; "vE"; "E_call"; "FUEL_vf"; "Pre_vf"; "X_vf"; "cutpcs_vf"; "objs_vf"; "vf_facts"; "CHv"; "C_go"; "O_Fv"; "O_Wv"; "O_arv"; "O_data"; "O_vec"; "P_fail"; "P_ok"; "P_zero"; "X_go"; "am_vf"; "nd_fail"; "nd_ok"; "nd_zero"; "vC"; "vHDn"; "vKv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup"; "vDp"; "c8"; "spm"; "Pre_ad"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "BI"; "ASv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.AA"; "ar_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize.VFAddr"; "vf_entry"; "vf_go"; "vf_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VFAddr.
  Definition vf_entry : Z := 0x907b0.
  Definition vf_go : Z := 0x90810.
  Definition vf_ret : Z := 0x9080c.
End VFAddr.
Import VFAddr ADAddr.

Definition FUEL_vf : nat := 100%nat.
Definition vV : sv := SVar 12. Definition vARv : sv := SVar 13.
Definition vD : sv := SVar 15. Definition vC : sv := SVar 16. Definition vL : sv := SVar 17. Definition vE : sv := SVar 18.
Definition vHDv : sv := SVar 53. Definition vKv : sv := SVar 54.
Definition eC : sv := SMd M_MUL vE vC.
Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S16PaA1SeN40A1SeZ0A1Vcells;S12A5").
Definition O_Wv : sobj := ltac2:(tb__ "0|0|
S13S48Z40A1S46SeZ0A1S2S10A1S12A5").
Definition O_vec : sobj := ltac2:(tb__ "0|1|
S13S25SeZ0M0A1SeZ20A1S0S10S47G0S24A2S0S10S47Z8S43A2S0S10S47Z10S45A2S0S10S47Z18S2cA2S2S10A1A3A3A3A3S12A5").
Definition O_arv (hd : sv) : sobj := ltac2:(tb__ "0|0|
S13S23SeZ0A1SeZ40A1S5cVhd;A1S12A5").
Definition O_data : sobj := ltac2:(tb__ "0|0|
S13S24SeZ0A1S26S2S10A1S12A5").
Definition vf_facts : list sprop := ltac2:(tb__ "0|a|
S0SdS15PaM0Z4M1A2S0SdSfS16G0A1M2SeS4bA1M3A2S0SdSfS16P1eA1M4S14S50S48Z40M5A1M6S46A3A2S0SdSfG4G6A2S0SdSfG4G2A2S0SdS18S51SeN1000A1S46A3S0SdS18S51S46SeS62S4aA1A1A3S0SdS15PdG1A2S0SdSfSeZ1000A1M7S23A2S0SdSfS14S50S23SeG5A1A3G4A2S0SdSfS23G3A2S0SdSfS29G4A2S0SdS15PcZ3A2S0SdSfG7S25A2S0SdSfS14S50S25SeZ20M8A1A3G4A2S0SdSfS25G3A2S0SdSfSeZ1A1S2cA2S0SdSfS2cG7A2S0SdSfS2aS26A2S0SdSfS26SeS63Z2G8A2A1A2S0SdSfS14S50S24S26A3G4A2S0SdSfS24G4A2S0SdSfSeZ7fff7f800000A1M9G4A2S0SdSfG4SeZ7fffff800000A1A2S0SdSfG9G2A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_vf : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS25SeZ20A1A4S0G0S1ScScS23SeZ40A1A4S0G0S1ScScS24S26A4S2G0A1A3A3A3").
Definition objs_vf (hd : sv) : list sobj := ltac2:(tb__ "0|0|
S9S11S0S11S36S2S10A1A1S0S11S37S0S11S3aS0S11S38Vhd;A1S0S11S39S2S11A1A3A3A3A3A3S53A3").
Definition Pre_vf : axst := ltac2:(tb__ "0|0|
S52S19S5eS59S57S17S5ScA1S32S29A1S33S56S4A9S30A2").

Definition CHv : list bitem := ltac2:(tb__ "0|5|
S0S4cS4eZ1M0Z0M1S0S3S1aS4dA2M2S1S1aS4dZ2S4fS2aA1M3A4S2G2A1M4A3Z60A4S0S4cS4eG1G0S0G2S1S1aS4dZ4G3A4G4A3Z40A4S2S4cA1A3A3").
Definition tv_vf : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS23SeZ40A1A4S2G0A1A3").
Definition am_vf : amode := AHead vHDv true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S21S2bS2S3S3ScS1aA2ScA2A1S34S3fA4").

Definition cutpcs_vf : list Z := ltac2:(tb__ "0|0|
S0S1aS5fS0S1aS5dS2S1aA1A3A3").
Definition optAv (x : option axst) : axst := match x with Some s => s | None => Pre_vf end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S5bS1cVk;S54S2eS31VS;Vpc;A4S2fA4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SaS1dS7SbS1dA1M0A1G0Lx;S1fS55S2eS31VS;S8A5G0R1Ll;S2S1dA1X7x2A2").

Definition X_go : axst := Eval vm_compute in leaf_at Pre_vf vf_go 0.
Definition go_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfSeZ1000A1S24A2S0SdSfSeZ1A1S2aA2S2SdA1A3A3").
Definition C_go : axst := ax_add_facts go_facts X_go.

Definition E_call : axst := Eval vm_compute in leaf_at C_go ad_entry 0.
Definition s_call : wsub := ltac2:(tb__ "0|0|
S0S3S1bScA2S1S1bScP13S46A4S61PaS1eS2dA1S1eS49A1A3A3").
Definition optRv (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition R_call : list sobj := Eval vm_compute in optRv (entails_frA E_call Pre_ad s_call).

Definition Xk_call : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S1ScScS25SeZ20A1A4S2G0A1A3").

Definition P_fail : axst := Eval vm_compute in T_afterA3 Pre_ad E_call s_call R_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.P_fail Xk_call.
Definition P_ok : axst := Eval vm_compute in T_afterA3 Pre_ad E_call s_call R_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.P_ok Xk_call.

Definition P_zero : axst := ltac2:(tb__ "0|1|
S52S19S60S5aS58S56A1S0S3S6ScA2M0S1S6ScUaSeZ0A1A4S2G0A1A3A2S57S17S5ScA1S32S29A1S33P84S4A9S30A2").
Goal map (fun k => leaf_matches1A NF (leaf_at Pre_vf vf_ret k) P_zero) [0; 1]%nat = [true; true]
  /\ entails_frA E_call Pre_ad s_call = Some R_call /\ call_checkPA E_call Pre_ad s_call R_call [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.P_fail; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.P_ok] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vHDn : sv := SVar 142.
Definition nd_zero : ndesc := nd0.
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S21S2bS2S3S3ScS1aA2ScA2A1S2S4cA1S22S29S4A2A4").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S21S2bS2S3S3ScS1aA2ScA2A1S2S4cA1S22S44S8A2A4").
Definition z0 : sv := SLit 0.
Definition cutsV : list edescA := ltac2:(tb__ "0|3|
S0S3S3S1cS20A2M0S3S1aScA2M1A2M2S1G0G1S1S1cS20S2fS28A4S1S1aScZ64S27A4A4S0G2S1G0G1S1S1cS20S35S28A4S1S1aScZ50S27A4A4S2G2A1A3A3").
Definition exitsV : list edescA := ltac2:(tb__ "0|4|
S0S3S3S1cS20A2M0S3S1aScA2M1A2M2S1G0G1S1S1cS20S3eS28A4S1S1aScZ5aS27A4A4S0G2S1G0G1S1S1cS20S2dS28A4S1S1aScZ46S27A4A4S0G2S1G0G1S1S1cS20S3dS42A4S1S1aScZ0S27A4M3A4S0G2S1G0G1S1S1cS20S3bS40A4G3A4S0G2S1G0G1S1S1cS20S3cS41A4G3A4S2G2A1A3A3A3A3A3").
Goal ejcertA segs NF FUEL_vf cutpcs_vf 100 cutsV exitsV = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
