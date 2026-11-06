(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_027.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8States0 DrvR_facts DrvM_states.

(* [comment removed for export] *)
Module Start8StatesB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "option"; "Some"; "app"; "prod"; "bool"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_objs"; "SVar"; "ss_next"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB"; "E23B"; "E24B"; "EGB"; "GPC"; "S23okB"; "S22okB"; "S24okB"; "SPIN22B"; "SPIN23B"; "SPIN24B"; "S23ok0B"; "E23B_R"; "E24B_R"; "EGB_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "fail_state"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0"; "E22B"; "F22"; "F23"; "F24"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States Start8States0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S22okB : axst := ltac2:(tb__ "0|2|
S40S41S3bS42S12S3aA1M0S20P9fM1A1SaS1eS1fG0A1S4S1eS43G1Z100000A2S5S1eA1A3A3Pa0A4A2A1").
Lemma S22okB_eq : eager_ok E22B 0x100000 160%positive = S22okB.
Proof. reflexivity. Qed.
Definition E23B_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5").
Local Strategy expand [E23B_run__R].
Definition E23B_R : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) E23B_run__R).
Lemma E23B_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5S34A3").
Proof. exact (@eq_refl (option (list leafA)) E23B_run__R <: E23B_run__R = E23B_R). Qed.
Definition E23B : axst := Eval vm_compute in (match E23B_R with Some (l :: _) => la_state l | _ => S22okB end).
Lemma run23B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2eS6A5S9G0S4SfS11S29S26A2S5SfA1A3A2A3").
Proof. rewrite E23B_run. reflexivity. Qed.
Definition run22B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S3aA1S6A5").
Local Strategy expand [run22B_fail__R].
Definition SPIN22B : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E22B) (ro2__))) run22B_fail__R).
Lemma run22B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S3aA1S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run22B_fail__R <: run22B_fail__R = Some [mkLeafA SPIN22B RsCut]). Qed.
Lemma spin22B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S30S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E23B_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S29A1M0A1M1Z7050cA3S3S2S1S21G0A1Pa0A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S29A1S5G2A1A3S3S2S1bS14S29A1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ800000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ4022A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S23ok0B : axst := ltac2:(tb__ "0|1|
S40S41S3cS42S12S29A1M0S20Pa0A1S1fG0A1Pa1A4A2A1").
Lemma S23ok0B_eq : null_rw_ok E23B 0x800000 161%positive = S23ok0B.
Proof. reflexivity. Qed.
Definition S23okB : axst := Eval vm_compute in set_objs' S23ok0B (ss_objs (ax_S S23ok0B) ++ [o13p]).
Lemma S23okB_eq : ltac2:(tb__ "0|2|
S3S2S16S15S33S28S12S33A1M0SaS1eS1fG0A1S4S1eS3eS5S1eA1A3A3A2M1A2S2dA3S2ScS44G0G1A2S6A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E24B_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5").
Local Strategy expand [E24B_run__R].
Definition E24B_R : option (list leafA) := Eval vm_compute in ((fun ro3__ : option (list leafA) => ro3__) E24B_run__R).
Lemma E24B_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5S35A3").
Proof. exact (@eq_refl (option (list leafA)) E24B_run__R <: E24B_run__R = E24B_R). Qed.
Definition E24B : axst := Eval vm_compute in (match E24B_R with Some (l :: _) => la_state l | _ => S23okB end).
Lemma run24B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z7050cS4S0Z6bd84S5S0A1A3A3S2dS6A5S9G0S4SfS11S2aS26A2S5SfA1A3A2A3").
Proof. rewrite E24B_run. reflexivity. Qed.
Definition run23B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S29A1S6A5").
Local Strategy expand [run23B_fail__R].
Definition SPIN23B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => (leaf1 (fail_state E23B) (ro4__))) run23B_fail__R).
Lemma run23B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S29A1S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run23B_fail__R <: run23B_fail__R = Some [mkLeafA SPIN23B RsCut]). Qed.
Lemma spin23B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S31S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E24B_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S2aA1M0A1M1Z7050cA3S3S2S1S21G0A1Pa1A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S2aA1S5G2A1A3S3S2S1bS14S2aA1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ1000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ22A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S24okB : axst := ltac2:(tb__ "0|2|
S40S41S3dS42S12S2aA1M0S20Pa1M1A1SaS1eS1fG0A1S4S1eS43G1Z1000A2S5S1eA1A3A3Pa2A4A2A1").
Lemma S24okB_eq : eager_ok E24B 4096 162%positive = S24okB.
Proof. reflexivity. Qed.
Definition GPC : Z := 0x49fec.
Definition EGB_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5").
Local Strategy expand [EGB_run__R].
Definition EGB_R : option (list leafA) := Eval vm_compute in ((fun ro5__ : option (list leafA) => ro5__) EGB_run__R).
Lemma EGB_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5S36A3").
Proof. exact (@eq_refl (option (list leafA)) EGB_run__R <: EGB_run__R = EGB_R). Qed.
Definition EGB : axst := Eval vm_compute in (match EGB_R with Some (l :: _) => la_state l | _ => S24okB end).
Lemma runGB : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z7050cS4S0Z6bd84S5S0A1A3A3A3S2fS6A5S9G0S4SfS11S2bS26A2S5SfA1A3A2A3").
Proof. rewrite EGB_run. reflexivity. Qed.
Definition run24B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bd84S5S0A1A3S37S2aA1S6A5").
Local Strategy expand [run24B_fail__R].
Definition SPIN24B : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => (leaf1 (fail_state E24B) (ro6__))) run24B_fail__R).
Lemma run24B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bd84S5S0A1A3S37S2aA1S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run24B_fail__R <: run24B_fail__R = Some [mkLeafA SPIN24B RsCut]). Qed.
Lemma spin24B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bd84S5S0A1A3S32S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EGB_at : ltac2:(tb__ "0|2|
S3S2S0S22S12S2bA1M0A1S2cA3S3S2S1S21G0A1Pa2A3S3S2S7SbS1bS1bA2M1A1S13S2bA1S5G1A1A3S3S2S1bS14S2bA1S1cS3fA1A3S2SeSdS1eS1fG0A1A2U31A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8StatesB.

(* [comment removed for export] *)
Module DrvM_tstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "Some"; "option"; "cons"; "nil"; "list"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "sym_runA"; "mkLeafA"; "ax_X"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.DrvM_tstates"; "CXM_oom"; "CM_oom"; "VM_oom"; "A2M_oom"; "B2M_oom"; "RM_oom"; "S1M_oom"; "TM_oom"; "UM_oom"; "XM_oom"; "sM_oom"; "B1M_oom"; "B3M_oom"; "B4M_oom"; "EM_fw"; "EM_oom"; "LVM_xoom"; "RM_xoom"; "A1M_oom"; "nUM_oom"; "nVM_oom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states"; "nd_M1"; "CUTS_M"; "N_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts"; "node_okb"; "N_exR"; "carve_chk"; "carve_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "sstate"; "ss_objs"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "Pre_fw"; "EBUF"; "P_fw"; "Posts_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "s_exR"; "x4_okb"; "ex_img_okb"; "fw_u1"; "fw_u2"; "splitA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lc_obj"; "lcarve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "T_after"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR AxXform DrvGlueA DrvGlueB SysStepA SysA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR DrvIfaceM DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR_facts DrvM_states.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition EM_oom : axst := DrvM_states.E_oom.
Definition EM_fw : axst := DrvM_states.E_fw.

Definition CM_oom : axst := Eval vm_compute in fw_siteM 0x14d77 19 EM_fw.
Definition sM_oom : wsub := Eval vm_compute in s_fwc 0x14d77 19 CM_oom.
Definition RM_oom : list sobj := Eval vm_compute in optR (entails_frA CM_oom (Pre_fw 0x14d77 19) sM_oom).
Lemma frM_oom : ltac2:(tb__ "0|1|
S0S5S8S30A1M0A1S3eS14S3aZ14d77Z13A2S1dA3S4G0S18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccM_oom : ltac2:(tb__ "0|0|
S0S3S3fS14S3aZ14d77Z13A2S1dS18S40SdSbS12S3dA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TM_oom : axst := Eval vm_compute in T_after (Pre_fw 0x14d77 19) CM_oom sM_oom RM_oom P_fw.
Definition UM_oom : axst := Eval vm_compute in fw_undo1 TM_oom.
Definition VM_oom : axst := Eval vm_compute in fw_undo2M UM_oom.
Definition runM_xoom__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS39U14S29S15S2A5").
Local Strategy expand [runM_xoom__R].
Definition LVM_xoom : list leafA := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) runM_xoom__R).
Lemma runM_xoom : ltac2:(tb__ "0|1|
S0S5S8SdA1M0A1SfS39U14S29S15S2A5S4G0S23A2A3"). Proof. exact (@eq_refl (option (list leafA)) runM_xoom__R <: runM_xoom__R = Some LVM_xoom). Qed.
Definition XM_oom : axst := Eval vm_compute in nthA VM_oom LVM_xoom 0.

Definition CXM_oom : axst := Eval vm_compute in ex_siteD (-1024) XM_oom.

Definition A1M_oom : axst := x4set (SLit TP) EM_fw.
Definition A2M_oom : axst := splitA 0 (SLit (-2400)) A1M_oom.
Definition nUM_oom : nat := length (ss_objs (ax_S TM_oom)).
Definition S1M_oom : axst := selA (fw_u1 nUM_oom) TM_oom.
Definition nVM_oom : nat := length (ss_objs (ax_S UM_oom)).
Definition B1M_oom : axst := ltac2:(tb__ "0|0|
S4bS47U0S2fN400A1S1cA3S7S9S31S31A2A1A2").
Definition B2M_oom : axst := ex_img B1M_oom.
Definition B3M_oom : axst := app_objs ex_carvedR B2M_oom.
Definition B4M_oom : axst := x4set (SLit TP) B3M_oom.
Definition RM_xoom : list sobj := ltac2:(tb__ "0|0|
S50S3eS13S41Z0Z2A2S42S3bS13A2A3A1").

Lemma oomM_facts : ltac2:(tb__ "0|e|
S1S0S3S2bS22S28A2S2A3S1S0S5S8SdA1M0A1SfS39U32S29S22S2A5S4G0S6SdS10S21S49A2S7SdA1M1A3A2A3S1S0S3S43S21S2fS4cA1M2A2S2A3S1S0S5S32A1M3S48ScS25A1U0M4S2fN960A1A3S4S32ScS16A1M5A2A3S1S0S3S2dS16S7S9S31S31A2A1M6S2aA3S2A3S1S0SbSeS16S2eG5S2aA2A2S14A3S1S0S3S2bS14S28A2S2A3S1S0SbS4fS3aZ14d77Z13A2S14S1dS18S3cA5S1aA3S1S0S3S2bS1aS28A2S2A3S1S0S5SbA1M7S37S1aS6S35S36S45S26A1A1S7S35A1M8A3A2S4SbS19A2A3S1S0S8S30A1M9S33ScS19A1MaA1SaS30S33ScS1bA1A1MbS40S4eS30S4dS2aA4A3A3S1S0S3S51S34GaA1S28A2S2A3S1S0SbSeS19S4aGaGbA2A2S1bA3S1S0G7S37S1bS6S35S36S46S27A1A1S6S35S38G4A1G8A3A3A2S4SbS15A2A3S1S0S3S2bS15S28A2S2A3S1S0G0S23S6SdS10S1cS49A2G1A3A3S1S0G3S48ScS1cA1G4S2fN400A1A3S4S32ScS1eA1A2A3S1S0S3S44S1eA1S2A3S1S0S3S2dS17G6S2cA3S2A3S1S0SbSeS17S2eScS17A1S2cA2A2S1fA3S1S0S3S43S1fG2A2S2A3S1S0S3S52G6S11S20A1A2S2A3S1S0SbS4bS20G6A2S13A3S1S0S3S2bS13S28A2S2A3S1S0S5G9A1S3eS13S41Z0Z2A2McS42S3bS13A2MdA3S4G9S24A2A3S0S3S3fS13GcGdS24S7SbA1A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvM_tstates.

