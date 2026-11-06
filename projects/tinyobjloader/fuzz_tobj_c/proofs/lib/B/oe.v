(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_006.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob DrvR_facts DrvM_states.

(* [comment removed for export] *)
Module Start8StatesB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "option"; "Some"; "app"; "prod"; "bool"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_objs"; "SVar"; "ss_next"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB"; "E23B"; "E24B"; "EGB"; "GPC"; "S23okB"; "S22okB"; "S24okB"; "SPIN22B"; "SPIN23B"; "SPIN24B"; "S23ok0B"; "E23B_R"; "E24B_R"; "EGB_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "fail_state"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0"; "E22B"; "F22"; "F23"; "F24"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0.
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
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5").
Local Strategy expand [E23B_run__R].
Definition E23B_R : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) E23B_run__R).
Lemma E23B_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5S34A3").
Proof. exact (@eq_refl (option (list leafA)) E23B_run__R <: E23B_run__R = E23B_R). Qed.
Definition E23B : axst := Eval vm_compute in (match E23B_R with Some (l :: _) => la_state l | _ => S22okB end).
Lemma run23B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5S9G0S4SfS11S29S26A2S5SfA1A3A2A3").
Proof. rewrite E23B_run. reflexivity. Qed.
Definition run22B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S3aA1S6A5").
Local Strategy expand [run22B_fail__R].
Definition SPIN22B : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E22B) (ro2__))) run22B_fail__R).
Lemma run22B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S3aA1S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run22B_fail__R <: run22B_fail__R = Some [mkLeafA SPIN22B RsCut]). Qed.
Lemma spin22B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S30S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E23B_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S29A1M0A1M1Z706a0A3S3S2S1S21G0A1Pa0A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S29A1S5G2A1A3S3S2S1bS14S29A1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ800000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ4022A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
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
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5").
Local Strategy expand [E24B_run__R].
Definition E24B_R : option (list leafA) := Eval vm_compute in ((fun ro3__ : option (list leafA) => ro3__) E24B_run__R).
Lemma E24B_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5S35A3").
Proof. exact (@eq_refl (option (list leafA)) E24B_run__R <: E24B_run__R = E24B_R). Qed.
Definition E24B : axst := Eval vm_compute in (match E24B_R with Some (l :: _) => la_state l | _ => S23okB end).
Lemma run24B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5S9G0S4SfS11S2aS26A2S5SfA1A3A2A3").
Proof. rewrite E24B_run. reflexivity. Qed.
Definition run23B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S29A1S6A5").
Local Strategy expand [run23B_fail__R].
Definition SPIN23B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => (leaf1 (fail_state E23B) (ro4__))) run23B_fail__R).
Lemma run23B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S29A1S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run23B_fail__R <: run23B_fail__R = Some [mkLeafA SPIN23B RsCut]). Qed.
Lemma spin23B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S31S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E24B_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S2aA1M0A1M1Z706a0A3S3S2S1S21G0A1Pa1A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S2aA1S5G2A1A3S3S2S1bS14S2aA1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ1000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ22A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S24okB : axst := ltac2:(tb__ "0|2|
S40S41S3dS42S12S2aA1M0S20Pa1M1A1SaS1eS1fG0A1S4S1eS43G1Z1000A2S5S1eA1A3A3Pa2A4A2A1").
Lemma S24okB_eq : eager_ok E24B 4096 162%positive = S24okB.
Proof. reflexivity. Qed.
Definition GPC : Z := 0x4a180.
Definition EGB_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5").
Local Strategy expand [EGB_run__R].
Definition EGB_R : option (list leafA) := Eval vm_compute in ((fun ro5__ : option (list leafA) => ro5__) EGB_run__R).
Lemma EGB_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5S36A3").
Proof. exact (@eq_refl (option (list leafA)) EGB_run__R <: EGB_run__R = EGB_R). Qed.
Definition EGB : axst := Eval vm_compute in (match EGB_R with Some (l :: _) => la_state l | _ => S24okB end).
Lemma runGB : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5S9G0S4SfS11S2bS26A2S5SfA1A3A2A3").
Proof. rewrite EGB_run. reflexivity. Qed.
Definition run24B_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S2aA1S6A5").
Local Strategy expand [run24B_fail__R].
Definition SPIN24B : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => (leaf1 (fail_state E24B) (ro6__))) run24B_fail__R).
Lemma run24B_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S2aA1S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run24B_fail__R <: run24B_fail__R = Some [mkLeafA SPIN24B RsCut]). Qed.
Lemma spin24B : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S32S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EGB_at : ltac2:(tb__ "0|2|
S3S2S0S22S12S2bA1M0A1S2cA3S3S2S1S21G0A1Pa2A3S3S2S7SbS1bS1bA2M1A1S13S2bA1S5G1A1A3S3S2S1bS14S2bA1S1cS3fA1A3S2SeSdS1eS1fG0A1A2U31A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8StatesB.

(* [comment removed for export] *)
Module DrvTLXi_f3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "Some"; "nil"; "list"; "option"; "false"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_facts"; "ss_next"; "SPUle"; "SVar"; "sobj"; "sprop"; "sprop_eqb"; "ss_lenient"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX"; "bd_J"; "keptX"; "CP"; "backedge_okb"; "bd_L"; "exitc_b"; "ndJX"; "ndLX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "PreF"; "PostF"; "CUTS_X"; "FUEL_X"; "vB"; "vCap"; "vPlen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states"; "R_fp_Pc0"; "R_fp_Pc1"; "T_fp_Pc0"; "T_fp_Pc1"; "J_E"; "LJa_Pc0"; "LJa_Pc1"; "LJb_Pc0"; "LJb_Pc1"; "LX_Pc0"; "LX_Pc1"; "s_fp"; "vP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvTLXi_h.

Lemma XPc0_facts : ltac2:(tb__ "0|12|
S1S0S8S7S13A1M0A1S45S20S37A1M1S26S39G1A1M2A3S5G0S2eA2A3S1S0S2S44G1S26G2S2eS4S18S27S6S18A1M3A3A5S3A3S1S0S2S4aS2dG2A2S3A3S1S0S2S3eS2dS10S1aS37A1M4A1M5A2S3A3S1S1S0S2S3dG5S25S22Z1M6A1M7A1A2S3A3S0S2S47G5S1eA2S3A3A2S1S1S0SdS3bG2PcA2S12S3aA1M8A3S0SdS3bG2PdA2S2cA3A2S1S0S2S48SfS1aG1A1M9A1MaSeZ0MbA1McS46G7S1eA5S3A3S1S0S2S42GaA1S3A3S1S0S2S41GaS1fS5SaU0A2MdS2eA4S3A3S1S0S2S43GaS1fGdS17G9A1S40S1cG1A1A6S3A3S1S0S2S4bS14S15S11SeZ1000A1G8A2A1GaA3S3A3S1S0S18S49S26G1G2S2eS27A5S30A3S1S1S0S2S3eS2dS10S1aS30A1MeA1MfA2S3A3S1S0S2S16GeA1S9A3S0S2S3dGfS24S1eA1A2S3A3A2A2S1S0S8S7S19A1M10A1S1dS3fS29S28S30S3A5S5G10S4S19S1bS33S3cA2S4S19S1bS35S3cA2S6S19A1A3A3A2A3S1S0S2S4cS18S21S32S4dGbG6A2GcA2S4ScSdSdA2M11SbSdSdS2aS2bA4S6G11A1A3S1eA3S4S18S33S4S18S35G3A3A3A3S3A3S0S2S23GbSfG4A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XPc1_facts : ltac2:(tb__ "0|11|
S1S0S8S7S13A1M0A1S45S20S38A1M1S26S39G1A1M2A3S5G0S2fA2A3S1S0S2S44G1S26G2S2fS4S18S27S6S18A1M3A3A5S3A3S1S0S2S4aS2dG2A2S3A3S1S0S2S3eS2dS10S1aS38A1M4A1M5A2S3A3S1S1S0S2S3dG5S25S22Z2A1M6A1A2S3A3S0S2S47G5S1eA2S3A3A2S1S1S0SdS3bG2PcA2S12S3aA1M7A3S0SdS3bG2PdA2S2cA3A2S1S0S2S48SfS1aG1A1M8A1M9SeZ0A1MaS46G6S1eA5S3A3S1S0S2S42G9A1S3A3S1S0S2S41G9S1fS5SaU0A2MbS2fA4S3A3S1S0S2S43G9S1fGbS17G8A1S40S1cG1A1A6S3A3S1S0S2S4bS14S15S11SeZ1000A1G7A2A1G9A3S3A3S1S0S18S49S26G1G2S2fS27A5S31A3S1S1S0S2S3eS2dS10S1aS31A1McA1MdA2S3A3S1S0S2S16GcA1S9A3S0S2S3dGdS24S1eA1A2S3A3A2A2S1S0S8S7S19A1MeA1S1dS3fS29S28S31S3A5S5GeS4S19S1bS34S3cA2S4S19S1bS36S3cA2S6S19A1A3A3A2A3S1S0S2S4cS18S21S32S4dZ1MfGfA2GaA2S4ScSdSdA2M10SbSdSdS2aS2bA4S6G10A1A3S1eA3S4S18S34S4S18S36G3A3A3A3S3A3S0S2S23GfSfG4A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f3.

(* [comment removed for export] *)
Module DrvM_tstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "Some"; "option"; "cons"; "nil"; "list"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "sym_runA"; "mkLeafA"; "ax_X"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.DrvM_tstates"; "CXM_oom"; "CM_oom"; "VM_oom"; "A2M_oom"; "B2M_oom"; "RM_oom"; "S1M_oom"; "TM_oom"; "UM_oom"; "XM_oom"; "sM_oom"; "B1M_oom"; "B3M_oom"; "B4M_oom"; "EM_fw"; "EM_oom"; "LVM_xoom"; "RM_xoom"; "A1M_oom"; "nUM_oom"; "nVM_oom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states"; "nd_M1"; "CUTS_M"; "N_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts"; "node_okb"; "N_exR"; "carve_chk"; "carve_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "sstate"; "ss_objs"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "Pre_fw"; "EBUF"; "P_fw"; "Posts_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates"; "s_exR"; "x4_okb"; "ex_img_okb"; "fw_u1"; "fw_u2"; "splitA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lc_obj"; "lcarve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states"; "T_after"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA DrvGlueB SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR DrvIfaceM DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvR_facts DrvM_states.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition EM_oom : axst := DrvM_states.E_oom.
Definition EM_fw : axst := DrvM_states.E_fw.

Definition CM_oom : axst := Eval vm_compute in fw_siteM 0x14d9d 19 EM_fw.
Definition sM_oom : wsub := Eval vm_compute in s_fwc 0x14d9d 19 CM_oom.
Definition RM_oom : list sobj := Eval vm_compute in optR (entails_frA CM_oom (Pre_fw 0x14d9d 19) sM_oom).
Lemma frM_oom : ltac2:(tb__ "0|1|
S0S5S8S30A1M0A1S3eS14S3aZ14d9dZ13A2S1dA3S4G0S18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccM_oom : ltac2:(tb__ "0|0|
S0S3S3fS14S3aZ14d9dZ13A2S1dS18S40SdSbS12S3dA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TM_oom : axst := Eval vm_compute in T_after (Pre_fw 0x14d9d 19) CM_oom sM_oom RM_oom P_fw.
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
S1S0S3S2bS22S28A2S2A3S1S0S5S8SdA1M0A1SfS39U32S29S22S2A5S4G0S6SdS10S21S49A2S7SdA1M1A3A2A3S1S0S3S43S21S2fS4cA1M2A2S2A3S1S0S5S32A1M3S48ScS25A1U0M4S2fN960A1A3S4S32ScS16A1M5A2A3S1S0S3S2dS16S7S9S31S31A2A1M6S2aA3S2A3S1S0SbSeS16S2eG5S2aA2A2S14A3S1S0S3S2bS14S28A2S2A3S1S0SbS4fS3aZ14d9dZ13A2S14S1dS18S3cA5S1aA3S1S0S3S2bS1aS28A2S2A3S1S0S5SbA1M7S37S1aS6S35S36S45S26A1A1S7S35A1M8A3A2S4SbS19A2A3S1S0S8S30A1M9S33ScS19A1MaA1SaS30S33ScS1bA1A1MbS40S4eS30S4dS2aA4A3A3S1S0S3S51S34GaA1S28A2S2A3S1S0SbSeS19S4aGaGbA2A2S1bA3S1S0G7S37S1bS6S35S36S46S27A1A1S6S35S38G4A1G8A3A3A2S4SbS15A2A3S1S0S3S2bS15S28A2S2A3S1S0G0S23S6SdS10S1cS49A2G1A3A3S1S0G3S48ScS1cA1G4S2fN400A1A3S4S32ScS1eA1A2A3S1S0S3S44S1eA1S2A3S1S0S3S2dS17G6S2cA3S2A3S1S0SbSeS17S2eScS17A1S2cA2A2S1fA3S1S0S3S43S1fG2A2S2A3S1S0S3S52G6S11S20A1A2S2A3S1S0SbS4bS20G6A2S13A3S1S0S3S2bS13S28A2S2A3S1S0S5G9A1S3eS13S41Z0Z2A2McS42S3bS13A2MdA3S4G9S24A2A3S0S3S3fS13GcGdS24S7SbA1A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvM_tstates.

(* [comment removed for export] *)
Module DrvR_tfacts.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "Some"; "pair"; "prod"; "option"; "list"; "nat"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_objs"; "sobj"; "sstate"; "sprop"; "ss_facts"; "ss_next"; "swf"; "SPUle"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "mkLeafA"; "ax_setS"; "sym_runA"; "ax_base"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXRebase"; "AXSelect"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts"; "node_okb"; "nd_R"; "N_exR"; "N_fw"; "bd_R"; "carve_st"; "carve_chk"; "bd_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.DrvR_tfacts"; "nobj"; "N_fp"; "tailF_facts"; "A3_ref"; "S1_ref"; "A2_ref"; "A4_ref"; "B1_ref"; "B4_ref"; "R_xref"; "nd_X"; "A1_ref"; "B2_ref"; "B3_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates"; "CX_ref"; "T_ref"; "x4_okb"; "U_ref"; "s_exR"; "C_ref"; "X_ref"; "V_ref"; "ex_img_okb"; "fp_u1"; "fw_u1"; "selA"; "splitA"; "CF_ov1"; "CF_sh0"; "CF_sh1"; "CF_shZ"; "CX_ov1"; "CX_sh0"; "CX_sh1"; "CX_shZ"; "C_ov1"; "C_sh0"; "C_sh1"; "C_shZ"; "E_ov1"; "E_ref"; "E_sh0"; "E_sh1"; "E_shZ"; "F_ov1"; "F_sh0"; "F_sh1"; "F_shZ"; "LV_xref"; "RF_ov1"; "RF_sh0"; "RF_sh1"; "RF_shZ"; "R_ov1"; "R_ref"; "R_sh0"; "R_sh1"; "R_shZ"; "TF_ov1"; "TF_sh0"; "TF_sh1"; "TF_shZ"; "T_ov1"; "T_sh0"; "T_sh1"; "T_shZ"; "U_ov1"; "U_sh0"; "U_sh1"; "U_shZ"; "V_ov1"; "V_sh0"; "V_sh1"; "V_shZ"; "W_ov1"; "W_sh0"; "W_sh1"; "W_shZ"; "X_ov1"; "X_sh0"; "X_sh1"; "X_shZ"; "exS_idxs"; "fp_rtc"; "fp_u2"; "fw_u2"; "ms16_at"; "sF_ov1"; "sF_sh0"; "sF_sh1"; "sF_shZ"; "s_ov1"; "s_ref"; "s_sh0"; "s_sh1"; "s_shZ"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "KU"; "BIc"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vB"; "vCap"; "PreF"; "DEEP"; "PostF"; "dropX"; "locate"; "spM"; "vTP"; "sp0"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.DrvR_tfacts.TF"; "ndT"; "E1x"; "TA2"; "TA3"; "TB2"; "TS1"; "R_xx"; "TB0'"; "TB1"; "TB4"; "TA1"; "TB0"; "TB3"; "ndTk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lc_obj"; "lcarve"; "carve_okb"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states"; "CUTS_R"; "T_after"; "optR"; "Lov1"; "Lref"; "Lsh0"; "Lsh1"; "LshZ"; "ax_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "KV_T"; "KP_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ANone"; "NDA"; "nd_below";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "EBUF"; "P_fw"; "Posts_fw"; "Pre_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvRGlue"; "pub_lit_okb2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "P_ref"; "Pre_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "CAP0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.Lists.List"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA DrvGlueB SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvR_facts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition carveA (A : axst) (N : list lcarve) : axst := ltac2:(tb__ "0|0|
S1eVA;S2dS1aVA;A1VN;A2A2").

Definition N_fp : list lcarve := ltac2:(tb__ "0|b|
S4S8S8S22S22A2M0SaS8S8S22SbA2M1S22A2M2A1M3A2M4S7G0G3S7S22S22Zeed98M5Zeed9aA4S4G2S7G1S22S7S22SbG5U1M6A4Z1M7A4S4G2S7G1S22S7S22SbZeed99G6A4G7A4S5G2A1M8A3A3A4S4G4S7G0G3S7S22S22Ze6778M9Ze6788A4S4G2S7G1S22S7S22SbG9U8MaA4Zdac00A4S4G2S7G1S22S7S22SbZe6780GaA4Zdb004A4G8A3A3A4S5G4A1A3A3").
Lemma N_fp_eq : ltac2:(tb__ "0|0|
S0SaS10A1Sa4SbaS10Sb9S31A4S83A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fp_un : ltac2:(tb__ "0|0|
S0S3SbcSc6S31A2S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition A1_ref : axst := x4set (SLit TP) E_ref.
Definition A2_ref : axst := splitA 0 (SLit (-2688)) A1_ref.
Definition A3_ref : axst := carveA A2_ref N_fp.
Definition A4_ref : axst := ltac2:(tb__ "0|0|
S96S33S4S8SdSdA2S7SdSdSeZ1a780A1SeZ80A1A4S1cS33A1A3A2").
Definition S1_ref : axst := ltac2:(tb__ "0|0|
S49S47S30S3fA1A1S3fA2").

Definition B1_ref : axst := ltac2:(tb__ "0|0|
S96S4aU0SeN480A1S44A3S5S8SdSdA2A1A2").
Definition B2_ref : axst := ex_img B1_ref.
Definition B3_ref : axst := carveA B2_ref N_exR.
Definition B4_ref : axst := x4set (SLit TP) B3_ref.
Definition R_xref : list sobj := ltac2:(tb__ "0|1|
SbfS97S3eSa5Z0M0Z2A2S42G0S3eA2A3A1").
Lemma ref_facts : ltac2:(tb__ "0|10|
S1S0S3S28Sc1S29A2S2A3S1S0S3S40S58SeSd0A1M0A2S2A3S1S0S9S11A1M1Sb4S1aS3bA1U0M2SeNa80A1A3S6S11S1aS35A1A2A3S1S0S3S2eS35S4S8SdSdA2M3S7SdSdS9aS9bA4S5G3A1M4A3M5S31A3S2A3S1S0S3Sd1S33G5Z1a780Z80A4S2A3S1S0S19SdaS4S12S86Sa3Z998A2M6S5S12A1A3S36A2S43A3S1S0S3Se1S12S17S14S1aS36A1M7A1A1S4S12G6S13G7A1A3A3S2A3S1S0S3S28S43S29A2S2A3S1S0S19SbeSd5S43S8cS66Sd4A5S3fA3S1S0S9S19A1M8S24S3fS4S23S26S47S30S3fA1A1A1S5S23A1M9A3A2S6S19S34A2A3S1S0SaS10A1MaSfS1aS34A1MbA1ScS10SfS1aS41A1A1McSa4SbaS10Sb9S31A4A3A3S1S0S3ScaS14GbA1S29A2S2A3S1S0S19S1eS34Sb7GbGcA2A2S41A3S1S0G8S24S41S4S23S25G2A1S4S23S26S84S30S41A1A1A1S4S23S27G2A1G9A3A3A3A2S6S19S45A2A3S1S0S3S28S45S29A2S2A3S1S0SaS1bA1S60S4S1bS1dS44Sb6A2S5S1bA1A3A3S1S0G1Sb4S1aS44A1G2SeN480A1A3S6S11S1aS37A1A2A3S1S0S3S46S37A1S2A3S1S0S3S2eS3cG5S2aA3S2A3S1S0S3S40S3dG0A2S2A3S1S0S3ScbG4S1cS38A1A2S2A3S1S0S19S96S38G4A2S3eA3S1S0S3S28S3eS29A2S2A3S1S0S9GaA1S97S3eSa5Z0MdZ2A2MeS42GdS3eA2MfA3S6GaS39A2A3S0S3S98S3eGeGfS39S5S19A1A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition nd_X : ndesc := ltac2:(tb__ "0|0|
Sc9S5S8SdSdA2A1S5S8S8SdS22A2SdA2A1S5S91A1Sc8A4").

Section TF.

Variables (tb tl : sv) (bd : list bitem) (msg len blkB blkL : Z).
Variables (Lx Ex Cx Tx Ux Vx Wx Fx CFx TFx Xx CXx : axst) (sx sF : wsub) (Rx RF : list sobj).
Definition ndT : ndesc := ltac2:(tb__ "0|1|
Sc9S4S8SdSdA2M0S7SdSdVtb;Vtl;A4S5G0A1A3S5S8S8SdS22A2SdA2A1Vbd;Sc8A4").
Definition ndTk : ndesc := ltac2:(tb__ "0|1|
Sc9S4S8SdSdA2M0S7SdSdVtb;Vtl;A4S5G0A1A3S5S8S8SdS22A2SdA2A1ScS91Vbd;S4S91S93Z0Z1S92A3S5S91A1A3A3Sc8A4").
Definition TA1 : axst := x4set (SLit TP) Ex.
Definition TA2 : axst := splitA 0 (SLit (-2528)) TA1.
Definition TA3 : axst := carveA TA2 N_fw.
Definition TS1 : axst := ltac2:(tb__ "0|0|
S49S48S30VTx;A1A1VTx;A2").
Definition E1x : axst := ltac2:(tb__ "0|0|
Sc5S24VXx;S4S23S25Sa0SfS1aVXx;A1A1Sa1SeSd3S9dA1A1A3A1S5S23A1A3A2VXx;A2").
Definition TB0 : axst := selA (exS_idxs E1x) E1x.
Definition TB0' : axst := mergeA 0 TB0.
Definition TB1 : axst := ltac2:(tb__ "0|0|
S96S4aU0SeN430A1SadA3S5S8SdSdA2A1A2").
Definition TB2 : axst := ex_img TB1.
Definition TB3 : axst := carveA TB2 N_exR.
Definition TB4 : axst := x4set (SLit TP) TB3.
Definition R_xx : list sobj := ltac2:(tb__ "0|0|
SbfS97VCXx;Sa5Z0Z2A2S42SccVCXx;A2A3A1").

Definition tailF_facts : Prop := ltac2:(tb__ "0|20|
S1S0S3S28VLx;Sa6A2S2A3S1S0S9SaS1bA1M0A1M1S1fSb8U14M2SbdVLx;S2A5S6G0S4S1bS1dVEx;Sb6A2S5S1bA1M3A3A2A3S1S0S3S40VEx;SeSd0A1M4A2S2A3S1S0S9S11A1M5Sb4S1aSb0A1U0M6SeN9e0A1A3S6S11S1aSa8A1M7A2A3S1S0S3S15S2dG7S2bA2A1S2A3S1S0S3SbbS13G7A1SfG7A1S1cSa8A1Sc6Sc7S4S8SdSdA2M8S7SdSdVtb;Vtl;A4M9S5G8A1MaA3MbS2bA7S2A3S1S0SdS20Sa8A1SeSdfA1McA3S1S0S3Sd1Sa9GbVblkB;VblkL;A4S2A3S1S0S19S96Sa9S4G8S7SdSdSeVblkB;A1SeVblkL;A1A4MdS1cSa9A1A3A2VCx;A3S1S0S3S28VCx;Sa6A2S2A3S1S0S9SaS10A1MeA1MfS97VCx;ScfVmsg;Vlen;A2M10Vsx;A3S6GeVRx;A2A3S1S0S3S98VCx;G10Vsx;VRx;Sa4S1bS19S21SceA4A5S2A3S1S0S19SbeG10VCx;Vsx;VRx;ScdA5VTx;A3S1S0S9S19A1M11S24VTx;S4S23S26S48S30VTx;A1A1A1S5S23A1M12A3A2S6S19SabA2A3S1S0GeSfS1aSabA1M13A1ScS10SfS1aVUx;A1A1M14Sa4SbaS10Sb9S2bA4A3A3S1S0S3ScaS14G13A1Sa6A2S2A3S1S0S19S1eSabSb7G13G14A2A2VUx;A3S1S0G11S24VUx;S4S23S25G6A1S4S23S26S85S30VUx;A1A1A1S4S23S27G6A1G12A3A3A3A2S6S19VVx;A2A3S1S0S3S40VVx;Sa2A2S2A3S1S0S19S90Sa2VVx;A2VWx;A3S1S0S3S28VWx;Sa6A2S2A3S1S0G1S1fSb8G2SbdVWx;S2A5S6G0S4S1bS1dVFx;Sb6A2G3A3A2A3S1S0S3ScbS1cVCFx;A1M15S1cVFx;A1A2S2A3S1S0S19S9fGdS9fG9VFx;A2A2VCFx;A3S1S0S3S28VCFx;Sb3A2S2A3S1S0GfS97VCFx;S9cVsF;A3S6GeVRF;A2A3S1S0S3S99VCFx;S9cVsF;VRF;S4S19S9eS5S19A1M16A3A5S2A3S1S0S3SdeSdcVsF;A2S2A3S1S0S3S94S14S1aVCFx;A1M17A1S5S91A1M18A2S2A3S1S0SdSd2VsF;PcA2Vtb;A3S1S0SdSd2VsF;PdA2Vtl;A3S1S0S3S95S13G17A1M19SeZ0M1aA1S92ScS91Vbd;S4S91S93G1aZ1S92A3G18A3A3G18A5S2A3S1S0S3Sd8G19GbS6SbG6A2M1bVRF;A4S2A3S1S0S3Sd9G19GbG1bSfG17A1Sd7G15A6S2A3S1S0S3Se0S12S18S16SeZ1000A1Vtb;A2A1G19A3S2A3S1S0S19SddS9cVCFx;VsF;VRF;S9eA5VTFx;A3S1S0S3S28VTFx;S3aA2S2A3S1S0G1S1fSb8U3cSbdVTFx;S2A5S6G0S4S1bS1dVXx;Sb6A2G3A3A2A3S1S0G11S24VXx;S4S23S25Sa0SfS1aVXx;A1A1Sa1SeSd3S9dA1A1A3A1G12A3A2S6S19Sa7A2A3S1S0S3SdbS30Sa7A1S82Sa7A1A2S2A3S1S0G5Sb5S1aSb1A1G6A2S6S11S1aSadA1M1cA2A3S1S0G5Sb4G1cG6SeN430A1A3S6S11S1aSaeA1A2A3S1S0S3S46SaeA1S2A3S1S0S3S15S2dS1aSaaA1M1dS2aA2A1S2A3S1S0S3SbbS13G1dA1SfG1dA1S1cSaaA1Sc6Sc7GaS2aA7S2A3S1S0SdS20SaaA1GcA3S1S0S3S40Sb2G4A2S2A3S1S0S3ScbGaS1cSafA1A2S2A3S1S0S19S96SafGaA2VCXx;A3S1S0S3S28VCXx;S3aA2S2A3S1S0GfS97VCXx;Sa5G1aZ2A2M1eS42SccVCXx;A2M1fA3S6GeSacA2A3S0S3S98VCXx;G1eG1fSacG16A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
End TF.

Lemma sh1_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ21447Z1fZ21440Z40Sc3S5aS55S70S74S78S7cS5eS4dS6cS80S51S8eS89S68S63A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ov1_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ160cdZ1fZ160c0Z40Sc0S57S53S6eS72S76S7aS5cS4bS6aS7eS4fS8bS87S65S61A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sh0_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ21447Z1fZ21440Z40Sc2S59S54S6fS73S77S7bS5dS4cS6bS7fS50S8dS88S67S62A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shZ_facts : ltac2:(tb__ "0|0|
S32S9aSeSd6A1S2fZ21447Z1fZ21440Z40Sc4S5bS56S71S75S79S7dS5fS4eS6dS81S52S8fS8aS69S64A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvR_tfacts.

