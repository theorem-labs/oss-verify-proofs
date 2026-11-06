(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_017.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.

(* [comment removed for export] *)
Module Start6Run2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2"; "M16_2"; "R16_2"; "IPm_2"; "F17_2"; "IPr_2"; "IP16_2"; "s16_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z2A1A1SfA5").
Local Strategy expand [run16_2__R].
Definition M16_2 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 2)) (ro1__)))) run16_2__R).
Lemma run16_2 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z2A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_2__R <: run16_2__R = Some [mkLeafA M16_2 RsCut]). Qed.
Lemma M16_2_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ2A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_2 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_2) (ax_S Pre_mszA).
Definition R16_2 : list sobj := Eval vm_compute in (match entails_frA M16_2 Pre_mszA s16_2 with Some R => R | None => [] end).
Lemma fr16_2 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_2 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_2 : axst := Eval vm_compute in import_postA s16_2 Pre_mszA (liftA P_msz) M16_2 R16_2.
Lemma IP16_2_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_2 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_2) 0.
Definition IPr_2 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_2 (set_objs IPm_2 R16_2)) (ss_facts (ax_S M16_2)).
Lemma IPr_2_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z2A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_2__R].
Definition F17_2 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_2 (ro2__)))) run17x_2__R).
Lemma run17x_2 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_2__R <: run17x_2__R = Some [mkLeafA F17_2 RsCut]). Qed.
Lemma F17_2_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run2.

(* [comment removed for export] *)
Module Start6Run3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3"; "M16_3"; "R16_3"; "IPm_3"; "F17_3"; "IPr_3"; "IP16_3"; "s16_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z3A1A1SfA5").
Local Strategy expand [run16_3__R].
Definition M16_3 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 3)) (ro1__)))) run16_3__R).
Lemma run16_3 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z3A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_3__R <: run16_3__R = Some [mkLeafA M16_3 RsCut]). Qed.
Lemma M16_3_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ3A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_3 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_3) (ax_S Pre_mszA).
Definition R16_3 : list sobj := Eval vm_compute in (match entails_frA M16_3 Pre_mszA s16_3 with Some R => R | None => [] end).
Lemma fr16_3 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_3 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_3 : axst := Eval vm_compute in import_postA s16_3 Pre_mszA (liftA P_msz) M16_3 R16_3.
Lemma IP16_3_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_3 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_3) 0.
Definition IPr_3 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_3 (set_objs IPm_3 R16_3)) (ss_facts (ax_S M16_3)).
Lemma IPr_3_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z3A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_3__R].
Definition F17_3 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_3 (ro2__)))) run17x_3__R).
Lemma run17x_3 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_3__R <: run17x_3__R = Some [mkLeafA F17_3 RsCut]). Qed.
Lemma F17_3_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run3.

(* [comment removed for export] *)
Module Start6Run4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4"; "M16_4"; "R16_4"; "IPm_4"; "F17_4"; "IPr_4"; "IP16_4"; "s16_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_4__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z4A1A1SfA5").
Local Strategy expand [run16_4__R].
Definition M16_4 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 4)) (ro1__)))) run16_4__R).
Lemma run16_4 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z4A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_4__R <: run16_4__R = Some [mkLeafA M16_4 RsCut]). Qed.
Lemma M16_4_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ4A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_4 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_4) (ax_S Pre_mszA).
Definition R16_4 : list sobj := Eval vm_compute in (match entails_frA M16_4 Pre_mszA s16_4 with Some R => R | None => [] end).
Lemma fr16_4 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_4 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_4 : axst := Eval vm_compute in import_postA s16_4 Pre_mszA (liftA P_msz) M16_4 R16_4.
Lemma IP16_4_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_4 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_4) 0.
Definition IPr_4 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_4 (set_objs IPm_4 R16_4)) (ss_facts (ax_S M16_4)).
Lemma IPr_4_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z4A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_4__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_4__R].
Definition F17_4 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_4 (ro2__)))) run17x_4__R).
Lemma run17x_4 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_4__R <: run17x_4__R = Some [mkLeafA F17_4 RsCut]). Qed.
Lemma F17_4_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run4.

