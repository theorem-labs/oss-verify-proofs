(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_016.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.

(* [comment removed for export] *)
Module Start6Run6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6"; "M16_6"; "R16_6"; "IPm_6"; "F17_6"; "IPr_6"; "IP16_6"; "s16_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
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

Definition run16_6__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z6A1A1SfA5").
Local Strategy expand [run16_6__R].
Definition M16_6 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 6)) (ro1__)))) run16_6__R).
Lemma run16_6 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z6A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_6__R <: run16_6__R = Some [mkLeafA M16_6 RsCut]). Qed.
Lemma M16_6_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ6A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_6 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_6) (ax_S Pre_mszA).
Definition R16_6 : list sobj := Eval vm_compute in (match entails_frA M16_6 Pre_mszA s16_6 with Some R => R | None => [] end).
Lemma fr16_6 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_6 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_6 : axst := Eval vm_compute in import_postA s16_6 Pre_mszA (liftA P_msz) M16_6 R16_6.
Lemma IP16_6_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_6 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_6) 0.
Definition IPr_6 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_6 (set_objs IPm_6 R16_6)) (ss_facts (ax_S M16_6)).
Lemma IPr_6_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z6A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_6__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_6__R].
Definition F17_6 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_6 (ro2__)))) run17x_6__R).
Lemma run17x_6 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_6__R <: run17x_6__R = Some [mkLeafA F17_6 RsCut]). Qed.
Lemma F17_6_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run6.

(* [comment removed for export] *)
Module Start6Run5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5"; "M16_5"; "R16_5"; "IPm_5"; "F17_5"; "IPr_5"; "IP16_5"; "s16_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
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

Definition run16_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z5A1A1SfA5").
Local Strategy expand [run16_5__R].
Definition M16_5 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 5)) (ro1__)))) run16_5__R).
Lemma run16_5 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z5A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_5__R <: run16_5__R = Some [mkLeafA M16_5 RsCut]). Qed.
Lemma M16_5_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ5A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_5 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_5) (ax_S Pre_mszA).
Definition R16_5 : list sobj := Eval vm_compute in (match entails_frA M16_5 Pre_mszA s16_5 with Some R => R | None => [] end).
Lemma fr16_5 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_5 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_5 : axst := Eval vm_compute in import_postA s16_5 Pre_mszA (liftA P_msz) M16_5 R16_5.
Lemma IP16_5_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_5 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_5) 0.
Definition IPr_5 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_5 (set_objs IPm_5 R16_5)) (ss_facts (ax_S M16_5)).
Lemma IPr_5_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z5A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_5__R].
Definition F17_5 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_5 (ro2__)))) run17x_5__R).
Lemma run17x_5 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_5__R <: run17x_5__R = Some [mkLeafA F17_5 RsCut]). Qed.
Lemma F17_5_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run5.

(* [comment removed for export] *)
Module Start6Run7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7"; "M16_7"; "R16_7"; "IPm_7"; "F17_7"; "IPr_7"; "IP16_7"; "s16_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
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

Definition run16_7__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z7A1A1SfA5").
Local Strategy expand [run16_7__R].
Definition M16_7 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 7)) (ro1__)))) run16_7__R).
Lemma run16_7 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S3dS37Z7A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_7__R <: run16_7__R = Some [mkLeafA M16_7 RsCut]). Qed.
Lemma M16_7_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S3cA3S1S0S4S26S1aA1S6S3bA1A3S1S0S4S7G0Z1A2S6S39A1A3S1S0S4S7G0ZaA2S3aZ7A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_7 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_7) (ax_S Pre_mszA).
Definition R16_7 : list sobj := Eval vm_compute in (match entails_frA M16_7 Pre_mszA s16_7 with Some R => R | None => [] end).
Lemma fr16_7 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_7 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_7 : axst := Eval vm_compute in import_postA s16_7 Pre_mszA (liftA P_msz) M16_7 R16_7.
Lemma IP16_7_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_7 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_7) 0.
Definition IPr_7 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_7 (set_objs IPm_7 R16_7)) (ss_facts (ax_S M16_7)).
Lemma IPr_7_facts : ltac2:(tb__ "0|3|
S1S0SeS3eS22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S38Z7A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_7__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_7__R].
Definition F17_7 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_7 (ro2__)))) run17x_7__R).
Lemma run17x_7 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_7__R <: run17x_7__R = Some [mkLeafA F17_7 RsCut]). Qed.
Lemma F17_7_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S3cA3S1S0S4S26S1dA1S6S3bA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run7.

