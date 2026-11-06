(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_002.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From Stdlib Require FunctionalExtensionality.
From stdpp Require bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_fuzz_iface2 DrvJ.

(* [comment removed for export] *)
Module Start6Run4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run4"; "M16_4"; "R16_4"; "IPm_4"; "F17_4"; "IPr_4"; "IP16_4"; "s16_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_4__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ4A1A1SfA5").
Local Strategy expand [run16_4__R].
Definition M16_4 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 4)) (ro1__)))) run16_4__R).
Lemma run16_4 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ4A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_4__R <: run16_4__R = Some [mkLeafA M16_4 RsCut]). Qed.
Lemma M16_4_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ4A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
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
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ4A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_4__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_4__R].
Definition F17_4 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_4 (ro2__)))) run17x_4__R).
Lemma run17x_4 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_4__R <: run17x_4__R = Some [mkLeafA F17_4 RsCut]). Qed.
Lemma F17_4_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run4.

(* [comment removed for export] *)
Module Start6Run5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run5"; "M16_5"; "R16_5"; "IPm_5"; "F17_5"; "IPr_5"; "IP16_5"; "s16_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ5A1A1SfA5").
Local Strategy expand [run16_5__R].
Definition M16_5 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 5)) (ro1__)))) run16_5__R).
Lemma run16_5 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ5A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_5__R <: run16_5__R = Some [mkLeafA M16_5 RsCut]). Qed.
Lemma M16_5_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ5A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
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
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ5A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_5__R].
Definition F17_5 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_5 (ro2__)))) run17x_5__R).
Lemma run17x_5 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_5__R <: run17x_5__R = Some [mkLeafA F17_5 RsCut]). Qed.
Lemma F17_5_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run5.

(* [comment removed for export] *)
Module Start6Run6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run6"; "M16_6"; "R16_6"; "IPm_6"; "F17_6"; "IPr_6"; "IP16_6"; "s16_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_6__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ6A1A1SfA5").
Local Strategy expand [run16_6__R].
Definition M16_6 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 6)) (ro1__)))) run16_6__R).
Lemma run16_6 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ6A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_6__R <: run16_6__R = Some [mkLeafA M16_6 RsCut]). Qed.
Lemma M16_6_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ6A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
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
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ6A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_6__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_6__R].
Definition F17_6 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_6 (ro2__)))) run17x_6__R).
Lemma run17x_6 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_6__R <: run17x_6__R = Some [mkLeafA F17_6 RsCut]). Qed.
Lemma F17_6_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run6.

(* [comment removed for export] *)
Module Start6Run7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run7"; "M16_7"; "R16_7"; "IPm_7"; "F17_7"; "IPr_7"; "IP16_7"; "s16_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_7__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ7A1A1SfA5").
Local Strategy expand [run16_7__R].
Definition M16_7 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 7)) (ro1__)))) run16_7__R).
Lemma run16_7 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ7A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_7__R <: run16_7__R = Some [mkLeafA M16_7 RsCut]). Qed.
Lemma M16_7_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ7A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
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
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ7A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_7__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_7__R].
Definition F17_7 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_7 (ro2__)))) run17x_7__R).
Lemma run17x_7 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_7__R <: run17x_7__R = Some [mkLeafA F17_7 RsCut]). Qed.
Lemma F17_7_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run7.

(* [comment removed for export] *)
Module DrvErrno.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "rl"; "rm"; "rw"; "obj_range"; "SLit"; "sprop"; "ss_objs"; "eval"; "sv"; "holds"; "ob_base"; "ranges_disjoint"; "sv_eqb"; "image_byte"; "ob_hi"; "ob_lo"; "obj_hi_of"; "obj_holds"; "obj_lo_of"; "soff"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "@Corelib.Init.Datatypes"; "nat"; "list"; "app"; "cons"; "nil"; "bool"; "true"; "pair"; "andb"; "option"; "S"; "prod"; "orb"; "snd"; "None"; "fst"; "length"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "xword"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "sub"; "lt"; "leb"; "mul"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvErrno"; "eidx"; "nobjs"; "errR"; "errR_okb"; "addE"; "objs_eqb"; "errC_idxs"; "errC_objs2"; "errR_idxs1"; "errR_idxs2"; "errR_objs1"; "errR_objs2"; "objs_off_errnob"; "errC"; "errC_okb"; "obj_off_errnob"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "O_errno"; "O_errno0"; "locate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA"; "errno_blind"; "@Stdlib.Lists.List"; "removelast"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "errno_addrA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "itv"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundL SymSoundM SymSoundR SymFrame SymEntail SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA GlueA3 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint objs_eqb (l l' : list sobj) : bool :=
  match l, l' with
  | [], [] => true
  | o :: t, o' :: t' => sobj_eqb o o' && objs_eqb t t'
  | _, _ => false
  end.
Lemma objs_eqb_sound : ltac2:(tb__ "0|1|
S20S2A1M0G0S19S24S4eR2R1A2S25A3S19G0R3R2A3F_;Fl';Fl;").
Proof.
  induction l as [|o t IH]; intros [|o' t'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sobj_eqb_sound in H1. rewrite H1, (IH t' H2). reflexivity.
Qed.

Lemma TP_errno : TP - 164 = ERRNO_A.
Proof. reflexivity. Qed.

Lemma O_errno_range : ltac2:(tb__ "0|0|
S3S19S2aS0S0A2S7R1S5aA2S26S0S0S1eS37S1eZ4A2A4A3Frho;").
Proof.
  intros rho. unfold obj_range, obj_lo_of, obj_hi_of, O_errno. cbn [ob_base ob_lo ob_hi eval].
  rewrite !soff_lit_small by (unfold TP; lia). rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP, ERRNO_A. f_equal.
Qed.
Lemma O_errno0_range : ltac2:(tb__ "0|0|
S3S19S2aS0S0A2S7R1S5bA2S26S0S0S1eS1eA4A3Frho;").
Proof.
  intros rho. unfold obj_range, obj_lo_of, obj_hi_of, O_errno0. cbn [ob_base ob_lo ob_hi eval].
  rewrite !soff_lit_small by (unfold TP; lia). rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP, ERRNO_A. f_equal.
Qed.

Lemma errno_bytes_w : ltac2:(tb__ "0|5|
S0S1aS38Z0R1A2S3bR1Z4A2A2S1aS1bS19S28S30Q8A1M0A1M1S60S1dS30Q40M2A1S2dG0A1M3L_;S32G2S37S1eR2A2A2M4A3G3A3A1S1bS19G1S11S1dG4A2G3A3A1A2F_;Foff;").
Proof.
  intros off Hoff. assert (E : off = 0 \/ off = 1 \/ off = 2 \/ off = 3) by lia.
  destruct E as [->|[->|[->| ->]]]; (split; [vm_compute; discriminate | vm_compute; discriminate]).
Qed.

Definition addE (a b : sv) : sv := SAlu ALU_ADD a b.
Definition obj_off_errnob (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|4|
S2bS2bS10S13Vo;A1M0S12Vo;A1M1A2S3cS37S1eZ4A2S2eS0S0S67Vfacts;S4dSeVo;A1M2G0A2A2M3A3A2A2S27S3eS2cS0S0G3A3S39Z2Z3eA2A2S3cS2cS0S0S67Vfacts;S4dG2G1A2A2A3S1eA2A2A2").
Definition objs_off_errnob (facts : list sprop) (objs : list sobj) : bool := forallb (obj_off_errnob facts) objs.

Lemma signed_mod : ltac2:(tb__ "0|1|
S30Q40M0A1S1cS0S0S19S0S33G0R2A2S3aS31G0R2A2S3dR1S39Z2Z40A2A2A2A3Lq;A2Fw;").
Proof.
  intros w. unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  destruct (Z_lt_le_dec (bv_unsigned w) (2 ^ 63)).
  - exists 0. rewrite Z.mod_small by lia. lia.
  - exists 1. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma U_addE : ltac2:(tb__ "0|1|
S3ScScS1cS0S0S19S0S31Q40M0SbR4S4dR3R2A2A2A2S3aS37S31G0SbR4R3A2A2S17R4R2A2A2S3dR1S39Z2Z40A2A2A2A3Lq;A2Fe;Fb;Frho;").
Proof.
  intros rho b e. unfold addE. cbn [eval]. rewrite add_val. unfold soff. destruct (signed_mod (eval rho e)) as [q Hq]. rewrite Hq.
  pose proof (Z.div_mod (bv_unsigned (eval rho b) + bv_unsigned (eval rho e)) (2 ^ 64) ltac:(lia)) as D.
  exists ((bv_unsigned (eval rho b) + bv_unsigned (eval rho e)) / 2 ^ 64 - q). lia.
Qed.

Lemma obj_off_errnob_sound : ltac2:(tb__ "0|3|
S3S20S9A1S2S44S9SdR3A1R2A3S31Q40SbR4SeR2A1A2A2S0S1aS38Z0S37R1S16R5R3A2M0A2A2S1aS38S37R1S14R5R3A2M1A2S39Z2M2Z40A2A2S1aS38G0G1A2S3bS3aG1G0A2S39G2Z3fA2A2A2A2A2Tb;S19S24S58R4R3A2S25A3SfS7R6R4A2S26S0S0S1eS37S1eZ4A2A4A2F_;F_;F_;Fo;Ffacts;Frho;").
Proof.
  intros rho facts o HF HB H. cbv zeta in HB. destruct HB as (B0 & B1 & B2 & B3).
  unfold obj_range, ranges_disjoint. cbn [fst snd]. unfold obj_lo_of, obj_hi_of in *.
  set (b := bv_unsigned (eval rho (ob_base o))) in *. set (lo := soff rho (ob_lo o)) in *. set (hi := soff rho (ob_hi o)) in *.
  unfold obj_off_errnob in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - apply sv_eqb_sound in H. left. unfold lo, hi. rewrite H. lia.
  - apply Z.leb_le in H. pose proof (itv_sound rho facts (addE (ob_base o) (ob_lo o)) HF) as I. unfold in_itv in I.
    destruct (itv facts (addE (ob_base o) (ob_lo o))) as [l h]. cbn [fst snd] in H, I.
    destruct (U_addE rho (ob_base o) (ob_lo o)) as [q Hq]. fold b lo in Hq.
    pose proof (bv_unsigned_in_range 64 (eval rho (addE (ob_base o) (ob_lo o)))) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    destruct (Z.eq_dec (b + lo) (2 ^ 64)) as [E|NE]; [left; lia|].
    assert (q = 0) by nia. subst q. right; right; right. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2.
    pose proof (itv_sound rho facts (addE (ob_base o) (ob_lo o)) HF) as I1. pose proof (itv_sound rho facts (addE (ob_base o) (ob_hi o)) HF) as I2.
    unfold in_itv in I1, I2.
    destruct (itv facts (addE (ob_base o) (ob_lo o))) as [l1 h1]. destruct (itv facts (addE (ob_base o) (ob_hi o))) as [l2 h2]. cbn [fst snd] in *.
    destruct (U_addE rho (ob_base o) (ob_lo o)) as [q1 Hq1]. destruct (U_addE rho (ob_base o) (ob_hi o)) as [q2 Hq2]. fold b lo in Hq1. fold b hi in Hq2.
    pose proof (bv_unsigned_in_range 64 (eval rho (addE (ob_base o) (ob_lo o)))) as R1. pose proof (bv_unsigned_in_range 64 (eval rho (addE (ob_base o) (ob_hi o)))) as R2.
    change (bv_modulus 64) with (2 ^ 64) in R1, R2.
    destruct (Z.eq_dec (b + lo) (2 ^ 64)) as [E|NE]; [left; lia|].
    assert (q1 = 0) by nia. subst q1. assert (b + hi < 2 ^ 64) by lia. assert (q2 = 0) by nia. subst q2.
    right; right; left. lia.
Qed.

Lemma objs_off_errnob_sound : ltac2:(tb__ "0|0|
S3S20S9A1S20S2A1S5fS44S9SdR4A1R3A3S44S2S15S1dR5R2A3R3A3S19S24S55R5R4A2S25A3S44S2S2SfS7R8R1A2S26S0S0S1eS37S1eZ4A2A4A2Lo;R5A3F_;F_;F_;Fms;Fobjs;Ffacts;Frho;").
Proof.
  intros rho facts objs ms HF Hall H. apply Forall_forall. intros o Ho.
  apply (obj_off_errnob_sound rho facts o HF).
  - exact (proj1 (proj1 (Forall_forall _ _) Hall o Ho)).
  - exact (proj1 (forallb_forall _ _) H o Ho).
Qed.

Definition eidx (E : axst) : nat := ltac2:(tb__ "0|0|
S5cSaS45VE;A1A1S8Z0A1S8S3aS6cZa4A2A1A3").
Definition nobjs (E : axst) : nat := length (ss_objs (ax_S E)).

Definition errC_idxs (i n : nat) : list nat := ltac2:(tb__ "0|2|
S21S1fS43U0Vi;A2S21S1fS22S1fVn;S23S1fA1M0A3S21S1fS43S29Vi;A1M1S59Vn;G1A2A2S22S1fVi;G0A3A3A3A3").
Definition errC_objs2 (E : axst) : list sobj := ltac2:(tb__ "0|0|
S61S21S2SaS45VE;A1A1S22S2S5aS23S2A1A3A3S4fS49VE;A1S4aVE;A1A2A2").
Definition errC (E : axst) : axst := ltac2:(tb__ "0|0|
S48VE;S68S45VE;A1S5eS2S50VE;A1A2A2A2").
Definition errC_okb (E : axst) : bool := ltac2:(tb__ "0|3|
S27S27S27S62S29S4aVE;A1M0A1S4fS49VE;A1G0A2A2S4eS50VE;A1M1S21S2S5eS2G1A2S22S2S5bS23S2A1A3A3A2A2S55S18S45VE;A1M2A1SaG2A1A2A2S10S47VE;A1S8S69A1A2A2").

Definition errR_idxs1 (i n : nat) : list nat := ltac2:(tb__ "0|1|
S21S1fS43U0Vi;A2S21S1fS43S29Vi;A1M0S59Vn;G0A2A2S22S1fVi;S23S1fA1A3A3A3").
Definition errR_objs1 (E : axst) : list sobj := ltac2:(tb__ "0|0|
S61SaS45VE;A1A1S51S49VE;A1S4aVE;A1A2A2").
Definition errR_idxs2 (i n : nat) : list nat := ltac2:(tb__ "0|1|
S21S1fS43U0Vi;A2S21S1fS22S1fS59Vn;U1A2M0S23S1fA1A3S43Vi;S59G0Vi;A2A2A3A3").
Definition errR_objs2 (E : axst) : list sobj := ltac2:(tb__ "0|0|
S21S2S5eS2S53VE;A1A2S22S2S5bS23S2A1A3A3").
Definition errR (E : axst) : axst := ltac2:(tb__ "0|0|
S48VE;S68S45VE;A1S61S54VE;A1S52S49VE;A1S4aVE;A1A2A2A2A2").
Definition errR_okb (E : axst) : bool := ltac2:(tb__ "0|3|
S27S27S62S4aVE;A1M0S51S49VE;A1M1G0A2A2S4eS53VE;A1M2S21S2S5eS2G2A2S22S2S5aS23S2A1A3A3A2A2S62S2fS2S54VE;A1A2S52G1G0A2A2A2").

Lemma rho_absorb_empty : ltac2:(tb__ "0|0|
S3S2S5fS3S19S2aS0S0A2S7R1R3A2S26S0S0S1eS1eA4A3Fr;S19S3S66R4S22S2R3S23S2A1A3R2A3R4A3F_;Fms;Fo;Frho;").
Proof.
  intros rho o ms Hr. unfold rho_absorb. destruct rho as [w l m]. cbn [rw rl rm]. f_equal.
  apply functional_extensionality. intros a. destruct (in_ranges_dec _ [o] a) as [Hin|Hn]; [|reflexivity].
  exfalso. destruct Hin as (o' & [<-|[]] & Hrng). rewrite Hr in Hrng. cbn [fst snd] in Hrng. lia.
Qed.

Lemma xword_off_errno : ltac2:(tb__ "0|2|
S3S46S30Q40M0A1S19ScS47R2A1S8S69A1A3S36R4R3R2A3S1bS1aS38S1eS31G0R3A2M1A2S3bG1S37S1eZ4A2A2A2A1F_;F_;Fx;FA;Frho;").
Proof.
  intros rho A x Hbase (r & y & j & _ & Hy & Hj & Hr & ->) Hx. rewrite Hbase in Hr, Hx. cbn [eval] in Hr, Hx.
  rewrite Z_to_bv_unsigned, bv_wrap_small in Hr, Hx by (unfold SHADOW_OFF; rewrite two64; lia).
  pose proof (bv_unsigned_in_range _ (eval rho (fst r))) as [R0 _].
  assert (Y0 : 0 <= y / 8) by (apply Z.div_pos; lia).
  unfold word_byte in Hx. set (z := SHADOW_OFF + y / 8) in *.
  assert (Z8 : SHADOW_OFF <= z / 8 * 8).
  { assert (SHADOW_OFF / 8 <= z / 8) by (apply Z.div_le_mono; unfold z; lia). unfold SHADOW_OFF in *. change (2147450880 / 8) with 268431360 in *. lia. }
  pose proof (Z.mul_div_le z 8 ltac:(lia)) as Z9.
  assert (Z10 : z / 8 * 8 <= 2 ^ 64 - 8).
  { assert (z / 8 <= (2 ^ 64 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 64 - 1) / 8) with 2305843009213693951 in *. lia. }
  rewrite Z_to_bv_unsigned, bv_wrap_small in Hx by (rewrite two64; lia). unfold SHADOW_OFF, ERRNO_A in *. lia.
Qed.

Lemma SPA_errC : ltac2:(tb__ "0|0|
S35S3S46S20S30Q40A1A1S40S19S24S57R3A1S25A3S34S1dR6R4R5R3R2A6S34S1dR7S56R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp [tr [ms md]] H HS. unfold errC_okb in H.
  apply andb_prop in H as [H Hbase]. apply andb_prop in H as [H Hoff]. apply andb_prop in H as [Hsel Heq].
  apply sv_eqb_sound in Hbase. apply objs_eqb_sound in Heq.

  assert (Hdis : Forall (fun o => ranges_disjoint (obj_range rho o) (ERRNO_A, ERRNO_A + 4)) (ss_objs (ax_S E))).
  { pose proof (proj1 HS) as (Hsm & _). unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
    exact (objs_off_errnob_sound rho _ _ _ (SPA_facts_hold segs J rho E tp _ HS) Hall Hoff). }

  pose proof (SPA_carve_unknown_w segs J rho E (SLit 0) (TP - 164) (TP - 160) tp tr ms md HS) as Hc. cbv zeta in Hc.
  assert (Eb : bv_unsigned (eval rho (SLit 0)) = 0) by (cbn [eval]; rewrite Z_to_bv_unsigned; reflexivity). rewrite Eb in Hc.
  assert (HS1 : SPA segs J (ax_setS E (set_objs (ax_S E) (ss_objs (ax_S E) ++ [O_errno]))) rho tp (tr, mkCfg ms md)).
  { apply Hc; try (unfold TP; lia); [reflexivity | | |].
    - intros off Hoff'. replace (0 + off) with (ERRNO_A + (off - ERRNO_A)) by lia. apply errno_bytes_w. unfold TP, ERRNO_A in *. lia.
    - exact Hdis.
    - intros x Hx Hr. apply (xword_off_errno rho E x Hbase Hx). unfold TP, ERRNO_A in *. lia. }

  assert (Hsel' : select_ok (length (ss_objs (ax_S (ax_setS E (set_objs (ax_S E) (ss_objs (ax_S E) ++ [O_errno])))))) (errC_idxs (eidx E) (nobjs E)) = true)
    by (cbn [ax_S ax_setS ss_objs set_objs]; rewrite length_app, Nat.add_comm; exact Hsel).
  pose proof (SPA_select segs J rho _ _ tp _ Hsel' HS1) as HS2.
  cbn [ax_S ax_setS ss_objs set_objs] in HS2. fold (errC_objs2 E) in HS2.

  match type of HS2 with SPA _ _ ?A2 _ _ _ =>
    pose proof (SPA_unobj segs J rho A2 (removelast (errC_objs2 E)) [O_errno0] tp tr ms md (Heq : ss_objs (ax_S A2) = _) HS2) as HS3 end. cbv zeta in HS3.
  rewrite (rho_absorb_empty rho O_errno0 _ O_errno0_range) in HS3. exact (HS3 (fun h => h)).
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S3fS3fS3fS40R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS3fS3fR3VTR;R3R2A2F_;VTR;S40S1aR5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").

Lemma SPA_errR : ltac2:(tb__ "0|1|
S35S3S46S20S30Q40A1A1S20S6bA1M0S5fS6aS19S24S4cR5A1S25A3S5dR8A1S34S1dR9R7R8R6S26G0S64R5S65R4R3A2A4A6S34S1dRaS4bR8A1S66R9S22S2S5aS23S2A1A3S6dR4R7R5A3A3R7S26G0S64R6S65R5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;FE;Frho;FJ;").
Proof using .
  intros J rho E tp tr ms md H HJ HS. unfold errR_okb in H. apply andb_prop in H as [H Hsel2]. apply andb_prop in H as [Hsel1 Heq].
  apply objs_eqb_sound in Heq.
  pose proof (SPA_select segs J rho E _ tp _ Hsel1 HS) as HS1. fold (errR_objs1 E) in HS1.
  match type of HS1 with SPA _ _ ?A1 _ _ _ =>
    pose proof (SPA_unobj segs J rho A1 (removelast (errR_objs1 E)) [O_errno] tp tr ms md (Heq : ss_objs (ax_S A1) = _) HS1) as HS2 end. cbv zeta in HS2.
  set (rho1 := rho_absorb rho [O_errno] (vms md tp ms)) in *.
  assert (HS2' : SPA segs J (ax_setS (ax_setS E (set_objs (ax_S E) (errR_objs1 E))) (set_objs (ax_S (ax_setS E (set_objs (ax_S E) (errR_objs1 E)))) (removelast (errR_objs1 E)))) rho1 tp (tr, mkCfg ms md)).
  { apply HS2. intros Hj. apply (HJ rho); [reflexivity | reflexivity | | exact Hj].
    intros a Ha. unfold rho1, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho [O_errno] a) as [Hin|Hn]; [|reflexivity].
    exfalso. apply Ha. destruct Hin as (o & [<-|[]] & Hr). rewrite O_errno_range in Hr. exact Hr. }

  pose proof (SPA_carve_unknown_w segs J rho1 _ (SLit 0) (TP - 164) (TP - 164) tp tr ms md HS2') as Hc. cbv zeta in Hc.
  assert (Eb : bv_unsigned (eval rho1 (SLit 0)) = 0) by (cbn [eval]; rewrite Z_to_bv_unsigned; reflexivity). rewrite Eb in Hc.
  assert (HS3 : SPA segs J (ax_setS E (set_objs (ax_S E) (errR_objs2 E))) rho1 tp (tr, mkCfg ms md)).
  { apply Hc; try reflexivity; try (unfold TP; lia).
    apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. right; left. lia. }
  exact (SPA_select segs J rho1 (ax_setS E (set_objs (ax_S E) (errR_objs2 E))) (errR_idxs2 (eidx E) (nobjs E)) tp _ Hsel2 HS3).
Qed.

Theorem errR_T : ltac2:(tb__ "0|3|
S35S46S3fS3S20S30Q40M0A1M1A1S19S24S4cR4A1S25A3S5dR6A1S3S19S1G1F_;S6R1A1S6R5A1A3S19S1S20S30Q8A1M2A1F_;S4R2A1S4R6A1A3G1S1bS63S31G0R1A2A1A1S19S28G2A1S5R5R2A2S5R9R2A2A3F_;Fa;VTR;S34S1dRbS4bRaA1R4R7A5R9A2F_;F_;F_;Frho1;VTR;S34S1dR8R7R5R4A5R6A2F_;F_;F_;Ftp;Frho;FQ;FE;FJ;").
Proof using TR_pre TR_exw TR_pureh.
  intros J E Q rho tp Hok HJ HT.
  apply (TR_pre (fun w => exists rho1, (rw rho1 = rw rho /\ rl rho1 = rl rho /\ (forall a, ~ errno_addrA (bv_unsigned a) -> rm rho1 a = rm rho a))
                                       /\ SPA segs J (errR E) rho1 tp w)).
  - intros [tr [ms md]] Hw. exists (rho_absorb rho [O_errno] (vms md tp ms)). split.
    + split; [reflexivity|]. split; [reflexivity|]. intros a Ha. unfold rho_absorb. cbn [rm].
      destruct (in_ranges_dec rho [O_errno] a) as [Hin|Hn]; [|reflexivity].
      exfalso. apply Ha. destruct Hin as (o & [<-|[]] & Hr). rewrite O_errno_range in Hr. exact Hr.
    + exact (SPA_errR J rho E tp tr ms md Hok HJ Hw).
  - apply TR_exw. intros rho1. apply TR_pureh. intros (E1 & E2 & E3). exact (HT rho1 E1 E2 E3).
Qed.
End T.

Lemma errR_Ts : ltac2:(tb__ "0|3|
S40OF_;S35S46S3fS3S20S30Q40M0A1M1A1S19S24S4cR4A1S25A3S5dR6A1S3S19S1G1F_;S6R1A1S6R5A1A3S19S1S20S30Q8A1M2A1F_;S4R2A1S4R6A1A3G1S1bS63S31G0R1A2A1A1S19S28G2A1S5R5R2A2S5R9R2A2A3F_;Fa;S42S1dRcS34S1dRbS4bRaA1R4R7A5R9A4F_;F_;F_;Frho1;S42S1dR9S34S1dR8R7R5R4A5R6A4F_;F_;F_;Ftp;Frho;FQ;FE;FJ;Fok;").
Proof.
  intros ok J E Q rho tp H HJ HT.
  exact (errR_T (triple segs ok) (fun P P' Q0 HP HTq => ltac:(eapply triple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq]))
           (fun A P Q0 => @triple_ex segs ok A P Q0) (fun X P Q0 => @triple_pure segs ok X P Q0) J E Q rho tp H HJ HT).
Qed.
Lemma errR_Te : ltac2:(tb__ "0|3|
S35S46S3fS3S20S30Q40M0A1M1A1S19S24S4cR4A1S25A3S5dR6A1S3S19S1G1F_;S6R1A1S6R5A1A3S19S1S20S30Q8A1M2A1F_;S4R2A1S4R6A1A3G1S1bS63S31G0R1A2A1A1S19S28G2A1S5R5R2A2S5R9R2A2A3F_;Fa;S41S1dS34S1dRbS4bRaA1R4R7A5R9A3F_;F_;F_;Frho1;S41S1dS34S1dR8R7R5R4A5R6A3F_;F_;F_;Ftp;Frho;FQ;FE;FJ;").
Proof.
  intros J E Q rho tp H HJ HT.
  exact (errR_T (etriple segs) (fun P P' Q0 HP HTq => ltac:(eapply etriple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq]))
           (fun A P Q0 => @etriple_ex segs A P Q0) (fun X P Q0 => @etriple_pure segs X P Q0) J E Q rho tp H HJ HT).
Qed.
End DrvErrno.

(* [comment removed for export] *)
Module DrvT_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "true"; "option"; "Some"; "list"; "pair"; "bool"; "app"; "length"; "prod"; "false"; "None"; "negb"; "fst"; "snd"; "S"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sstate"; "sprop"; "ss_objs"; "ss_pc"; "SPUle"; "SVar"; "DUnknown"; "cell"; "mkObj"; "ss_next"; "ss_regs"; "SAlu"; "mkSS"; "swf"; "FcsrFrm0"; "SExt"; "SPAlign"; "SPBranch"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "sv_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "mkLeafA"; "ax_setS"; "mkAX"; "ax_X"; "ax_base"; "la_state"; "axwf"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states"; "jv"; "T_after"; "vP"; "CUTS_T"; "optS"; "PreM"; "optR"; "C_fbE_00"; "C_fbE_02"; "C_fbE_10"; "C_fbE_20"; "C_fbE_30"; "C_fbE_40"; "J_E"; "E_mP1"; "E_mPc"; "U_mc1"; "ex_site"; "fb_site"; "ib2"; "mc_u9"; "nthA"; "E_mc1"; "E_mcc"; "L_E"; "L_E1"; "PreP"; "S_T1"; "T_mc1"; "s_pf"; "C_mc1"; "C_mcc"; "FUEL_L"; "FUEL_T1"; "FUEL_T2"; "L_Ec"; "O_srcT"; "R_mP1"; "R_mPc"; "T_mok1"; "T_mokc"; "runL"; "s_fp"; "s_fz"; "s_mP1"; "s_mPc"; "C_exE_00"; "C_exE_02"; "C_exE_10"; "C_exE_20"; "C_exE_30"; "C_exE_40"; "E_exE_00"; "E_exE_02"; "E_exE_10"; "E_exE_20"; "E_exE_30"; "E_exE_40"; "L_P"; "NX_L"; "PreFN"; "R_fbE_00"; "R_fbE_02"; "R_fbE_10"; "R_fbE_20"; "R_fbE_30"; "R_fbE_40"; "R_mc1"; "R_mcc"; "S_T2"; "T_mnull1"; "T_mnullc"; "cnt_reg"; "fregs_L"; "ib0"; "ib1"; "mc_b1"; "mc_b2"; "mc_b3"; "mc_w1"; "mc_w2"; "s_mc1"; "s_mcc"; "set_printf_hist"; "AND3"; "E_fbE_00"; "E_fbE_02"; "E_fbE_10"; "E_fbE_20"; "E_fbE_30"; "E_fbE_40"; "FUEL_T0"; "L_P1"; "L_Pc"; "O_cstkB"; "O_srcB"; "PostsM"; "T_fbE_00"; "T_fbE_02"; "T_fbE_10"; "T_fbE_20"; "T_fbE_30"; "T_fbE_40"; "T_mcc"; "U_mcc"; "WDP"; "X_LP"; "X_payE"; "cnt_facts"; "mc_rtc"; "mc_site"; "mc_u1"; "mc_u2"; "mc_u3"; "mc_u4"; "mc_u5"; "mc_u6"; "mc_u7"; "mc_u8"; "regs_L"; "runX"; "s_fn"; "sel_buf"; "sel_rtc_last"; "sel_win"; "CUTS_L"; "LN1a"; "LN1b"; "LNca"; "LNcb"; "LV_E10"; "LV_Ec0"; "LV_Ec1"; "LV_Ec2"; "LV_Ec3"; "LV_P10"; "LV_Pc0"; "LV_Pc1"; "LV_Pc2"; "LV_Pc3"; "LX_E10"; "LX_Ec0"; "LX_Ec1"; "LX_Ec2"; "LX_Ec3"; "LX_P10"; "LX_Pc0"; "LX_Pc1"; "LX_Pc2"; "LX_Pc3"; "O_WfzT"; "O_WloT"; "O_payE"; "O_winT"; "PostFN"; "R_exE_00"; "R_exE_02"; "R_exE_10"; "R_exE_20"; "R_exE_30"; "R_exE_40"; "T_fp0"; "blkP_facts"; "ex_carved"; "facts_LE"; "facts_LP"; "fjv"; "mc_cv"; "mc_hints"; "mc_rs"; "mc_undo"; "objs_LE"; "objs_LP"; "pf_cv"; "pf_hints"; "pf_rtc"; "pf_u1"; "pf_w1"; "regs_J"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "GOT_HI"; "GOT_LO"; "RTC_HI"; "RTC_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "PreF"; "s_fb"; "FUEL_X"; "CUTS_X"; "vPlen"; "locate"; "vB"; "PostF"; "vClen"; "spT"; "S_T"; "DEEP"; "s_ex"; "vLen"; "dropX"; "sp0"; "vTOPv"; "X_T"; "facts_T"; "vCap"; "ATOPHI"; "IMGHI"; "spM"; "vH"; "vTP";
"O_deepM"; "O_deepS"; "payload"; "vFlg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "RsFuel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "add"; "O_rtc2"; "P_pf"; "ms16"; "O_realm"; "O_rtc3w"; "O_sbsh"; "Pre_pf"; "Pre_pf0"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"; "add"; "eqb"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "free_stub"; "loop_head"; "EMPTY"; "TR_INIT"; "malloc_stub"; "RD_STAGE"; "TP"; "fz_stub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "map"; "nth"; "skipn"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "exit_entry"; "Pre_exit"; "FERR"; "O_ofile"; "O_osbuf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "O_real"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "L_free_null"; "Pre_free_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "Pre_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states.ExitP"; "XF1"; "R_fp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states.XChainE"; "C_fbEk"; "C_exEk"; "st_c"; "JEk"; "R_fbEk"; "R_fnk"; "T_fbEk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states.XChainP"; "XF1k"; "R_fpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "flat_map"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.MCAddr"; "mc_entry"; "mc_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "fz_frame"; "fz_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states.IterE"; "C_fzE"; "C_pfE"; "R_fzE"; "R_pfE"; "T_fzE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states.IterP"; "C_fzP"; "C_pfP"; "R_fzP"; "R_pfP"; "T_fzP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.PFAddr"; "emit_entry"; "FILE"; "PW"; "SBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P_fz"; "fcallee_saved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sprop_subst"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT Lib_fuzz_iface2 DrvJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CUTS_T : list Z := ltac2:(tb__ "0|0|
S0S40S133S0S40S12fS0S40S164S0S40S136S0S40S17eS0S40S13fS0S40S130S2S40A1A3A3A3A3A3A3A3").
Definition runT (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S4S6S35A1M0A1G0Lx;S37Sf5Vfuel;S45VA;S3A5G0R1Ll;S2S35A1X4x2").
Definition nthA (d : axst) (l : list leafA) (i : nat) : axst := ltac2:(tb__ "0|0|
S3dS13bS35Vi;Vl;S38Vd;S11eA2A4A1").
Definition optS (d : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
S4S16A1S36Lx;Vx;S16S39Vd;R1A2LS';Vd;X4x2").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition T_after (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S168S2cS34VCl;A1A1S11bVs;VPre;VL;VCl;VR;A5A2").

Definition set_printf_hist (n : Z) (objs : list sobj) : list sobj := ltac2:(tb__ "0|3|
S100Vobjs;S14Z0A1M0S14S17fA1A3S1S100Vobjs;G0S14S181A1A3S1S9S15S139S15R2Vobjs;A3S9S15S0S15S142Vn;A1S2S15A1M1A3S13cS15S11R2A1M2Vobjs;A3A3A3S6S15A1S9S15S139S15R2R1A3S9S15S0S15S143Vn;A1G1A3S13cS15G2R1A3A3A3To1;Tj;Ti;").

Definition S_T1 : axst := Eval vm_compute in optS S_T (split_obj_at (ax_S S_T) 0 (SLit (-208))).
Lemma S_T1_eq : ltac2:(tb__ "0|0|
S33S32S4S16A1S11fS34S105A1U0S14Nd0A1A3S5S16S34S5dA1A2A3S33S32S6SbS13S13A2A1S3bS5dA1S3bS105A1A3S32S13S3cS5dA1S3cS105A1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S_T2 : axst := Eval vm_compute in ax_setS S_T1 (img_cell_apply (ax_S S_T1) (locate (ss_objs (ax_S S_T1)) (SLit 0) (SLit TR_INIT)) (TR_INIT + 4) 1 0).
Lemma S_T2_eq : ltac2:(tb__ "0|5|
S33S32S8S14bSf5S34S5dA1M0S100S18G0A1S14Z0M1A1S14S132A1A3M2S12cS132Z4A2M3Z1M4G1A6S3A3S32S36S39S5dS14aG0G2G3G4G1A5A2S87A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition FUEL_T0 : nat := 300%nat.
Definition run_T0__R : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5S9dS45S87S3A5").
Local Strategy expand [run_T0__R].
Definition LV_T0 : list leafA := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) run_T0__R).

Definition E_mP1 : axst := Eval vm_compute in nthA S_T LV_T0 0.
Definition L_E1 : axst := Eval vm_compute in nthA S_T LV_T0 1.
Definition L_Ec : axst := Eval vm_compute in nthA S_T LV_T0 2.
Definition E_mPc : axst := Eval vm_compute in nthA S_T LV_T0 3.
Lemma run_T0 : ltac2:(tb__ "0|1|
S32S4S6S35A1M0A1S37Sf5S9dS45S87S3A5S5G0S0S35S38S50S11cA2S0S35S38S5bS11cA2S0S35S38S65S11cA2S0S35S38S51S11cA2S2S35A1A3A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_T0__R <: run_T0__R = Some [mkLeafA E_mP1 RsCut; mkLeafA L_E1 RsCut; mkLeafA L_Ec RsCut; mkLeafA E_mPc RsCut]). Qed.
Lemma T0_pcs : ltac2:(tb__ "0|0|
S32S6S40A1S13aS36S40S36S19S34R1A1A1LA;S0S36S50S0S36S5bS0S36S65S0S36S51S2S36A1A3A3A3A3A4S0S40S133S0S40S130S0S40S130S0S40S133S2S40A1A3A3A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition PreM : axst := Pre_malloc AE_A [] UStopLe.
Definition PostsM : list axst := ltac2:(tb__ "0|1|
S0S36S14fS14cS2S14eA1M0S14dA3S0S36S150S14cG0S14dA3S2S36A1A3A3").
Definition s_m (E : axst) : wsub := ltac2:(tb__ "0|0|
S0SbS41S13A2S7S41S13PfS14S12aS12bS106Z50A2A1A1A4S13eP1S34VE;A1S34S47A1A3A3").
Definition s_mP1 : wsub := Eval vm_compute in s_m E_mP1.
Definition s_mPc : wsub := Eval vm_compute in s_m E_mPc.
Definition R_mP1 : list sobj := Eval vm_compute in optR (entails_frA E_mP1 PreM s_mP1).
Definition R_mPc : list sobj := Eval vm_compute in optR (entails_frA E_mPc PreM s_mPc).
Lemma fr_mP1 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S50S47S6eA3S5G0S67A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_mPc : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S51S47S6fA3S5G0S68A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mP1 : ltac2:(tb__ "0|0|
S32S8S119S50S47S6eS67Sa2A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mPc : ltac2:(tb__ "0|0|
S32S8S119S51S47S6fS68Sa2A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_mnull1 : axst := Eval vm_compute in T_after PreM E_mP1 s_mP1 R_mP1 (L_malloc_null AE_A [] UStopLe).
Definition T_mnullc : axst := Eval vm_compute in T_after PreM E_mPc s_mPc R_mPc (L_malloc_null AE_A [] UStopLe).
Definition T_mok1 : axst := Eval vm_compute in T_after PreM E_mP1 s_mP1 R_mP1 (L_malloc_ok AE_A [] UStopLe).
Definition T_mokc : axst := Eval vm_compute in T_after PreM E_mPc s_mPc R_mPc (L_malloc_ok AE_A [] UStopLe).
Lemma T_m_eqs : ltac2:(tb__ "0|3|
S33S32S36S43S47S50S6eS67S14fS14cS2S14eA1M0S14dA3M1A5S88A3S33S32S36S43S47S51S6fS68G1A5S89A3S33S32S36S43S47S50S6eS67S150S14cG0S14dA3M2A5S69A3S32S36S43S47S51S6fS68G2A5S6aA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vP : positive := Eval vm_compute in match nth 10 (ss_regs (ax_S T_mok1)) (SLit 0) with SVar v => v | _ => 1%positive end.
Lemma vP_eq : ltac2:(tb__ "0|3|
S33S32S13S13bS13UaM0S20S34S69A1A1S14Z0A1M1A4S1bS44A1M2A3S32S13S13bS13G0S20S34S6aA1A1G1A4G2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition FUEL_T1 : nat := 100%nat.
Definition run_T1__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5S63S45S69S3A5").
Local Strategy expand [run_T1__R1].
Definition E_mc1 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => nthA S_T ((match ro2__ with Some l => l | None => [] end)) 0) run_T1__R1).
Definition run_T1__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5S63S45S6aS3A5").
Local Strategy expand [run_T1__R2].
Definition E_mcc : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => nthA S_T ((match ro3__ with Some l => l | None => [] end)) 0) run_T1__R2).
Lemma run_T1 : ltac2:(tb__ "0|3|
S33S32S4S6S35A1M0A1M1S37Sf5S63S45S69S3A5S5G0S0S35S38S58S11cA2S2S35A1M2A3A2A3S32G1S37Sf5S63S45S6aS3A5S5G0S0S35S38S59S11cA2G2A3A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_T1__R1 <: run_T1__R1 = Some [mkLeafA E_mc1 RsCut]) (@eq_refl (option (list leafA)) run_T1__R2 <: run_T1__R2 = Some [mkLeafA E_mcc RsCut])). Qed.
Lemma E_mc_pcs : ltac2:(tb__ "0|3|
S33S32S40S19S34S58A1M0A1S164A3S33S32S40S19S34S59A1M1A1S164A3S33S32S41S1fG0A1P8cM2A3S32S41S1fG1A1G2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition O_srcT : sobj := ltac2:(tb__ "0|0|
S1eS121S101S121S103S14Z6A1A2A2S14Z0A1SffS2S1dA1S1cA5").

Definition mc_hints : list sprop := ltac2:(tb__ "0|3|
S0S17S1aS1bS44A1M0S14S10fA1M1A2S0S17S1aS121G0SffA2M2G1A2S0S17S1aS14S110A1G0A2S0S17S1aG2S10bA2S0S17S1aG0S10bA2S2S17A1A3A3A3A3A3").
Definition mc_rtc : list sobj := ltac2:(tb__ "0|0|
S0S15S149S0S15S122S0S15S148S2S15A1A3A3A3").
Definition mc_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1U0S14N870A1A3A2").
Definition mc_w2 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1U0S14N8c0A1A3A2").
Definition ib0 (E : axst) : nat := ltac2:(tb__ "0|0|
S100S18S34VE;A1A1S101S14Z0A1A3").
Definition ib1 (E : axst) : nat := ltac2:(tb__ "0|0|
S100S18S34VE;A1A1S101S14Z6A1A3").
Definition ib2 (E : axst) : nat := ltac2:(tb__ "0|0|
S100S18S34VE;A1A1S101S121S103S14Z6A1A2A3").
Definition mc_b1 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1S8cVE;A1S14Z6A1A3A2").
Definition mc_b2 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1S8dVE;A1S121S103S14Z6A1A2A3A2").
Definition mc_b3 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1S55VE;A1S108A3A2").
Definition mc_rs (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S137S34VE;A1S55VE;A1S66A3A2").
Definition mc_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S39VE;S11dS34VE;A1M0S9S15S18G0A1SafA3A2A2").
Definition mc_site (E : axst) : axst := ltac2:(tb__ "0|0|
S168SeaSe9SebS90S8fS8eS92S91VE;A1A1A1A1A1A1A1A2").
Definition C_mc1 : axst := Eval vm_compute in mc_site E_mc1.
Definition C_mcc : axst := Eval vm_compute in mc_site E_mcc.

Lemma mc_pipe1 : ltac2:(tb__ "0|f|
S33S32S4S16A1M0S11fS34S58A1U0M1S14N870A1A3S5S16S34S91S58A1M2A1M3A2A3S33S32G0S11fG3G1S14N8c0A1A3S5S16S34S92G2A1M4A1M5A2A3S33S32G0S11fG5S8cG4A1S14Z6A1M6A3S5S16S34S8eG4A1M7A1M8A2A3S33S32G0S11fG8S8dG7A1S121S103G6A2M9A3S5S16S34S8fG7A1MaA1MbA2A3S33S32G0S11fGbS55GaA1S108A3S5S16S34S90GaA1McA1MdA2A3S33S32S4S15A1S161S15S18GdA1S55GcA1MeA3S5S15S1eS101G9S108S2S1dA1S1cA5A2A3S33S32S8S15fGdS137GdGeS66A3A2S3A3S32S36Sb0S58A1S60A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma mc_pipec : ltac2:(tb__ "0|f|
S33S32S4S16A1M0S11fS34S59A1U0M1S14N870A1A3S5S16S34S91S59A1M2A1M3A2A3S33S32G0S11fG3G1S14N8c0A1A3S5S16S34S92G2A1M4A1M5A2A3S33S32G0S11fG5S8cG4A1S14Z6A1M6A3S5S16S34S8eG4A1M7A1M8A2A3S33S32G0S11fG8S8dG7A1S121S103G6A2M9A3S5S16S34S8fG7A1MaA1MbA2A3S33S32G0S11fGbS55GaA1S108A3S5S16S34S90GaA1McA1MdA2A3S33S32S4S15A1S161S15S18GdA1S55GcA1MeA3S5S15S1eS101G9S108S2S1dA1S1cA5A2A3S33S32S8S15fGdS137GdGeS66A3A2S3A3S32S36Sb0S59A1S61A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_mc (C : axst) : wsub := ltac2:(tb__ "0|1|
S0SbS41S13A2M0S7S41S13P13S101A4S0G0S7S41S13P35S121S103S14Z6A1A2A4S0G0S7S41S13PfS1bS44A1A4S0G0S7S41S13P11S14Z0A1A4S0G0S7S41S13P10SffA4S0G0S7S41S13P34S10eA4S13eP1S34VC;A1S34S145A1A3A3A3A3A3A3A3").
Definition s_mc1 : wsub := Eval vm_compute in s_mc C_mc1.
Definition s_mcc : wsub := Eval vm_compute in s_mc C_mcc.
Definition R_mc1 : list sobj := Eval vm_compute in optR (entails_frA C_mc1 Pre_mc0 s_mc1).
Definition R_mcc : list sobj := Eval vm_compute in optR (entails_frA C_mcc Pre_mc0 s_mcc).
Lemma fr_mc1 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S60S145S93A3S5G0S85A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_mcc : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S61S145S94A3S5G0S86A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mc1 : ltac2:(tb__ "0|0|
S32S8S11aS60S145S93S85S13aS35S36S3dS147A4A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mcc : ltac2:(tb__ "0|0|
S32S8S11aS61S145S94S86S13aS35S36S3dS147A4A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_mc1 : axst := Eval vm_compute in T_after Pre_mc0 C_mc1 s_mc1 R_mc1 P_icpt.
Definition T_mcc : axst := Eval vm_compute in T_after Pre_mc0 C_mcc s_mcc R_mcc P_icpt.
Lemma T_mc_eqs : ltac2:(tb__ "0|0|
S33S32S36S43S145S60S93S85S146A5S5eA3S32S36S43S145S61S94S86S146A5Sa9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma T_mc_shape : ltac2:(tb__ "0|a|
S33S32S6SbSbS13S13A2M0S13A2M1A1M2S13aS15G1S15S7G0S13S7S13S13S29R1A1S2bR1A1A4S2aR1A1A4Lo;M3S139S15UaM4S18S34S5eA1M5A1A3A4M6S0G1S7G0S13S7S13S13S104S14N870A1A4S14Z0A1M7A4S0G1S7G0S13S7S13S13S121S10aS14N940A1A2S14N50A1A4G7A4S0G1S7G0S13S7S13S13S1bS44A1G7A4SffA4S0G1S7G0S13S7S13S13S121S101S121S103S14Z6A1A2A2G7A4SffA4S0G1S7G0S13S7S13S13G7S14Zeed98A1A4S14Zeed9aA1A4S0G1S7G0S13S7S13S13G7S14Zeeda0A1A4S14Zeedb8A1A4S0G1S7G0S13S7S13S13G7S14Ze6778A1A4S14Ze6780A1A4S0G1S7G0S13S7S13S13G7S14Sf8A1A4S14Sf7A1A4S0G1S7G0S13S7S13S13G7S14SfaA1A4S14Sf9A1A4S0G1S7G0S13S7S13S13S104S14Nff30A1A4S14N8c0A1A4S2G1A1A3A3A3A3A3A3A3A3A3A3A3S33S32S41S1fG5A1Pb4M8A3S33S32S40S19G5A1S165A3S33S32G2S13aS15G1G3S139S15G4S18S34Sa9A1M9A1A3A4G6A3S32S41S1fG9A1G8A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition sel_rtc_last (n : nat) : list nat := ltac2:(tb__ "0|2|
S9S1S0S1U0S0S1U1S0S1U2S0S1U3S2S1A1M0A3A3A3A3S9S1S138U7M1S13dVn;G1A2A2S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3").
Definition mc_u1 (T : axst) : axst := ltac2:(tb__ "0|2|
S39VT;S11dS34VT;A1M0S144S18G0A1M1SbdSaS15G1A2A1A2A2A2").
Definition mc_u2 (T : axst) : axst := ltac2:(tb__ "0|2|
S39VT;S11dS34VT;A1M0S139S15S13dSaS15S18G0A1M1A2U3A2G1A3A2A2").
Definition O_srcB : sobj := ltac2:(tb__ "0|0|
S1eS101S121S103S14Z6A1A2S108S2S1dA1S1cA5").
Definition mc_u3 (T : axst) : axst := ltac2:(tb__ "0|0|
S39VT;S137S34VT;A1U3Sa1A3A2").
Definition O_cstkB : sobj := ltac2:(tb__ "0|0|
S1eS104S14N8c0A1S14N870A1S2S1dA1S1cA5").
Definition mc_u4 (T : axst) : axst := ltac2:(tb__ "0|0|
S39VT;S137S34VT;A1U1Sa0A3A2").

Definition sel_win (n : nat) : list nat := ltac2:(tb__ "0|1|
S9S1S0S1U6S0S1U1S0S1U0S0S1U2S0S1U3S0S1U4S0S1U5S2S1A1A3A3A3A3A3A3A3S138U7M0S13dVn;G0A2A2A3").
Definition mc_u5 (T : axst) : axst := ltac2:(tb__ "0|2|
S39VT;S11dS34VT;A1M0S144S18G0A1M1SbeSaS15G1A2A1A2A2A2").
Definition mc_u6 (T : axst) : axst := ltac2:(tb__ "0|0|
S46VT;S120S34VT;A1U0A2A2").
Definition mc_u7 (T : axst) : axst := ltac2:(tb__ "0|0|
S46VT;S120S34VT;A1U0A2A2").

Definition sel_buf (objs : list sobj) : list nat := ltac2:(tb__ "0|3|
S0S1S100Vobjs;S101S14Z0A1A3S0S1S100Vobjs;S101S14Z6A1M0A3S0S1S100Vobjs;S101S121S103G0A2A3S0S1S100Vobjs;S101S108A3S2S1A1A3A3A3A3S6S1A1M1S9S1R1S16eS1G1S170S1A1S1S16dSeS160S1S16cR1A1R2A3A1M2A1Li;S1S16fG2A1Lx;S138U0SaS15Vobjs;A2A2A6A3Tks;").
Definition mc_u8 (T : axst) : axst := ltac2:(tb__ "0|2|
S39VT;S11dS34VT;A1M0S144S18G0A1M1SbcG1A1A2A2A2").
Definition mc_u9 (T : axst) : axst := ltac2:(tb__ "0|0|
S46VT;S120S34VT;A1U0A2A2").
Definition mc_undo (T : axst) : axst := ltac2:(tb__ "0|0|
S56S56S56Sb8Sb7Sb6Sb5Sb4Sb3Sb2Sb1VT;A1A1A1A1A1A1A1A1A1A1A1").
Definition U_mc1 : axst := Eval vm_compute in mc_undo T_mc1.
Definition U_mcc : axst := Eval vm_compute in mc_undo T_mcc.
Lemma mc_undo1 : ltac2:(tb__ "0|18|
S33S32S8S169SaS15S18S34S5eA1A1A2M0SbdG0A1A2S3A3S33S32S6S15A1S18S34Sb1S5eA1M1A1A1M2S9S15S139S15S13dG0U3M3A2G2A3SafA3A3S33S32S4S15A1M4S161S15S18S34Sb2G1A1M5A1M6A1G3A3S5S15S66A2A3S33S32S8S15fG6S137G6G3Sa1A3A2S3A3S33S32G4S161S15S18S34Sb3G5A1M7A1M8A1U1M9A3S5S15S1eS121S10aS14N940A1A2S14N50A1S14Z0A1S2S1dA1S1cA5A2A3S33S32S8S15fG8S137G8G9Sa0A3A2S3A3S33S32S8S169SaS15S18S34Sb4G7A1MaA1A1A2MbSbeGbA1A2S3A3S33S32S4S16A1McS120S34Sb5GaA1MdA1U0MeA2S5S16S34Sb6GdA1MfA1M10A2A3S33S32GcS120G10GeA2S5S16S34Sb7GfA1M11A1A2A3S33G11S36S33S32S8S169SaS15S18S34R1A1A1M12A2SbcG12A1A2S3A3S33S32GcS120S34Sb8R1A1M13A1GeA2S5S16S34S56G13A1M14A1M15A2A3S33S32GcS120G15GeA2S5S16S34S56G14A1M16A1M17A2A3S32GcS120G17GeA2S5S16S34S56G16A1A1A2A3A2A2A2TT7;S32S36SecS5eA1S52A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma mc_undoc : mc_undo T_mcc = U_mcc. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_mc_shape : ltac2:(tb__ "0|4|
S33S32S6SbSbS13S13A2M0S13A2M1A1S13aS15G1S15S7G0S13S7S13S13S29R1A1S2bR1A1A4S2aR1A1A4Lo;S139S15U3S18S34S52A1M2A1A3A4S0G1S7G0S13S7S13S13S101S14Z0A1M3A4S10eA4S0G1S7G0S13S7S13S13S104S14Nff30A1A4G3A4S0G1S7G0S13S7S13S13S1bS44A1G3A4SffA4S2G1A1A3A3A3A3S32S40S19G2A1S165A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition FUEL_T2 : nat := 100%nat.
Definition run_T2__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5S64S45S52S3A5").
Local Strategy expand [run_T2__R1].
Definition L_P1 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => nthA S_T ((match ro4__ with Some l => l | None => [] end)) 0) run_T2__R1).
Definition run_T2__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5S64S45SaaS3A5").
Local Strategy expand [run_T2__R2].
Definition L_Pc : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => nthA S_T ((match ro5__ with Some l => l | None => [] end)) 0) run_T2__R2).
Lemma run_T2 : ltac2:(tb__ "0|3|
S33S32S4S6S35A1M0A1M1S37Sf5S64S45S52S3A5S5G0S0S35S38S9eS11cA2S2S35A1M2A3A2A3S32G1S37Sf5S64S45SaaS3A5S5G0S0S35S38S9fS11cA2G2A3A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_T2__R1 <: run_T2__R1 = Some [mkLeafA L_P1 RsCut]) (@eq_refl (option (list leafA)) run_T2__R2 <: run_T2__R2 = Some [mkLeafA L_Pc RsCut])). Qed.
Lemma L_P_shape : ltac2:(tb__ "0|8|
S33S32S40S19S34S9eA1M0A1S130A3S33S32S40S19S34S9fA1M1A1S130A3S33S32S6S13A1M2S13aS1S13S1S13bS13R1S20G0A1S14Z0A1M3A4Lr;S0S1U8S0S1U9S0S1U12S0S1U15S2S1A1A3A3A3A3M4A4S0S13SffS0S13S1bS44A1M5S0S13G5S0S13S14Z1A1M6S2S13A1M7A3A3A3A3A3S32G2S13aS1S13S1S13bS13R1S20G1A1G3A4Lr;G4A4S0S13SffS0S13G5S0S13G5S0S13S121S21S171S25ScQ8S21S172S112S14Z10A1A3A3S14Z3A1A3G6A2G7A3A3A3A3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition jv (k : nat) : sv := SVar (Pos.of_nat (140 + k)).

Definition fjv (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition fregs_L : list sv := ltac2:(tb__ "0|0|
S13aS1S13S1S8S13L_;S183R1A1S14Z0A1Se8R1A1X8x2Lr;S138U0U20A2A4").
Definition NX_L : positive := 232%positive.

Definition AND3 : sv := ltac2:(tb__ "0|0|
S21S171S25ScQ8S21S172S112S14Z10A1A3A3S14Z3A1A3").
Definition CNT_c : sv := add AND3 (SLit 1).
Definition cnt_reg (v : bool) (k : Z) : sv := ltac2:(tb__ "0|1|
S8S13Lv;Vv;S8S13L_;S12dVk;Z1M0A2S96S121S96S14S12bG0Vk;A2A1A2X8x2S14G0A1X8x2").
Definition regs_L (p own cnt : sv) : list sv := ltac2:(tb__ "0|1|
S0S13S14Z0A1M0S0S13S42U1A1S0S13S104S0S13S14Z10800A1S0S13S113S0S13S42U5A1S0S13S42U6A1S0S13S42U7A1S0S13SffS0S13Vp;S0S13S42UaA1S0S13S42UbA1S0S13S42UcA1S0S13S42UdA1S0S13S42UeA1S0S13S42UfA1S0S13S42U10A1S0S13S42U11A1S0S13Vown;S0S13S42U13A1S0S13S14S132A1S0S13Vcnt;S0S13G0S0S13S14ZfffffffffffffffeA1S0S13G0S0S13G0S0S13G0S0S13G0S0S13S42U1cA1S0S13S42U1dA1S0S13S42U1eA1S0S13S42U1fA1S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition blkP_facts : list sprop := ltac2:(tb__ "0|3|
S0S17S26S44Z4A2S0S17S26S44Z3A2S0S17S28S27S173S1bS44A1M0S14Z0A1A3A1S0S17S1aS14Z1000A1G0A2S0S17S1aS121G0SffA2M1S14S10fA1M2A2S0S17S1aG0G2A2S0S17S1aS14S110A1G0A2S0S17S1aG1S10bA2S0S17S1aG0S10bA2S0S17S1aS14Z1A1SffA2S2S17A1A3A3A3A3A3A3A3A3A3A3").
Definition cnt_facts (v : bool) (k : Z) : list sprop := ltac2:(tb__ "0|3|
S8S6S17A1Lv;Vv;S0S17S1aS14Z1A1S8aS3Vk;A2M0A2S0S17S1aG0S14S12bZ4Vk;A2A1A2S0S17S28S27S173S103S14Z0A1A3M1A1S2S17A1M2A3A3A3S0S17G1G2A3X8x2").
Definition facts_LP (v : bool) (k : Z) : list sprop := ltac2:(tb__ "0|0|
S9S17SaeVv;Vk;A2S9S17Se4S10dA3A3").

Definition objs_LP (k : Z) : list sobj := ltac2:(tb__ "0|0|
S95Vk;S18S34S52A1A1A2").

Definition X_LP : list (sv * sv) := ltac2:(tb__ "0|1|
S9SbS13S13A2M0S10cS0G0S7S13S13S1bS44A1SffA4S2G0A1A3A3").
Definition L_P (v : bool) (k : Z) : axst := ltac2:(tb__ "0|1|
S3aS22S130Sb9S1bS44A1M0G0S8aVv;Vk;A2A3S8bS24SdS13A1SeeVk;A1Se7Vv;Vk;A2S7dScA9SacS14Sf6A1A3").
Lemma L_P_wf : ltac2:(tb__ "0|3|
S33S32S8S3eS7cS3Z0M0A2M1A1S3A3S33S32S8S23S34G1A1A1S3A3S33S32S8S23S34S7cScG0A2A1A1S3A3S32S8S163SbS13S13A2M2G2S160G2G2S12S2dSfS13S13R2A3SfS13S13R1A3A2S2dS10S13S13R2A3S10S13S13R1A3A2A2Lr';S3bS52A1A3Lr;SacA3S3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition fz_ra : Z := 0x108b84.
Definition WDP : Z := DEEP - 80 - fz_frame.
Definition O_WfzT : sobj := ltac2:(tb__ "0|0|
S1eS121S104S14S12aS166A1A1A2S14S12aSabA1A1S14Z0A1S2S1dA1S1cA5").
Definition O_WloT : sobj := ltac2:(tb__ "0|0|
S1eS104S14S12aS12bS106Z50A2A1A1S14S12aS166A1A1S2S1dA1S1cA5").
Definition O_payE : sobj := ltac2:(tb__ "0|1|
S1eS14S131A1S14Z0A1M0G0S2S1dA1S1cA5").
Definition X_payE : (sv * sv) := ltac2:(tb__ "0|0|
S7S13S13S14S131A1S14Z0A1A4").
Definition fz_site (modeE : bool) (E : axst) : axst := ltac2:(tb__ "0|2|
S34VE;A1S16S100S18R1A1M0S104S14S12aS12bS106Z50A2A1A1A3S1S4S16A1S16Lx;S11fR2R1S14S12aS166A1A1A3S16R1Lx;R2X4x2S16S137R1R2Sd8A3S16S8S16LmodeE;VmodeE;S11dR1S9S15G0S0S15SdaS2S15A1A3A3A2R1X8x2S16S39VE;R1A2S36S8S36LmodeE;VmodeE;S3aS34R1A1S9SbS13S13A2M1S3bR1A1S0G1SadS2G1A1A3A3S3cR1A1A3R1X8x2TA;TS3;TS2;TS1;Tiw;TS;").
Definition s_fz (C : axst) : wsub := ltac2:(tb__ "0|0|
S0SbS41S13A2S7S41S13P13S14S12aSabA1A1A4S13eP1S34VC;A1S34S153A1A3A3").

Definition fz_undo (modeE : bool) (T : axst) : axst := ltac2:(tb__ "0|5|
S34VT;A1S16SaS15S18R1A1M0A2S1S137R2U1M1Sd9A3S16S11dR1S144G0S9S1S0S1G1S0S1U0M2S2S1A1A3A3S138U2M3S13dR2G3A2A2A3A2A2S16S4S16A1S16Lx;S120R1G2A2S16R1Lx;R1X4x2S16S8S16LmodeE;VmodeE;S11dR1S9S15S139S15G1G0A3S13cS15G3G0A3A3A2R1X8x2S16S8S36LmodeE;VmodeE;S109SadS39VT;R1A2M4A2G4X8x2TS4;TS3;TS2;TS1;Tn;TS;").

Definition CUTS_L : list Z := ltac2:(tb__ "0|0|
S0S40S167S0S40S17eS0S40S12fS0S40S130S0S40S13fS2S40A1A3A3A3A3A3").
Definition runL (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S4S6S35A1M0A1G0Lx;S37Sf5Vfuel;SbfVA;S3A5G0R1Ll;S2S35A1X4x2").
Definition FUEL_L : nat := 60%nat.

Definition pf_rtc : list sobj := ltac2:(tb__ "0|0|
S0S15S127S0S15S126S0S15S122S0S15S125S2S15A1A3A3A3A3").
Definition pf_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S11fS34VE;A1U0S14S12aS180A1A1A3A2").
Definition pf_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S39VE;S11dS34VE;A1M0S9S15S18G0A1Sf1A3A2A2").
Definition PreP (k : Z) : axst := ltac2:(tb__ "0|0|
S8S36L_;S12dVk;Z0A2S129S128Vk;A1X8x2").
Definition s_pf (C : axst) (k : Z) : wsub := ltac2:(tb__ "0|0|
S13eP1S34VC;A1S34S5cVk;A1A1A3").

Definition pf_hints (C : axst) (k : Z) : list sprop := ltac2:(tb__ "0|1|
S162S17S17S17S4S17A1S6S17A1Lx;S184S5fVC;Vk;A2R1A2S17S0S17R1S2S17A1M0A3Lq;G0X4x2Lp;S0S17S124Z958A1S0S17S124Z928A1G0A3A3A4").
Definition pf_site (E : axst) (k : Z) : axst := ltac2:(tb__ "0|0|
SefSf3VE;A1A1S36S168Sf0R1Vk;A2R1A2TC;").

Definition pf_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
S9S1S0S1U0S0S1U1S0S1U2S0S1U6S0S1U7S0S1U9S0S1UaS0S1UbS2S1A1M0A3A3A3A3A3A3A3A3S9S1S138UcM1S13dVn;G1A2A2S0S1U3S0S1U4S0S1U5S0S1U8G0A3A3A3A3A3A3").
Definition pf_undo (T : axst) : axst := ltac2:(tb__ "0|5|
S34VT;A1S16SaS15S18R1A1M0A2S1S11dR2S144S18R2A1M1Sf2R1A1A2A2S16S11dR1S139S15S13dR2U4M2A2G0A3A2S16S13dR3G2A2S1S11dR2S144G1S9S1S0S1U8S0S1U0M3S2S1A1A3A3S9S1S138U1U7A2S138U9M4S13dR1G4A2A2A3A3A2A2S16S46S39VT;R1A2S120R1G3A2A2TS3;Tm;TS2;TS1;Tn;TS;").

Section IterP.

  Definition E_fzP (k : Z) : axst := ltac2:(tb__ "0|0|
S57S105S6bS62S7cS3Vk;A2A2U0A3").
  Definition C_fzP (k : Z) : axst := fz_site false (E_fzP k).
  Definition R_fzP (k : Z) : list sobj := ltac2:(tb__ "0|1|
S48S118S179Vk;A1M0S153S6dG0A1A3A1").
  Definition TT_fzP (k : Z) : axst := ltac2:(tb__ "0|1|
S43S153S179Vk;A1M0S6dG0A1S17bVk;A1S182A5").
  Definition T_fzP (k : Z) : axst := fz_undo false (TT_fzP k).
  Definition E_pfP (k : Z) : axst := ltac2:(tb__ "0|0|
S57S105S6bS62S17dVk;A1A2U0A3").
  Definition C_pfP (k : Z) : axst := pf_site (E_pfP k) k.
  Definition R_pfP (k : Z) : list sobj := ltac2:(tb__ "0|1|
S48S118S17aVk;A1M0S5cVk;A1S5fG0Vk;A2A3A1").
  Definition T_pfP (k : Z) : axst := ltac2:(tb__ "0|1|
S43S5cVk;A1S17aVk;A1M0S5fG0Vk;A2S17cVk;A1S123Vk;A1A5").
  Definition U_pfP (k : Z) : axst := pf_undo (T_pfP k).
  Definition LV_endP (k : Z) : list leafA := runL FUEL_L (U_pfP k).
End IterP.

Definition E_fzP10 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_P false 0)) 0.
Definition C_fzP10 : axst := Eval vm_compute in fz_site false E_fzP10.
Definition R_fzP10 : list sobj := Eval vm_compute in optR (entails_frA C_fzP10 Pre_fz (s_fz C_fzP10)).
Definition TT_fzP10 : axst := Eval vm_compute in T_after Pre_fz C_fzP10 (s_fz C_fzP10) R_fzP10 P_fz.
Definition T_fzP10 : axst := Eval vm_compute in fz_undo false TT_fzP10.
Definition E_pfP10 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzP10) 0.
Definition C_pfP10 : axst := Eval vm_compute in pf_site E_pfP10 0.
Definition R_pfP10 : list sobj := Eval vm_compute in optR (entails_frA C_pfP10 (PreP 0) (s_pf C_pfP10 0)).
Definition T_pfP10 : axst := Eval vm_compute in T_after (PreP 0) C_pfP10 (s_pf C_pfP10 0) R_pfP10 (P_pf 0).
Definition U_pfP10 : axst := Eval vm_compute in pf_undo T_pfP10.
Definition LV_P10 : list leafA := Eval vm_compute in runL FUEL_L U_pfP10.
Definition LX_P10 : axst := Eval vm_compute in nthA S_T LV_P10 0.
Lemma LV_P10_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc9A2U1A3S32S40S19S34Sd3A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzPc0 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_P true 0)) 0.
Definition C_fzPc0 : axst := Eval vm_compute in fz_site false E_fzPc0.
Definition R_fzPc0 : list sobj := Eval vm_compute in optR (entails_frA C_fzPc0 Pre_fz (s_fz C_fzPc0)).
Definition TT_fzPc0 : axst := Eval vm_compute in T_after Pre_fz C_fzPc0 (s_fz C_fzPc0) R_fzPc0 P_fz.
Definition T_fzPc0 : axst := Eval vm_compute in fz_undo false TT_fzPc0.
Definition E_pfPc0 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzPc0) 0.
Definition C_pfPc0 : axst := Eval vm_compute in pf_site E_pfPc0 0.
Definition R_pfPc0 : list sobj := Eval vm_compute in optR (entails_frA C_pfPc0 (PreP 0) (s_pf C_pfPc0 0)).
Definition T_pfPc0 : axst := Eval vm_compute in T_after (PreP 0) C_pfPc0 (s_pf C_pfPc0 0) R_pfPc0 (P_pf 0).
Definition U_pfPc0 : axst := Eval vm_compute in pf_undo T_pfPc0.
Definition LV_Pc0 : list leafA := Eval vm_compute in runL FUEL_L U_pfPc0.
Definition LB_Pc0 : axst := Eval vm_compute in nthA S_T LV_Pc0 0.
Definition LX_Pc0 : axst := Eval vm_compute in nthA S_T LV_Pc0 1.
Lemma LV_Pc0_len : ltac2:(tb__ "0|0|
S33S32S1SaS35ScaA2U2A3S32S40S19S34Sd4A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzPc1 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_P true 1)) 0.
Definition C_fzPc1 : axst := Eval vm_compute in fz_site false E_fzPc1.
Definition R_fzPc1 : list sobj := Eval vm_compute in optR (entails_frA C_fzPc1 Pre_fz (s_fz C_fzPc1)).
Definition TT_fzPc1 : axst := Eval vm_compute in T_after Pre_fz C_fzPc1 (s_fz C_fzPc1) R_fzPc1 P_fz.
Definition T_fzPc1 : axst := Eval vm_compute in fz_undo false TT_fzPc1.
Definition E_pfPc1 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzPc1) 0.
Definition C_pfPc1 : axst := Eval vm_compute in pf_site E_pfPc1 1.
Definition R_pfPc1 : list sobj := Eval vm_compute in optR (entails_frA C_pfPc1 (PreP 1) (s_pf C_pfPc1 1)).
Definition T_pfPc1 : axst := Eval vm_compute in T_after (PreP 1) C_pfPc1 (s_pf C_pfPc1 1) R_pfPc1 (P_pf 1).
Definition U_pfPc1 : axst := Eval vm_compute in pf_undo T_pfPc1.
Definition LV_Pc1 : list leafA := Eval vm_compute in runL FUEL_L U_pfPc1.
Definition LB_Pc1 : axst := Eval vm_compute in nthA S_T LV_Pc1 0.
Definition LX_Pc1 : axst := Eval vm_compute in nthA S_T LV_Pc1 1.
Lemma LV_Pc1_len : ltac2:(tb__ "0|0|
S33S32S1SaS35ScbA2U2A3S32S40S19S34Sd5A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzPc2 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_P true 2)) 0.
Definition C_fzPc2 : axst := Eval vm_compute in fz_site false E_fzPc2.
Definition R_fzPc2 : list sobj := Eval vm_compute in optR (entails_frA C_fzPc2 Pre_fz (s_fz C_fzPc2)).
Definition TT_fzPc2 : axst := Eval vm_compute in T_after Pre_fz C_fzPc2 (s_fz C_fzPc2) R_fzPc2 P_fz.
Definition T_fzPc2 : axst := Eval vm_compute in fz_undo false TT_fzPc2.
Definition E_pfPc2 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzPc2) 0.
Definition C_pfPc2 : axst := Eval vm_compute in pf_site E_pfPc2 2.
Definition R_pfPc2 : list sobj := Eval vm_compute in optR (entails_frA C_pfPc2 (PreP 2) (s_pf C_pfPc2 2)).
Definition T_pfPc2 : axst := Eval vm_compute in T_after (PreP 2) C_pfPc2 (s_pf C_pfPc2 2) R_pfPc2 (P_pf 2).
Definition U_pfPc2 : axst := Eval vm_compute in pf_undo T_pfPc2.
Definition LV_Pc2 : list leafA := Eval vm_compute in runL FUEL_L U_pfPc2.
Definition LB_Pc2 : axst := Eval vm_compute in nthA S_T LV_Pc2 0.
Definition LX_Pc2 : axst := Eval vm_compute in nthA S_T LV_Pc2 1.
Lemma LV_Pc2_len : ltac2:(tb__ "0|0|
S33S32S1SaS35SccA2U2A3S32S40S19S34Sd6A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzPc3 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_P true 3)) 0.
Definition C_fzPc3 : axst := Eval vm_compute in fz_site false E_fzPc3.
Definition R_fzPc3 : list sobj := Eval vm_compute in optR (entails_frA C_fzPc3 Pre_fz (s_fz C_fzPc3)).
Definition TT_fzPc3 : axst := Eval vm_compute in T_after Pre_fz C_fzPc3 (s_fz C_fzPc3) R_fzPc3 P_fz.
Definition T_fzPc3 : axst := Eval vm_compute in fz_undo false TT_fzPc3.
Definition E_pfPc3 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzPc3) 0.
Definition C_pfPc3 : axst := Eval vm_compute in pf_site E_pfPc3 3.
Definition R_pfPc3 : list sobj := Eval vm_compute in optR (entails_frA C_pfPc3 (PreP 3) (s_pf C_pfPc3 3)).
Definition T_pfPc3 : axst := Eval vm_compute in T_after (PreP 3) C_pfPc3 (s_pf C_pfPc3 3) R_pfPc3 (P_pf 3).
Definition U_pfPc3 : axst := Eval vm_compute in pf_undo T_pfPc3.
Definition LV_Pc3 : list leafA := Eval vm_compute in runL FUEL_L U_pfPc3.
Definition LX_Pc3 : axst := Eval vm_compute in nthA S_T LV_Pc3 0.
Lemma LV_Pc3_len : ltac2:(tb__ "0|0|
S33S32S1SaS35ScdA2U1A3S32S40S19S34Sd7A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_fp (E : axst) : wsub := ltac2:(tb__ "0|1|
S0SbS41S13A2M0S7S41S13PfS14S12aS12bS106Z50A2A1A1A4S0G0S7S41S13PdSffA4S13eP1S34VE;A1S34SfbA1A3A3A3").
Definition runX (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S4S6S35A1M0A1G0Lx;S37Sf5Vfuel;SfeVA;S3A5G0R1Ll;S2S35A1X4x2").
Section ExitP.
  Variable LX : axst.
  Definition XF1 : axst := ltac2:(tb__ "0|0|
S109S7S13S13S1bS44A1SffA4VLX;A2").
  Definition R_fp : list sobj := ltac2:(tb__ "0|0|
S48S118S154SfbS6cS154A1A3A1").
  Definition T_fp : axst := ltac2:(tb__ "0|0|
S43SfbS154S6cS154A1S155S102A5").

  Definition LV_j : list leafA := runX FUEL_X T_fp.
End ExitP.
Definition T_fp0 : axst := Eval vm_compute in T_fp LX_Pc0.

Definition regs_J (status : sv) : list sv := ltac2:(tb__ "0|1|
S0S13S14Z0A1M0S0S13S42U1A1S0S13S111S0S13S14Z10800A1S0S13S113S0S13S42U5A1S0S13S42U6A1S0S13S42U7A1S0S13Vstatus;S0S13S101S0S13S42UaA1S0S13S42UbA1S0S13S42UcA1S0S13S42UdA1S0S13S42UeA1S0S13S42UfA1S0S13S42U10A1S0S13S42U11A1S0S13S103S0S13S116S0S13SffS0S13S117S0S13S14S134A1S0S13G0S0S13G0S0S13G0S0S13G0S0S13G0S0S13S42U1cA1S0S13S42U1dA1S0S13S42U1eA1S0S13S42U1fA1S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition J_P (n : Z) (status : sv) : axst := ltac2:(tb__ "0|0|
S3aS22Z8c718Sf4Vstatus;A1S8bS24SdS13A1S95Vn;S18S34Se3A1A1A2S10dS7dScA9S10cS14Sf6A1A3").

Definition fb_site (E : axst) : axst := ltac2:(tb__ "0|4|
S34VE;A1S16S18R1A1S6S15A1SaS15R1A2S1S100R2S104S14S12aS12bS106Z50A2A1A1A3S1S100R3S10aS14Nd0A1A3S1S137R5R2S114A3S16S16eS1S6S1A1M0S170S1A1S1S16dSeS160S1S16cR1A1S0S1R4S0S1R3S2S1A1A3A3M1A3A1M2A1Li;S1S16fG2A1Lx;S138U0M3R4A2A6G0S11dR2S144S18R2A1S9S1G1R1A3A2A2S16S4S16A1S16Lx;S120R1G3A2S16R1Lx;R1X4x2S16S109S7S13S13S101S10eA4S39VE;R1A2A2TS4;TS3;Trest;TS2;Tit;Tiw;Tn;Tobjs;TS;").

Definition ex_carved : list sobj := map lc_obj N_ex.
Definition ex_site (E : axst) : axst := ltac2:(tb__ "0|a|
S34VE;A1S16S18R1A1M0S6S15A1SaS15R1A2S1S100R2S111S14S12aS106A1A1A3S1S100R3S10aS14N80A1A3S1S137R5R2S115A3S16S100R5S14Z0M1A1S14S141A1A3S1S14aS14aS14aS14aS14aR2R1S12cS141Z8cA2Z4S12bS12eZ2Z20A2Z1A2A5R1S12cS141Z10A2Z8M2G1A5R1S12cS141G2A2G2G1A5R1S12cS141Z38A2G2G1A5R1S12cS141Z28A2G2G1A5S16S16eS1S6S1A1M3S170S1A1S1S16dSeS160S1S16cR1A1S0S1R6S0S1R5S2S1A1A3A3M4A3A1M5A1Li;S1S16fG5A1Lx;S138U0M6R6A2A6G3S11dR2S144S18R2A1S9S1G4R1A3A2A2S16S4S16A1S16Lx;M7S120R1G6A2S16R1Lx;M8R1X4x2S16G7S11fR1G6S14N430A1A3G8R1X4x2S16S11dR1S9S15G0Se5A3A2S16S22S19R1A1S16bS20R1A1S0SbS1S13A2M9S7S1S13U4S14S135A1A4S2G9A1A3A2S2fR1A1S2eR1A1S31R1A1G0S2cR1A1S1fR1A1S30R1A1A9S16S3aR1S2SbS13S13A2A1S3cVE;A1A3TS8;TS7;TS6;TS5;TS4;Trest;TS1;Tie;TS0;Tim;Tiw;Tn;Tobjs;TS;").

Section XChainP.
  Variable k : Z.
  Variable LX : axst.
  Definition XF1k : axst := ltac2:(tb__ "0|0|
S109S7S13S13S1bS44A1SffA4VLX;A2").
  Definition R_fpk : list sobj := ltac2:(tb__ "0|0|
S48S118S15dSfbS6cS15dA1A3A1").
  Definition T_fpk : axst := ltac2:(tb__ "0|0|
S43SfbS15dS6cS15dA1S15eS102A5").
End XChainP.

Definition R_fp_P10 : list sobj := Eval vm_compute in R_fpk LX_P10.
Definition T_fp_P10 : axst := Eval vm_compute in T_fpk LX_P10.
Definition LJa_P10 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_P10) 0.
Definition LJb_P10 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_P10) 1.

Definition R_fp_Pc0 : list sobj := Eval vm_compute in R_fpk LX_Pc0.
Definition T_fp_Pc0 : axst := Eval vm_compute in T_fpk LX_Pc0.
Definition LJa_Pc0 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc0) 0.
Definition LJb_Pc0 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc0) 1.

Definition R_fp_Pc1 : list sobj := Eval vm_compute in R_fpk LX_Pc1.
Definition T_fp_Pc1 : axst := Eval vm_compute in T_fpk LX_Pc1.
Definition LJa_Pc1 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc1) 0.
Definition LJb_Pc1 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc1) 1.

Definition R_fp_Pc2 : list sobj := Eval vm_compute in R_fpk LX_Pc2.
Definition T_fp_Pc2 : axst := Eval vm_compute in T_fpk LX_Pc2.
Definition LJa_Pc2 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc2) 0.
Definition LJb_Pc2 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc2) 1.

Definition R_fp_Pc3 : list sobj := Eval vm_compute in R_fpk LX_Pc3.
Definition T_fp_Pc3 : axst := Eval vm_compute in T_fpk LX_Pc3.
Definition LJa_Pc3 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc3) 0.
Definition LJb_Pc3 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fp_Pc3) 1.

Definition O_winT : sobj := ltac2:(tb__ "0|0|
S1eS104S14S12aS12bS106Z50A2A1A1S14Z0A1S2S1dA1S1cA5").
Definition objs_LE (k : Z) : list sobj := ltac2:(tb__ "0|0|
S95Vk;S0S15SdbS13cS15U1S18S34S5bA1A1A3A3A2").
Definition facts_LE (v : bool) (k : Z) : list sprop := ltac2:(tb__ "0|0|
S9S17SaeVv;Vk;A2S9S17S0S17S1aSffS14Z0A1A2S2S17A1A3S10dA3A3").
Definition L_E (v : bool) (k : Z) : axst := ltac2:(tb__ "0|0|
S3aS22S130Sb9S14S131A1S14Z0A1S8aVv;Vk;A2A3S8bS24SdS13A1SedVk;A1Se6Vv;Vk;A2S7dScA9S10cS14Sf6A1A3").
Lemma L_E_wf : ltac2:(tb__ "0|2|
S33S32S8S3eS5aS3Z0M0A2M1A1S3A3S33S32S8S23S34G1A1A1S3A3S32S8S23S34S5aScG0A2A1A1S3A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ent_LE_in : ltac2:(tb__ "0|3|
S33S32S8S3fS5bS5aScZ0M0A2M1S13eS16aS34S5bA1S34G1A1A3A3S3A3S32S8S3fS65S5aS3G0A2M2S13eS16aS34S65A1S34G2A1A3A3S3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section IterE.
  Definition E_fzE (k : Z) : axst := ltac2:(tb__ "0|0|
S57S105S6bS62S5aS3Vk;A2A2U0A3").
  Definition C_fzE (k : Z) : axst := fz_site true (E_fzE k).
  Definition R_fzE (k : Z) : list sobj := ltac2:(tb__ "0|1|
S48S118S174Vk;A1M0S153S6dG0A1A3A1").
  Definition TT_fzE (k : Z) : axst := ltac2:(tb__ "0|1|
S43S153S174Vk;A1M0S6dG0A1S176Vk;A1S182A5").
  Definition T_fzE (k : Z) : axst := fz_undo true (TT_fzE k).
  Definition E_pfE (k : Z) : axst := ltac2:(tb__ "0|0|
S57S105S6bS62S178Vk;A1A2U0A3").
  Definition C_pfE (k : Z) : axst := pf_site (E_pfE k) k.
  Definition R_pfE (k : Z) : list sobj := ltac2:(tb__ "0|1|
S48S118S175Vk;A1M0S5cVk;A1S5fG0Vk;A2A3A1").
  Definition T_pfE (k : Z) : axst := ltac2:(tb__ "0|1|
S43S5cVk;A1S175Vk;A1M0S5fG0Vk;A2S177Vk;A1S123Vk;A1A5").
  Definition U_pfE (k : Z) : axst := pf_undo (T_pfE k).
  Definition LV_endE (k : Z) : list leafA := runL FUEL_L (U_pfE k).
End IterE.

Definition E_fzE10 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_E false 0)) 0.
Definition C_fzE10 : axst := Eval vm_compute in fz_site true E_fzE10.
Definition R_fzE10 : list sobj := Eval vm_compute in optR (entails_frA C_fzE10 Pre_fz (s_fz C_fzE10)).
Definition TT_fzE10 : axst := Eval vm_compute in T_after Pre_fz C_fzE10 (s_fz C_fzE10) R_fzE10 P_fz.
Definition T_fzE10 : axst := Eval vm_compute in fz_undo true TT_fzE10.
Definition E_pfE10 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzE10) 0.
Definition C_pfE10 : axst := Eval vm_compute in pf_site E_pfE10 0.
Definition R_pfE10 : list sobj := Eval vm_compute in optR (entails_frA C_pfE10 (PreP 0) (s_pf C_pfE10 0)).
Definition T_pfE10 : axst := Eval vm_compute in T_after (PreP 0) C_pfE10 (s_pf C_pfE10 0) R_pfE10 (P_pf 0).
Definition U_pfE10 : axst := Eval vm_compute in pf_undo T_pfE10.
Definition LV_E10 : list leafA := Eval vm_compute in runL FUEL_L U_pfE10.
Definition LX_E10 : axst := Eval vm_compute in nthA S_T LV_E10 0.
Lemma LV_E10_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc4A2U1A3S32S40S19S34SceA1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzEc0 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_E true 0)) 0.
Definition C_fzEc0 : axst := Eval vm_compute in fz_site true E_fzEc0.
Definition R_fzEc0 : list sobj := Eval vm_compute in optR (entails_frA C_fzEc0 Pre_fz (s_fz C_fzEc0)).
Definition TT_fzEc0 : axst := Eval vm_compute in T_after Pre_fz C_fzEc0 (s_fz C_fzEc0) R_fzEc0 P_fz.
Definition T_fzEc0 : axst := Eval vm_compute in fz_undo true TT_fzEc0.
Definition E_pfEc0 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzEc0) 0.
Definition C_pfEc0 : axst := Eval vm_compute in pf_site E_pfEc0 0.
Definition R_pfEc0 : list sobj := Eval vm_compute in optR (entails_frA C_pfEc0 (PreP 0) (s_pf C_pfEc0 0)).
Definition T_pfEc0 : axst := Eval vm_compute in T_after (PreP 0) C_pfEc0 (s_pf C_pfEc0 0) R_pfEc0 (P_pf 0).
Definition U_pfEc0 : axst := Eval vm_compute in pf_undo T_pfEc0.
Definition LV_Ec0 : list leafA := Eval vm_compute in runL FUEL_L U_pfEc0.
Definition LB_Ec0 : axst := Eval vm_compute in nthA S_T LV_Ec0 0.
Definition LX_Ec0 : axst := Eval vm_compute in nthA S_T LV_Ec0 1.
Lemma LV_Ec0_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc5A2U2A3S32S40S19S34ScfA1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzEc1 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_E true 1)) 0.
Definition C_fzEc1 : axst := Eval vm_compute in fz_site true E_fzEc1.
Definition R_fzEc1 : list sobj := Eval vm_compute in optR (entails_frA C_fzEc1 Pre_fz (s_fz C_fzEc1)).
Definition TT_fzEc1 : axst := Eval vm_compute in T_after Pre_fz C_fzEc1 (s_fz C_fzEc1) R_fzEc1 P_fz.
Definition T_fzEc1 : axst := Eval vm_compute in fz_undo true TT_fzEc1.
Definition E_pfEc1 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzEc1) 0.
Definition C_pfEc1 : axst := Eval vm_compute in pf_site E_pfEc1 1.
Definition R_pfEc1 : list sobj := Eval vm_compute in optR (entails_frA C_pfEc1 (PreP 1) (s_pf C_pfEc1 1)).
Definition T_pfEc1 : axst := Eval vm_compute in T_after (PreP 1) C_pfEc1 (s_pf C_pfEc1 1) R_pfEc1 (P_pf 1).
Definition U_pfEc1 : axst := Eval vm_compute in pf_undo T_pfEc1.
Definition LV_Ec1 : list leafA := Eval vm_compute in runL FUEL_L U_pfEc1.
Definition LB_Ec1 : axst := Eval vm_compute in nthA S_T LV_Ec1 0.
Definition LX_Ec1 : axst := Eval vm_compute in nthA S_T LV_Ec1 1.
Lemma LV_Ec1_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc6A2U2A3S32S40S19S34Sd0A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzEc2 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_E true 2)) 0.
Definition C_fzEc2 : axst := Eval vm_compute in fz_site true E_fzEc2.
Definition R_fzEc2 : list sobj := Eval vm_compute in optR (entails_frA C_fzEc2 Pre_fz (s_fz C_fzEc2)).
Definition TT_fzEc2 : axst := Eval vm_compute in T_after Pre_fz C_fzEc2 (s_fz C_fzEc2) R_fzEc2 P_fz.
Definition T_fzEc2 : axst := Eval vm_compute in fz_undo true TT_fzEc2.
Definition E_pfEc2 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzEc2) 0.
Definition C_pfEc2 : axst := Eval vm_compute in pf_site E_pfEc2 2.
Definition R_pfEc2 : list sobj := Eval vm_compute in optR (entails_frA C_pfEc2 (PreP 2) (s_pf C_pfEc2 2)).
Definition T_pfEc2 : axst := Eval vm_compute in T_after (PreP 2) C_pfEc2 (s_pf C_pfEc2 2) R_pfEc2 (P_pf 2).
Definition U_pfEc2 : axst := Eval vm_compute in pf_undo T_pfEc2.
Definition LV_Ec2 : list leafA := Eval vm_compute in runL FUEL_L U_pfEc2.
Definition LB_Ec2 : axst := Eval vm_compute in nthA S_T LV_Ec2 0.
Definition LX_Ec2 : axst := Eval vm_compute in nthA S_T LV_Ec2 1.
Lemma LV_Ec2_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc7A2U2A3S32S40S19S34Sd1A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fzEc3 : axst := Eval vm_compute in nthA S_T (runL FUEL_L (L_E true 3)) 0.
Definition C_fzEc3 : axst := Eval vm_compute in fz_site true E_fzEc3.
Definition R_fzEc3 : list sobj := Eval vm_compute in optR (entails_frA C_fzEc3 Pre_fz (s_fz C_fzEc3)).
Definition TT_fzEc3 : axst := Eval vm_compute in T_after Pre_fz C_fzEc3 (s_fz C_fzEc3) R_fzEc3 P_fz.
Definition T_fzEc3 : axst := Eval vm_compute in fz_undo true TT_fzEc3.
Definition E_pfEc3 : axst := Eval vm_compute in nthA S_T (runL FUEL_L T_fzEc3) 0.
Definition C_pfEc3 : axst := Eval vm_compute in pf_site E_pfEc3 3.
Definition R_pfEc3 : list sobj := Eval vm_compute in optR (entails_frA C_pfEc3 (PreP 3) (s_pf C_pfEc3 3)).
Definition T_pfEc3 : axst := Eval vm_compute in T_after (PreP 3) C_pfEc3 (s_pf C_pfEc3 3) R_pfEc3 (P_pf 3).
Definition U_pfEc3 : axst := Eval vm_compute in pf_undo T_pfEc3.
Definition LV_Ec3 : list leafA := Eval vm_compute in runL FUEL_L U_pfEc3.
Definition LX_Ec3 : axst := Eval vm_compute in nthA S_T LV_Ec3 0.
Lemma LV_Ec3_len : ltac2:(tb__ "0|0|
S33S32S1SaS35Sc8A2U1A3S32S40S19S34Sd2A1A1S12fA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PreFN : axst := ltac2:(tb__ "0|0|
S152S14cS2S14eA1S14dA3").
Definition PostFN : axst := ltac2:(tb__ "0|0|
S151S14cS2S14eA1S14dA3").
Definition s_fn (E : axst) : wsub := ltac2:(tb__ "0|0|
S0SbS41S13A2S7S41S13PfS14S12aS12bS106Z50A2A1A1A4S13eP1S34VE;A1S34S7eA1A3A3").

Definition J_E (n : Z) (status : sv) : axst := J_P n status.

Section XChainE.
  Variable n : Z.
  Variable st : sv.
  Variable LX : axst.
  Definition R_fnk : list sobj := ltac2:(tb__ "0|0|
S48S118VLX;S7eSbbVLX;A1A3A1").
  Definition T_fnk : axst := ltac2:(tb__ "0|0|
S43S7eVLX;SbbVLX;A1S15bSdcA5").
  Definition JEk : axst := J_E n st.
  Definition E_fbEk : axst := ltac2:(tb__ "0|0|
S57S105SbaSfdS159A2U0A3").
  Definition C_fbEk : axst := fb_site E_fbEk.
  Definition R_fbEk : list sobj := ltac2:(tb__ "0|0|
S48S118S156SfbSfcS156A1A3A1").
  Definition T_fbEk : axst := ltac2:(tb__ "0|0|
S43SfbS156SfcS156A1S15aS102A5").
  Definition E_exEk : axst := ltac2:(tb__ "0|0|
S57S105SbaSfdS15cA2U0A3").
  Definition C_exEk : axst := ex_site E_exEk.
  Definition st_c : Z := match st with SLit c => c | _ => 0 end.
  Definition R_exEk : list sobj := ltac2:(tb__ "0|0|
S48S118S157S140Vn;S158A2S107S157Vn;S158A3A3A1").
End XChainE.

Definition R_fn_E10 : list sobj := Eval vm_compute in R_fnk LX_E10.
Definition T_fn_E10 : axst := Eval vm_compute in T_fnk LX_E10.
Definition LJEa_E10 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_E10) 0.
Definition LJEb_E10 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_E10) 1.

Definition R_fn_Ec0 : list sobj := Eval vm_compute in R_fnk LX_Ec0.
Definition T_fn_Ec0 : axst := Eval vm_compute in T_fnk LX_Ec0.
Definition LJEa_Ec0 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec0) 0.
Definition LJEb_Ec0 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec0) 1.

Definition R_fn_Ec1 : list sobj := Eval vm_compute in R_fnk LX_Ec1.
Definition T_fn_Ec1 : axst := Eval vm_compute in T_fnk LX_Ec1.
Definition LJEa_Ec1 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec1) 0.
Definition LJEb_Ec1 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec1) 1.

Definition R_fn_Ec2 : list sobj := Eval vm_compute in R_fnk LX_Ec2.
Definition T_fn_Ec2 : axst := Eval vm_compute in T_fnk LX_Ec2.
Definition LJEa_Ec2 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec2) 0.
Definition LJEb_Ec2 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec2) 1.

Definition R_fn_Ec3 : list sobj := Eval vm_compute in R_fnk LX_Ec3.
Definition T_fn_Ec3 : axst := Eval vm_compute in T_fnk LX_Ec3.
Definition LJEa_Ec3 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec3) 0.
Definition LJEb_Ec3 : axst := Eval vm_compute in nthA S_T (runX FUEL_X T_fn_Ec3) 1.

Definition E_fbE_10 : axst := Eval vm_compute in E_fbEk 1 (SLit 0).
Definition C_fbE_10 : axst := Eval vm_compute in C_fbEk 1 (SLit 0).
Definition R_fbE_10 : list sobj := Eval vm_compute in R_fbEk 1 (SLit 0).
Definition T_fbE_10 : axst := Eval vm_compute in T_fbEk 1 (SLit 0).
Lemma run_XEb_10 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ1S14Z0A1A2S3A5S5G0S0S35S38S99S11cA2S2S35A1A3A2A3S33S32S36S54S99A1S4bA3S32S36S43SfbS4bSfcS4bA1S81S102A5Sa5A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_10 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S4bSfbSfcS4bA1A3S5G0S81A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_10 : ltac2:(tb__ "0|0|
S32S8S119S4bSfbSfcS4bA1S81S0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_10 : axst := Eval vm_compute in E_exEk 1 (SLit 0).
Definition C_exE_10 : axst := Eval vm_compute in C_exEk 1 (SLit 0).
Definition R_exE_10 : list sobj := Eval vm_compute in R_exEk 1 (SLit 0).
Lemma run_XEc_10 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa5S3A5S5G0S0S35S38S78S11cA2S2S35A1A3A2A3S33S32S40S19S34S78A1A1S13fA3S32S36S53S78A1S72A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_10 : ltac2:(tb__ "0|3|
S32S4S6S15A1M0A1S118S72S140Z1M1Z0M2A2S107S72G1G2A3A3S5G0SdfA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fbE_20 : axst := Eval vm_compute in E_fbEk 2 (SLit 0).
Definition C_fbE_20 : axst := Eval vm_compute in C_fbEk 2 (SLit 0).
Definition R_fbE_20 : list sobj := Eval vm_compute in R_fbEk 2 (SLit 0).
Definition T_fbE_20 : axst := Eval vm_compute in T_fbEk 2 (SLit 0).
Lemma run_XEb_20 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ2S14Z0A1A2S3A5S5G0S0S35S38S9aS11cA2S2S35A1A3A2A3S33S32S36S54S9aA1S4cA3S32S36S43SfbS4cSfcS4cA1S82S102A5Sa6A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_20 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S4cSfbSfcS4cA1A3S5G0S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_20 : ltac2:(tb__ "0|0|
S32S8S119S4cSfbSfcS4cA1S82S0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_20 : axst := Eval vm_compute in E_exEk 2 (SLit 0).
Definition C_exE_20 : axst := Eval vm_compute in C_exEk 2 (SLit 0).
Definition R_exE_20 : list sobj := Eval vm_compute in R_exEk 2 (SLit 0).
Lemma run_XEc_20 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa6S3A5S5G0S0S35S38S79S11cA2S2S35A1A3A2A3S33S32S40S19S34S79A1A1S13fA3S32S36S53S79A1S73A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_20 : ltac2:(tb__ "0|3|
S32S4S6S15A1M0A1S118S73S140Z2M1Z0M2A2S107S73G1G2A3A3S5G0Se0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fbE_30 : axst := Eval vm_compute in E_fbEk 3 (SLit 0).
Definition C_fbE_30 : axst := Eval vm_compute in C_fbEk 3 (SLit 0).
Definition R_fbE_30 : list sobj := Eval vm_compute in R_fbEk 3 (SLit 0).
Definition T_fbE_30 : axst := Eval vm_compute in T_fbEk 3 (SLit 0).
Lemma run_XEb_30 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ3S14Z0A1A2S3A5S5G0S0S35S38S9bS11cA2S2S35A1A3A2A3S33S32S36S54S9bA1S4dA3S32S36S43SfbS4dSfcS4dA1S83S102A5Sa7A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_30 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S4dSfbSfcS4dA1A3S5G0S83A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_30 : ltac2:(tb__ "0|0|
S32S8S119S4dSfbSfcS4dA1S83S0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_30 : axst := Eval vm_compute in E_exEk 3 (SLit 0).
Definition C_exE_30 : axst := Eval vm_compute in C_exEk 3 (SLit 0).
Definition R_exE_30 : list sobj := Eval vm_compute in R_exEk 3 (SLit 0).
Lemma run_XEc_30 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa7S3A5S5G0S0S35S38S7aS11cA2S2S35A1A3A2A3S33S32S40S19S34S7aA1A1S13fA3S32S36S53S7aA1S74A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_30 : ltac2:(tb__ "0|3|
S32S4S6S15A1M0A1S118S74S140Z3M1Z0M2A2S107S74G1G2A3A3S5G0Se1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fbE_40 : axst := Eval vm_compute in E_fbEk 4 (SLit 0).
Definition C_fbE_40 : axst := Eval vm_compute in C_fbEk 4 (SLit 0).
Definition R_fbE_40 : list sobj := Eval vm_compute in R_fbEk 4 (SLit 0).
Definition T_fbE_40 : axst := Eval vm_compute in T_fbEk 4 (SLit 0).
Lemma run_XEb_40 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ4S14Z0A1A2S3A5S5G0S0S35S38S9cS11cA2S2S35A1A3A2A3S33S32S36S54S9cA1S4eA3S32S36S43SfbS4eSfcS4eA1S84S102A5Sa8A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_40 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S4eSfbSfcS4eA1A3S5G0S84A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_40 : ltac2:(tb__ "0|0|
S32S8S119S4eSfbSfcS4eA1S84S0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_40 : axst := Eval vm_compute in E_exEk 4 (SLit 0).
Definition C_exE_40 : axst := Eval vm_compute in C_exEk 4 (SLit 0).
Definition R_exE_40 : list sobj := Eval vm_compute in R_exEk 4 (SLit 0).
Lemma run_XEc_40 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa8S3A5S5G0S0S35S38S7bS11cA2S2S35A1A3A2A3S33S32S40S19S34S7bA1A1S13fA3S32S36S53S7bA1S75A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_40 : ltac2:(tb__ "0|3|
S32S4S6S15A1M0A1S118S75S140Z4M1Z0M2A2S107S75G1G2A3A3S5G0Se2A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fbE_02 : axst := Eval vm_compute in E_fbEk 0 (SLit 2).
Definition C_fbE_02 : axst := Eval vm_compute in C_fbEk 0 (SLit 2).
Definition R_fbE_02 : list sobj := Eval vm_compute in R_fbEk 0 (SLit 2).
Definition T_fbE_02 : axst := Eval vm_compute in T_fbEk 0 (SLit 2).
Lemma run_XEb_02 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ0S14Z2A1A2S3A5S5G0S0S35S38S98S11cA2S2S35A1A3A2A3S33S32S36S54S98A1S4aA3S32S36S43SfbS4aSfcS4aA1S80S102A5Sa4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_02 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S4aSfbSfcS4aA1A3S5G0S80A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_02 : ltac2:(tb__ "0|0|
S32S8S119S4aSfbSfcS4aA1S80S0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_02 : axst := Eval vm_compute in E_exEk 0 (SLit 2).
Definition C_exE_02 : axst := Eval vm_compute in C_exEk 0 (SLit 2).
Definition R_exE_02 : list sobj := Eval vm_compute in R_exEk 0 (SLit 2).
Lemma run_XEc_02 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa4S3A5S5G0S0S35S38S77S11cA2S2S35A1A3A2A3S33S32S40S19S34S77A1A1S13fA3S32S36S53S77A1S71A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_02 : ltac2:(tb__ "0|3|
S32S4S6S15A1M0A1S118S71S140Z0M1Z2M2A2S107S71G1G2A3A3S5G0SdeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_fbE_00 : axst := Eval vm_compute in E_fbEk 0 (SLit 0).
Definition C_fbE_00 : axst := Eval vm_compute in C_fbEk 0 (SLit 0).
Definition R_fbE_00 : list sobj := Eval vm_compute in R_fbEk 0 (SLit 0).
Definition T_fbE_00 : axst := Eval vm_compute in T_fbEk 0 (SLit 0).
Lemma run_XEb_00 : ltac2:(tb__ "0|2|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeS4fZ0M1S14G1A1A2S3A5S5G0S0S35S38S97S11cA2S2S35A1A3A2A3S33S32S36S54S97A1S49A3S32S36S43SfbS49SfcS49A1S7fS102A5Sa3A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_fbE_00 : ltac2:(tb__ "0|1|
S32S4S6S15A1M0A1S118S49SfbSfcS49A1A3S5G0S7fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_fbE_00 : ltac2:(tb__ "0|0|
S32S8S119S49SfbSfcS49A1S7fS0S36S102S2S36A1A3A5S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_exE_00 : axst := Eval vm_compute in E_exEk 0 (SLit 0).
Definition C_exE_00 : axst := Eval vm_compute in C_exEk 0 (SLit 0).
Definition R_exE_00 : list sobj := Eval vm_compute in R_exEk 0 (SLit 0).
Lemma run_XEc_00 : ltac2:(tb__ "0|1|
S33S32S4S6S35A1M0A1S37Sf5SfdSfeSa3S3A5S5G0S0S35S38S76S11cA2S2S35A1A3A2A3S33S32S40S19S34S76A1A1S13fA3S32S36S53S76A1S70A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma fr_exE_00 : ltac2:(tb__ "0|2|
S32S4S6S15A1M0A1S118S70S140Z0M1G1A2S107S70G1G1A3A3S5G0SddA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run_N__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5SfdSfeS88S3A5").
Local Strategy expand [run_N__R1].
Definition LN1a : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => nthA S_T ((match ro6__ with Some l => l | None => [] end)) 0) run_N__R1).
Definition LN1b : axst := Eval vm_compute in ((fun ro7__ : option (list leafA) => nthA S_T ((match ro7__ with Some l => l | None => [] end)) 1) run_N__R1).
Definition run_N__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S37Sf5SfdSfeS89S3A5").
Local Strategy expand [run_N__R2].
Definition LNca : axst := Eval vm_compute in ((fun ro8__ : option (list leafA) => nthA S_T ((match ro8__ with Some l => l | None => [] end)) 0) run_N__R2).
Definition LNcb : axst := Eval vm_compute in ((fun ro9__ : option (list leafA) => nthA S_T ((match ro9__ with Some l => l | None => [] end)) 1) run_N__R2).
Lemma run_N : ltac2:(tb__ "0|3|
S33S32S4S6S35A1M0A1M1S37Sf5SfdSfeS88S3A5S5G0S0S35S38Sc0S11cA2S0S35S38Sc1S11cA2S2S35A1M2A3A3A2A3S32G1S37Sf5SfdSfeS89S3A5S5G0S0S35S38Sc2S11cA2S0S35S38Sc3S11cA2G2A3A3A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_N__R1 <: run_N__R1 = Some [mkLeafA LN1a RsCut; mkLeafA LN1b RsCut]) (@eq_refl (option (list leafA)) run_N__R2 <: run_N__R2 = Some [mkLeafA LNca RsCut; mkLeafA LNcb RsCut])). Qed.
Definition s_JE (L : axst) (st : sv) : wsub := ltac2:(tb__ "0|0|
S13eS16aS34VL;A1S34S4fZ0Vst;A2A1A3").

End DrvT_states.

