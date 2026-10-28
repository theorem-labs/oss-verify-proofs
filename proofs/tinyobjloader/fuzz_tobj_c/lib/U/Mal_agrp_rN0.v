(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "true"; "prod"; "list"; "option"; "pair"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN0"; "CUTS_N"; "segs"; "SN_0_30_L"; "SN_0_30_Z"; "SN_1_15_L"; "SN_1_15_Z"; "SN_1_31_L"; "SN_1_31_Z"; "SN_2_10_L"; "SN_2_10_Z"; "SN_2_20_L"; "SN_2_20_Z"; "RN_0_30_L"; "RN_0_30_Z"; "RN_1_15_L"; "RN_1_15_Z"; "RN_1_31_L"; "RN_1_31_Z"; "RN_2_10_L"; "RN_2_10_Z"; "RN_2_20_L"; "RN_2_20_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "leaf"; "lf_state"; "stop_reason"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "sprop_eqb"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "sh"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "existsb"; "filter"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymEntail SymHeap Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.
Definition segs := segsU.
Definition CUTS_N : list Z := [0x202a8].
Definition lfs (l : list leaf) (i : nat) (d : sstate) : sstate := ltac2:(tb__ "0|0|
S1eS2bS1dVi;Vl;S21Vd;S20A2A4A1").
Definition unopt (o : option (list leaf)) : list leaf := match o with Some l => l | None => [] end.
Definition showX (S : sstate) (L : leaf) : ltac2:(tb__ "0|0|
S1S1S1S1S1S1S1S2aS1fA2S22A2S22A2S22A2S22A2S22A2S2S23A1A2") := ltac2:(tb__ "0|6|
S4S1S1S1S1S1S1S2aS1fA2M0S22A2M1S22A2M2S22A2M3S22A2M4S22A2S2S23A1S4G4S22S4G3S22S4G2S22S4G1S22S4G0S22S29VL;A1S28S1eVL;A1M5U13A2A4S28G5UeA2A4S28G5UaA2A4S28G5UbA2A4S28G5U19A2A4S2dS23S23S5S2cS23S25R1A1S24VS;A1A3A1Lp;S24G5A1A3A4").

Definition SN_0_30_L : sstate := ltac:(let x := eval vm_compute in (SN3z 0 30 false) in exact x).
Lemma SN_0_30_L_eq : SN3z 0 30 false = SN_0_30_L. Proof. vm_cast_no_check (@eq_refl sstate SN_0_30_L). Qed.
Definition MRN_0_30_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S8S0A5").
Definition MRN_0_30_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S8S0A5").
Definition RN_0_30_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_0_30_L__f in exact x).
Lemma MRN_0_30_L_c : MRN_0_30_L = RN_0_30_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_0_30_L MRN_0_30_L__f. Qed.
Lemma runN_0_30_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S8S0A5S12A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_0_30_L true) MRN_0_30_L RN_0_30_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_0_30_L true)) MRN_0_30_L_c). Qed.
Definition LN_0_30_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_0_30_L) in exact x).
Definition SN_0_30_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 0 30 true) in exact x).
Lemma SN_0_30_Z_eq : SN3z 0 30 true = SN_0_30_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_0_30_Z). Qed.
Definition MRN_0_30_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S9S0A5").
Definition MRN_0_30_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S9S0A5").
Definition RN_0_30_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_0_30_Z__f in exact x).
Lemma MRN_0_30_Z_c : MRN_0_30_Z = RN_0_30_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_0_30_Z MRN_0_30_Z__f. Qed.
Lemma runN_0_30_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S9S0A5S13A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_0_30_Z true) MRN_0_30_Z RN_0_30_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_0_30_Z true)) MRN_0_30_Z_c). Qed.
Definition LN_0_30_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_0_30_Z) in exact x).
Definition SN_1_15_L : sstate := ltac:(let x := eval vm_compute in (SN3z 1 15 false) in exact x).
Lemma SN_1_15_L_eq : SN3z 1 15 false = SN_1_15_L. Proof. vm_cast_no_check (@eq_refl sstate SN_1_15_L). Qed.
Definition MRN_1_15_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SaS0A5").
Definition MRN_1_15_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SaS0A5").
Definition RN_1_15_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_1_15_L__f in exact x).
Lemma MRN_1_15_L_c : MRN_1_15_L = RN_1_15_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_1_15_L MRN_1_15_L__f. Qed.
Lemma runN_1_15_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SaS0A5S14A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_1_15_L true) MRN_1_15_L RN_1_15_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_1_15_L true)) MRN_1_15_L_c). Qed.
Definition LN_1_15_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_1_15_L) in exact x).
Definition SN_1_15_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 1 15 true) in exact x).
Lemma SN_1_15_Z_eq : SN3z 1 15 true = SN_1_15_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_1_15_Z). Qed.
Definition MRN_1_15_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SbS0A5").
Definition MRN_1_15_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SbS0A5").
Definition RN_1_15_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_1_15_Z__f in exact x).
Lemma MRN_1_15_Z_c : MRN_1_15_Z = RN_1_15_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_1_15_Z MRN_1_15_Z__f. Qed.
Lemma runN_1_15_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SbS0A5S15A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_1_15_Z true) MRN_1_15_Z RN_1_15_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_1_15_Z true)) MRN_1_15_Z_c). Qed.
Definition LN_1_15_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_1_15_Z) in exact x).
Definition SN_1_31_L : sstate := ltac:(let x := eval vm_compute in (SN3z 1 31 false) in exact x).
Lemma SN_1_31_L_eq : SN3z 1 31 false = SN_1_31_L. Proof. vm_cast_no_check (@eq_refl sstate SN_1_31_L). Qed.
Definition MRN_1_31_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6ScS0A5").
Definition MRN_1_31_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6ScS0A5").
Definition RN_1_31_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_1_31_L__f in exact x).
Lemma MRN_1_31_L_c : MRN_1_31_L = RN_1_31_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_1_31_L MRN_1_31_L__f. Qed.
Lemma runN_1_31_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6ScS0A5S16A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_1_31_L true) MRN_1_31_L RN_1_31_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_1_31_L true)) MRN_1_31_L_c). Qed.
Definition LN_1_31_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_1_31_L) in exact x).
Definition SN_1_31_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 1 31 true) in exact x).
Lemma SN_1_31_Z_eq : SN3z 1 31 true = SN_1_31_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_1_31_Z). Qed.
Definition MRN_1_31_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SdS0A5").
Definition MRN_1_31_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SdS0A5").
Definition RN_1_31_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_1_31_Z__f in exact x).
Lemma MRN_1_31_Z_c : MRN_1_31_Z = RN_1_31_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_1_31_Z MRN_1_31_Z__f. Qed.
Lemma runN_1_31_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SdS0A5S17A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_1_31_Z true) MRN_1_31_Z RN_1_31_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_1_31_Z true)) MRN_1_31_Z_c). Qed.
Definition LN_1_31_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_1_31_Z) in exact x).
Definition SN_2_10_L : sstate := ltac:(let x := eval vm_compute in (SN3z 2 10 false) in exact x).
Lemma SN_2_10_L_eq : SN3z 2 10 false = SN_2_10_L. Proof. vm_cast_no_check (@eq_refl sstate SN_2_10_L). Qed.
Definition MRN_2_10_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SeS0A5").
Definition MRN_2_10_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SeS0A5").
Definition RN_2_10_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_2_10_L__f in exact x).
Lemma MRN_2_10_L_c : MRN_2_10_L = RN_2_10_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_2_10_L MRN_2_10_L__f. Qed.
Lemma runN_2_10_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SeS0A5S18A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_2_10_L true) MRN_2_10_L RN_2_10_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_2_10_L true)) MRN_2_10_L_c). Qed.
Definition LN_2_10_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_2_10_L) in exact x).
Definition SN_2_10_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 2 10 true) in exact x).
Lemma SN_2_10_Z_eq : SN3z 2 10 true = SN_2_10_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_2_10_Z). Qed.
Definition MRN_2_10_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SfS0A5").
Definition MRN_2_10_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SfS0A5").
Definition RN_2_10_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_2_10_Z__f in exact x).
Lemma MRN_2_10_Z_c : MRN_2_10_Z = RN_2_10_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_2_10_Z MRN_2_10_Z__f. Qed.
Lemma runN_2_10_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SfS0A5S19A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_2_10_Z true) MRN_2_10_Z RN_2_10_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_2_10_Z true)) MRN_2_10_Z_c). Qed.
Definition LN_2_10_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_2_10_Z) in exact x).
Definition SN_2_20_L : sstate := ltac:(let x := eval vm_compute in (SN3z 2 20 false) in exact x).
Lemma SN_2_20_L_eq : SN3z 2 20 false = SN_2_20_L. Proof. vm_cast_no_check (@eq_refl sstate SN_2_20_L). Qed.
Definition MRN_2_20_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S10S0A5").
Definition MRN_2_20_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S10S0A5").
Definition RN_2_20_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_2_20_L__f in exact x).
Lemma MRN_2_20_L_c : MRN_2_20_L = RN_2_20_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_2_20_L MRN_2_20_L__f. Qed.
Lemma runN_2_20_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S10S0A5S1aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_2_20_L true) MRN_2_20_L RN_2_20_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_2_20_L true)) MRN_2_20_L_c). Qed.
Definition LN_2_20_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_2_20_L) in exact x).
Definition SN_2_20_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 2 20 true) in exact x).
Lemma SN_2_20_Z_eq : SN3z 2 20 true = SN_2_20_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_2_20_Z). Qed.
Definition MRN_2_20_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S11S0A5").
Definition MRN_2_20_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S11S0A5").
Definition RN_2_20_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_2_20_Z__f in exact x).
Lemma MRN_2_20_Z_c : MRN_2_20_Z = RN_2_20_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_2_20_Z MRN_2_20_Z__f. Qed.
Lemma runN_2_20_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S11S0A5S1bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_2_20_Z true) MRN_2_20_Z RN_2_20_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_2_20_Z true)) MRN_2_20_Z_c). Qed.
Definition LN_2_20_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_2_20_Z) in exact x).

