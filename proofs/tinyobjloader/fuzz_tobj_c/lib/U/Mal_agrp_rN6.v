(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "true"; "prod"; "list"; "option"; "pair"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN6"; "CUTS_N"; "segs"; "SN_13_3_L"; "SN_13_3_Z"; "SN_13_6_L"; "SN_13_6_Z"; "SN_14_5_L"; "SN_14_5_Z"; "SN_15_2_L"; "SN_15_2_Z"; "SN_15_4_L"; "SN_15_4_Z"; "RN_13_3_L"; "RN_13_3_Z"; "RN_13_6_L"; "RN_13_6_Z"; "RN_14_5_L"; "RN_14_5_Z"; "RN_15_2_L"; "RN_15_2_Z"; "RN_15_4_L"; "RN_15_4_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "leaf"; "lf_state"; "stop_reason"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "sprop_eqb"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "sh"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "existsb"; "filter"].
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

Definition SN_13_3_L : sstate := ltac:(let x := eval vm_compute in (SN3z 13 3 false) in exact x).
Lemma SN_13_3_L_eq : SN3z 13 3 false = SN_13_3_L. Proof. vm_cast_no_check (@eq_refl sstate SN_13_3_L). Qed.
Definition MRN_13_3_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S8S0A5").
Definition MRN_13_3_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S8S0A5").
Definition RN_13_3_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_13_3_L__f in exact x).
Lemma MRN_13_3_L_c : MRN_13_3_L = RN_13_3_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_13_3_L MRN_13_3_L__f. Qed.
Lemma runN_13_3_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S8S0A5S12A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_13_3_L true) MRN_13_3_L RN_13_3_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_13_3_L true)) MRN_13_3_L_c). Qed.
Definition LN_13_3_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_13_3_L) in exact x).
Definition SN_13_3_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 13 3 true) in exact x).
Lemma SN_13_3_Z_eq : SN3z 13 3 true = SN_13_3_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_13_3_Z). Qed.
Definition MRN_13_3_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S9S0A5").
Definition MRN_13_3_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S9S0A5").
Definition RN_13_3_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_13_3_Z__f in exact x).
Lemma MRN_13_3_Z_c : MRN_13_3_Z = RN_13_3_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_13_3_Z MRN_13_3_Z__f. Qed.
Lemma runN_13_3_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S9S0A5S13A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_13_3_Z true) MRN_13_3_Z RN_13_3_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_13_3_Z true)) MRN_13_3_Z_c). Qed.
Definition LN_13_3_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_13_3_Z) in exact x).
Definition SN_13_6_L : sstate := ltac:(let x := eval vm_compute in (SN3z 13 6 false) in exact x).
Lemma SN_13_6_L_eq : SN3z 13 6 false = SN_13_6_L. Proof. vm_cast_no_check (@eq_refl sstate SN_13_6_L). Qed.
Definition MRN_13_6_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SaS0A5").
Definition MRN_13_6_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SaS0A5").
Definition RN_13_6_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_13_6_L__f in exact x).
Lemma MRN_13_6_L_c : MRN_13_6_L = RN_13_6_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_13_6_L MRN_13_6_L__f. Qed.
Lemma runN_13_6_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SaS0A5S14A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_13_6_L true) MRN_13_6_L RN_13_6_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_13_6_L true)) MRN_13_6_L_c). Qed.
Definition LN_13_6_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_13_6_L) in exact x).
Definition SN_13_6_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 13 6 true) in exact x).
Lemma SN_13_6_Z_eq : SN3z 13 6 true = SN_13_6_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_13_6_Z). Qed.
Definition MRN_13_6_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SbS0A5").
Definition MRN_13_6_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SbS0A5").
Definition RN_13_6_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_13_6_Z__f in exact x).
Lemma MRN_13_6_Z_c : MRN_13_6_Z = RN_13_6_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_13_6_Z MRN_13_6_Z__f. Qed.
Lemma runN_13_6_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SbS0A5S15A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_13_6_Z true) MRN_13_6_Z RN_13_6_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_13_6_Z true)) MRN_13_6_Z_c). Qed.
Definition LN_13_6_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_13_6_Z) in exact x).
Definition SN_14_5_L : sstate := ltac:(let x := eval vm_compute in (SN3z 14 5 false) in exact x).
Lemma SN_14_5_L_eq : SN3z 14 5 false = SN_14_5_L. Proof. vm_cast_no_check (@eq_refl sstate SN_14_5_L). Qed.
Definition MRN_14_5_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6ScS0A5").
Definition MRN_14_5_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6ScS0A5").
Definition RN_14_5_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_14_5_L__f in exact x).
Lemma MRN_14_5_L_c : MRN_14_5_L = RN_14_5_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_14_5_L MRN_14_5_L__f. Qed.
Lemma runN_14_5_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6ScS0A5S16A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_14_5_L true) MRN_14_5_L RN_14_5_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_14_5_L true)) MRN_14_5_L_c). Qed.
Definition LN_14_5_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_14_5_L) in exact x).
Definition SN_14_5_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 14 5 true) in exact x).
Lemma SN_14_5_Z_eq : SN3z 14 5 true = SN_14_5_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_14_5_Z). Qed.
Definition MRN_14_5_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SdS0A5").
Definition MRN_14_5_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SdS0A5").
Definition RN_14_5_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_14_5_Z__f in exact x).
Lemma MRN_14_5_Z_c : MRN_14_5_Z = RN_14_5_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_14_5_Z MRN_14_5_Z__f. Qed.
Lemma runN_14_5_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SdS0A5S17A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_14_5_Z true) MRN_14_5_Z RN_14_5_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_14_5_Z true)) MRN_14_5_Z_c). Qed.
Definition LN_14_5_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_14_5_Z) in exact x).
Definition SN_15_2_L : sstate := ltac:(let x := eval vm_compute in (SN3z 15 2 false) in exact x).
Lemma SN_15_2_L_eq : SN3z 15 2 false = SN_15_2_L. Proof. vm_cast_no_check (@eq_refl sstate SN_15_2_L). Qed.
Definition MRN_15_2_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SeS0A5").
Definition MRN_15_2_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SeS0A5").
Definition RN_15_2_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_15_2_L__f in exact x).
Lemma MRN_15_2_L_c : MRN_15_2_L = RN_15_2_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_15_2_L MRN_15_2_L__f. Qed.
Lemma runN_15_2_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SeS0A5S18A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_15_2_L true) MRN_15_2_L RN_15_2_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_15_2_L true)) MRN_15_2_L_c). Qed.
Definition LN_15_2_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_15_2_L) in exact x).
Definition SN_15_2_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 15 2 true) in exact x).
Lemma SN_15_2_Z_eq : SN3z 15 2 true = SN_15_2_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_15_2_Z). Qed.
Definition MRN_15_2_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SfS0A5").
Definition MRN_15_2_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SfS0A5").
Definition RN_15_2_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_15_2_Z__f in exact x).
Lemma MRN_15_2_Z_c : MRN_15_2_Z = RN_15_2_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_15_2_Z MRN_15_2_Z__f. Qed.
Lemma runN_15_2_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SfS0A5S19A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_15_2_Z true) MRN_15_2_Z RN_15_2_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_15_2_Z true)) MRN_15_2_Z_c). Qed.
Definition LN_15_2_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_15_2_Z) in exact x).
Definition SN_15_4_L : sstate := ltac:(let x := eval vm_compute in (SN3z 15 4 false) in exact x).
Lemma SN_15_4_L_eq : SN3z 15 4 false = SN_15_4_L. Proof. vm_cast_no_check (@eq_refl sstate SN_15_4_L). Qed.
Definition MRN_15_4_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S10S0A5").
Definition MRN_15_4_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S10S0A5").
Definition RN_15_4_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_15_4_L__f in exact x).
Lemma MRN_15_4_L_c : MRN_15_4_L = RN_15_4_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_15_4_L MRN_15_4_L__f. Qed.
Lemma runN_15_4_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S10S0A5S1aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_15_4_L true) MRN_15_4_L RN_15_4_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_15_4_L true)) MRN_15_4_L_c). Qed.
Definition LN_15_4_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_15_4_L) in exact x).
Definition SN_15_4_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 15 4 true) in exact x).
Lemma SN_15_4_Z_eq : SN3z 15 4 true = SN_15_4_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_15_4_Z). Qed.
Definition MRN_15_4_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S11S0A5").
Definition MRN_15_4_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S11S0A5").
Definition RN_15_4_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_15_4_Z__f in exact x).
Lemma MRN_15_4_Z_c : MRN_15_4_Z = RN_15_4_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_15_4_Z MRN_15_4_Z__f. Qed.
Lemma runN_15_4_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S11S0A5S1bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_15_4_Z true) MRN_15_4_Z RN_15_4_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_15_4_Z true)) MRN_15_4_Z_c). Qed.
Definition LN_15_4_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_15_4_Z) in exact x).

