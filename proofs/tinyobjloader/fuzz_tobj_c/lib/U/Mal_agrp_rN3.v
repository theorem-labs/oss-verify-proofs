(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "true"; "prod"; "list"; "option"; "pair"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN3"; "CUTS_N"; "segs"; "SN_6_18_L"; "SN_6_18_Z"; "SN_6_8_L"; "SN_6_8_Z"; "SN_7_15_L"; "SN_7_15_Z"; "SN_7_7_L"; "SN_7_7_Z"; "SN_8_6_L"; "SN_8_6_Z"; "RN_6_18_L"; "RN_6_18_Z"; "RN_6_8_L"; "RN_6_8_Z"; "RN_7_15_L"; "RN_7_15_Z"; "RN_7_7_L"; "RN_7_7_Z"; "RN_8_6_L"; "RN_8_6_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "leaf"; "lf_state"; "stop_reason"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "sprop_eqb"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "sh"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "existsb"; "filter"].
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

Definition SN_6_8_L : sstate := ltac:(let x := eval vm_compute in (SN3z 6 8 false) in exact x).
Lemma SN_6_8_L_eq : SN3z 6 8 false = SN_6_8_L. Proof. vm_cast_no_check (@eq_refl sstate SN_6_8_L). Qed.
Definition MRN_6_8_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SaS0A5").
Definition MRN_6_8_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SaS0A5").
Definition RN_6_8_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_8_L__f in exact x).
Lemma MRN_6_8_L_c : MRN_6_8_L = RN_6_8_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_8_L MRN_6_8_L__f. Qed.
Lemma runN_6_8_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SaS0A5S14A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_8_L true) MRN_6_8_L RN_6_8_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_8_L true)) MRN_6_8_L_c). Qed.
Definition LN_6_8_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_8_L) in exact x).
Definition SN_6_8_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 6 8 true) in exact x).
Lemma SN_6_8_Z_eq : SN3z 6 8 true = SN_6_8_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_6_8_Z). Qed.
Definition MRN_6_8_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SbS0A5").
Definition MRN_6_8_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SbS0A5").
Definition RN_6_8_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_8_Z__f in exact x).
Lemma MRN_6_8_Z_c : MRN_6_8_Z = RN_6_8_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_8_Z MRN_6_8_Z__f. Qed.
Lemma runN_6_8_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SbS0A5S15A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_8_Z true) MRN_6_8_Z RN_6_8_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_8_Z true)) MRN_6_8_Z_c). Qed.
Definition LN_6_8_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_8_Z) in exact x).
Definition SN_6_18_L : sstate := ltac:(let x := eval vm_compute in (SN3z 6 18 false) in exact x).
Lemma SN_6_18_L_eq : SN3z 6 18 false = SN_6_18_L. Proof. vm_cast_no_check (@eq_refl sstate SN_6_18_L). Qed.
Definition MRN_6_18_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S8S0A5").
Definition MRN_6_18_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S8S0A5").
Definition RN_6_18_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_18_L__f in exact x).
Lemma MRN_6_18_L_c : MRN_6_18_L = RN_6_18_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_18_L MRN_6_18_L__f. Qed.
Lemma runN_6_18_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S8S0A5S12A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_18_L true) MRN_6_18_L RN_6_18_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_18_L true)) MRN_6_18_L_c). Qed.
Definition LN_6_18_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_18_L) in exact x).
Definition SN_6_18_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 6 18 true) in exact x).
Lemma SN_6_18_Z_eq : SN3z 6 18 true = SN_6_18_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_6_18_Z). Qed.
Definition MRN_6_18_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S9S0A5").
Definition MRN_6_18_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S9S0A5").
Definition RN_6_18_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_18_Z__f in exact x).
Lemma MRN_6_18_Z_c : MRN_6_18_Z = RN_6_18_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_18_Z MRN_6_18_Z__f. Qed.
Lemma runN_6_18_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S9S0A5S13A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_18_Z true) MRN_6_18_Z RN_6_18_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_18_Z true)) MRN_6_18_Z_c). Qed.
Definition LN_6_18_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_18_Z) in exact x).
Definition SN_7_7_L : sstate := ltac:(let x := eval vm_compute in (SN3z 7 7 false) in exact x).
Lemma SN_7_7_L_eq : SN3z 7 7 false = SN_7_7_L. Proof. vm_cast_no_check (@eq_refl sstate SN_7_7_L). Qed.
Definition MRN_7_7_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SeS0A5").
Definition MRN_7_7_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SeS0A5").
Definition RN_7_7_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_7_7_L__f in exact x).
Lemma MRN_7_7_L_c : MRN_7_7_L = RN_7_7_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_7_7_L MRN_7_7_L__f. Qed.
Lemma runN_7_7_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SeS0A5S18A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_7_7_L true) MRN_7_7_L RN_7_7_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_7_7_L true)) MRN_7_7_L_c). Qed.
Definition LN_7_7_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_7_7_L) in exact x).
Definition SN_7_7_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 7 7 true) in exact x).
Lemma SN_7_7_Z_eq : SN3z 7 7 true = SN_7_7_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_7_7_Z). Qed.
Definition MRN_7_7_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SfS0A5").
Definition MRN_7_7_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SfS0A5").
Definition RN_7_7_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_7_7_Z__f in exact x).
Lemma MRN_7_7_Z_c : MRN_7_7_Z = RN_7_7_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_7_7_Z MRN_7_7_Z__f. Qed.
Lemma runN_7_7_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SfS0A5S19A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_7_7_Z true) MRN_7_7_Z RN_7_7_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_7_7_Z true)) MRN_7_7_Z_c). Qed.
Definition LN_7_7_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_7_7_Z) in exact x).
Definition SN_7_15_L : sstate := ltac:(let x := eval vm_compute in (SN3z 7 15 false) in exact x).
Lemma SN_7_15_L_eq : SN3z 7 15 false = SN_7_15_L. Proof. vm_cast_no_check (@eq_refl sstate SN_7_15_L). Qed.
Definition MRN_7_15_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6ScS0A5").
Definition MRN_7_15_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6ScS0A5").
Definition RN_7_15_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_7_15_L__f in exact x).
Lemma MRN_7_15_L_c : MRN_7_15_L = RN_7_15_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_7_15_L MRN_7_15_L__f. Qed.
Lemma runN_7_15_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6ScS0A5S16A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_7_15_L true) MRN_7_15_L RN_7_15_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_7_15_L true)) MRN_7_15_L_c). Qed.
Definition LN_7_15_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_7_15_L) in exact x).
Definition SN_7_15_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 7 15 true) in exact x).
Lemma SN_7_15_Z_eq : SN3z 7 15 true = SN_7_15_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_7_15_Z). Qed.
Definition MRN_7_15_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SdS0A5").
Definition MRN_7_15_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SdS0A5").
Definition RN_7_15_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_7_15_Z__f in exact x).
Lemma MRN_7_15_Z_c : MRN_7_15_Z = RN_7_15_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_7_15_Z MRN_7_15_Z__f. Qed.
Lemma runN_7_15_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SdS0A5S17A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_7_15_Z true) MRN_7_15_Z RN_7_15_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_7_15_Z true)) MRN_7_15_Z_c). Qed.
Definition LN_7_15_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_7_15_Z) in exact x).
Definition SN_8_6_L : sstate := ltac:(let x := eval vm_compute in (SN3z 8 6 false) in exact x).
Lemma SN_8_6_L_eq : SN3z 8 6 false = SN_8_6_L. Proof. vm_cast_no_check (@eq_refl sstate SN_8_6_L). Qed.
Definition MRN_8_6_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S10S0A5").
Definition MRN_8_6_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S10S0A5").
Definition RN_8_6_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_8_6_L__f in exact x).
Lemma MRN_8_6_L_c : MRN_8_6_L = RN_8_6_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_8_6_L MRN_8_6_L__f. Qed.
Lemma runN_8_6_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S10S0A5S1aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_8_6_L true) MRN_8_6_L RN_8_6_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_8_6_L true)) MRN_8_6_L_c). Qed.
Definition LN_8_6_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_8_6_L) in exact x).
Definition SN_8_6_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 8 6 true) in exact x).
Lemma SN_8_6_Z_eq : SN3z 8 6 true = SN_8_6_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_8_6_Z). Qed.
Definition MRN_8_6_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S11S0A5").
Definition MRN_8_6_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S11S0A5").
Definition RN_8_6_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_8_6_Z__f in exact x).
Lemma MRN_8_6_Z_c : MRN_8_6_Z = RN_8_6_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_8_6_Z MRN_8_6_Z__f. Qed.
Lemma runN_8_6_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S11S0A5S1bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_8_6_Z true) MRN_8_6_Z RN_8_6_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_8_6_Z true)) MRN_8_6_Z_c). Qed.
Definition LN_8_6_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_8_6_Z) in exact x).

