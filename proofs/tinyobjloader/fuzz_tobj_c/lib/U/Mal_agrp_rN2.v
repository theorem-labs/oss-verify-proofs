(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "true"; "prod"; "list"; "option"; "pair"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN2"; "CUTS_N"; "segs"; "SN_4_25_L"; "SN_4_25_Z"; "SN_5_10_L"; "SN_5_10_Z"; "SN_5_21_L"; "SN_5_21_Z"; "SN_5_5_L"; "SN_5_5_Z"; "SN_6_4_L"; "SN_6_4_Z"; "RN_4_25_L"; "RN_4_25_Z"; "RN_5_10_L"; "RN_5_10_Z"; "RN_5_21_L"; "RN_5_21_Z"; "RN_5_5_L"; "RN_5_5_Z"; "RN_6_4_L"; "RN_6_4_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sym_run"; "leaf"; "lf_state"; "stop_reason"; "RsFuel"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "sprop_eqb"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "reg"; "sh"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "@Stdlib.Lists.List"; "existsb"; "filter"].
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

Definition SN_4_25_L : sstate := ltac:(let x := eval vm_compute in (SN3z 4 25 false) in exact x).
Lemma SN_4_25_L_eq : SN3z 4 25 false = SN_4_25_L. Proof. vm_cast_no_check (@eq_refl sstate SN_4_25_L). Qed.
Definition MRN_4_25_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S8S0A5").
Definition MRN_4_25_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S8S0A5").
Definition RN_4_25_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_4_25_L__f in exact x).
Lemma MRN_4_25_L_c : MRN_4_25_L = RN_4_25_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_4_25_L MRN_4_25_L__f. Qed.
Lemma runN_4_25_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S8S0A5S12A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_4_25_L true) MRN_4_25_L RN_4_25_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_4_25_L true)) MRN_4_25_L_c). Qed.
Definition LN_4_25_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_4_25_L) in exact x).
Definition SN_4_25_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 4 25 true) in exact x).
Lemma SN_4_25_Z_eq : SN3z 4 25 true = SN_4_25_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_4_25_Z). Qed.
Definition MRN_4_25_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S9S0A5").
Definition MRN_4_25_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S9S0A5").
Definition RN_4_25_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_4_25_Z__f in exact x).
Lemma MRN_4_25_Z_c : MRN_4_25_Z = RN_4_25_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_4_25_Z MRN_4_25_Z__f. Qed.
Lemma runN_4_25_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S9S0A5S13A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_4_25_Z true) MRN_4_25_Z RN_4_25_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_4_25_Z true)) MRN_4_25_Z_c). Qed.
Definition LN_4_25_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_4_25_Z) in exact x).
Definition SN_5_5_L : sstate := ltac:(let x := eval vm_compute in (SN3z 5 5 false) in exact x).
Lemma SN_5_5_L_eq : SN3z 5 5 false = SN_5_5_L. Proof. vm_cast_no_check (@eq_refl sstate SN_5_5_L). Qed.
Definition MRN_5_5_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SeS0A5").
Definition MRN_5_5_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SeS0A5").
Definition RN_5_5_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_5_L__f in exact x).
Lemma MRN_5_5_L_c : MRN_5_5_L = RN_5_5_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_5_L MRN_5_5_L__f. Qed.
Lemma runN_5_5_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SeS0A5S18A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_5_L true) MRN_5_5_L RN_5_5_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_5_L true)) MRN_5_5_L_c). Qed.
Definition LN_5_5_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_5_L) in exact x).
Definition SN_5_5_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 5 5 true) in exact x).
Lemma SN_5_5_Z_eq : SN3z 5 5 true = SN_5_5_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_5_5_Z). Qed.
Definition MRN_5_5_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SfS0A5").
Definition MRN_5_5_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SfS0A5").
Definition RN_5_5_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_5_Z__f in exact x).
Lemma MRN_5_5_Z_c : MRN_5_5_Z = RN_5_5_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_5_Z MRN_5_5_Z__f. Qed.
Lemma runN_5_5_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SfS0A5S19A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_5_Z true) MRN_5_5_Z RN_5_5_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_5_Z true)) MRN_5_5_Z_c). Qed.
Definition LN_5_5_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_5_Z) in exact x).
Definition SN_5_10_L : sstate := ltac:(let x := eval vm_compute in (SN3z 5 10 false) in exact x).
Lemma SN_5_10_L_eq : SN3z 5 10 false = SN_5_10_L. Proof. vm_cast_no_check (@eq_refl sstate SN_5_10_L). Qed.
Definition MRN_5_10_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SaS0A5").
Definition MRN_5_10_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SaS0A5").
Definition RN_5_10_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_10_L__f in exact x).
Lemma MRN_5_10_L_c : MRN_5_10_L = RN_5_10_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_10_L MRN_5_10_L__f. Qed.
Lemma runN_5_10_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SaS0A5S14A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_10_L true) MRN_5_10_L RN_5_10_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_10_L true)) MRN_5_10_L_c). Qed.
Definition LN_5_10_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_10_L) in exact x).
Definition SN_5_10_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 5 10 true) in exact x).
Lemma SN_5_10_Z_eq : SN3z 5 10 true = SN_5_10_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_5_10_Z). Qed.
Definition MRN_5_10_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SbS0A5").
Definition MRN_5_10_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SbS0A5").
Definition RN_5_10_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_10_Z__f in exact x).
Lemma MRN_5_10_Z_c : MRN_5_10_Z = RN_5_10_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_10_Z MRN_5_10_Z__f. Qed.
Lemma runN_5_10_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SbS0A5S15A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_10_Z true) MRN_5_10_Z RN_5_10_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_10_Z true)) MRN_5_10_Z_c). Qed.
Definition LN_5_10_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_10_Z) in exact x).
Definition SN_5_21_L : sstate := ltac:(let x := eval vm_compute in (SN3z 5 21 false) in exact x).
Lemma SN_5_21_L_eq : SN3z 5 21 false = SN_5_21_L. Proof. vm_cast_no_check (@eq_refl sstate SN_5_21_L). Qed.
Definition MRN_5_21_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6ScS0A5").
Definition MRN_5_21_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6ScS0A5").
Definition RN_5_21_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_21_L__f in exact x).
Lemma MRN_5_21_L_c : MRN_5_21_L = RN_5_21_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_21_L MRN_5_21_L__f. Qed.
Lemma runN_5_21_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6ScS0A5S16A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_21_L true) MRN_5_21_L RN_5_21_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_21_L true)) MRN_5_21_L_c). Qed.
Definition LN_5_21_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_21_L) in exact x).
Definition SN_5_21_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 5 21 true) in exact x).
Lemma SN_5_21_Z_eq : SN3z 5 21 true = SN_5_21_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_5_21_Z). Qed.
Definition MRN_5_21_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6SdS0A5").
Definition MRN_5_21_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6SdS0A5").
Definition RN_5_21_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_5_21_Z__f in exact x).
Lemma MRN_5_21_Z_c : MRN_5_21_Z = RN_5_21_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_5_21_Z MRN_5_21_Z__f. Qed.
Lemma runN_5_21_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6SdS0A5S17A3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_5_21_Z true) MRN_5_21_Z RN_5_21_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_5_21_Z true)) MRN_5_21_Z_c). Qed.
Definition LN_5_21_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_5_21_Z) in exact x).
Definition SN_6_4_L : sstate := ltac:(let x := eval vm_compute in (SN3z 6 4 false) in exact x).
Lemma SN_6_4_L_eq : SN3z 6 4 false = SN_6_4_L. Proof. vm_cast_no_check (@eq_refl sstate SN_6_4_L). Qed.
Definition MRN_6_4_L : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S10S0A5").
Definition MRN_6_4_L__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S10S0A5").
Definition RN_6_4_L : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_4_L__f in exact x).
Lemma MRN_6_4_L_c : MRN_6_4_L = RN_6_4_L. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_4_L MRN_6_4_L__f. Qed.
Lemma runN_6_4_L : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S10S0A5S1aA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_4_L true) MRN_6_4_L RN_6_4_L (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_4_L true)) MRN_6_4_L_c). Qed.
Definition LN_6_4_L : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_4_L) in exact x).
Definition SN_6_4_Z : sstate := ltac:(let x := eval vm_compute in (SN3z 6 4 true) in exact x).
Lemma SN_6_4_Z_eq : SN3z 6 4 true = SN_6_4_Z. Proof. vm_cast_no_check (@eq_refl sstate SN_6_4_Z). Qed.
Definition MRN_6_4_Z : option (list leaf) := ltac2:(tb__ "0|0|
S1cS7U1f4S6S11S0A5").
Definition MRN_6_4_Z__f : option (list leaf) := ltac2:(tb__ "0|0|
S27S7U1f4S6S11S0A5").
Definition RN_6_4_Z : option (list leaf) := ltac:(let x := eval vm_compute in MRN_6_4_Z__f in exact x).
Lemma MRN_6_4_Z_c : MRN_6_4_Z = RN_6_4_Z. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN_6_4_Z MRN_6_4_Z__f. Qed.
Lemma runN_6_4_Z : ltac2:(tb__ "0|0|
S26S3S2S1dA1A1S1cS7U1f4S6S11S0A5S1bA3"). Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_N SN_6_4_Z true) MRN_6_4_Z RN_6_4_Z (@eq_refl _ (sym_run segs 500 CUTS_N SN_6_4_Z true)) MRN_6_4_Z_c). Qed.
Definition LN_6_4_Z : list leaf := ltac:(let x := eval vm_compute in (unopt RN_6_4_Z) in exact x).

