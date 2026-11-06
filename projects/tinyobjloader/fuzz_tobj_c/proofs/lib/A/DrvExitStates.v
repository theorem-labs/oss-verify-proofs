(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "mkLeafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "true"; "option"; "Some"; "list"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvExitStates"; "CUTS_X"; "FUEL_X"; "E0_02"; "E_00"; "E_02"; "E_10"; "W_2"; "W_3"; "W_4"; "leaf1X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "reg_sv"; "sv"; "ss_next"; "ss_pc"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "Pre_exit"; "exit_ecall"; "wl_ecallA"; "vSPx"; "Pre_exit0"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition leaf1X (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
SaScS2A1M0A1S6Lo;Vo;G0G0S6Ll0;R1VA;S2G0G0S6Ll1;R1S7R2A1S2G0VA;Ll3;Ll2;Xcx2Ll1;Ll;Xcx2Ll0;VA;Xax2").
Definition run_toX (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S18VA;S3S8Vfuel;Vcuts;VA;S9A5A2").

Definition CUTS_X : list Z := ltac2:(tb__ "0|0|
SdS24S20SdS24S21SeS24A1A3A3").
Definition FUEL_X : nat := 9000%nat.

Definition run0_02__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS23Z0Z2A2S9A5").
Local Strategy expand [run0_02__R].
Definition E0_02 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1X (Pre_exit0 0 2) (ro1__)))) run0_02__R).
Lemma run0_02 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS23Z0Z2A2S9A5SbG0SdS2S5S11S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run0_02__R <: run0_02__R = Some [mkLeafA E0_02 RsCut]). Qed.
Lemma E0_02_at : ltac2:(tb__ "0|2|
S1S0S24S1dS4S11A1M0A1M1S20A3S1S0SaS26A1S2aS8G1A2SbS26S27A2A3S1S0S1bS1aG0Z11A2S19Z5eA1A3S1S0S1bS1aG0ZaA2S19Z2A1A3S0S25S1cG0A1S2bA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_00__R : option (list leafA) := ltac2:(tb__ "0|1|
S3S8S10SfS1fZ0M0G0A2S9A5").
Local Strategy expand [run_00__R].
Definition E_00 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1X (Pre_exit 0 0) (ro2__)))) run_00__R).
Lemma run_00 : ltac2:(tb__ "0|2|
S0SaScS2A1M0A1S3S8S10SfS1fZ0M1G1A2S9A5SbG0SdS2S5S12S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_00__R <: run_00__R = Some [mkLeafA E_00 RsCut]). Qed.
Definition run_02__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS1fZ0Z2A2S9A5").
Local Strategy expand [run_02__R].
Definition E_02 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1X (Pre_exit 0 2) (ro3__)))) run_02__R).
Lemma run_02 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS1fZ0Z2A2S9A5SbG0SdS2S5S13S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_02__R <: run_02__R = Some [mkLeafA E_02 RsCut]). Qed.
Definition run_10__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS1fZ1Z0A2S9A5").
Local Strategy expand [run_10__R].
Definition E_10 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1X (Pre_exit 1 0) (ro4__)))) run_10__R).
Lemma run_10 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS1fZ1Z0A2S9A5SbG0SdS2S5S14S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_10__R <: run_10__R = Some [mkLeafA E_10 RsCut]). Qed.

Lemma E_00_at : ltac2:(tb__ "0|2|
S1S0S24S1dS4S12A1M0A1M1S20A3S1S0SaS26A1S2aS8G1A2SbS26S27A2A3S1S0S1bS1aG0Z11A2S19Z5eA1A3S1S0S1bS1aG0ZaA2S19Z0A1A3S0S25S1cG0A1S2bA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E_02_at : ltac2:(tb__ "0|2|
S1S0S24S1dS4S13A1M0A1M1S20A3S1S0SaS26A1S2aS8G1A2SbS26S27A2A3S1S0S1bS1aG0Z11A2S19Z5eA1A3S1S0S1bS1aG0ZaA2S19Z2A1A3S0S25S1cG0A1S2bA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E_10_at : ltac2:(tb__ "0|2|
S1S0S24S1dS4S14A1M0A1M1S20A3S1S0SaS26A1S2aS8G1A2SbS26S27A2A3S1S0S1bS1aG0Z11A2S19Z5eA1A3S1S0S1bS1aG0ZaA2S19Z0A1A3S0S25S1cG0A1S2bA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_20__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS1fZ2Z0A2S9A5").
Local Strategy expand [run_20__R].
Definition W_2 : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => ((leaf1X (Pre_exit 2 0) (ro5__)))) run_20__R).
Lemma run_20 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS1fZ2Z0A2S9A5SbG0SdS2S5S15S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_20__R <: run_20__R = Some [mkLeafA W_2 RsCut]). Qed.
Definition run_30__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS1fZ3Z0A2S9A5").
Local Strategy expand [run_30__R].
Definition W_3 : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => ((leaf1X (Pre_exit 3 0) (ro6__)))) run_30__R).
Lemma run_30 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS1fZ3Z0A2S9A5SbG0SdS2S5S16S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_30__R <: run_30__R = Some [mkLeafA W_3 RsCut]). Qed.
Definition run_40__R : option (list leafA) := ltac2:(tb__ "0|0|
S3S8S10SfS1fZ4Z0A2S9A5").
Local Strategy expand [run_40__R].
Definition W_4 : axst := Eval vm_compute in ((fun ro7__ : option (list leafA) => ((leaf1X (Pre_exit 4 0) (ro7__)))) run_40__R).
Lemma run_40 : ltac2:(tb__ "0|1|
S0SaScS2A1M0A1S3S8S10SfS1fZ4Z0A2S9A5SbG0SdS2S5S17S29A2SeS2A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_40__R <: run_40__R = Some [mkLeafA W_4 RsCut]). Qed.

Lemma W_2_at : ltac2:(tb__ "0|1|
S1S0S24S1dS4S15A1M0A1S21A3S1S0S25S1cG0A1S2bA3S1S0S1bS1aG0Z11A2S19Z42A1A3S0S1bS1aG0Z2A2S1eS28S22S19N90A1A3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma W_3_at : ltac2:(tb__ "0|1|
S1S0S24S1dS4S16A1M0A1S21A3S1S0S25S1cG0A1S2bA3S1S0S1bS1aG0Z11A2S19Z42A1A3S0S1bS1aG0Z2A2S1eS28S22S19N90A1A3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma W_4_at : ltac2:(tb__ "0|1|
S1S0S24S1dS4S17A1M0A1S21A3S1S0S25S1cG0A1S2bA3S1S0S1bS1aG0Z11A2S19Z42A1A3S0S1bS1aG0Z2A2S1eS28S22S19N90A1A3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
