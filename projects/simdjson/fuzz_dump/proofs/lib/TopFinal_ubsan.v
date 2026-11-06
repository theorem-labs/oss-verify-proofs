(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling Cfg.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib Require Import TopLevel Obligations ProofBase TopE TopSidesPU TopFinal_plain.
From OSSVerify.simdjson.fuzz_dump.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump.images Require Import Ubsan.
Require OSSVerify.Proofs.simdjson.fuzz_dump.lib.P.Rnd OSSVerify.Proofs.simdjson.fuzz_dump.lib.U.Sj_iface OSSVerify.Proofs.simdjson.fuzz_dump.lib.U.Impl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition client_U_stmt : Prop :=
  forall (CE : Ceiling) (RN : OSSVerify.Proofs.simdjson.fuzz_dump.lib.P.Rnd.RunRnd), @OSSVerify.Proofs.simdjson.fuzz_dump.lib.U.Sj_iface.rfuzz_one_stmt CE RN.

Lemma HU : client_U_stmt -> impl_U_stmt.
Proof. intros CU. exact (OSSVerify.Proofs.simdjson.fuzz_dump.lib.U.Impl_closed.impl_U_closed CU). Qed.

Theorem off_ubsan_cfg : client_P_stmt -> client_U_stmt -> strong_universal_error_free_T_scfg ACFG (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros CP CU. exact (ubsan_off (HP CP) (HU CU)). Qed.
Theorem base_ubsan_cfg : client_P_stmt -> client_U_stmt ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros CP CU. exact (ubsan_base (HP CP) (HU CU)). Qed.

