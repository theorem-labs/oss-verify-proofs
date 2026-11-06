(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Ceiling Cfg.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevel Obligations ProofBase TopFinal_plain TopFinal_ubsan.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Require OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P.Drt_client_closed.
Require OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.U.Drt_client_closed.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P.Drt_client_closed.rfuzz_one_closed CE RN). Qed.

Lemma client_U_closed : client_U_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.U.Drt_client_closed.rfuzz_one_closed CE RN). Qed.

Theorem off_ubsan_cfg : strong_universal_error_free_T_scfg ACFG
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (TopFinal_ubsan.off_ubsan_cfg client_P_closed client_U_closed). Qed.
Theorem base_ubsan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
  ShippedBudgets.lim_source ShippedBudgets.lim_target
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (TopFinal_ubsan.base_ubsan_cfg client_P_closed client_U_closed). Qed.
