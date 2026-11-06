(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase TopFinal_plain.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Require OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_init2.
Require OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_exit.
Require OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_client_closed.

Lemma client_P_closed : client_P_stmt.
Proof.
  refine (conj _ (conj _ _)).
  - exact OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_init2.ios_init_proof.
  - intros CE. exact (@OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_exit.ios_exit_proof CE).
  - intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_client_closed.rfuzz_one_closed CE RN).
Qed.
