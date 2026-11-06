(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase.
Require OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Rnd OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Sj_iface OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_iface
        OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_exit_top OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Impl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition client_fuzz_P_stmt : Prop :=
  forall (CE : Ceiling) (RN : OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Rnd.RunRnd), @OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Sj_iface.rfuzz_one_stmt CE RN.
Definition iosinit_P_stmt : Prop := OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_ios_iface.ios_init_stmt.
Definition iosexit_P_stmt : Prop := forall (CE : Ceiling), @OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Imp_exit_top.ios_exit_stmt CE.

Definition client_P_stmt : Prop := iosinit_P_stmt /\ iosexit_P_stmt /\ client_fuzz_P_stmt.

Lemma HP : client_P_stmt -> impl_P_stmt.
Proof. intros [HI [HX CP]]. exact (OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P.Impl_closed.impl_P_closed HI HX CP). Qed.

