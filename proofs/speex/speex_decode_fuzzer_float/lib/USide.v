(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1br X1bo X1bs X1c2 X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw X0qx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel TopE TopSides.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r3 X1r6 X1nu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require PSide.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1h7 X1m9.
Import ListNotations.
Open Scope Z_scope.

Section Harness.

Hypothesis HARNESS : forall RCEIL : RunCeiling, @U.X1h7.harness_stmt RCEIL.

Theorem HU_proof :
impl_root Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs RSTAGE_ubsan.
Proof.
intros en inp Hv Hi.
pose proof (PSide.alloc_ceiling_RP _ _ _ _ _ Hv Hi) as EC.
pose proof (@U.X1m9.ref_impl_from_harness (PSide.RP en) (HARNESS _) en inp Hv Hi
ltac:(rewrite EC; unfold ceil_of, stack_max_size; reflexivity) eq_refl eq_refl) as X.
rewrite EC in X. exact X.
Qed.

End Harness.
