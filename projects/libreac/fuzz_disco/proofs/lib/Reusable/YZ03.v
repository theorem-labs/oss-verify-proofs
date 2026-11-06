(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v for fuzz_disco: TFIB_T is
   fuzz_disco's asan-ubsan obligation lib/A/DiscoAsanTop.v ASAN_UBSAN_T itself (one obligation, not a second
   statement of it), and the equivalence from it is DiscoAsanTop's asan_ubsan_agrees_of_asan_side, at fuzz_disco's
   statement asan_ubsan_agrees; theorem names cgif_file_fuzzer -> fuzz_disco; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanTop.

Definition TFIB_T : Prop := DiscoAsanTop.ASAN_UBSAN_T.

Section a.
Hypothesis TFIB : TFIB_T.
Theorem fuzz_disco_both_equiv_of_tfib : Statements.asan_ubsan_agrees.
Proof. exact (DiscoAsanTop.asan_ubsan_agrees_of_asan_side TFIB). Qed.
End a.
Theorem strong_universal_error_free_fuzz_disco_both_of_tfib : TFIB_T -> Statements.asan_ubsan_agrees.
Proof. exact fuzz_disco_both_equiv_of_tfib. Qed.
