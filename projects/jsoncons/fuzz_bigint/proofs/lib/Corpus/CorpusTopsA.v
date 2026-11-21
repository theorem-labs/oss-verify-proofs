(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the asan and both halts theorems of projects/jsoncons/fuzz_json_cursor/proofs/lib/Theorems.v at theorem-labs/oss-verify-proofs@c5665593c2d8 (two of its four halts_allowed_jsoncons_fuzz_json_cursor_halts_* theorems), with fuzz_json_cursor renamed to fuzz_bigint, the two theorems renamed, and each proof term replaced by the matching theorem of Corpus.CorpusHalts{A,B}; the HaltsCfgForcedOnly and JsonconsFuzzBigintHaltsExits modules they use are read from Corpus/CorpusTops.v (Required), so that the plain and UBSan theorems there require nothing of the two ASan builds. *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.jsoncons.fuzz_bigint.images.Asan.
Require OSSVerify.jsoncons.fuzz_bigint.images.AsanUbsan.

Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsA.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsB.

Theorem halts_allowed_jsoncons_fuzz_bigint_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.JsonconsFuzzBigintHaltsExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.jsoncons.fuzz_bigint.images.Asan.M.loaded_segments OSSVerify.jsoncons.fuzz_bigint.images.Asan.M.init_pc OSSVerify.jsoncons.fuzz_bigint.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsA.bigint_pm_halts_asan.
Qed.

Theorem halts_allowed_jsoncons_fuzz_bigint_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusTops.JsonconsFuzzBigintHaltsExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.jsoncons.fuzz_bigint.images.AsanUbsan.M.loaded_segments OSSVerify.jsoncons.fuzz_bigint.images.AsanUbsan.M.init_pc OSSVerify.jsoncons.fuzz_bigint.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsB.bigint_pm_halts_both.
Qed.
