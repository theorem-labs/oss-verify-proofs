(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the halts half of projects/jsoncons/fuzz_json_cursor/proofs/lib/Theorems.v at c395a1e0dfa (its four halts_allowed_jsoncons_fuzz_json_cursor_halts_* theorems and the HaltsCfgForcedOnly and *Exits modules they use), with fuzz_json_cursor renamed to fuzz_bigint, the four theorems renamed, and each proof term replaced by the matching theorem of Corpus.CorpusHalts{P,U,A,B}; the equivalence theorems of that file are not carried over, since fuzz_bigint already proves its own in lib/Theorems.v. *)
(* Modified by Theorem Labs, 2026-11: taken from ossv175b/bigint at b5b2fc487168, with the asan and both theorems removed together with their Require lines for Corpus.CorpusHaltsA, Corpus.CorpusHaltsB, images.Asan and images.AsanUbsan. Those two images contain self-jump words, so the premise ~ spin_site_present that Corpus/CorpusSpin.v now needs has no proof for them; asan_halts and asan_ubsan_halts stay open (tracked internally). *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.jsoncons.fuzz_bigint.images.Plain.
Require OSSVerify.jsoncons.fuzz_bigint.images.Ubsan.

Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsP.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsU.


Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module JsonconsFuzzBigintHaltsExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBigintHaltsExits.

Theorem halts_allowed_jsoncons_fuzz_bigint_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzBigintHaltsExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.jsoncons.fuzz_bigint.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_bigint.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_bigint.images.Plain.M.phdrs).
Proof.
exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsP.bigint_pm_halts_plain.
Qed.

Theorem halts_allowed_jsoncons_fuzz_bigint_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    JsonconsFuzzBigintHaltsExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.jsoncons.fuzz_bigint.images.Ubsan.M.loaded_segments OSSVerify.jsoncons.fuzz_bigint.images.Ubsan.M.init_pc OSSVerify.jsoncons.fuzz_bigint.images.Ubsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus.CorpusHaltsU.bigint_pm_halts_ubsan.
Qed.
