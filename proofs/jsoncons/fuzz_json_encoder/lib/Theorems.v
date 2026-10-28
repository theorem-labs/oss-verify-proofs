(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.
Require OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Asan.
Require OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.
Require OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.AsanUbsan.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmXasan.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmXboth.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmXubsan.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module JsonconsFuzzBigintHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBigintHaltsPlainExits.

Module JsonconsFuzzBigintHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBigintHaltsAsanExits.

Module JsonconsFuzzBigintHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBigintHaltsUbsanExits.

Module JsonconsFuzzBigintHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBigintHaltsBothExits.

Module JsonconsFuzzBsonHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonHaltsPlainExits.

Module JsonconsFuzzBsonHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonHaltsAsanExits.

Module JsonconsFuzzBsonHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonHaltsUbsanExits.

Module JsonconsFuzzBsonHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonHaltsBothExits.

Module JsonconsFuzzBsonEncoderHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonEncoderHaltsPlainExits.

Module JsonconsFuzzBsonEncoderHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonEncoderHaltsAsanExits.

Module JsonconsFuzzBsonEncoderHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonEncoderHaltsUbsanExits.

Module JsonconsFuzzBsonEncoderHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonEncoderHaltsBothExits.

Module JsonconsFuzzBsonParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonParserMaxHaltsPlainExits.

Module JsonconsFuzzBsonParserMaxHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonParserMaxHaltsAsanExits.

Module JsonconsFuzzBsonParserMaxHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonParserMaxHaltsUbsanExits.

Module JsonconsFuzzBsonParserMaxHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzBsonParserMaxHaltsBothExits.

Module JsonconsFuzzCborHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborHaltsPlainExits.

Module JsonconsFuzzCborHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborHaltsAsanExits.

Module JsonconsFuzzCborHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborHaltsUbsanExits.

Module JsonconsFuzzCborHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborHaltsBothExits.

Module JsonconsFuzzCborEncoderHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborEncoderHaltsPlainExits.

Module JsonconsFuzzCborEncoderHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborEncoderHaltsAsanExits.

Module JsonconsFuzzCborEncoderHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborEncoderHaltsUbsanExits.

Module JsonconsFuzzCborEncoderHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborEncoderHaltsBothExits.

Module JsonconsFuzzCborParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborParserMaxHaltsPlainExits.

Module JsonconsFuzzCborParserMaxHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborParserMaxHaltsAsanExits.

Module JsonconsFuzzCborParserMaxHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborParserMaxHaltsUbsanExits.

Module JsonconsFuzzCborParserMaxHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCborParserMaxHaltsBothExits.

Module JsonconsFuzzCsvHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCsvHaltsPlainExits.

Module JsonconsFuzzCsvHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCsvHaltsAsanExits.

Module JsonconsFuzzCsvHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCsvHaltsUbsanExits.

Module JsonconsFuzzCsvHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzCsvHaltsBothExits.

Module JsonconsFuzzJsonCursorHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsPlainExits.

Module JsonconsFuzzJsonCursorHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsAsanExits.

Module JsonconsFuzzJsonCursorHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsUbsanExits.

Module JsonconsFuzzJsonCursorHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonCursorHaltsBothExits.

Module JsonconsFuzzJsonEncoderHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonEncoderHaltsPlainExits.

Module JsonconsFuzzJsonEncoderHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonEncoderHaltsAsanExits.

Module JsonconsFuzzJsonEncoderHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonEncoderHaltsUbsanExits.

Module JsonconsFuzzJsonEncoderHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonEncoderHaltsBothExits.

Module JsonconsFuzzJsonParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonParserMaxHaltsPlainExits.

Module JsonconsFuzzJsonParserMaxHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonParserMaxHaltsAsanExits.

Module JsonconsFuzzJsonParserMaxHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonParserMaxHaltsUbsanExits.

Module JsonconsFuzzJsonParserMaxHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzJsonParserMaxHaltsBothExits.

Module JsonconsFuzzMsgpackHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackHaltsPlainExits.

Module JsonconsFuzzMsgpackHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackHaltsAsanExits.

Module JsonconsFuzzMsgpackHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackHaltsUbsanExits.

Module JsonconsFuzzMsgpackHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackHaltsBothExits.

Module JsonconsFuzzMsgpackEncoderHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackEncoderHaltsPlainExits.

Module JsonconsFuzzMsgpackEncoderHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackEncoderHaltsAsanExits.

Module JsonconsFuzzMsgpackEncoderHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackEncoderHaltsUbsanExits.

Module JsonconsFuzzMsgpackEncoderHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackEncoderHaltsBothExits.

Module JsonconsFuzzMsgpackParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackParserMaxHaltsPlainExits.

Module JsonconsFuzzMsgpackParserMaxHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackParserMaxHaltsAsanExits.

Module JsonconsFuzzMsgpackParserMaxHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackParserMaxHaltsUbsanExits.

Module JsonconsFuzzMsgpackParserMaxHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzMsgpackParserMaxHaltsBothExits.

Module JsonconsFuzzParseHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzParseHaltsPlainExits.

Module JsonconsFuzzParseHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzParseHaltsAsanExits.

Module JsonconsFuzzParseHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzParseHaltsUbsanExits.

Module JsonconsFuzzParseHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzParseHaltsBothExits.

Module JsonconsFuzzUbjsonHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonHaltsPlainExits.

Module JsonconsFuzzUbjsonHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonHaltsAsanExits.

Module JsonconsFuzzUbjsonHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonHaltsUbsanExits.

Module JsonconsFuzzUbjsonHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonHaltsBothExits.

Module JsonconsFuzzUbjsonEncoderHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonEncoderHaltsPlainExits.

Module JsonconsFuzzUbjsonEncoderHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonEncoderHaltsAsanExits.

Module JsonconsFuzzUbjsonEncoderHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonEncoderHaltsUbsanExits.

Module JsonconsFuzzUbjsonEncoderHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonEncoderHaltsBothExits.

Module JsonconsFuzzUbjsonParserMaxHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonParserMaxHaltsPlainExits.

Module JsonconsFuzzUbjsonParserMaxHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonParserMaxHaltsAsanExits.

Module JsonconsFuzzUbjsonParserMaxHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonParserMaxHaltsUbsanExits.

Module JsonconsFuzzUbjsonParserMaxHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End JsonconsFuzzUbjsonParserMaxHaltsBothExits.

Theorem strong_universal_error_free_fuzz_json_encoder_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Asan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Asan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Asan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmXasan.PmXasan.xasan_base).
Qed.

Theorem strong_universal_error_free_fuzz_json_encoder_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmXubsan.PmXubsan.xubsan_top).
Qed.

Theorem strong_universal_error_free_fuzz_json_encoder_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.AsanUbsan.M.phdrs).
Proof.
exact (OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmXboth.PmXboth.xboth_base).
Qed.
