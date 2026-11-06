(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BsonPmFinal
     HeapIface HeapIfaceA IcptIfaceA BatIfaceInst BatIfaceLayoutPM PnALayFacts PnAClosePkg PnAClose PnADec128Close BsonPmAsanTop BsonPmAsanRows.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma parse_closed : parse_stmt.
Proof.
  exact (@PNACL.parse_closed ScfgP_cfg0 art_L art_C art_IL art_pma_layout art_IL_ok
           (@PNADCL.dec128_closed ScfgP_cfg0 art_L art_C art_IL art_pma_layout art_IL_ok)).
Qed.
Lemma pkg_closed : pkg_stmt.
Proof. exact (pkg_of_parse parse_closed). Qed.

(* [comment removed for export] *)
Definition bson_pm_asan_base := BsonPmAsanRows.bson_pm_asan_base pkg_closed.
(* [comment removed for export] *)
Definition bson_pm_asan_base_abort := BsonPmAsanRows.bson_pm_asan_base_abort pkg_closed.
