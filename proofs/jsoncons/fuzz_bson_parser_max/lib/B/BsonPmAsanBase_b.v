(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BsonPmFinal
     HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b BatIfaceInst_b BatIfaceLayoutPM_b PnALayFacts_b PnAClosePkg_b PnAClose_b PnADec128Close_b BsonPmAsanTop_b BsonPmAsanRows_b.
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
Definition bson_pm_asan_base := BsonPmAsanRows_b.bson_pm_asan_base pkg_closed.
(* [comment removed for export] *)
Definition bson_pm_asan_base_abort := BsonPmAsanRows_b.bson_pm_asan_base_abort pkg_closed.
