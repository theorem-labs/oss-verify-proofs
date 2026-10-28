(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatIfaceLaws_b BatIfaceInst_b PnSpecsAmc_b.
Import ListNotations.
Open Scope Z_scope.

Lemma art_mcmp_cells : PMAMC.mcmp_cells art_C.
Proof.
  unfold PMAMC.mcmp_cells. cbn [art_C art_statics_cells asc_cells].
  split; [apply in_or_app; left; cbn [art_cells_d4 In]; tauto|].
  split; [apply in_or_app; right; cbn [art_cells_drv In]; tauto|].
  split; apply in_or_app; right; cbn [art_cells_drv In]; tauto.
Qed.
