(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIfaceA HeapIfaceAEx EarIfaceLaws EarIfaceInst PeSpecsAmc.
Import ListNotations.
Open Scope Z_scope.

Lemma art_mcmp_cells : PMAMC.mcmp_cells art_C.
Proof.
  unfold PMAMC.mcmp_cells. cbn [art_C art_statics_cells asc_cells].
  split; [apply in_or_app; left; cbn [art_cells_d4 In]; tauto|].
  split; [apply in_or_app; right; cbn [art_cells_drv In]; tauto|].
  split; apply in_or_app; right; cbn [art_cells_drv In]; tauto.
Qed.
