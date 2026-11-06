(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceA JatIfaceLaws JatIfaceInst PmSpecsAmc.
Import ListNotations.
Open Scope Z_scope.
Lemma art_mcmp_cells : PMAMC.mcmp_cells art_C.
Proof.
unfold PMAMC.mcmp_cells. cbn [art_C art_statics_cells asc_cells].
split; [apply in_or_app; left; cbn [art_cells_d4 In]; tauto|].
split; [apply in_or_app; right; cbn [art_cells_drv In]; tauto|].
split; apply in_or_app; right; cbn [art_cells_drv In]; tauto.
Qed.
