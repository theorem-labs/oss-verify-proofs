(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import RMallocRep_u RMallocTree_u RF_aligned_u RF_aligned_spec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require Import PmHeapInst10_u.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pm0_layout_L0 : forall sptop : Z, 0xf8000 <= sptop -> PmLayout.pm0_layout (L0 sptop).
Proof.
  intros sptop Hsp. constructor.
  1-8: reflexivity.
  - cbn [hl_stack L0]. vm_compute. reflexivity.
  - intros a Ha. cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_sptop L0] in *. unfold IMG_LO, IMG_HI, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in *. lia.
  - intros a Ha. cbn [hl_alloc_static L0] in Ha. unfold RMLOCK, RCTX in Ha. lia.
  - cbn [hl_k_per_malloc L0]. unfold KPM. lia.
  - cbn [hl_b_overhead L0]. vm_compute. discriminate.
  - intros a Ha Hi. cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_sptop L0] in *. unfold IMG_LO, IMG_HI, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in *. lia.
Qed.
