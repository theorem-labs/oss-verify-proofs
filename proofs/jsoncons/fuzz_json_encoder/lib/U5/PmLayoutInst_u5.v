(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import RMallocRep_u5 RMallocTree_u5 RF_aligned_u5 RF_aligned_spec_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pm0_layout_L0 : forall sptop : Z, 0xfe000 <= sptop -> PmLayout.pm0_layout (L0 sptop).   (* [comment removed for export] *)
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
