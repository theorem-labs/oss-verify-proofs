(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Ref Require Import RMallocRep_u RMallocTree_u RMalloc_iface_u RF_aligned_u RF_aligned_spec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require Import HeapInst0_u HeapClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma pm_layout_L0 : forall sptop : Z, 0x100000 <= sptop -> PMS.layout (L0 sptop).
Proof.
  intros sptop Hsp. constructor; try reflexivity.
  - intros a Ha. cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_sptop L0] in *. unfold IMG_LO, IMG_HI, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in *. lia.
  - intros a Ha. cbn [hl_alloc_static L0] in Ha. unfold RMLOCK, RCTX in Ha. lia.
  - cbn [hl_k_per_malloc L0]. split; [vm_compute; discriminate | vm_compute; discriminate].
  - cbn [hl_b_overhead L0]. split; [vm_compute; discriminate | vm_compute; discriminate].
  - intros a Ha. cbn [hl_alloc_ro L0] in Ha. unfold IMG_LO, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in Ha.
    intros X. lia.
Qed.
