(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMalloc_iface RF_aligned RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PnLayoutS PmModel PmStatics PmSpecs PnSpecsS.
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
