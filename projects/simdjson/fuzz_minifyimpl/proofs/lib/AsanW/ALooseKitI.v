(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame InitMem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface APoisonR_iface AFake_iface AFake_arep
     AInstance AInstanceM AInstanceF AU_kit AU_iface AHarnessU_iface AU_parts_iface ALoose ALooseInst ALooseSet ALooseLaws ALoose_iface ALooseOps AM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma AHL_cell_some : forall L RNG st LB m p A n (bs : list byte),
  AHEAP_L (set_blk L p A n (Some bs)) RNG st LB m -> In (HB p A n) LB -> length bs = Z.to_nat (granules n) ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) bs].
Proof. intros L RNG st LB m p A n bs AH HIN LEN. eapply AHL_block_cell_some; [exact AH| exact HIN| apply blk_entry_set_blk| exact LEN]. Qed.

Definition ALooseKitI (FREE : afree_stmt aci_I AHEAP_I) : ALooseKit (AI_of FREE) fflag afake_rng :=
  mkALooseKit (AI_of FREE) fflag afake_rng
    AHEAP_L set_blk al_tight
    (AHL_of_AI FREE) (AHL_to_AI FREE)
    AHL_set_annot AHL_set_annot_tight
    AHL_cell_some
    set_blk_set_blk set_blk_tight
    set_blk_top set_blk_bot set_blk_U set_blk_sp0 set_blk_V_at
    set_blk_fflag set_blk_afake_rng_iff set_blk_aps_ok
    AHL_frame AHL_rng_mono AHL_perm
    AHL_fake_flag AHL_fake_release
    AHL_lblock AHL_block_bounds AHL_blocks_disjoint AHL_hb_ids AHL_layout AHL_rtcells AHL_relro AHL_premap
    AHL_opdelete_sz.
End CANSEC1.
