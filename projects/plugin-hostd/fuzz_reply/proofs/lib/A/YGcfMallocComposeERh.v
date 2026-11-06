(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch; plan row (c)): the PRIMED raw Deallocate contracts of the cf
   layer under the re-hide, beside YGcfMallocComposeE's released ones, for the realloc composition (lane CfR, R-1),
   the free composition (lane RealSegA, row (b)) and the primed free top (YGcfInstFreeTopRh).  rule 24: no function
   proved (kind: contract definitions and their weakening from the released contracts).

   A secondary free re-hides the dead map's shadow, so the released post (plain wle, a frame with no exception)
   cannot hold at a real recycle.  The primed forms change exactly two things:
   - the post is YGcfRehidePost.dealloc_post_raw_rh (wle_in over the call's dead set dead_shadow_new, the frame
     outside it) in place of DeallocG.dealloc_post_raw;
   - the run is YG0dH.amreal' over YGcfRehidePost.RZ_cf (amreal at the relation wle') in place of amreal.
   The errno, memnorm-keep, lpost and apath conjuncts are MemnormT's; the contract takes MemnormT's memory predicate MP
   at Deallocate's entry memory (field round 3 part 3, MemnormT.v:474-489), and the cf form is at YGcfMallocComposeE's
   MP := arodata_ok_cf (part 3c: memnorm is no longer part of MP).

   - [dealloc_leaf_raw_em_rh] / [adealloc_realizes_raw_em_rh] (+ their _of, dealloc_post_raw_rh_E_mono): in
     YGcfMallocComposeERhBase.v (below the cf compose layer, for the frame-generic big arm), re-exported here.
   - [adealloc_realizes_raw_cf_em_m_rh]: the twin of YGcfMallocComposeE.adealloc_realizes_raw_cf_em_m
     (YGcfMallocComposeE.v:214-219), same arguments; [adealloc_realizes_raw_cf_em_m_rh_of]: the released one gives it.
   Generic over CfImg / CfParams; no image constant; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Export YGcfMallocComposeERhBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfMallocCompose.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The compose's primed Deallocate Prop (the twin of YGcfMallocComposeE.adealloc_realizes_raw_cf_em_m).               *)
Section F.
Variable segs : list Segment.
Variable B : asyms.
Variable atpD : Z.

Definition adealloc_realizes_raw_cf_em_m_rh (ARX : ARXh_t segs) : Prop :=
forall Hp,
adealloc_realizes_raw_em_rh segs B (admits (as_universe B)) free_cf (ARX Hp) (aowned B)
  (rpreD_free_cf B) qtight (fpre_hp_cf segs B Hp) cf_pc_deallocate atpD
  (fun m => arodata_ok_cf segs B m).

(* A free that re-hides nothing: the released compose contract gives the primed one, at every ghost set. *)
Lemma adealloc_realizes_raw_cf_em_m_rh_of : forall ARX : ARXh_t segs,
  adealloc_realizes_raw_cf_em_m segs B atpD ARX -> adealloc_realizes_raw_cf_em_m_rh ARX.
Proof. intros ARX H Hp. apply adealloc_realizes_raw_em_rh_of. exact (H Hp). Qed.
End F.
End G.
