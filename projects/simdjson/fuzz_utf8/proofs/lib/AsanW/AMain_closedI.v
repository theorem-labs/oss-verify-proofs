(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Stdio AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg AMalloc_iface AU_iface AIos_iface AExitU_kit ADriver_iface AD_handoff AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.

Set Keyed Unification.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition xp_closed_stmt (XPf : Z -> ExitParams) : Prop :=
  (forall T : Z, @xp_chains_stmt rc (XPf T)) /\ xp_init_fam_stmt XPf ATsafeMain.A0.

Section WithFree.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  Variable XPf : Z -> ExitParams.
  Hypothesis XPC : xp_closed_stmt XPf.

  (* [comment removed for export] *)
  Lemma exit_ci_I : forall iv, In iv exit_ci_need -> In iv (aci (AI_of FREE)).
  Proof.
    intros iv H. unfold exit_ci_need, exit_img_ranges in H. cbn [app In] in H.
    repeat (destruct H as [<-|H];
            [ first [ apply (AI_of_DRV_CI FREE); unfold drv_img_ranges; cbn [In]; tauto
                    | apply (AI_of_URI_CI FREE); unfold client_ranges; cbn [In]; tauto ] |]).
    destruct H.
  Qed.

  Theorem adrv_of_free : adrv_stmt ATsafeMain.A0.
  Proof.
    destruct XPC as (XCH & XP_INIT).
    exact (adrv (AI_of FREE) (AI_of_E FREE) (AI_of_CI_OK FREE) (AI_of_DRV_CI FREE) (AI_of_URI_CI FREE)
             (AI_of_chunk FREE) (AI_of_premap FREE) (AI_of_lsan FREE) (AI_of_frame_lsan' FREE) exit_ci_I
             XPf XCH XP_INIT).
  Qed.
End WithFree.
End CANSEC1.

(* [comment removed for export] *)
Theorem asan_impl_of_free :
  (forall rc : runConstT, afree_stmt aci_I AHEAP_I) ->
  forall XPf : (forall rc : runConstT, Z -> ExitParams), (forall rc : runConstT, @xp_closed_stmt rc (XPf rc)) ->
  impl_stmt ASTAGE.
Proof.
  intros FREE XPf XPC.
  exact (asan_impl ATsafeMain.NMAX ATsafeMain.A0
           (fun rc : runConstT => @adrv_of_free rc (FREE rc) (XPf rc) (XPC rc))
           (fun rc : runConstT => @model_ok rc)
           ATsafeMain.A0_init).
Qed.
