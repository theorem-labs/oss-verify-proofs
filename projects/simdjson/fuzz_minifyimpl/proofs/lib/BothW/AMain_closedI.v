(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import BothMainU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Stdio AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AMalloc_iface AU_iface AIos_iface AExitU_kit ADriver_iface AD_handoff AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  Hypothesis CLIENT : asan_client_at (AI_of FREE).      (* [comment removed for export] *)

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
    exact (adrv (AI_of FREE) (AI_of_E FREE) (AI_of_CI_OK FREE) (AI_of_DRV_CI FREE) (AI_of_URI_CI FREE) exit_ci_I CLIENT
             XPf XCH XP_INIT).      (* [comment removed for export] *)
  Qed.
End WithFree.
End CANSEC1.

(* [comment removed for export] *)
Theorem both_impl_of_free :
  forall FREE : (forall rc : runConstT, afree_stmt aci_I AHEAP_I),
  forall XPf : (forall rc : runConstT, Z -> ExitParams), (forall rc : runConstT, @xp_closed_stmt rc (XPf rc)) ->
  (forall rc : runConstT, @asan_client_at rc (AI_of (FREE rc))) ->      (* [comment removed for export] *)
  impl_stmt ASTAGE.
Proof.
  intros FREE XPf XPC CLIENT.
  exact (both_impl ATsafeMain.NMAX ATsafeMain.A0
           (fun rc : runConstT => @adrv_of_free rc (FREE rc) (XPf rc) (XPC rc) (CLIENT rc))
           (fun rc : runConstT => @model_ok rc)
           ATsafeMain.A0_init).
Qed.
