(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma lib_state_err_cleared : forall s LB ls m m' OW AD EA W,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA ->
  munch ((ea_ES EA, ea_ES EA + 904) :: W) m m' -> wmono psegs m m' -> Forall (w_ok OW LB ls AD EA []) W ->
  rw_cells psegs m' (ea_ES EA) [CB 904 ES_CLEARED] -> lib_state ls m' OW AD EA.
Proof.
  intros s LB ls m m' OW AD EA W HEAP LS MU WM HW NEW.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof ERRB as (_ & _ & _ & HinE). pose proof (RH_range _ _ _ _ _ _ _ HEAP HinE) as (EA0 & _ & _ & EAC & EAI).
  pose proof LS as (_ & (_ & (_ & _ & _ & _ & _ & _ & _ & _ & OLD)) & _).
  unfold lib_state. eapply lib_state_hc_agree; [exact LS|]. intros x Hx HO. split; [|apply WM].
  destruct (Z_lt_ge_dec x (ea_ES EA)) as [L|G]; [|destruct (Z_lt_ge_dec x (ea_ES EA + 904)) as [L2|G2]].
  - apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [lia|].
    eapply own_fp_outside; eauto.
  - (* [comment removed for export] *)
    destruct OLD as [[_ (_ & _ & BO)] _]. destruct NEW as [[_ (_ & _ & BN)] _]. cbn [cells_bytes cbytes] in BO, BN. rewrite app_nil_r in BO, BN.
    assert (LES : length ES_CLEARED = 904%nat) by reflexivity.
    specialize (BO (Z.to_nat (x - ea_ES EA)) ltac:(lia)). specialize (BN (Z.to_nat (x - ea_ES EA)) ltac:(lia)).
    replace (ea_ES EA + Z.of_nat (Z.to_nat (x - ea_ES EA))) with x in BO, BN by lia.
    rewrite ref_mrd_overlay in BO, BN by (unfold wa; rewrite unsigned_lit by lia; lia). congruence.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [lia|].
    eapply own_fp_outside; eauto.
Qed.

End WithCeiling0.
