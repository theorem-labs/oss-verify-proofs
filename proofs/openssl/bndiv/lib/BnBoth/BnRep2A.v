(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_cache_defs RT_freelift.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma mrd_overlayA : forall (m : mem) (x : word), bv_unsigned x + 1 <= 0x10000 \/ 0xbfd000 <= bv_unsigned x -> mrd bsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply fn_seg_rom_off. unfold img_hull_lo, img_hull_hi. exact Hx. Qed.

Lemma lib_state_err_clearedA : forall Σ LB ls m m' OW AD EA SP,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (ea_ES EA <= a < ea_ES EA + 904)) m m' ->
  rw_cells bsegs m' (ea_ES EA) [CB 904 ES_CLEARED] -> lib_state ls m' OW AD EA.
Proof.
  intros Σ LB ls m m' OW AD EA SP HEAP LS AG NEW.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof ERRB as (_ & _ & _ & HinE). pose proof (AH_range _ _ _ _ _ _ _ HEAP HinE) as (EA0 & _ & _ & EAC & EAI).
  pose proof LS as (_ & (_ & (_ & _ & _ & _ & _ & _ & _ & _ & OLD)) & _).
  unfold lib_state. eapply lib_state_hc_agree; [exact LS|]. intros x Hx HO.
  destruct (Z_lt_ge_dec x (ea_ES EA)) as [L|G]; [|destruct (Z_lt_ge_dec x (ea_ES EA + 904)) as [L2|G2]].
  - apply AG; [exact Hx|]. split; [|lia].
    destruct (own_fp_lib _ _ _ _ _ _ _ LS HO) as [HL|(b & Hb & Hr)]; [apply libw_client; exact HL|].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
  - (* [comment removed for export] *)
    destruct OLD as [[_ (_ & _ & BO)] _]. destruct NEW as [[_ (_ & _ & BN)] _]. cbn [cells_bytes cbytes] in BO, BN. rewrite app_nil_r in BO, BN.
    assert (LES : length ES_CLEARED = 904%nat) by reflexivity.
    specialize (BO (Z.to_nat (x - ea_ES EA)) ltac:(lia)). specialize (BN (Z.to_nat (x - ea_ES EA)) ltac:(lia)).
    replace (ea_ES EA + Z.of_nat (Z.to_nat (x - ea_ES EA))) with x in BO, BN by lia.
    rewrite mrd_overlayA in BO, BN by (unfold wa; rewrite unsigned_lit by lia; lia). congruence.
  - apply AG; [exact Hx|]. split; [|lia].
    destruct (own_fp_lib _ _ _ _ _ _ _ LS HO) as [HL|(b & Hb & Hr)]; [apply libw_client; exact HL|].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
Qed.

End WithRT.
