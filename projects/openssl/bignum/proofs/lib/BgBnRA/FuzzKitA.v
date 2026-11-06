(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA BnRep2A.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitA BnCallA W_expandA PlaceKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition hpl_only (PL : placement) : Prop := pl_frames PL = [].

Lemma nil_of_no_In : forall {T} (l : list T), (forall x, ~ In x l) -> l = [].
Proof. intros T l H. destruct l as [|x l]; [reflexivity|]. exfalso. apply (H x). left. reflexivity. Qed.

Lemma hpl_only_empty : hpl_only pl_empty.
Proof. unfold hpl_only. apply pl_frames_empty. Qed.

Lemma hpl_only_set_heap : forall PL r a q off, hpl_only PL -> hpl_only (pl_set PL r (Some (PHeap a q off))).
Proof.
  intros PL r a q off H. unfold hpl_only in *. apply nil_of_no_In. intros iv Hiv. apply pl_frames_set_In in Hiv.
  destruct Hiv as [[]|Hiv]. rewrite H in Hiv. destruct Hiv.
Qed.

Lemma hpl_only_set_none : forall PL r, hpl_only PL -> hpl_only (pl_set PL r None).
Proof.
  intros PL r H. unfold hpl_only in *. apply nil_of_no_In. intros iv Hiv. apply pl_frames_set_In in Hiv.
  destruct Hiv as [[]|Hiv]. rewrite H in Hiv. destruct Hiv.
Qed.

Lemma hpl_only_set_ctx : forall PL c, hpl_only PL -> hpl_only (pl_set_ctx PL c).
Proof. intros PL c H. exact H. Qed.

Lemma xw_hpl_only : forall PL PL', hpl_only PL -> hpl_only PL' -> XW PL' = XW PL.
Proof. intros PL PL' H H'. unfold XW. rewrite H, H'. reflexivity. Qed.

Lemma frames_ok_hpl : forall PL PL' SPX BX, hpl_only PL' -> frames_ok PL SPX BX -> frames_ok PL' SPX BX.
Proof. intros PL PL' SPX BX H [_ LE]. split; [|exact LE]. intros iv Hiv. unfold hpl_only in H. rewrite H in Hiv. destruct Hiv. Qed.

Lemma frames_al_hpl : forall PL, hpl_only PL -> frames_al PL.
Proof. intros PL H iv Hiv. unfold hpl_only in H. rewrite H in Hiv. destruct Hiv. Qed.

Lemma refs_stable_noitems : forall (st : bstate bptr) OW st' OW', gx_items (st_ctx st) = [] -> refs_stable st OW st' OW'.
Proof.
  intros st OW st' OW' E PL i a H. apply ref_at_pool in H. destruct H as (q & H0 & Eq & _). rewrite E in Eq.
  destruct ((i / BN_CTX_POOL_SIZE)%nat); discriminate Eq.
Qed.

Lemma lib_state_err_clearedA : forall Σ LB ls m m' OW PL EA SP SPX BX,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok PL SPX BX -> SP <= SPX -> BX <= USTACK_TOP ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (BnRepDefs.ea_ES EA <= a < BnRepDefs.ea_ES EA + 904)) m m' ->
  rw_cells bgasegs m' (BnRepDefs.ea_ES EA) [CB 904 BnRepDefs.ES_CLEARED] -> lib_state ls m' OW PL EA.
Proof.
  intros Σ LB ls m m' OW PL EA SP SPX BX HEAP LS FROK LE BXT AG NEW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (_ & _ & _ & _ & ERRB).
  pose proof ERRB as (_ & _ & _ & HinE). pose proof (AH_range _ _ _ _ _ _ _ HEAP HinE) as (EA0 & _ & _ & EAC & EAI).
  pose proof LS as (_ & (_ & (_ & _ & _ & _ & _ & _ & _ & _ & OLD)) & _).
  unfold lib_state. eapply lib_state_hc_agreeA; [exact LS|]. intros x Hx HO.
  destruct (Z_lt_ge_dec x (BnRepDefs.ea_ES EA)) as [L|G]; [|destruct (Z_lt_ge_dec x (BnRepDefs.ea_ES EA + 904)) as [L2|G2]].
  - apply AG; [exact Hx|]. split; [|clear - L; lia].
    destruct (own_fp_libA _ _ _ _ _ _ _ _ _ LS FROK HO) as [HL|[(b & Hb & Hr)|Hs]]; [apply libw_clientA; exact HL| | left; clear - Hs LE BXT; lia].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
  -
    destruct OLD as [[_ (_ & _ & BO)] _]. destruct NEW as [[_ (_ & _ & BN)] _]. cbn [cells_bytes cbytes] in BO, BN. rewrite app_nil_r in BO, BN.
    assert (LES : length BnRepDefs.ES_CLEARED = 904%nat) by reflexivity.
    specialize (BO (Z.to_nat (x - BnRepDefs.ea_ES EA)) ltac:(lia)). specialize (BN (Z.to_nat (x - BnRepDefs.ea_ES EA)) ltac:(lia)).
    replace (BnRepDefs.ea_ES EA + Z.of_nat (Z.to_nat (x - BnRepDefs.ea_ES EA))) with x in BO, BN by lia.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
    rewrite BnRep2A.mrd_overlayA in BO, BN by (unfold wa; rewrite unsigned_lit by lia; clear - EAI G L2; lia). congruence.
  - apply AG; [exact Hx|]. split; [|clear - G2; lia].
    destruct (own_fp_libA _ _ _ _ _ _ _ _ _ LS FROK HO) as [HL|[(b & Hb & Hr)|Hs]]; [apply libw_clientA; exact HL| | left; clear - Hs LE BXT; lia].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
Qed.

Lemma cenv_rebaseA : forall LB PL PL' lo SPv FB s0w raw TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW cost Σ' (ls' : bstate bptr) m' OW',
  cenvA LB PL lo SPv FB s0w raw None TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  AHEAP Σ' OW' LB m' -> stk bgasegs m' lo FB -> mem_inv bgasegs m' -> ax_pres LB FB (XW PL) m m' -> rt_credit RT Σ - cost <= rt_credit RT Σ' ->
  hpl_only PL' -> cnt_ok ls' OW' LB ->
  cenvA LB PL' lo SPv FB s0w raw None TOTAL Σ0 ls' OW' m0 pre (used + cost) Σ' ls' m' OW'.
Proof.
  intros LB PL PL' lo SPv FB s0w raw TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW cost Σ' ls' m' OW'
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) HEAP' ST' MI' AXP' CR' HPL' CNT'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  assert (EXW : XW PL' = XW PL) by (apply xw_hpl_only; [exact NOFR| exact HPL']).
  assert (AG : agree_on (fun a => FB <= a < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AXP'|]. intros a Ha. cbv beta in Ha. split; [|left; lia]. unfold XW. rewrite NOFR, app_nil_r.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
    unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  unfold cenvA, cenv_ok. rewrite EXW.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|]. split; [exact CNT'|].
           split; [exact CRED0|]. split; [exact (frames_ok_hpl PL PL' _ _ HPL' FROK)|]. split; [apply frames_al_hpl; exact HPL'| exact HPL']. }
  split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
  split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [exact AXP'| lia]. }
  split; [lia|].
  split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
  split. { eapply rw_cells_agree; [exact AG | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
           unfold USTACK_TOP in *. lia. }
  split; [exact FSZ| exact I].
Qed.

End WithRT.
