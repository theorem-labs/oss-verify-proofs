(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_libiface.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LIBA_BAL : Z := 1600.

Definition LIBA (RT : rt_sig) (Σ : rts RT) (LW : list (Z * Z)) (m : mem) : Prop :=
  exists (OW : list block) (EA : BnRepDefs.err_addrs),
    LW = map blk_an OW /\ List.NoDup (map blk_id OW) /\ Forall blk_okA OW
    /\ lib_state st_init m OW pl_empty EA /\ List.NoDup (BnRepDefs.ea_ids EA).

Lemma ref_at_init : forall OW r a, ref_at (st_init : ST) OW pl_empty r a -> r = ROne.
Proof.
  intros OW r a H. unfold ref_at in H. destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - destruct H as (p & E & _). destruct (Nat.eq_dec r ROne) as [->|NE]; [reflexivity|]. exfalso.
    destruct (pl_of_cases pl_empty r p E) as [[-> _]|[(am & qm & _ & Em & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate Em| discriminate Eb].
  - exfalso. destruct H as (q & H0 & Eq & _). unfold st_init in Eq. cbn [st_ctx gx_items gx_nil] in Eq. destruct ((r - NFIX) / BN_CTX_POOL_SIZE)%nat; cbn [nth_error] in Eq; discriminate Eq.
Qed.

Lemma own_fpA_init : forall cxo hs OW EA x, own_fpA cxo hs (st_init : ST) OW pl_empty EA x -> BnRepA.libw x \/ BnRepA.err_fp OW EA x.
Proof.
  intros cxo hs OW EA x [HL|[(r & a & HA & _ & _ & NRO & _)|[[_ HC]|[HM|HE]]]].
  - left. exact HL.
  - exfalso. exact (NRO (ref_at_init _ _ _ HA)).
  - exfalso. destruct HC as [(ac & qc & Ec & _)|[(q & H & Hq & _)|(q & Ix & Eq & _)]]; [discriminate Ec| exact Hq| discriminate Eq].
  - exfalso. destruct HM as [(am & qm & Em & _)|(c & Ec & _)]; [discriminate Em| discriminate Ec].
  - right. exact HE.
Qed.

Section Facts.
Variable RT : rt_sig.

Lemma in_block_live : forall (OW : list block) x, in_block OW x -> in_live (map blk_an OW) x.
Proof. intros OW x H. apply in_live_blocks. exact H. Qed.

Lemma libw_in_LIB_FP : forall x, rin_ivs LIBW_A x -> in_ranges LIB_FP x.
Proof.
  intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold in_ranges, LIB_FP.
  destruct H as [H|[H|[H|[]]]].
  - exists 0x5aa520, 0x5aad40. split; [cbn; tauto | exact H].
  - exists 0xb9f7c0, 0xba3be0. split; [cbn; tauto | exact H].
  - exists 0xbc58a0, 0xbc5c98. split; [cbn; tauto | exact H].
Qed.

Theorem liba_frameA : liba_frame RT (LIBA RT).
Proof.
  intros Σ Σ' LW m m' (OW & EA & -> & ND & OK & LS & NDE) HAG.
  exists OW, EA. split; [reflexivity|]. split; [exact ND|]. split; [exact OK|]. split; [|exact NDE].
  eapply lib_state_hc_agreeA; [exact LS|]. intros a Ha Hown. apply HAG. unfold wa. rewrite unsigned_lit by lia.
  destruct (own_fpA_init _ _ _ _ _ Hown) as [HL|HE]; [left; apply libw_in_LIB_FP; exact HL | right; apply in_block_live].
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & _ & (E1 & E2 & E3 & E4)).
  unfold BnRepA.err_fp in HE.
  destruct HE as [HE|[HE|[HE|HE]]]; [eapply (BnRepA.in_block_intro _ _ _ _ _ E1 HE)| eapply (BnRepA.in_block_intro _ _ _ _ _ E2 HE)
                                  | eapply (BnRepA.in_block_intro _ _ _ _ _ E3 HE)| eapply (BnRepA.in_block_intro _ _ _ _ _ E4 HE)].
Qed.

Theorem liba_exitA : liba_exit RT (LIBA RT).
Proof.
  intros Σ LW m (OW & EA & _ & _ & _ & LS & _). destruct LS as (_ & _ & (HO & _) & _). exact HO.
Qed.

Theorem LIBA_init : forall (Σ : rts RT) (m : mem) (OW : list block),
  lib_inv_bgr m OW -> List.NoDup (map blk_id OW) -> Forall blk_okA OW -> Z.of_nat (length OW) <= LIBA_BAL ->
  LIBA RT Σ (map blk_an OW) m.
Proof.
  intros Σ m OW HI ND OK LEN. destruct (lib_state_init m OW HI) as (EA & LS & NDE).
  exists OW, EA. split; [reflexivity|]. split; [exact ND|]. split; [exact OK|]. split; [exact LS|]. exact NDE.
Qed.

End Facts.
