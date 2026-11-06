(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ModelInvBg.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgLib BgExp BgTree BgBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXP Require Import HxpInstBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgRep Require LibInstBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_mod_exp W_exp_simple ExpClosed.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocP Require RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_fuzz FuzzTop.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Rnd.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Lib_iface Driver_iface Impl_closed.
Require OSSVerify.openssl.bignum.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgPbg := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation RunRnd := OSSVerify.Proofs.openssl.bignum.lib.P.Rnd.RunRnd.

Definition LM_bignum : LibModel := LM_bg unit tt bg_lib_one.

Definition PcapBg (c : Z) : Z := if (0 <=? c) && (c <? 48) then (if c <=? 2 then 1700 else 96) else if c =? 63 then 96 else 0.

Lemma PcapBg_nonneg : forall c, 0 <= PcapBg c.
Proof. intros c. unfold PcapBg. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma caps_bg : caps_ok PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ.
Proof. apply caps_ok_b_ok. vm_compute. reflexivity. Qed.

Lemma ops_checked_bg : ops_wf bignum_ops [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma H_init_bg : lwf (okT (sizes_of bignum_ops)) (lib_init (LibModel := LM_bignum)) [] (fun ls Li => bg_linv ls [] /\ subms (map snd Li) (sizes_of bignum_ops)).
Proof.
  eapply lwf_mono; [apply (init_of_ops_lwf bignum_ops (tt : @LS LM_bignum) ops_checked_bg)|]. intros ls Li [E HS]. split; [|exact HS].
  reflexivity.
Qed.

Lemma H_one_bg : forall (ls : @LS LM_bignum) d X, bg_linv ls X -> zlength d <= MAX_INPUT ->
  lwf (okB BG_NBLKZ BG_BSZZ) (lib_one ls d) X (fun r X' => bg_linv (fst r) X').
Proof. intros ls d X H _. exact (bg_H_one ls d X H). Qed.

Lemma STK2 : ExpClosed.SIMPLE_STACK <= W_fuzz.FUZZ_CALLEE_MAX.
Proof. vm_compute. intros X; discriminate X. Qed.

Lemma STK1 : ExpClosed.MEXP_STACK <= W_fuzz.FUZZ_CALLEE_MAX.
Proof. vm_compute. intros X; discriminate X. Qed.

Lemma EXP : forall (CE__ : Ceiling) (RN__ : RunRnd),
  @W_mod_exp.exp_stmt_f CE__ RN__ W_fuzz.BN_MOD_EXP ExpClosed.MEXP_STACK (BN_mod_exp (tree_ops bptr)) None.
Proof. intros CE RN. exact (@ExpClosed.BN_mod_exp_closed CE RN RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof). Qed.

Lemma implG_plain_bg : implG_stmt (LM := LM_bignum) bgpsegs Plain.M.init_pc Plain.M.phdrs bgpstage.
Proof.
  exact (BgP.Impl_closed.implG_P_stmt_closed LM_bignum
           (fun CE RN => LibInstBg.LSP_bgr unit tt bg_lib_one)
           (fun CE RN => LibInstBg.LL_bgr unit tt bg_lib_one)
           (fun CE RN => @LibInstBg.rinit_bgr CE RN unit tt bg_lib_one)
           (fun CE RN => @FuzzTop.rfuzz_one_bgr_of_exp CE RN ExpClosed.MEXP_STACK ExpClosed.SIMPLE_STACK STK1 STK2 (EXP CE RN)
                           (@ExpClosed.BN_mod_exp_simple_closed CE RN RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof))).
Qed.

Lemma side_plain_bg_lim : forall lim, KLIM + SMALLREQ <= lim -> side_canon_off ncfg Tc imgPbg lim.
Proof.
  intros lim Hlim.
  exact (G_side_off (LM := LM_bignum) PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ bg_linv PcapBg_nonneg caps_bg H_init_bg H_one_bg bg_H_rc
           bgpsegs _ _ bgpstage lim image_low_bgpsegs Hlim implG_plain_bg).
Qed.

Lemma side_plain_bg_san : side_canon_off ncfg Tc imgPbg SanitizerBudgets.lim_source.
Proof. apply side_plain_bg_lim. unfold KLIM, SMALLREQ, SanitizerBudgets.lim_source, sanitizer_source_limit. lia. Qed.

Lemma side_plain_bg : side_canon_off ncfg Tc imgPbg source_alloc_limit.
Proof.
  exact (G_side_off (LM := LM_bignum) PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ bg_linv PcapBg_nonneg caps_bg H_init_bg H_one_bg bg_H_rc
           bgpsegs _ _ bgpstage source_alloc_limit image_low_bgpsegs lim_source_ok implG_plain_bg).
Qed.
