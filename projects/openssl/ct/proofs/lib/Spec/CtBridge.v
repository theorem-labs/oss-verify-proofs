(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Malloc Driver Prog MI_Cnt MI_Inv LB_Inv LB_Sum LB_Raw LB_StmtA LibProg LibSafe LibOps.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState
  ApBase ApState ApLogic ApErr ApInv ApParse ApOwner ApBridge
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtSpecs3 CtSpecs4 CtOwner CtCaps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ct_consts_same : CtLogic.CT_NBT = CtCaps.CT_NBT /\ CtLogic.CT_SMB = CtCaps.CT_SMB /\ CtLogic.CT_NB63 = CtCaps.CT_NB63
  /\ CtLogic.CT_BIGB = CtCaps.CT_BIGB /\ CtLogic.CT_NSEC = CtCaps.CT_NSEC /\ CtLogic.ASAN_SEC_MIN = CtCaps.ASAN_SEC_MIN
  /\ CtLogic.CT_MAXREQ = CtCaps.CT_MAXREQ /\ CtSpecs4.CT_MAX_INPUT = MAX_INPUT.
Proof. repeat split; reflexivity. Qed.

Lemma n63_same (X : list (bptr * Z)) : CtLogic.n63 X = n63X X.
Proof.
  induction X as [|[p n] X IH]; [reflexivity|]. unfold CtLogic.n63 in *. rewrite msum_cons. unfold n63X in *. rewrite zcount_cons. cbn [snd].
  rewrite IH. unfold isbig. destruct (MMAP_THRESHOLD <=? n); lia.
Qed.

Lemma nsec_same (X : list (bptr * Z)) : CtLogic.nsec X = nsecX X.
Proof.
  induction X as [|[p n] X IH]; [reflexivity|]. unfold CtLogic.nsec in *. rewrite msum_cons. rewrite nsecX_cons. cbn [snd].
  rewrite IH. unfold issec, CtLogic.ASAN_SEC_MIN, CtCaps.ASAN_SEC_MIN. destruct (64513 <=? n); lia.
Qed.

Lemma smsum_same (X : list (bptr * Z)) : CtLogic.smsum X = CtCaps.smsum X.
Proof.
  induction X as [|[p n] X IH]; [reflexivity|]. unfold CtLogic.smsum in *. rewrite msum_cons, CtCaps.smsum_cons. cbn [snd]. rewrite IH. reflexivity.
Qed.

Lemma r63_same (X : list (bptr * Z)) : CtLogic.r63 X = R63X X.
Proof.
  induction X as [|[p n] X IH]; [reflexivity|]. unfold CtLogic.r63 in *. rewrite msum_cons, R63X_cons. cbn [snd]. rewrite IH. reflexivity.
Qed.

Lemma okC_okCt (X : list (bptr * Z)) n : okC X n -> okCt X n.
Proof.
  intros (H0 & HB & H1 & H2 & H3 & H4 & H5 & H6). unfold okCt.
  rewrite <- n63_same, <- nsec_same, <- smsum_same, <- r63_same.
  unfold bnonneg in HB. unfold zlength in H1. unfold zlen.
  unfold CtLogic.CT_NBT, CtLogic.CT_SMB, CtLogic.CT_NB63, CtLogic.CT_BIGB, CtLogic.CT_NSEC, CtLogic.CT_MAXREQ, isbig, issec, CtLogic.ASAN_SEC_MIN in *.
  unfold CtCaps.CT_NBT, CtCaps.CT_SMB, CtCaps.CT_NB63, CtCaps.CT_BIGB, CtCaps.CT_NSEC, CtCaps.CT_MAXREQ, CtCaps.ASAN_SEC_MIN.
  unfold CtCaps.smsz, CtLogic.smsz, CtLogic.bigb, LB_StmtA.bigb in *.
  repeat split; first [assumption| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ct_grow_b : bool := forallb (fun na => (21844 <? na) || realloc_crit_b (8 * na) (8 * (na * 8 / 5))) GROWTH.
Lemma ct_grow_b_true : ct_grow_b = true. Proof. vm_compute. reflexivity. Qed.

Lemma ct_grow : forall na, In na GROWTH -> na <= 21844 -> realloc_crit (8 * na) (8 * (na * 8 / 5)).
Proof.
  intros na Hin Hle. pose proof ct_grow_b_true as H. unfold ct_grow_b in H. rewrite forallb_forall in H. specialize (H na Hin).
  apply orb_prop in H as [H|H]; [apply Z.ltb_lt in H; lia|]. apply realloc_crit_b_ok. exact H.
Qed.

Lemma ct_inI : inplace_crit SZ_GEN_DATA SZ_GENSTR.
Proof. apply inplace_crit_b_ok. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ct_lib_one (ls : ap_ls bptr) (d : list Z) : lprog (ap_ls bptr * Z) := ap_embed (ct_one ls d).
Definition ct_linv : ap_ls bptr -> list (bptr * Z) -> Prop := CtOwner.ct_linv.
Definition ct_ls0 : ap_ls bptr := ap_ls0.

(* [comment removed for export] *)
Lemma ct_linv_nil : forall ls X, ct_linv ls X -> X = [] /\ ls_blocks ls = [] /\ ap_linv ls X.
Proof. intros ls X H. split; [exact (CtOwner.ct_linv_nil ls X H)|]. split; [exact (CtOwner.ct_linv_blocks ls X H)| exact (proj1 H)]. Qed.

Theorem ct_H_one : forall ls d X, ct_linv ls X -> zlength d <= MAX_INPUT ->
  lwf okCt (ct_lib_one ls d) X (fun r X' => ct_linv (fst r) X').
Proof.
  intros ls d X HL Hd. unfold ct_lib_one, ct_linv in *.
  apply (lwf_ok_mono (@okC bptr)); [intros X' n H; apply okC_okCt; exact H|].
  apply ap_embed_lwf.
  apply (ct_one_awp realloc_crit shrink_crit inplace_crit ap_spre ct_grow ct_inI); [exact HL|].
  unfold CT_MAX_INPUT. unfold MAX_INPUT in Hd. exact Hd.
Qed.

Theorem ct_H_rc : forall ls d, lleaves (ct_lib_one ls d) (fun r => snd r = 0).
Proof. intros ls d. unfold ct_lib_one. apply ap_embed_lleaves. apply ct_one_leaves. Qed.

Theorem ct_linv_init : ct_linv ct_ls0 [].
Proof. unfold ct_linv, ct_ls0. apply CtOwner.ct_linv_init. Qed.

