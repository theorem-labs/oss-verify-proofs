(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require ITree Nodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Definition cj_silent_node (n : Nodes.node) : Prop :=
  silent_node Nodes.nstep Nodes.nexit n.

Lemma silent_NBrk : forall req, cj_silent_node (Nodes.NBrk req).
Proof. intros req. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMmap : forall addr len prot flags, cj_silent_node (Nodes.NMmap addr len prot flags).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMunmap : forall addr len, cj_silent_node (Nodes.NMunmap addr len).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMprotect : forall addr len prot, cj_silent_node (Nodes.NMprotect addr len prot).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

(* [comment removed for export] *)
Lemma silent_NSetTid : cj_silent_node Nodes.NSetTid.
Proof. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NIoctl : forall fd req, cj_silent_node (Nodes.NIoctl fd req).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NClose : forall fd, cj_silent_node (Nodes.NClose fd).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NOpen : forall path, cj_silent_node (Nodes.NOpen path).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NRead : forall fd buf count, cj_silent_node (Nodes.NRead fd buf count).
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

(* [comment removed for export] *)
Definition is_silent_kind (n : Nodes.node) : bool :=
  match n with
  | Nodes.NWrite _ _ | Nodes.NWritev _ _ | Nodes.NExit _ => false
  | _ => true
  end.

Lemma is_silent_kind_sound : forall n, is_silent_kind n = true -> cj_silent_node n.
Proof.
  intros n H. destruct n; try discriminate H.
  - apply silent_NOpen.
  - apply silent_NRead.
  - apply silent_NClose.
  - apply silent_NIoctl.
  - apply silent_NSetTid.
  - apply silent_NBrk.
  - apply silent_NMmap.
  - apply silent_NMunmap.
  - apply silent_NMprotect.
Qed.
