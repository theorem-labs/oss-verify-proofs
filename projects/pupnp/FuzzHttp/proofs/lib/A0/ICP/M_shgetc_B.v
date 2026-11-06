(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import M_memcpy M_memchr M_printf_lib.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Export M_shgetc_A.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((- (T + zlength pre + 1)) mod 8 <= zlength post)%Z /\ (zlength txt <= 2^40)%Z.

Definition win (p co : Z) : Z := if (p - co <? 257)%Z then p else (co + 257)%Z.
Lemma win_range : forall p co, (0 <= co <= p)%Z -> (co <= win p co <= p /\ (co < p -> co < win p co) /\ win p co <= co + 257)%Z.
Proof. intros p co H. unfold win. destruct (Z.ltb_spec0 (p - co) 257); lia. Qed.

Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
  intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
  pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
  pose proof (f_equal bv_unsigned E) as E2. rewrite !unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. LiaTuning.ctauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells asegs m A [CB 1 bs] -> exists b, rw_cells asegs m A [CB 1 [b]].
Proof.
  intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
  destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells asegs m A (CB 0 [] :: cs) -> rw_cells asegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

