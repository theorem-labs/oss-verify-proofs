(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs, PBC *)
(* Row img-su-syslog-A of a Theorem Labs lane's REPLY-IMG-ROWS.md:66 (sha256 a33a582e3ffd; internal record)
   (CF-UNIT-HYPS.md:155 (sha256 77b3f94c95d2; internal record), Table 4, a START-UP fact): common_flags + 0x40 (log_to_syslog) = 0 in reply image A's state
   after AsanInitInternal. Twin of img-su-syslog-B (a Theorem Labs lane, lib/B/ReplyImg_su_syslog.v, same two shapes).
   cgif's pattern (STARTUP-FACTS-CHECK.md:49-51 sha256 e2dc89b75692; internal record): KWord a_off := 1277416 (common_flags 0x137da8 + 0x40) 8 (ELit 0)
   in YB01.v:14 HS_tfib_0_kn and YB03.v:12 JS_tfib_band.
   At reply A: common_flags = 0x137be8 (AB1w.v:591 tfib_D_common_flags_dont_use_CommonFlags_struct_common; the pinned
   fuzz_reply.asan 42c58610 nm: _ZN11__sanitizer21common_flags_dont_useE 0x137be8 size 0x120), so log_to_syslog is the
   word at 0x137be8 + 0x40 = 0x137c28 = 1276968, inside the 0x120-byte struct. It is AF0m.v:50 (Tfib_const_abs row 8),
   AB01.v:19 (HS_tfib_0_kn) and AB03.v:15 (JS_tfib_band). The text names it once in AB01.v, but HS_tfib_k_kn for k >= 1
   is built from HS_tfib_0_kn by seg (AB01.v:21-36), so the word reaches the later hand-off states without appearing in
   their text; replya_log_to_syslog_hs states it for all 50 (a Theorem Labs lane measured the same on B).
   Proofs: the const form by ts_const (AF0m.v:886) and list membership; the start forms by kentry_eqb (YK09.v:365) and
   kentry_eqb_eq (YA0e.v:694), decided by a whole-goal vm_compute. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YK0c YK09 YA0e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AB1w AB01 AB03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
Import ListNotations.
Open Scope Z_scope.

(* the address of common_flags()->log_to_syslog in reply image A *)
Definition replya_log_to_syslog_addr : Z :=
  AB1w.tfib_D_common_flags_dont_use_CommonFlags_struct_common + 0x40.

Lemma replya_log_to_syslog_addr_val : replya_log_to_syslog_addr = 0x137c28.
Proof. reflexivity. Qed.

(* (1) const-table form, over TfibSyms: the instance's const cells hold the word, = 0 *)
Lemma replya_log_to_syslog_const : forall B ly, TfibSyms B ->
  In (z8 (ANum replya_log_to_syslog_addr) 0) (as_const B ly).
Proof.
  intros B ly H. rewrite (@ts_const B H ly). unfold Tfib_const.
  apply in_or_app; right. apply in_or_app; left. unfold Tfib_const_abs.
  repeat first [apply in_eq | apply in_cons].
Qed.

(* the consumer form (REPLY-IMG-ROWS.md:15 (sha256 a33a582e3ffd; internal record) NAMING: stem su_syslog in both twins, over @im_syms AImg_reply B; the B twin
   is a Theorem Labs lane's su_syslog_B), stated over the image class's const cells (as SB_CONST states `In (...) (im_const ly)`) *)
Lemma su_syslog_A : forall (B : asyms) (ly : alayout), @im_syms AImg_reply B ->
  In (z8 (ANum replya_log_to_syslog_addr) 0) (@im_const AImg_reply ly).
Proof.
  intros B ly TS. rewrite <- (@im_const_eq AImg_reply B ly TS). exact (replya_log_to_syslog_const B ly TS).
Qed.

(* (2) start-state form, cgif's evidence: the first hand-off state and the band state know the word as 0 *)
(* the names of the start-up records live in modules: kentry / KWord / SA / ELit in AX2 (YK0c.v), kn / kentry_eqb in
   APC (YK09.v), kentry_eqb_eq in APSG (YA0e.v); they are written qualified, so nothing shadows the YG / AF0m names *)
Definition replya_log_to_syslog_cell : AX2.kentry :=
  AX2.KWord {| AX2.a_base := AX2.ELit 0; AX2.a_off := replya_log_to_syslog_addr |} 8 (AX2.ELit 0).

Lemma kentry_in_of_existsb : forall (c : AX2.kentry) (l : list AX2.kentry),
  existsb (APC.kentry_eqb c) l = true -> In c l.
Proof.
  intros c l; induction l as [|y l IH]; simpl; [discriminate|].
  intros H. apply orb_true_iff in H. destruct H as [H|H].
  - left. symmetry. apply APSG.kentry_eqb_eq. exact H.
  - right. apply IH. exact H.
Qed.

Lemma replya_log_to_syslog_HS0_kn : In replya_log_to_syslog_cell AB01.HS_tfib_0_kn.
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma replya_log_to_syslog_HS0 : In replya_log_to_syslog_cell (APC.kn AB01.HS_tfib_0).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma replya_log_to_syslog_band : In replya_log_to_syslog_cell (APC.kn AB03.JS_tfib_band).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma replya_log_to_syslog_start :
  In replya_log_to_syslog_cell AB01.HS_tfib_0_kn /\ In replya_log_to_syslog_cell (APC.kn AB03.JS_tfib_band).
Proof. exact (conj replya_log_to_syslog_HS0_kn replya_log_to_syslog_band). Qed.

(* all 50 hand-off states (HS_tfib h := nth_error HS_tfib_list h, AB01.v) know the word as 0 *)
Lemma replya_log_to_syslog_hs : forall h cs, AB01.HS_tfib h = Some cs -> In replya_log_to_syslog_cell (APC.kn cs).
Proof.
  intros h cs H. unfold AB01.HS_tfib in H. apply nth_error_In in H.
  assert (Hall : forallb (fun cs => existsb (APC.kentry_eqb replya_log_to_syslog_cell) (APC.kn cs)) AB01.HS_tfib_list
                 = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. apply kentry_in_of_existsb. apply Hall. exact H.
Qed.
