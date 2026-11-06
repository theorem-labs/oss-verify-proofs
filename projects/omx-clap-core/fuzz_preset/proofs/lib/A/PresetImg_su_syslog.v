(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_su_syslog.v (commit eb934de95d13, blob fc0053fccb17) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YK0c YK09 YA0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1w AB01 AB03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
Import ListNotations.
Open Scope Z_scope.

Definition preseta_log_to_syslog_addr : Z :=
  0x13c9e8 + 0x40.

Lemma preseta_log_to_syslog_addr_val : preseta_log_to_syslog_addr = 0x13ca28.
Proof. reflexivity. Qed.

Lemma preseta_log_to_syslog_const : forall B ly, TfibSyms B ->
  In (z8 (ANum preseta_log_to_syslog_addr) 0) (as_const B ly).
Proof.
  intros B ly H. rewrite (@ts_const B H ly). unfold Tfib_const.
  apply in_or_app; right. apply in_or_app; left. unfold Tfib_const_abs.
  repeat first [apply in_eq | apply in_cons].
Qed.

Lemma su_syslog_A : forall (B : asyms) (ly : alayout), @im_syms AImg_A B ->
  In (z8 (ANum preseta_log_to_syslog_addr) 0) (@im_const AImg_A ly).
Proof.
  intros B ly TS. rewrite <- (@im_const_eq AImg_A B ly TS). exact (preseta_log_to_syslog_const B ly TS).
Qed.

Definition preseta_log_to_syslog_cell : AX2.kentry :=
  AX2.KWord {| AX2.a_base := AX2.ELit 0; AX2.a_off := preseta_log_to_syslog_addr |} 8 (AX2.ELit 0).

Lemma kentry_in_of_existsb : forall (c : AX2.kentry) (l : list AX2.kentry),
  existsb (APC.kentry_eqb c) l = true -> In c l.
Proof.
  intros c l; induction l as [|y l IH]; simpl; [discriminate|].
  intros H. apply orb_true_iff in H. destruct H as [H|H].
  - left. symmetry. apply APSG.kentry_eqb_eq. exact H.
  - right. apply IH. exact H.
Qed.

Lemma preseta_log_to_syslog_HS0_kn : In preseta_log_to_syslog_cell AB01.HS_tfib_0_kn.
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma preseta_log_to_syslog_HS0 : In preseta_log_to_syslog_cell (APC.kn AB01.HS_tfib_0).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma preseta_log_to_syslog_band : In preseta_log_to_syslog_cell (APC.kn AB03.JS_tfib_band).
Proof. apply kentry_in_of_existsb. vm_compute. reflexivity. Qed.

Lemma preseta_log_to_syslog_start :
  In preseta_log_to_syslog_cell AB01.HS_tfib_0_kn /\ In preseta_log_to_syslog_cell (APC.kn AB03.JS_tfib_band).
Proof. exact (conj preseta_log_to_syslog_HS0_kn preseta_log_to_syslog_band). Qed.

Lemma preseta_log_to_syslog_hs : forall h cs, AB01.HS_tfib h = Some cs -> In preseta_log_to_syslog_cell (APC.kn cs).
Proof.
  intros h cs H. unfold AB01.HS_tfib in H. apply nth_error_In in H.
  assert (Hall : forallb (fun cs => existsb (APC.kentry_eqb preseta_log_to_syslog_cell) (APC.kn cs)) AB01.HS_tfib_list
                 = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. apply kentry_in_of_existsb. apply Hall. exact H.
Qed.
