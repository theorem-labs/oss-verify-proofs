(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Mem Cells Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma dj_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. intros W1 W2 a n H1 H2. apply disjoint_from_app. split; assumption. Qed.

Ltac wokapp H1 H2 :=
  repeat first [ progress intros | split ];
  (apply dj_app; [ eapply H1; eauto | eapply H2; eauto ]).

Lemma WOK_link_app : forall W1 W2, WOK_link W1 -> WOK_link W2 -> WOK_link (W1 ++ W2).
Proof. unfold WOK_link. intros W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_alloc_app : forall W1 W2, WOK_alloc W1 -> WOK_alloc W2 -> WOK_alloc (W1 ++ W2).
Proof. unfold WOK_alloc. intros W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_regions_app : forall st W1 W2, WOK_regions st W1 -> WOK_regions st W2 -> WOK_regions st (W1 ++ W2).
Proof. unfold WOK_regions. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_avail_app : forall st W1 W2, WOK_avail st W1 -> WOK_avail st W2 -> WOK_avail st (W1 ++ W2).
Proof. unfold WOK_avail. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_thread_app : forall st W1 W2, WOK_thread st W1 -> WOK_thread st W2 -> WOK_thread st (W1 ++ W2).
Proof. unfold WOK_thread. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_live_app : forall st W1 W2, WOK_live st W1 -> WOK_live st W2 -> WOK_live st (W1 ++ W2).
Proof. unfold WOK_live, WOK_block. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_quar_app : forall st W1 W2, WOK_quar st W1 -> WOK_quar st W2 -> WOK_quar st (W1 ++ W2).
Proof. unfold WOK_quar, WOK_block. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_batches_app : forall st W1 W2, WOK_batches st W1 -> WOK_batches st W2 -> WOK_batches st (W1 ++ W2).
Proof. unfold WOK_batches, WOK_batch. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_ptrarr_app : forall st W1 W2, WOK_ptrarr st W1 -> WOK_ptrarr st W2 -> WOK_ptrarr st (W1 ++ W2).
Proof. unfold WOK_ptrarr. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_depot_app : forall st W1 W2, WOK_depot st W1 -> WOK_depot st W2 -> WOK_depot st (W1 ++ W2).
Proof. unfold WOK_depot. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_fs_app : forall st W1 W2, WOK_fs st W1 -> WOK_fs st W2 -> WOK_fs st (W1 ++ W2).
Proof. unfold WOK_fs. intros st W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_ia_app : forall W1 W2, WOK_ia W1 -> WOK_ia W2 -> WOK_ia (W1 ++ W2).
Proof. unfold WOK_ia. intros W1 W2 H1 H2. wokapp H1 H2. Qed.
Lemma WOK_lowshadow_app : forall W1 W2, WOK_lowshadow W1 -> WOK_lowshadow W2 -> WOK_lowshadow (W1 ++ W2).
Proof. unfold WOK_lowshadow. intros W1 W2 H1 H2. wokapp H1 H2. Qed.

End CeilWrap.
