(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition t_body_g (KT : list byte -> Fs.Fs -> TSet) (data : list byte) (fs : Fs.Fs) : TSet :=
  if body_pre_target data then t_body_pre data fs else KT data fs.

Definition spec_g (KT : list byte -> Fs.Fs -> TSet) (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match drv_classify argv fs0 with
  | DcUsage => t_die (msg_usage (hd [] argv)) fs0
  | DcNoOpen path => t_die (msg_cannot_open path) fs0
  | DcDir path => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
  | DcFile path data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body_g KT data fs0)
  end.

Lemma t_body_g_target : t_body_g t_target = t_body.
Proof. unfold t_body_g. apply FunctionalExtensionality.functional_extensionality. intros data.
       apply FunctionalExtensionality.functional_extensionality. intros fs. symmetry. apply t_body_split. Qed.

(* [comment removed for export] *)
Lemma spec_g_acc : forall KT argv fs0, drv_verdict argv fs0 = true -> spec_g KT argv fs0 = spec argv fs0.
Proof.
  intros KT argv fs0 H. unfold spec_g, spec, drv_verdict in *.
  destruct (drv_classify argv fs0) as [| path | path | path data]; try reflexivity.
  unfold t_opened, t_body_g. rewrite H. rewrite (t_body_pre_target data fs0 H). reflexivity.
Qed.

Lemma spec_g_file : forall KT argv fs0 path data, drv_classify argv fs0 = DcFile path data -> body_pre_target data = false ->
  spec_g KT argv fs0 = t_alt2 (t_die (msg_cannot_open path) fs0) (KT data fs0).
Proof. intros KT argv fs0 path data H Hb. unfold spec_g, t_body_g. rewrite H, Hb. reflexivity. Qed.
