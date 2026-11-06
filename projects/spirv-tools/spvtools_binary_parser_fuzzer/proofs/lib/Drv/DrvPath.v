(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Lemma argv1_facts : forall (a0s path : list byte), valid_argv [a0s; path] ->
  path_has_slash path = false /\ path_eqb path dotdot_path = false.
Proof. intros a0s path (_ & _ & _ & _ & H). cbn [tl] in H. inversion H; subst. assumption. Qed.

Lemma argv1_no_slash : forall (a0s path : list byte), valid_argv [a0s; path] -> path_has_slash path = false.
Proof. intros a0s path H. exact (proj1 (argv1_facts a0s path H)). Qed.

Lemma argv1_not_dirref : forall (a0s path : list byte), valid_argv [a0s; path] -> path <> [Z_to_bv 8 46] ->
  path_is_dirref path = false.
Proof.
  intros a0s path Hva Hnd. destruct (argv1_facts a0s path Hva) as [_ Hdd]. unfold path_is_dirref.
  rewrite Hdd, orb_false_r. destruct (path_eqb path dot_path) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. exfalso. apply Hnd. exact E.
Qed.
