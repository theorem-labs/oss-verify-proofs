(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatSim ExistsRun ClaVerdict.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Record hb_input (inp : ProcInput) (a0 path data : list byte) : Prop := HB_INPUT {
  hbi_argv  : in_argv inp = [a0; path];
  hbi_va    : valid_argv (in_argv inp);
  hbi_ve    : valid_envp (in_envp inp);
  hbi_plen  : (length path < 4096)%nat;
  hbi_pne   : path <> [];
  hbi_slash : path_has_slash path = false;
  hbi_dirref: path_is_dirref path = false;
  hbi_file  : fs_lookup (in_fs inp) path = Some data;
  hbi_len6  : (6 <= length data)%nat;
  hbi_cfg   : (6 + config_len data <= length data)%nat;
  hbi_max   : (Z.of_nat (length data) < 67108864)%Z
}.

Lemma hb_input_of_verdict : forall f,
  valid_fin_input f -> cla_verdict f = false ->
  exists a0 path data, hb_input (to_proc_input f) a0 path data.
Proof.
  intros f Hv Hc.
  apply cla_verdict_false_iff in Hc as (path & data & Hcl & Hb).
  apply drv_classify_DcFile_inv in Hcl as (a0 & Hargv & Hlen & Hne & Hnd & Hfs).
  apply body_pre_target_false_iff in Hb as (Hmax & H6 & Hcfg).
  destruct Hv as (Hva & Hve & _).
  exists a0, path, data.
  cbn [to_proc_input in_argv in_envp in_fs] in Hva, Hve. rewrite Hargv in Hva.
  assert (Hdd : path_eqb path dotdot_path = false).
  { destruct Hva as (_ & _ & _ & _ & H). cbn [tl] in H. apply Forall_cons_iff in H as [[_ H] _]. exact H. }
  assert (Hsl : path_has_slash path = false).
  { destruct Hva as (_ & _ & _ & _ & H). cbn [tl] in H. apply Forall_cons_iff in H as [[H _] _]. exact H. }
  unfold HDR_MIN, MAX_INPUT in *.
  constructor; cbn [to_proc_input in_argv in_envp in_fs]; rewrite ?Hargv; try assumption; try reflexivity.
  unfold path_is_dirref. rewrite Hdd, Bool.orb_false_r. apply path_eqb_neq. exact Hnd.
Qed.

