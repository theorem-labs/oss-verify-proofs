(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3 SymExec3Sound.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil HMem HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition wagree (k : N) (W W' : list word) : Prop :=
  forall n, (32 <= n < k)%N -> ev (wenv W) n = ev (wenv W') n.

Lemma wagree_sym : forall k W W', wagree k W W' -> wagree k W' W.
Proof. intros k W W' A n Hn. symmetry. exact (A n Hn). Qed.

Lemma wagree_prefix : forall (P X X' : list word), wagree (32 + N.of_nat (length P)) (P ++ X) (P ++ X').
Proof.
  intros P X X' n Hn. unfold wenv, HLib.Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [lia|]. rewrite !app_nth1 by lia. reflexivity.
Qed.

Lemma rtbl_wch : forall k W W' R RT, wagree k W W' ->
  forallb (fun re : reg * expr => wcl k (snd re)) RT = true -> rtbl W R RT -> rtbl W' R RT.
Proof.
  intros k W W' R RT A C HT. unfold rtbl in *. rewrite Forall_forall in *. intros re Hin.
  rewrite (HT re Hin). apply (edenot_wcl _ _ k); [exact (proj1 (forallb_forall _ _) C re Hin) | exact A].
Qed.

Lemma ftbl_wch : forall k W W' B m T, wagree k W W' -> fwcl k T = true -> ftbl W B m T -> ftbl W' B m T.
Proof.
  intros k W W' B m T A C HT. unfold ftbl, fwcl in *. rewrite Forall_forall in *. intros [[o w] e] Hin.
  pose proof (HT _ Hin) as K. cbn beta iota in K.
  pose proof (proj1 (forallb_forall _ _) C _ Hin) as Ce. cbn beta iota in Ce.
  rewrite <- (edenot_wcl _ _ k e Ce A). exact K.
Qed.
