(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import ListNotations.

Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

Lemma m_halted_of_killed : forall (m : Model) (s : word),
  m_killed m = Some s -> m_halted m = Some s.
Proof.
  intros m s H. unfold m_killed, m_halted in *.
  destruct (procst_killed (m_proc m)); [exact H | discriminate H].
Qed.

Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Lemma halt_ev_exit : forall m' code, m_killed m' = None -> halt_ev m' code = ExitEv code (m_fs m').
Proof. intros m' code H. unfold halt_ev. rewrite H. reflexivity. Qed.

Lemma halt_ev_killed : forall m' sig, m_killed m' = Some sig -> halt_ev m' sig = KillEv sig (m_fs m').
Proof. intros m' sig H. unfold halt_ev. rewrite H. reflexivity. Qed.
