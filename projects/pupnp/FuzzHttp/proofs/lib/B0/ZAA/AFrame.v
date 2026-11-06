(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim PEnv.
Import ListNotations.
Open Scope Z_scope.

Lemma disjoint_from_of_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n F; cbn; [exact I|].
  inversion F; subst. cbn in *. split; [lia| apply IH; assumption].
Qed.

Definition above_img (W : list (Z * Z)) : Prop := Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0x609000 <= fst iv) W.

Ltac frame_cell C MU WM F :=
  eapply rw_cells_transport; [exact C| exact MU| exact WM|
    apply disjoint_from_of_Forall; eapply Forall_impl; [| exact F]; intros [lo' hi'] Hiv'; cbn in Hiv' |- *; lia].

Lemma poison_env_frame : forall E W m m',
  poison_env E m -> munch W m m' -> wmono asegs m m' -> above_img W -> poison_env E m'.
Proof.
  intros E W m m' PE MU WM F. unfold above_img in F. pe_split PE. unfold poison_env.
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell C MU WM F end.
Qed.

Section T.
Context {HC : HasCeiling}.

#[using="Type"] Lemma prim_env_frame : forall AL W m m',
  prim_env AL m -> munch W m m' -> wmono asegs m m' -> above_img W -> prim_env AL m'.
Proof. intros AL W m m' P MU WM F. unfold above_img in F. unfold prim_env in *. frame_cell P MU WM F. Qed.

Definition thread_clear (L : athread) (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => (snd iv <= 0x10000 \/ 0x609000 <= fst iv)
     /\ (at_ctx L + 160 <= fst iv \/ snd iv <= at_ctx L + 152)
     /\ (at_thr L + 24 <= fst iv \/ snd iv <= at_thr L + 8)
     /\ (at_thr L + 41 <= fst iv \/ snd iv <= at_thr L + 40)
     /\ (at_thr L + 3169 <= fst iv \/ snd iv <= at_thr L + 3168)) W.

#[using="Type"] Lemma thread_env_frame : forall L W m m',
  thread_env L m -> munch W m m' -> wmono asegs m m' -> thread_clear L W -> thread_env L m'.
Proof.
  intros L W m m' TE MU WM F. unfold thread_clear in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell C MU WM F end.
Qed.
End T.

Ltac env_clear := first [unfold above_img | unfold thread_clear];
  repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; try lia.
