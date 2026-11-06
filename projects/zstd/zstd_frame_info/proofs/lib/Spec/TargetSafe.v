(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad MSafe MSafeP Harness Adapter Driver.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Keeps.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
Variable emit : Z -> M St unit.
Variable own : list ptr -> assn St.

(* [comment removed for export] *)
Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
(* [comment removed for export] *)
Hypothesis HmS : forall X n, 0 <= n <= OPNEW_MAX ->
  mspecP (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => False end).
Hypothesis Hf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
(* [comment removed for export] *)
Hypothesis Hleak : forall X Y s mo, own (Y ++ X) s mo -> own X s mo.
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).

(* [comment removed for export] *)
Definition olist (o : option ptr) : list ptr := match o with Some p => [p] | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="HmS"] Lemma fuzz_malloc_spec : forall X n, n <= OPNEW_MAX ->
  mspecP (own X) (fuzz_malloc raw_malloc new_handler n) (fun r => own (olist r ++ X)).
Proof.
  intros X n Hn. unfold fuzz_malloc.
  apply mspecP_if; intros C.
  - apply Z.ltb_lt in C.
    eapply mspecP_bind; [apply HmS; lia|].
    intros [p|]; cbn beta iota.
    + apply mspecP_pure. intros _. apply mspecP_ret. intros s mo H; exact H.
    + intros s mo [].
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

#[using="Hf"] Lemma free_opt_spec : forall X o,
  mspec (own (olist o ++ X)) (free_opt raw_free o) (fun _ => own X).
Proof.
  intros X [p|]; cbn [free_opt olist app]; [apply Hf| apply mspec_ret; intros s mo H; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fuzz_one_spec : forall X data, zlength data <= MAX_INPUT ->
  mspecP (own X) (fuzz_one raw_malloc raw_free new_handler data) (fun _ => own X).
Proof.   (* [comment removed for export] *)
  intros X data _. unfold fuzz_one. apply mspecP_ret. intros s mo H; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hemit"] Lemma run_calls_spec : forall X n payload rc, zlength payload <= MAX_INPUT ->
  mspecP (own X) (run_calls (fuzz_one raw_malloc raw_free new_handler) emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc Hlen; cbn [run_calls].
  - apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply fuzz_one_spec; exact Hlen|]. intros rc'.
    eapply mspecP_seq; [apply mspec_mspecP; apply Hemit|]. intros _. apply IH. exact Hlen.
Qed.

Theorem target_run_spec : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspecP (own X) (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler) emit cfg payload) (fun _ => own X).
Proof using Hm HmS Hf Hperm Hleak Hemit.   (* [comment removed for export] *)
  intros X cfg payload Hlen. unfold target_run.
  eapply mspecP_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  { apply mspecP_if; intros _; [apply mspecP_ret; intros s mo H; exact H|].
    eapply mspecP_bind; [apply mspec_mspecP; apply Hm; unfold zlength; lia|]. intros [p|]; apply mspecP_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspec_mspecP; apply Hf|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspecP_ret; intros s mo H; exact H|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafe.
