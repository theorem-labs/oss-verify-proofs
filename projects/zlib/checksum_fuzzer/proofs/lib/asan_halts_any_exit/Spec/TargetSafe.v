(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad MSafe MSafeP Harness Adapter Driver.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import Keeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable emit : Z -> M St unit.
Variable own : list ptr -> assn St.

Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).


Lemma fuzz_one_spec : forall X data,
  mspecP (own X) (fuzz_one data) (fun _ => own X).
Proof. intros X data. unfold fuzz_one. apply mspecP_ret. intros s mo H; exact H. Qed.


Lemma run_calls_spec : forall X n payload rc,
  mspecP (own X) (run_calls fuzz_one emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc; cbn [run_calls].
  - apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply fuzz_one_spec|]. intros rc'.
    eapply mspecP_seq; [apply mspec_mspecP; apply Hemit|]. intros _. apply IH.
Qed.

Theorem target_run_spec : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspecP (own X) (target_run raw_malloc raw_free fuzz_one emit cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload Hlen. unfold target_run.
  eapply mspecP_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  { apply mspecP_if; intros _; [apply mspecP_ret; intros s mo H; exact H|].
    eapply mspecP_bind; [apply mspec_mspecP; apply Hm; unfold zlength; lia|]. intros [p|]; apply mspecP_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecP_seq; [apply run_calls_spec|]. intros rc. eapply mspecP_seq; [apply mspec_mspecP; apply Hf|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply run_calls_spec|]. intros rc. eapply mspecP_seq; [apply mspecP_ret; intros s mo H; exact H|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafe.
