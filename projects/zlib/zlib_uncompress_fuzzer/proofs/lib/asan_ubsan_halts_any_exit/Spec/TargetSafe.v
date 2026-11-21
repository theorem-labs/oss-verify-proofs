(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad MSafe MSafeP Harness Adapter Driver.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import Keeps.
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
Variable script : list Z -> list Z.
Hypothesis Hscript : forall data, Forall (fun n => 0 <= n) (script data).

Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).


Local Notation fuzz_one := (fuzz_one raw_malloc raw_free script).

Lemma alloc_all_spec : forall ns acc X, Forall (fun n => 0 <= n) ns ->
  mspec (own (acc ++ X)) (alloc_all raw_malloc ns acc) (fun ps => own (ps ++ X)).
Proof.
  induction ns as [|n ns IH]; intros acc X Hns; cbn [alloc_all].
  - apply mspec_ret. intros s mo H; exact H.
  - inversion Hns as [|n' ns' Hn Hns' E]; subst.
    eapply mspec_bind; [apply Hm; exact Hn|].
    intros [p|]; cbn beta iota.
    + apply mspec_pure. intros _. apply (IH (p :: acc) X Hns').
    + apply mspec_ret. intros s mo H; exact H.
Qed.

Lemma free_all_spec : forall ps X, mspec (own (ps ++ X)) (free_all raw_free ps) (fun _ => own X).
Proof.
  induction ps as [|p ps IH]; intros X; cbn [free_all app].
  - apply mspec_ret. intros s mo H; exact H.
  - eapply mspec_seq; [apply Hf|]. intros _. apply IH.
Qed.

Lemma fuzz_one_spec : forall X data,
  mspecP (own X) (fuzz_one data) (fun _ => own X).
Proof.
  intros X data. unfold Harness.fuzz_one. apply mspec_mspecP.
  eapply mspec_bind; [apply (alloc_all_spec (script data) [] X (Hscript data))|]. intros ps.
  eapply mspec_seq; [apply free_all_spec|]. intros _. apply mspec_ret. intros s mo H; exact H.
Qed.


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
