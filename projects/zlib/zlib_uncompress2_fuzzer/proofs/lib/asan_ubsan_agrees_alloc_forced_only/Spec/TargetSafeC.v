(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe MSafeP CMonad CLogic Harness HarnessC Adapter AdapterC Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetSafeC.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable emit : Z -> M St unit.
Variable own : list ptr -> assn St.
Variables pre opt : list Z.

Hypothesis Hm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hemit : forall X v, mspec (own X) (emit v) (fun _ => own X).

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

Lemma fuzz_without_spec : forall ps X, mspec (own (ps ++ X)) (fuzz_without raw_free ps) (fun _ => own X).
Proof.
  intros ps X. unfold fuzz_without. eapply mspec_seq; [apply free_all_spec|]. intros _. apply mspec_ret. intros s mo H; exact H.
Qed.

Lemma fuzz_with_spec : forall ps X, Forall (fun n => 0 <= n) opt ->
  mspec (own (ps ++ X)) (fuzz_with raw_malloc raw_free opt ps) (fun _ => own X).
Proof.
  intros ps X Hopt. unfold fuzz_with. eapply mspec_bind; [apply (alloc_all_spec opt ps X Hopt)|]. intros ps'.
  eapply mspec_seq; [apply free_all_spec|]. intros _. apply mspec_ret. intros s mo H; exact H.
Qed.

Hypothesis Hpre : Forall (fun n => 0 <= n) pre.
Hypothesis Hopt : Forall (fun n => 0 <= n) opt.
Local Notation fuzz_one := (HarnessC.fuzz_one raw_malloc raw_free pre opt).

Lemma fuzz_one_spec : forall X data, cspecP (own X) (fuzz_one data) (fun _ => own X).
Proof.
  intros X data. unfold HarnessC.fuzz_one.
  eapply cspecP_bind; [apply cspecP_lift, mspec_mspecP; apply (alloc_all_spec pre [] X Hpre)|]. intros ps.
  apply cspecP_if; intros _.
  - apply cspecP_lift, mspec_mspecP. apply fuzz_without_spec.
  - apply cspecP_choice; apply cspecP_lift, mspec_mspecP; [apply fuzz_with_spec; exact Hopt| apply fuzz_without_spec].
Qed.

Lemma run_calls_spec : forall X n payload rc,
  cspecP (own X) (AdapterC.run_calls fuzz_one emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc; cbn [AdapterC.run_calls].
  - apply cspecP_ret. intros s mo H; exact H.
  - eapply cspecP_seq; [apply fuzz_one_spec|]. intros rc'.
    eapply cspecP_seq; [apply cspecP_lift, mspec_mspecP; apply Hemit|]. intros _. apply IH.
Qed.

Lemma payload_copy_spec : forall X payload,
  mspec (own X) (AdapterC.payload_copy raw_malloc payload)
        (fun a s mo => match a with
                       | None => own X s mo
                       | Some None => own X s mo
                       | Some (Some p) => own (p :: X) s mo
                       end).
Proof.
  intros X payload. unfold AdapterC.payload_copy.
  apply mspec_if; intros _; [apply mspec_ret; intros s mo H; exact H|].
  eapply mspec_bind; [apply Hm; unfold zlength; lia|].
  intros [p|]; apply mspec_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H].
Qed.

Theorem target_run_spec : forall X cfg payload,
  cspecP (own X) (AdapterC.target_run raw_malloc raw_free fuzz_one emit cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload. unfold AdapterC.target_run.
  eapply cspecP_bind; [apply cspecP_lift, mspec_mspecP; apply payload_copy_spec|].
  intros [[p|]|]; cbn beta iota.
  - eapply cspecP_seq; [apply run_calls_spec|]. intros rc.
    eapply cspecP_seq; [apply cspecP_lift, mspec_mspecP; apply Hf|]. intros _. apply cspecP_ret. intros s mo H; exact H.
  - eapply cspecP_seq; [apply run_calls_spec|]. intros rc.
    eapply cspecP_seq; [apply cspecP_lift, mspec_mspecP; apply mspec_ret; intros s mo H; exact H|]. intros _.
    apply cspecP_ret. intros s mo H; exact H.
  - apply cspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafeC.
