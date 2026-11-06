(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad MSafe Stdio HexModel Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store Target.ops lib_free_opt].

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n)
        (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hout : forall X, mspec (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma mspec_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (ret ops a) Q.
Proof. intros H. cbn. apply mspec_ret. exact H. Qed.

Lemma mspec_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (bind ops m f) Q.
Proof. intros H1 H2. cbn. eapply mspec_bind; eauto. Qed.

Lemma zlength_nonneg {A} (l : list A) : 0 <= zlength l.
Proof. unfold zlength. lia. Qed.

Lemma fuzz_one_mspec : forall d X,
  mspec (own X) (fuzz_one ops d) (fun rc s mo => own X s mo /\ rc = 0).
Proof.
  intros d X. unfold fuzz_one.
  apply (mspec_bind_ops _ _ _
           (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end)).
  { red_ops. eapply mspec_post; [apply Hdm|].
    - pose proof (zlength_nonneg d). unfold HEX_SIZE. lia.
    - intros [p|] s mo H; [exact (proj1 H)| exact H]. }
  intros r.
  apply (mspec_bind_ops _ _ _ (fun _ => own X)).
  - red_ops. destruct r as [p|]; [apply Hdf|]. apply mspec_ret. auto.
  - intros _. apply mspec_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

Lemma run_calls_mspec : forall d X n rc, rc = 0 ->
  mspec (own X) (run_calls ops d n rc) (fun rc' s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc Hrc; cbn [run_calls].
  - apply mspec_ret_ops. intros s mo H. auto.
  - apply (mspec_bind_ops _ _ _ (fun rc' s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_mspec|].
    intros rc'. apply mspec_pure. intros ->.
    apply (mspec_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0. apply Hout.
    + intros _. apply IH. reflexivity.
Qed.

Theorem target_run_mspec : forall X cfg payload,
  mspec (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload. unfold Target.target_run, HexModel.target_run. fold ops.
  apply (mspec_bind_ops _ _ _
           (fun a s mo => match a with
                          | None => own X s mo
                          | Some None => own X s mo
                          | Some (Some p) => own (p :: X) s mo
                          end)).
  - destruct (zlength payload =? 0).
    + apply mspec_ret_ops. auto.
    + apply (mspec_bind_ops _ _ _
               (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end)).
      * red_ops. eapply mspec_post; [apply Hdm; apply zlength_nonneg|].
        intros [p|] s mo H; [exact (proj1 H)| exact H].
      * intros [p|]; apply mspec_ret_ops; auto.
  - intros [[p|]|]; [| |apply mspec_ret_ops; auto].
    + apply (mspec_bind_ops _ _ _ (fun rc s mo => own (p :: X) s mo /\ rc = 0)); [apply run_calls_mspec; reflexivity|].
      intros rc. apply (mspec_bind_ops _ _ _ (fun _ => own X)).
      * red_ops. eapply mspec_pre; [apply Hdf|]. intros s mo H. exact (proj1 H).
      * intros _. apply mspec_ret_ops. auto.
    + apply (mspec_bind_ops _ _ _ (fun rc s mo => own X s mo /\ rc = 0)); [apply run_calls_mspec; reflexivity|].
      intros rc. apply (mspec_bind_ops _ _ _ (fun _ => own X)).
      * red_ops. apply mspec_ret. intros s mo H. exact (proj1 H).
      * intros _. apply mspec_ret_ops. auto.
Qed.

End TargetSafe.
