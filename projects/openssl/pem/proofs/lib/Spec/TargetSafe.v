(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad MSafeA Stdio Harness Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free choose out_stderr out_stdout msg_store Target.ops lib_free_opt].

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list ptr -> @assn St.

(* [comment removed for export] *)
Hypothesis Hdm : forall X n, 0 <= n < 2^62 ->
  mspec (own X) (raw_malloc n) (fun r s mo => exists p, r = Some p /\ own (p :: X) s mo).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hout : forall X, mspec (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Definition fn_blocks (f : option ptr) : list ptr := match f with Some p => [p] | None => [] end.

Lemma mspec_ret_ops {A} (a : A) (P : @assn St) (Q : A -> @assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (ret ops a) Q.
Proof. intros H. cbn. apply mspec_ret. exact H. Qed.

Lemma mspec_bind_ops {A B} (m : Monad.M St A) (f : A -> Monad.M St B) P Q1 Q :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (bind ops m f) Q.
Proof. intros. cbn. eapply mspec_bind; eauto. Qed.

Lemma mspec_lib_free_opt : forall X (p : option ptr),
  mspec (own (fn_blocks p ++ X)) (lib_free_opt raw_free p) (fun _ => own X).
Proof.
  intros X [p|]; cbn.
  - apply Hdf.
  - apply mspec_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma mspec_malloc_some {B} : forall X n (k : option ptr -> Monad.M St B) (Q : B -> @assn St),
  0 <= n < 2^62 ->
  (forall p, mspec (own (p :: X)) (k (Some p)) Q) ->
  mspec (own X) (bind ops (lib_malloc ops n) k) Q.
Proof.
  intros X n k Q Hn Hk.
  apply (mspec_bind_ops _ _ _ (fun r s mo => exists p, r = Some p /\ own (p :: X) s mo)).
  - red_ops. apply Hdm. exact Hn.
  - intros r. apply mspec_exI. intros p. apply mspec_pure_l. intros ->. apply Hk.
Qed.

(* [comment removed for export] *)
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Lemma cremove_perm : forall (L : @clist ptr) i p n, nth_error L i = Some (p, n) ->
  Permutation (map fst L) (p :: map fst (cremove i L)).
Proof.
  induction L as [|x L IH]; intros i p n H; destruct i; cbn in *; try discriminate.
  - inversion H; subst. cbn. apply Permutation_refl.
  - specialize (IH i p n H). cbn. eapply Permutation_trans; [apply perm_skip; exact IH| apply perm_swap].
Qed.

Lemma client_any_mspec : forall fuel L X,
  mspec (own (map fst L ++ X)) (client_any ops fuel L) (fun L' => own (map fst L' ++ X)).
Proof.
  induction fuel as [|f IH]; intros L X; cbn [client_any].
  - apply mspec_ret_ops. auto.
  - apply (mspec_bind_ops _ _ _ (fun a s mo => cvalid L a /\ own (map fst L ++ X) s mo)).
    { red_ops. apply mspec_choice. intros a s mo Hv H. split; assumption. }
    intros [k n i]. apply mspec_pure_l. intros Hv.
    destruct k as [|k|k]; [apply mspec_ret_ops; auto| |apply mspec_ret_ops; auto].
    destruct k as [k|k|]; [apply mspec_ret_ops; auto| |].
    + (* [comment removed for export] *)
      destruct k as [k|k|]; try (apply mspec_ret_ops; auto; fail).
      cbn in Hv. destruct (nth_error L (Z.to_nat n)) as [[p sz]|] eqn:E.
      * apply (mspec_bind_ops _ _ _ (fun _ => own (map fst (cremove (Z.to_nat n) L) ++ X))).
        { red_ops. eapply mspec_pre; [apply (Hdf (map fst (cremove (Z.to_nat n) L) ++ X) p)|].
          intros s mo H. eapply Hperm; [|exact H]. change (p :: map fst (cremove (Z.to_nat n) L) ++ X) with ((p :: map fst (cremove (Z.to_nat n) L)) ++ X).
          apply Permutation_app_tail. exact (cremove_perm L _ p sz E). }
        intros _. apply IH.
      * exfalso. apply nth_error_None in E. lia.
    + (* [comment removed for export] *)
      cbn in Hv. destruct Hv as (Hn & _).
      apply mspec_malloc_some; [unfold SZ_MAX in Hn; lia|]. intros p. exact (IH ((p, n) :: L) X).
Qed.

Lemma fuzz_one_mspec : forall d L X,
  mspec (own (map fst L ++ X)) (fuzz_one ops d L) (fun r s mo => own (map fst (snd r) ++ X) s mo /\ fst r = 0).
Proof.
  intros d L X. unfold fuzz_one.
  apply (mspec_bind_ops _ _ _ (fun L' => own (map fst L' ++ X))); [apply client_any_mspec|].
  intros L'. apply mspec_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

Lemma run_calls_mspec : forall d X n rc L,
  rc = 0 ->
  mspec (own (map fst L ++ X)) (run_calls ops d n rc L) (fun rc' => fun s mo => (exists L' : @clist ptr, own (map fst L' ++ X) s mo) /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc L Hrc; cbn [run_calls].
  - apply mspec_ret_ops. intros s mo H. split; [exists L; exact H| exact Hrc].
  - apply (mspec_bind_ops _ _ _ (fun r => fun s mo => own (map fst (snd r) ++ X) s mo /\ fst r = 0)); [apply fuzz_one_mspec|].
    intros [rc' L']. cbn [fst snd]. apply mspec_pure. intros ->. apply (mspec_bind_ops _ _ _ (fun _ => own (map fst L' ++ X))).
    + red_ops. apply Hout.
    + intros u. apply IH. reflexivity.
Qed.

Theorem target_run_mspec : forall X cfg payload, zlength payload + 1 < 2^62 ->
  mspec (own X) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ s mo => exists Y, own (Y ++ X) s mo).
Proof.
  intros X cfg payload Hpl. unfold Target.target_run, Harness.target_run.
  (* [comment removed for export] *)
  apply (mspec_bind_ops _ _ _ (fun L0 => own (map fst L0 ++ X))).
  { unfold fuzz_init. apply (client_any_mspec INIT_FUEL [] X). }
  intros L0.
  apply (mspec_bind_ops _ _ _ (fun a => match a with None => fun _ _ => False | Some owned => own (map fst L0 ++ fn_blocks owned ++ X) end)).
  - destruct (zlength payload =? 0) eqn:EZ.
    + apply mspec_ret_ops. intros s mo H. cbn [fn_blocks app]. exact H.
    + apply mspec_malloc_some; [unfold zlength in *; lia|]. intros p.
      apply mspec_ret_ops. intros s mo H. cbn [fn_blocks app]. eapply Hperm; [|exact H]. apply Permutation_middle.
  - intros [owned|]; [| apply mspec_false].
    apply (mspec_bind_ops _ _ _ (fun rc => fun s mo => (exists L' : @clist ptr, own (map fst L' ++ fn_blocks owned ++ X) s mo) /\ rc = 0));
      [apply run_calls_mspec; reflexivity|].
    intros rc. apply mspec_pure. intros ->. apply mspec_exI. intros L'.
    apply (mspec_bind_ops _ _ _ (fun _ => own (map fst L' ++ X))).
    + eapply mspec_pre; [apply (mspec_lib_free_opt (map fst L' ++ X) owned)|].
      intros s mo H. eapply Hperm; [|exact H]. destruct owned as [p|]; cbn [fn_blocks app]; [| apply Permutation_refl].
      apply Permutation_sym, Permutation_middle.
    + intros u. apply mspec_ret_ops. intros s mo H. exists (map fst L'). exact H.
Qed.

End TargetSafe.
