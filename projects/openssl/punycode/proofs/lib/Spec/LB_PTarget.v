(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Monad MSafe Stdio Harness Target Driver LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store Target.ops lib_free_opt].

(* [comment removed for export] *)
Definition smallX {ptr : Type} (X : list (ptr * Z)) : Prop :=
  Forall (fun xb => 0 <= snd xb <= MAX_INPUT + 1) X.

Section TargetL.
Context {St ptr : Type}.
Variable B : Z.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list (ptr * Z) -> assn St.
Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hout : forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X).
Hypothesis OK_tgt : forall X n, (length X <= 4)%nat -> smallX X -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. cbn. apply mspecL_ret. exact H. Qed.

Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros. cbn. eapply mspecL_bind; eauto. Qed.

Lemma malloc_L : forall X n, (length X <= 4)%nat -> smallX X -> 0 <= n <= MAX_INPUT + 1 ->
  mspecL B (own X) (raw_malloc n) (fun r s mo => match r with Some p => own ((p, n) :: X) s mo | None => own X s mo end).
Proof.
  intros X n HL SX Hn. eapply mspecL_conseq; [apply (Hdm X n); lia| |].
  - intros s mo H. split; [exact H| apply OK_tgt; assumption].
  - intros [p|] s mo H; [exact (proj1 H)| exact H].
Qed.

Lemma smallX_cons (p : ptr) n X : 0 <= n <= MAX_INPUT + 1 -> smallX X -> smallX ((p, n) :: X).
Proof. intros; unfold smallX in *; constructor; auto. Qed.

(* [comment removed for export] *)
Lemma fuzz_one_L : forall d X, (length X <= 2)%nat -> smallX X -> zlength d <= MAX_INPUT ->
  mspecL B (own X) (fuzz_one ops d) (fun rc s mo => own X s mo /\ rc = 0).
Proof.
  intros d X HL SX Hd. unfold fuzz_one.
  assert (Hn : 0 <= zlength d + 1 <= MAX_INPUT + 1) by (unfold zlength in *; lia).
  apply (mspecL_bind_ops _ _ _ (fun r s mo => match r with Some p => own ((p, zlength d + 1) :: X) s mo | None => own X s mo end)).
  { red_ops. apply malloc_L; [lia| exact SX| exact Hn]. }
  intros [b|]; [| red_ops; apply mspecL_munr].
  apply (mspecL_bind_ops _ _ _ (fun r s mo => match r with Some q => own ((q, WPACKET_SUB_SIZE) :: (b, zlength d + 1) :: X) s mo
                                                 | None => own ((b, zlength d + 1) :: X) s mo end)).
  { red_ops. apply malloc_L; [cbn [length]; lia| apply smallX_cons; assumption| unfold WPACKET_SUB_SIZE, MAX_INPUT; lia]. }
  intros [q|]; [| red_ops; apply mspecL_munr].
  apply (mspecL_bind_ops _ _ _ (fun _ => own ((b, zlength d + 1) :: X))); [red_ops; apply Hdf|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ => own X)); [red_ops; apply Hdf|]. intros _.
  apply mspecL_ret_ops. intros s mo H. split; [exact H| reflexivity].
Qed.

Lemma run_calls_L : forall d X n rc, (length X <= 2)%nat -> smallX X -> zlength d <= MAX_INPUT ->
  rc = 0 ->
  mspecL B (own X) (run_calls ops d n rc) (fun rc' => fun s mo => own X s mo /\ rc' = 0).
Proof.
  intros d X n. induction n as [|n IH]; intros rc HL SX Hd Hrc; cbn [run_calls].
  - apply mspecL_ret_ops. intros s mo H. auto.
  - apply (mspecL_bind_ops _ _ _ (fun rc' => fun s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_L; assumption|].
    intros rc'. apply mspecL_pure. intros ->. apply (mspecL_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. apply Hout.
    + intros u. apply IH; [assumption| assumption| assumption| reflexivity].
Qed.
End TargetL.

(* [comment removed for export] *)
Theorem target_run_L {St ptr : Type} (B : Z)
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St)
  (own : list (ptr * Z) -> assn St) (mal_ok : list (ptr * Z) -> Z -> Prop) :
  (forall X n, 0 <= n ->
     mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
            (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  (forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall X ps, mspecL B (own X) (stderr_fprintf (St:=St) ps) (fun _ => own X)) ->
  (forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X)) ->
  (forall X n, (length X <= 4)%nat -> smallX X -> 0 <= n <= MAX_INPUT + 1 -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> smallX X0 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X0).
Proof.
  intros Hdm Hdf _ _ Hout OK X0 cfg payload HX0 SX0 Hpl.
  unfold Target.target_run, Harness.target_run.
  pose proof (@malloc_L St ptr B raw_malloc own mal_ok Hdm OK) as ML.
  set (owned_blocks := fun (o : option ptr) => match o with Some p => [(p, zlength payload)] | None => [] end).
  apply (mspecL_bind _ _ _ _ (fun a => match a with None => own X0 | Some owned => own (owned_blocks owned ++ X0) end)).
  - destruct (zlength payload =? 0) eqn:EZ.
    + cbn. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT]. apply (mspecL_bind _ _ _ _ (fun r s mo => match r with Some p => own ((p, zlength payload) :: X0) s mo | None => own X0 s mo end)).
      * apply ML; [lia| exact SX0| unfold zlength in *; lia].
      * intros [p|]; apply mspecL_ret; intros s mo H; exact H.
  - intros [owned|]; [| cbn; apply mspecL_ret; intros s mo H; exact H].
    assert (HXX : (length (owned_blocks owned ++ X0) <= 2)%nat) by (destruct owned; cbn [owned_blocks length app]; lia).
    assert (SXX : smallX (owned_blocks owned ++ X0)).
    { destruct owned as [p|]; cbn [owned_blocks app]; [| exact SX0]. apply smallX_cons; [unfold zlength in *; lia| exact SX0]. }
    cbn -[MAX_INPUT run_calls].
    apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => own (owned_blocks owned ++ X0) s mo /\ rc = 0)).
    { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hout OK payload _ _ 0 HXX SXX Hpl). reflexivity. }
    intros rc. apply mspecL_pure. intros ->.
    apply (mspecL_bind _ _ _ _ (fun _ => own X0)).
    + destruct owned as [p|]; cbn [owned_blocks app lib_free_opt]; [apply Hdf| apply mspecL_ret; intros s mo H; exact H].
    + intros u. apply mspecL_ret. intros s mo H. exact H.
Qed.
