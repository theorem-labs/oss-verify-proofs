(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe Stdio HexModel Target TargetSafe Driver LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store Target.ops lib_free_opt].

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
(* [comment removed for export] *)
Definition smallX (X : list (ptr * Z)) : Prop :=
  Forall (fun xb => 0 <= snd xb <= MAX_INPUT + 1) X.
Hypothesis OK_tgt : forall X n, (length X <= 2)%nat -> smallX X -> 0 <= n <= 2 * (MAX_INPUT + 1) -> mal_ok X n.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma smallX_app Y X : smallX Y -> smallX X -> smallX (Y ++ X).
Proof. intros; unfold smallX in *; apply Forall_app; auto. Qed.
Lemma smallX_cons p n X : 0 <= n <= MAX_INPUT + 1 -> smallX X -> smallX ((p, n) :: X).
Proof. intros; unfold smallX in *; constructor; auto. Qed.
Lemma smallX_nil : smallX [].
Proof. constructor. Qed.
Lemma smallX_tail x X : smallX (x :: X) -> smallX X.
Proof. intros H. inversion H. assumption. Qed.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. cbn. apply mspecL_ret. exact H. Qed.
Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros H1 H2. cbn. eapply mspecL_bind; eauto. Qed.

Lemma zlength_nonneg {A} (l : list A) : 0 <= zlength l.
Proof. unfold zlength. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Calls.
Variable X : list (ptr * Z).
Hypothesis HX : (length X <= 2)%nat.
Hypothesis SX : smallX X.
Variable d : list Z.
Hypothesis Hd : zlength d <= MAX_INPUT.

Lemma fuzz_one_L :
  mspecL B (own X) (fuzz_one ops d) (fun rc => fun s mo => own X s mo /\ rc = 0).
Proof.
  unfold fuzz_one. pose proof (zlength_nonneg d) as Hd0.
  apply (mspecL_bind_ops _ _ _
           (fun r s mo => match r with Some p => own ((p, HEX_SIZE (zlength d)) :: X) s mo | None => own X s mo end)).
  { red_ops. eapply mspecL_conseq; [apply (Hdm X (HEX_SIZE (zlength d))); unfold HEX_SIZE; lia| |].
    - intros s mo H. split; [exact H|]. apply OK_tgt; [exact HX| exact SX| unfold HEX_SIZE; lia].
    - intros [p|] s mo H; [exact (proj1 H)| exact H]. }
  intros r. apply (mspecL_bind_ops _ _ _ (fun _ => own X)).
  - red_ops. destruct r as [p|]; [apply Hdf|]. apply mspecL_ret. auto.
  - intros u. apply mspecL_ret_ops. intros s mo H. auto.
Qed.

Lemma run_calls_L : forall n rc,
  rc = 0 ->
  mspecL B (own X) (run_calls ops d n rc) (fun rc' => fun s mo => own X s mo /\ rc' = 0).
Proof.
  induction n as [|n IH]; intros rc Hrc; cbn [run_calls].
  - apply mspecL_ret_ops. intros s mo H. auto.
  - apply (mspecL_bind_ops _ _ _ (fun rc' => fun s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_L|].
    intros rc'. apply mspecL_pure. intros ->. apply (mspecL_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. apply Hout.
    + intros u. apply IH. reflexivity.
Qed.
End Calls.
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
  (forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X)) ->
  (forall X n, (length X <= 2)%nat -> smallX X -> 0 <= n <= 2 * (MAX_INPUT + 1) -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> smallX X0 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X0).
Proof.
  intros Hdm Hdf Hout OK X0 cfg payload HX0 SX0 Hpl.
  unfold Target.target_run, HexModel.target_run.
  pose proof (@zlength_nonneg Z payload) as Hpl0.
  apply (mspecL_bind _ _ _ _
           (fun a s mo => match a with
                          | None => own X0 s mo
                          | Some None => own X0 s mo
                          | Some (Some p) => own ((p, zlength payload) :: X0) s mo
                          end)).
  - destruct (zlength payload =? 0) eqn:EZ.
    + cbn. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT].
      apply (mspecL_bind _ _ _ _
               (fun r s mo => match r with Some p => own ((p, zlength payload) :: X0) s mo | None => own X0 s mo end)).
      * eapply mspecL_conseq; [apply (Hdm X0 (zlength payload)); lia| |].
        -- intros s mo H. split; [exact H|]. apply OK; [lia| exact SX0| unfold MAX_INPUT in *; lia].
        -- intros [p|] s mo H; [exact (proj1 H)| exact H].
      * intros [p|]; apply mspecL_ret; intros s mo H; exact H.
  - intros [[p|]|]; [| |cbn; apply mspecL_ret; intros s mo H; exact H].
    + cbn -[MAX_INPUT run_calls].
      assert (HXX : (length ((p, zlength payload) :: X0) <= 2)%nat) by (cbn [length]; lia).
      assert (SXX : smallX ((p, zlength payload) :: X0)) by (apply smallX_cons; [lia| exact SX0]).
      apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => own ((p, zlength payload) :: X0) s mo /\ rc = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hout OK _ HXX SXX payload Hpl). reflexivity. }
      intros rc. apply (mspecL_bind _ _ _ _ (fun _ => own X0)).
      * eapply mspecL_pre; [apply Hdf|]. intros s mo H. exact (proj1 H).
      * intros u. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT run_calls].
      assert (HXX : (length X0 <= 2)%nat) by lia.
      apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => own X0 s mo /\ rc = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hout OK _ HXX SX0 payload Hpl). reflexivity. }
      intros rc. apply (mspecL_bind _ _ _ _ (fun _ => own X0)).
      * apply mspecL_ret. intros s mo H. exact (proj1 H).
      * intros u. apply mspecL_ret. intros s mo H. exact H.
Qed.
