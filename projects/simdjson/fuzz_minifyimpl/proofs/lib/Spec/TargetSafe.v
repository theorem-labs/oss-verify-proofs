(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad MSafe MSafeP HarnessM Adapter Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
Variable emit : Z -> M St unit.
Variable cl_get : St -> option ptr.
Variable cl_set : option ptr -> St -> St.
Variable ownc : option ptr -> list ptr -> assn St.

(* [comment removed for export] *)
Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall c X n, 0 <= n ->
  mspec (ownc c X) (raw_malloc n) (fun r s mo => match r with Some p => ownc c (p :: X) s mo /\ n < 2^63 | None => ownc c X s mo end).
(* [comment removed for export] *)
Hypothesis HmS : forall c X n, 0 <= n <= OPNEW_MAX ->
  mspecP (ownc c X) (raw_malloc n) (fun r s mo => match r with Some p => ownc c (p :: X) s mo /\ n < 2^63 | None => False end).
Hypothesis Hf : forall c X p, mspec (ownc c (p :: X)) (raw_free p) (fun _ => ownc c X).
Hypothesis Hperm : forall c X Y s mo, Permutation X Y -> ownc c X s mo -> ownc c Y s mo.
Hypothesis Hemit : forall c X v, mspec (ownc c X) (emit v) (fun _ => ownc c X).
(* [comment removed for export] *)
Hypothesis Hcl : forall c X s mo, ownc c X s mo -> cl_get s = c.
Hypothesis Hset : forall c c' X s mo, ownc c X s mo -> ownc c' X (cl_set c' s) mo.

(* [comment removed for export] *)
Definition clb (c : option ptr) : list ptr := match c with Some p => [p] | None => [] end.
Definition own (X : list ptr) : assn St := fun s mo => exists c, ownc c (clb c ++ X) s mo.

Lemma own_perm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Proof. intros X Y s mo HP [c H]. exists c. eapply Hperm; [| exact H]. apply Permutation_app_head. exact HP. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma own_malloc : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Proof.
  intros X n Hn. apply mspec_exI. intros c. eapply mspec_post; [apply (Hm c (clb c ++ X) n Hn)|].
  intros [p|] s mo; cbn beta iota.
  - intros [H H63]. split; [| exact H63]. exists c. eapply Hperm; [| exact H]. apply Permutation_middle.
  - intros H. exists c. exact H.
Qed.

Lemma own_mallocS : forall X n, 0 <= n <= OPNEW_MAX ->
  mspecP (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => False end).
Proof.
  intros X n Hn. apply mspecP_exI. intros c. eapply mspecP_post; [apply (HmS c (clb c ++ X) n Hn)|].
  intros [p|] s mo; cbn beta iota; [| intros []].
  intros [H H63]. split; [| exact H63]. exists c. eapply Hperm; [| exact H]. apply Permutation_middle.
Qed.

Lemma own_free : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Proof.
  intros X p. apply mspec_exI. intros c. eapply mspec_conseq; [apply (Hf c (clb c ++ X) p)| |].
  - intros s mo H. eapply Hperm; [| exact H]. apply Permutation_sym, Permutation_middle.
  - intros a s mo H. exists c. exact H.
Qed.

Lemma own_emit : forall X v, mspec (own X) (emit v) (fun _ => own X).
Proof. intros X v. apply mspec_exI. intros c. eapply mspec_post; [apply Hemit|]. intros a s mo H. exists c. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma opnew_spec_c : forall c X n, 0 <= n <= OPNEW_MAX ->
  mspecP (ownc c X) (opnew raw_malloc new_handler n) (fun p => ownc c (p :: X)).
Proof.
  intros c X n Hn. unfold opnew.
  eapply mspecP_bind; [apply HmS; unfold OPNEW_MAX in *; destruct (n =? 0); lia|].
  intros [p|]; cbn beta iota.
  - apply mspecP_pure. intros _. apply mspecP_ret. intros s mo H; exact H.
  - intros s mo [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma client_init_spec : forall X, mspecP (own X) (client_init raw_malloc new_handler cl_get cl_set) (fun _ => own X).
Proof.
  intros X. unfold client_init.
  eapply mspecP_bind; [apply mspecP_get|]. intros s0. cbn beta.
  destruct (cl_get s0) as [q|] eqn:E.
  - apply mspecP_ret. intros s mo [_ H]. exact H.
  - eapply mspecP_bind.
    + eapply mspecP_pre; [apply (opnew_spec_c None X CLIENT_VEC_BYTES); unfold CLIENT_VEC_BYTES, OPNEW_MAX; lia|].
      intros s mo [-> [c H]]. pose proof (Hcl _ _ _ _ H) as Hc. rewrite E in Hc. subst c. exact H.
    + intros p. apply mspecP_upd'. intros s mo H. exists (Some p). cbn [clb app]. apply (Hset None (Some p)). exact H.
Qed.

(* [comment removed for export] *)
Definition ob (b : option ptr) : list ptr := match b with Some p => [p] | None => [] end.

Lemma opnew_spec : forall X n, 0 <= n <= OPNEW_MAX ->
  mspecP (own X) (opnew raw_malloc new_handler n) (fun p => own (p :: X)).
Proof.
  intros X n Hn. apply mspecP_exI. intros c. eapply mspecP_post; [apply (opnew_spec_c c (clb c ++ X) n Hn)|].
  intros p s mo H. exists c. eapply Hperm; [| exact H]. apply Permutation_middle.
Qed.

Lemma odelete_spec : forall X b, mspec (own (ob b ++ X)) (odelete raw_free b) (fun _ => own X).
Proof.
  intros X [p|]; cbn [ob app odelete].
  - unfold opdelete. apply own_free.
  - apply mspec_ret. intros s mo H; exact H.
Qed.

Lemma minify_call_spec : forall X data, zlength data <= MAX_INPUT ->
  mspecP (own X) (minify_call raw_malloc raw_free new_handler data) (fun _ => own X).
Proof.
  intros X data Hlen. unfold minify_call. cbv zeta.
  assert (Hn : 0 <= Z.of_nat (length data) <= OPNEW_MAX) by (unfold OPNEW_MAX, zlength, MAX_INPUT in *; lia).
  eapply mspecP_bind with (Q1 := fun b => own (ob b ++ X)).
  { destruct (Z.of_nat (length data) =? 0).
    - apply mspecP_ret. intros s mo H; exact H.
    - eapply mspecP_bind; [apply opnew_spec; exact Hn|]. intros p. apply mspecP_ret. intros s mo H; exact H. }
  intros b. destruct (unclosed data).
  - eapply mspecP_bind; [apply (opnew_spec (ob b ++ X) ERRSTR_BYTES); unfold ERRSTR_BYTES, OPNEW_MAX; lia|]. intros t.
    eapply mspecP_bind with (Q1 := fun b' => own (t :: ob b' ++ X)).
    { destruct (ERRMSG_LEN <=? Z.of_nat (length data)).
      - apply mspecP_ret. intros s mo H; exact H.
      - eapply mspecP_seq with (R := own (t :: X)).
        + apply mspec_mspecP. eapply mspec_pre; [apply (odelete_spec (t :: X) b)|].
          intros s mo H. eapply own_perm; [| exact H]. destruct b as [p|]; cbn [ob app]; [apply perm_swap| apply Permutation_refl].
        + intros _. eapply mspecP_bind; [apply (opnew_spec (t :: X) ERRMSG_LEN); unfold ERRMSG_LEN, OPNEW_MAX; lia|]. intros p'.
          apply mspecP_ret. intros s mo H. eapply own_perm; [| exact H]. cbn [ob app]. apply perm_swap. }
    intros b'. eapply mspecP_seq with (R := own (ob b' ++ X)).
    + apply mspec_mspecP. unfold opdelete. apply own_free.
    + intros _. apply mspec_mspecP. apply odelete_spec.
  - apply mspec_mspecP. apply odelete_spec.
Qed.

Lemma fuzz_one_spec : forall X data, zlength data <= MAX_INPUT ->
  mspecP (own X) (fuzz_one raw_malloc raw_free new_handler cl_get cl_set data) (fun _ => own X).
Proof.
  intros X data Hlen. unfold fuzz_one.
  eapply mspecP_seq; [apply client_init_spec|]. intros _.
  eapply mspecP_seq; [apply minify_call_spec; exact Hlen|]. intros _. apply mspecP_ret. intros s mo H; exact H.
Qed.

Lemma client_exit_spec : forall X, mspec (own X) (client_exit raw_free cl_get cl_set) (fun _ => own X).
Proof.
  intros X. unfold client_exit.
  eapply mspec_bind; [apply mspec_get|]. intros s0. cbn beta.
  destruct (cl_get s0) as [q|] eqn:E.
  - eapply mspec_seq with (R := ownc (Some q) X).
    + unfold opdelete. eapply mspec_pre; [apply (Hf (Some q) X q)|].
      intros s mo [-> [c H]]. pose proof (Hcl _ _ _ _ H) as Hc. rewrite E in Hc. subst c. exact H.
    + intros _. apply mspec_upd'. intros s mo H. exists None. cbn [clb app]. apply (Hset (Some q) None). exact H.
  - apply mspec_ret. intros s mo [_ H]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_spec : forall X n payload rc, zlength payload <= MAX_INPUT ->
  mspecP (own X) (run_calls (fuzz_one raw_malloc raw_free new_handler cl_get cl_set) emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc Hlen; cbn [run_calls].
  - apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply fuzz_one_spec; exact Hlen|]. intros rc'.
    eapply mspecP_seq; [apply mspec_mspecP; apply own_emit|]. intros _. apply IH. exact Hlen.
Qed.

Theorem target_run_spec : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspecP (own X) (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler cl_get cl_set) emit cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload Hlen. unfold target_run.
  eapply mspecP_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  { apply mspecP_if; intros _; [apply mspecP_ret; intros s mo H; exact H|].
    eapply mspecP_bind; [apply mspec_mspecP; apply own_malloc; unfold zlength; lia|]. intros [p|]; apply mspecP_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspec_mspecP; apply own_free|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspecP_ret; intros s mo H; exact H|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafe.
