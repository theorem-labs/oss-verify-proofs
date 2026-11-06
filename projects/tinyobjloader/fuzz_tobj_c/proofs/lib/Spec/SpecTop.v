(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition post_open_traces (p : list byte) (fs : Fs) : list (list event) :=
  if is_dot p then [die fs (msg_read_error p)]
  else match fs_lookup fs p with
       | Some F => file_traces fs F
       | None => []
       end.

Lemma spec_traces_argc2 : forall argv fs, length argv = 2%nat ->
  spec_traces argv fs =
  die fs (msg_cannot_open (nth 1 argv []))
  :: if open_may_succeed_b (nth 1 argv []) fs then post_open_traces (nth 1 argv []) fs else [].
Proof. intros argv fs H. unfold spec_traces. rewrite H. reflexivity. Qed.

Lemma spec_traces_argc_ne2 : forall argv fs, length argv <> 2%nat ->
  spec_traces argv fs = [die fs (msg_usage (hd [] argv))].
Proof.
  intros argv fs H. unfold spec_traces. destruct (Nat.eqb_spec (length argv) 2); [exfalso; lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Spec_cases : forall inp t, Spec inp t ->
  let argv := in_argv inp in let fs := in_fs inp in let p := nth 1 argv [] in
  (length argv <> 2%nat /\ t = die fs (msg_usage (hd [] argv)))
  \/ (length argv = 2%nat /\ t = die fs (msg_cannot_open p))
  \/ (length argv = 2%nat /\ open_may_succeed p fs /\ In t (post_open_traces p fs)).
Proof.
  intros inp t H. unfold Spec in H. cbn zeta.
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [E|NE].
  - rewrite (spec_traces_argc2 _ _ E) in H. destruct H as [<-|H]; [right; left; auto|].
    destruct (open_may_succeed_b (nth 1 (in_argv inp) []) (in_fs inp)) eqn:Eo; [|destruct H].
    right; right. split; [exact E|]. split; [apply open_may_succeed_b_iff; exact Eo | exact H].
  - rewrite (spec_traces_argc_ne2 _ _ NE) in H. destruct H as [<-|[]]. left. auto.
Qed.

(* [comment removed for export] *)
Lemma Spec_nonempty : forall inp, exists t, Spec inp t.
Proof.
  intros inp. unfold Spec.
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [E|NE].
  - exists (die (in_fs inp) (msg_cannot_open (nth 1 (in_argv inp) []))). apply spec_cannot_open. exact E.
  - exists (die (in_fs inp) (msg_usage (hd [] (in_argv inp)))). apply spec_usage. exact NE.
Qed.

Lemma post_open_in_spec : forall argv fs t, length argv = 2%nat -> open_may_succeed (nth 1 argv []) fs ->
  In t (post_open_traces (nth 1 argv []) fs) -> In t (spec_traces argv fs).
Proof.
  intros argv fs t H Ho Ht. rewrite (spec_traces_argc2 _ _ H). right.
  rewrite (proj2 (open_may_succeed_b_iff _ _) Ho). exact Ht.
Qed.
