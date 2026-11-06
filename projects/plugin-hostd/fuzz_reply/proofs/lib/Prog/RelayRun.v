From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract.
Import ListNotations.
Local Open Scope Z_scope.

(* The allocator requests of a run, in program order: what the resource form F counts. *)
Inductive rev : Type :=
| RMalloc (n : Z)       (* malloc (n), strndup's malloc, realloc (NULL, n) *)
| RFree (n : Z)         (* free of a live block of n bytes *)
| RRealloc (k n : Z).   (* realloc of a live block of k bytes to n bytes *)

Section Run.
Variable F : ResForm.

Definition rev_step (b : rf_R F) (e : rev) : rf_R F :=
  match e with
  | RMalloc n => rf_malloc F b n
  | RFree n => rf_free F b n
  | RRealloc k n => rf_realloc F b k n
  end.

(* The resource state after the requests tr, from b. *)
Definition run_tr (b : rf_R F) (tr : list rev) : rf_R F := fold_left rev_step tr b.

(* Each request that takes memory finds room in the state the earlier requests left. *)
Fixpoint room_run (b : rf_R F) (tr : list rev) : Prop :=
  match tr with
  | [] => True
  | e :: r =>
      match e with
      | RMalloc n => rf_room F b n
      | RRealloc _ n => rf_room F b n
      | RFree _ => True
      end /\ room_run (rev_step b e) r
  end.

Lemma run_tr_nil : forall b, run_tr b [] = b.
Proof using. reflexivity. Qed.

Lemma run_tr_cons : forall b e tr, run_tr b (e :: tr) = run_tr (rev_step b e) tr.
Proof using. reflexivity. Qed.

Lemma run_tr_app : forall b t1 t2, run_tr b (t1 ++ t2) = run_tr (run_tr b t1) t2.
Proof using. intros b t1 t2. unfold run_tr. apply fold_left_app. Qed.

Lemma room_run_app : forall t1 b t2,
    room_run b (t1 ++ t2) <-> room_run b t1 /\ room_run (run_tr b t1) t2.
Proof using.
  induction t1 as [|e t1 IH]; intros b t2; simpl.
  - tauto.
  - rewrite IH. unfold run_tr. simpl. tauto.
Qed.

Lemma room_run_concat : forall ts b,
    room_run b (concat ts) <->
    (fix go (b0 : rf_R F) (l : list (list rev)) : Prop :=
       match l with
       | [] => True
       | t :: l' => room_run b0 t /\ go (run_tr b0 t) l'
       end) b ts.
Proof.
  induction ts as [|t ts IH]; intros b; simpl.
  - tauto.
  - rewrite room_run_app, IH. tauto.
Qed.

End Run.
