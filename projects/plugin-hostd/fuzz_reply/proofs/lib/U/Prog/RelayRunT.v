From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Local Open Scope Z_scope.

(* The allocator requests of a run, in program order, for a resource form whose free and realloc take the block's
   address (ContractT.ResFormT). An address in a trace is a start-state pointer (Known) or the address returned by
   the i-th RMalloc / RRealloc of the same run (Ret i, 0-based). Generic in the form's operations and the pointer
   type, so a trace function does not depend on which form a unit uses. *)
Section RunT.
Variables (R P : Type) (pdef : P).
Variable rmal : R -> Z -> R.
Variable rfre : R -> Z -> P -> R.
Variable rrea : R -> Z -> Z -> P -> P -> R.
Variable rroom : R -> Z -> Prop.

Inductive addr : Type :=
| Known (p : P)
| Ret (i : nat).

Inductive rev : Type :=
| RMalloc (n : Z)               (* malloc (n), strndup's malloc, realloc (NULL, n) *)
| RFree (n : Z) (a : addr)      (* free of the live block of n bytes at a *)
| RRealloc (k n : Z) (a : addr). (* realloc of the live block of k bytes at a to n bytes *)

(* Requests that return an address. *)
Definition rets (e : rev) : nat := match e with RFree _ _ => 0 | _ => 1 end.
Definition nret (tr : list rev) : nat := fold_right (fun e k => (rets e + k)%nat) 0%nat tr.

Definition resolve (qs : list P) (a : addr) : P :=
  match a with Known p => p | Ret i => nth i qs pdef end.

(* The fold from resource state b, with j the index of the next returned address in qs. *)
Fixpoint run_from (qs : list P) (b : R) (j : nat) (tr : list rev) : R :=
  match tr with
  | [] => b
  | RMalloc n :: r => run_from qs (rmal b n) (S j) r
  | RFree n a :: r => run_from qs (rfre b n (resolve qs a)) j r
  | RRealloc k n a :: r => run_from qs (rrea b k n (resolve qs a) (nth j qs pdef)) (S j) r
  end.

Definition run_tr (qs : list P) (b : R) (tr : list rev) : R := run_from qs b 0 tr.

(* Each request that takes memory finds room in the state the earlier requests left. *)
Fixpoint room_from (qs : list P) (b : R) (j : nat) (tr : list rev) : Prop :=
  match tr with
  | [] => True
  | RMalloc n :: r => rroom b n /\ room_from qs (rmal b n) (S j) r
  | RFree n a :: r => room_from qs (rfre b n (resolve qs a)) j r
  | RRealloc k n a :: r => rroom b n /\ room_from qs (rrea b k n (resolve qs a) (nth j qs pdef)) (S j) r
  end.

Definition room_run (qs : list P) (b : R) (tr : list rev) : Prop := room_from qs b 0 tr.

(* Ret i refers only to an address returned earlier in the same trace. *)
Fixpoint wf_from (j : nat) (tr : list rev) : Prop :=
  match tr with
  | [] => True
  | e :: r =>
      match e with
      | RMalloc _ => True
      | RFree _ a | RRealloc _ _ a => match a with Known _ => True | Ret i => (i < j)%nat end
      end /\ wf_from (j + rets e) r
  end.

Definition wf_tr (tr : list rev) : Prop := wf_from 0 tr.

(* Renumbering a callee's trace into a caller's: its Ret i becomes Ret (s + i). *)
Definition shift_addr (s : nat) (a : addr) : addr := match a with Known p => Known p | Ret i => Ret (s + i) end.
Definition shift_ev (s : nat) (e : rev) : rev :=
  match e with
  | RMalloc n => RMalloc n
  | RFree n a => RFree n (shift_addr s a)
  | RRealloc k n a => RRealloc k n (shift_addr s a)
  end.
Definition shift_tr (s : nat) (tr : list rev) : list rev := map (shift_ev s) tr.

Lemma nret_app : forall t1 t2, nret (t1 ++ t2) = (nret t1 + nret t2)%nat.
Proof using. induction t1 as [|e t1 IH]; intros t2; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma nret_shift : forall s tr, nret (shift_tr s tr) = nret tr.
Proof using. induction tr as [|e tr IH]; simpl; [reflexivity | rewrite IH; destruct e; reflexivity]. Qed.

Lemma run_from_app : forall qs t1 t2 b j,
    run_from qs b j (t1 ++ t2) = run_from qs (run_from qs b j t1) (j + nret t1) t2.
Proof using.
  intros qs t1 t2. induction t1 as [|e t1 IH]; intros b j; simpl.
  - now rewrite Nat.add_0_r.
  - destruct e; simpl; rewrite IH; f_equal; lia.
Qed.

Lemma room_from_app : forall qs t1 t2 b j,
    room_from qs b j (t1 ++ t2) <-> room_from qs b j t1 /\ room_from qs (run_from qs b j t1) (j + nret t1) t2.
Proof using.
  intros qs t1 t2. induction t1 as [|e t1 IH]; intros b j; simpl.
  - rewrite Nat.add_0_r. tauto.
  - destruct e; simpl; rewrite IH; replace (j + S (nret t1))%nat with (S j + nret t1)%nat by lia; tauto.
Qed.

(* A callee's trace run inside a caller's address list: pre is what the caller's earlier requests returned. *)
Lemma resolve_shift : forall pre qc post a j,
    match a with Known _ => True | Ret i => (i < length qc)%nat end -> length pre = j ->
    resolve (pre ++ qc ++ post) (shift_addr j a) = resolve qc a.
Proof using.
  intros pre qc post [p|i] j Hi Hj; simpl; [reflexivity|].
  subst j. rewrite app_nth2 by lia. replace (length pre + i - length pre)%nat with i by lia.
  now rewrite app_nth1.
Qed.

Lemma run_shift : forall pre qc post tc b j k,
    wf_from k tc -> (k + nret tc <= length qc)%nat -> length pre = j ->
    run_from (pre ++ qc ++ post) b (j + k) (shift_tr j tc) = run_from qc b k tc.
Proof using.
  intros pre qc post tc. induction tc as [|e tc IH]; intros b j k Hw Hn Hj; simpl; [reflexivity|].
  destruct Hw as [He Hw]. destruct e as [n|n a|kk n a]; simpl in *.
  - replace (S (j + k)) with (j + S k)%nat by lia.
    apply IH; [replace (S k) with (k + 1)%nat by lia; exact Hw | lia | exact Hj].
  - rewrite resolve_shift with (j := j) by (auto; destruct a; auto; lia).
    apply IH; [rewrite Nat.add_0_r in Hw; exact Hw | lia | exact Hj].
  - rewrite resolve_shift with (j := j) by (auto; destruct a; auto; lia).
    replace (nth (j + k) (pre ++ qc ++ post) pdef) with (nth k qc pdef).
    + replace (S (j + k)) with (j + S k)%nat by lia.
      apply IH; [replace (S k) with (k + 1)%nat by lia; exact Hw | lia | exact Hj].
    + subst j. rewrite app_nth2 by lia. replace (length pre + k - length pre)%nat with k by lia.
      rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma room_shift : forall pre qc post tc b j k,
    wf_from k tc -> (k + nret tc <= length qc)%nat -> length pre = j ->
    room_from (pre ++ qc ++ post) b (j + k) (shift_tr j tc) <-> room_from qc b k tc.
Proof using.
  intros pre qc post tc. induction tc as [|e tc IH]; intros b j k Hw Hn Hj; simpl; [tauto|].
  destruct Hw as [He Hw]. destruct e as [n|n a|kk n a]; simpl in *.
  - replace (S (j + k)) with (j + S k)%nat by lia.
    rewrite (IH _ j (S k)); [tauto | replace (S k) with (k + 1)%nat by lia; exact Hw | lia | exact Hj].
  - rewrite resolve_shift with (j := j) by (auto; destruct a; auto; lia).
    apply IH; [rewrite Nat.add_0_r in Hw; exact Hw | lia | exact Hj].
  - rewrite resolve_shift with (j := j) by (auto; destruct a; auto; lia).
    replace (nth (j + k) (pre ++ qc ++ post) pdef) with (nth k qc pdef).
    + replace (S (j + k)) with (j + S k)%nat by lia.
      rewrite (IH _ j (S k)); [tauto | replace (S k) with (k + 1)%nat by lia; exact Hw | lia | exact Hj].
    + subst j. rewrite app_nth2 by lia. replace (length pre + k - length pre)%nat with k by lia.
      rewrite app_nth1 by lia. reflexivity.
Qed.

End RunT.

Arguments Known {P} p.
Arguments Ret {P} i.
Arguments RMalloc {P} n.
Arguments RFree {P} n a.
Arguments RRealloc {P} k n a.
