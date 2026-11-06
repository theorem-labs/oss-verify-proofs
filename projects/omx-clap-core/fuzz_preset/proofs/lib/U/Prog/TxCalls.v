From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Export TxModel.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Variable F : ResForm.

Definition tx_step (b : rf_R F) (cap c : Z) : rf_R F :=
  if cap =? 0 then rf_malloc F b c else rf_realloc F b cap c.

Definition tx_next (b : rf_R F) (len cap n : Z) : rf_R F :=
  if len + n + 1 <=? cap then b else tx_step b cap (2 * (len + n + 1)).

Fixpoint tx_fold (b : rf_R F) (len cap : Z) (ns : list Z) : rf_R F :=
  match ns with
  | [] => b
  | n :: r => tx_fold (tx_next b len cap n) (len + n) (tx_cap1 len cap n) r
  end.

Fixpoint tx_rooms (b : rf_R F) (len cap : Z) (ns : list Z) : Prop :=
  match ns with
  | [] => True
  | n :: r => (cap < len + n + 1 -> rf_room F b (2 * (len + n + 1))) /\
              tx_rooms (tx_next b len cap n) (len + n) (tx_cap1 len cap n) r
  end.

Lemma tx_fold_app : forall l1 l2 b len cap,
  tx_fold b len cap (l1 ++ l2) = tx_fold (tx_fold b len cap l1) (len + zsum l1) (tx_capf len cap l1) l2.
Proof.
  induction l1 as [|n l1 IH]; intros l2 b len cap; cbn [app tx_fold tx_capf zsum].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. lia.
Qed.

Lemma tx_rooms_app : forall l1 l2 b len cap,
  tx_rooms b len cap (l1 ++ l2) <->
  tx_rooms b len cap l1 /\ tx_rooms (tx_fold b len cap l1) (len + zsum l1) (tx_capf len cap l1) l2.
Proof.
  induction l1 as [|n l1 IH]; intros l2 b len cap; cbn [app tx_rooms tx_fold tx_capf zsum].
  - rewrite Z.add_0_r. tauto.
  - rewrite IH. replace (len + n + zsum l1) with (len + (n + zsum l1)) by lia. tauto.
Qed.

Lemma tx_rooms_mid : forall l1 l2 l3 b len cap, tx_rooms b len cap (l1 ++ l2 ++ l3) ->
  tx_rooms (tx_fold b len cap l1) (len + zsum l1) (tx_capf len cap l1) l2.
Proof.
  intros l1 l2 l3 b len cap H. apply tx_rooms_app in H. destruct H as [_ H]. apply tx_rooms_app in H. exact (proj1 H).
Qed.

Lemma tx_fold_one : forall b len cap n, tx_fold b len cap [n] = tx_next b len cap n.
Proof. reflexivity. Qed.

End R.
