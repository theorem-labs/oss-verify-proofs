From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT.
Import ListNotations.
Local Open Scope Z_scope.

Section Names.
Variables (R P : Type) (pdef : P).
Variable rmal : R -> Z -> R.
Variable rfre : R -> Z -> P -> R.
Variable rrea : R -> Z -> Z -> P -> P -> R.
Variable rroom : R -> Z -> Prop.

Definition ad_eq (qs1 qs2 : list P) (a1 a2 : addr P) : Prop := resolve P pdef qs1 a1 = resolve P pdef qs2 a2.

Inductive ev_rel (qs1 qs2 : list P) : rev P -> rev P -> Prop :=
| er_mal : forall n, ev_rel qs1 qs2 (RMalloc n) (RMalloc n)
| er_fre : forall n a1 a2, ad_eq qs1 qs2 a1 a2 -> ev_rel qs1 qs2 (RFree n a1) (RFree n a2)
| er_rea : forall k n a1 a2, ad_eq qs1 qs2 a1 a2 -> ev_rel qs1 qs2 (RRealloc k n a1) (RRealloc k n a2).

Definition tr_rel (qs1 qs2 : list P) : list (rev P) -> list (rev P) -> Prop := Forall2 (ev_rel qs1 qs2).

Definition ret_agree (qs1 qs2 : list P) (j1 j2 m : nat) : Prop :=
  forall k, (k < m)%nat -> nth (j1 + k) qs1 pdef = nth (j2 + k) qs2 pdef.

Lemma tr_rel_nret : forall qs1 qs2 t1 t2, tr_rel qs1 qs2 t1 t2 -> nret P t1 = nret P t2.
Proof.
  intros qs1 qs2 t1 t2 H. induction H as [|e1 e2 t1 t2 He _ IH]; [reflexivity|].
  simpl. rewrite IH. destruct He; reflexivity.
Qed.

Lemma ret_agree_step : forall qs1 qs2 j1 j2 m, ret_agree qs1 qs2 j1 j2 (S m) ->
  nth j1 qs1 pdef = nth j2 qs2 pdef /\ ret_agree qs1 qs2 (S j1) (S j2) m.
Proof.
  intros qs1 qs2 j1 j2 m H. split.
  - specialize (H 0%nat ltac:(lia)). rewrite !Nat.add_0_r in H. exact H.
  - intros k Hk. specialize (H (S k) ltac:(lia)). replace (S j1 + k)%nat with (j1 + S k)%nat by lia.
    replace (S j2 + k)%nat with (j2 + S k)%nat by lia. exact H.
Qed.

Lemma run_rel : forall qs1 qs2 t1 t2 b j1 j2,
    tr_rel qs1 qs2 t1 t2 -> ret_agree qs1 qs2 j1 j2 (nret P t2) ->
    run_from R P pdef rmal rfre rrea qs1 b j1 t1 = run_from R P pdef rmal rfre rrea qs2 b j2 t2.
Proof.
  intros qs1 qs2 t1 t2 b j1 j2 H. revert b j1 j2.
  induction H as [|e1 e2 t1 t2 He _ IH]; intros b j1 j2 Hr; [reflexivity|].
  destruct He as [n|n a1 a2 Ha|k n a1 a2 Ha]; simpl in *.
  - destruct (ret_agree_step _ _ _ _ _ Hr) as [_ Hr']. apply IH, Hr'.
  - unfold ad_eq in Ha. rewrite Ha. apply IH, Hr.
  - destruct (ret_agree_step _ _ _ _ _ Hr) as [Hq Hr']. unfold ad_eq in Ha. rewrite Ha, Hq. apply IH, Hr'.
Qed.

Lemma room_rel : forall qs1 qs2 t1 t2 b j1 j2,
    tr_rel qs1 qs2 t1 t2 -> ret_agree qs1 qs2 j1 j2 (nret P t2) ->
    (room_from R P pdef rmal rfre rrea rroom qs1 b j1 t1 <-> room_from R P pdef rmal rfre rrea rroom qs2 b j2 t2).
Proof.
  intros qs1 qs2 t1 t2 b j1 j2 H. revert b j1 j2.
  induction H as [|e1 e2 t1 t2 He _ IH]; intros b j1 j2 Hr; [tauto|].
  destruct He as [n|n a1 a2 Ha|k n a1 a2 Ha]; simpl in *.
  - destruct (ret_agree_step _ _ _ _ _ Hr) as [_ Hr']. rewrite (IH _ _ _ Hr'). tauto.
  - unfold ad_eq in Ha. rewrite Ha. apply IH, Hr.
  - destruct (ret_agree_step _ _ _ _ _ Hr) as [Hq Hr']. unfold ad_eq in Ha. rewrite Ha, Hq.
    rewrite (IH _ _ _ Hr'). tauto.
Qed.

Lemma tr_rel_app : forall qs1 qs2 a1 a2 b1 b2,
    tr_rel qs1 qs2 a1 a2 -> tr_rel qs1 qs2 b1 b2 -> tr_rel qs1 qs2 (a1 ++ b1) (a2 ++ b2).
Proof. intros. apply Forall2_app; assumption. Qed.

Lemma tr_rel_concat : forall qs1 qs2 l1 l2,
    Forall2 (tr_rel qs1 qs2) l1 l2 -> tr_rel qs1 qs2 (concat l1) (concat l2).
Proof.
  intros qs1 qs2 l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; [constructor|].
  simpl. apply tr_rel_app; assumption.
Qed.

Lemma ret_agree_embed : forall pre qc post k m,
    (k + m <= length qc)%nat -> ret_agree (pre ++ qc ++ post) qc (length pre + k) k m.
Proof.
  intros pre qc post k m Hm i Hi.
  rewrite app_nth2 by lia. replace (length pre + k + i - length pre)%nat with (k + i)%nat by lia.
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma ad_eq_ret_embed : forall pre qc post i,
    (i < length qc)%nat -> ad_eq (pre ++ qc ++ post) qc (Ret (length pre + i)) (Ret i).
Proof.
  intros pre qc post i Hi. unfold ad_eq. simpl.
  rewrite app_nth2 by lia. replace (length pre + i - length pre)%nat with i by lia.
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma ad_eq_known : forall qs1 qs2 p, ad_eq qs1 qs2 (Known p) (Known p).
Proof. reflexivity. Qed.

End Names.
