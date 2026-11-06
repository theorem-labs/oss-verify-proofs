From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

#[warnings="-register-all"]
Inductive jv : Type :=
| JNull
| JFalse
| JTrue
| JNum (txt : list Z) (bits : Z)
| JStr (s : list Z)
| JArr (items : list jv)
| JObj (members : list (list Z * jv)).

Definition tag (t : jv) : Z :=
  match t with
  | JNull => 0
  | JFalse => 1
  | JTrue => 2
  | JNum _ _ => 3
  | JStr _ => 4
  | JArr _ => 5
  | JObj _ => 6
  end.

Fixpoint size (t : jv) : nat :=
  match t with
  | JArr items => S (list_sum (map size items))
  | JObj members => S (list_sum (map (fun '(_, v) => size v) members))
  | _ => 1%nat
  end.

Fixpoint depth (t : jv) : nat :=
  match t with
  | JArr items => S (list_max (map depth items))
  | JObj members => S (list_max (map (fun '(_, v) => depth v) members))
  | _ => 0%nat
  end.

Fixpoint pj_set_model (ms : list (list Z * jv)) (kname : list Z) (tv : jv) : list (list Z * jv) :=
  match ms with
  | [] => [(kname, tv)]
  | (k, v) :: r => if list_eq_dec Z.eq_dec k kname then (k, tv) :: r else (k, v) :: pj_set_model r kname tv
  end.

Definition jv_ind' (P : jv -> Prop)
  (HNull : P JNull) (HFalse : P JFalse) (HTrue : P JTrue)
  (HNum : forall txt bits, P (JNum txt bits))
  (HStr : forall s, P (JStr s))
  (HArr : forall items, Forall P items -> P (JArr items))
  (HObj : forall members, Forall (fun m => P (snd m)) members -> P (JObj members)) :
  forall t, P t :=
  fix go (t : jv) : P t :=
    match t return P t with
    | JNull => HNull
    | JFalse => HFalse
    | JTrue => HTrue
    | JNum txt bits => HNum txt bits
    | JStr s => HStr s
    | JArr items =>
      HArr items
        ((fix gl (l : list jv) : Forall P l :=
            match l return Forall P l with
            | [] => @Forall_nil jv P
            | u :: r => @Forall_cons jv P u r (go u) (gl r)
            end) items)
    | JObj members =>
      HObj members
        ((fix gm (l : list (list Z * jv)) : Forall (fun m => P (snd m)) l :=
            match l return Forall (fun m => P (snd m)) l with
            | [] => @Forall_nil (list Z * jv) (fun m => P (snd m))
            | (nm, u) :: r => @Forall_cons (list Z * jv) (fun m => P (snd m)) (nm, u) r (go u) (gm r)
            end) members)
    end.

Lemma size_pos : forall t, (1 <= size t)%nat.
Proof. destruct t; simpl; auto with arith. Qed.

Lemma depth_item : forall items u, In u items -> (depth u < depth (JArr items))%nat.
Proof.
  intros items u H. simpl. apply Nat.lt_succ_r.
  induction items as [|a r IH]; simpl in *; [contradiction|].
  destruct H as [<-|H]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma depth_member : forall members nm u, In (nm, u) members -> (depth u < depth (JObj members))%nat.
Proof.
  intros members nm u H. simpl. apply Nat.lt_succ_r.
  induction members as [|[a v] r IH]; simpl in *; [contradiction|].
  destruct H as [H|H]; [inversion H; subst; apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.
