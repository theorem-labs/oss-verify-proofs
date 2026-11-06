(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record ast : Type := AST {
  a_on   : bool ;                 (* [comment removed for export] *)
  a_rgs  : list region ;          (* [comment removed for export] *)
  a_fcts : list fact ;            (* [comment removed for export] *)
  a_own  : list (lin * lin) ;     (* [comment removed for export] *)
  a_dep  : lin * lin ;            (* [comment removed for export] *)
  a_nl   : lin ;                  (* [comment removed for export] *)
  a_live : list (lin * lin) ;     (* [comment removed for export] *)
  a_pri  : list lin               (* [comment removed for export] *)
}.

Definition ast0 : ast := AST false [] [] [] (lc0, lc0) lc0 [] [].

(* [comment removed for export] *)
Definition a_ext (a : ast) : list (lin * lin) := List.map (fun R => (rg_base R, rg_size R)) (a_rgs a).
Definition ext_rg (b z : lin) : region := RG b z RW TEmpty.
Definition ext_add (a : ast) (b z : lin) : ast :=
  AST (a_on a) (ext_rg b z :: a_rgs a) (a_fcts a) (a_own a) (a_dep a) (a_nl a) (a_live a) (a_pri a).
Fixpoint drop_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with [], _ => [] | _ :: r, O => r | x :: r, Datatypes.S i' => x :: drop_nth i' r end.
Definition ext_drop (a : ast) (i : nat) : ast :=
  AST (a_on a) (drop_nth i (a_rgs a)) (a_fcts a) (a_own a) (a_dep a) (a_nl a) (a_live a) (a_pri a).
Lemma In_drop_nth : forall {A} i (l : list A) x, In x (drop_nth i l) -> In x l.
Proof. intros A i l. revert i. induction l as [|y r IH]; intros [|i] x H; cbn in *; auto. destruct H as [H|H]; [left; exact H | right; exact (IH i x H)]. Qed.
Lemma a_ext_add : forall a b z, a_ext (ext_add a b z) = (b, z) :: a_ext a.
Proof. reflexivity. Qed.
Lemma In_ext_drop : forall a i p, In p (a_ext (ext_drop a i)) -> In p (a_ext a).
Proof.
  intros a i p H. unfold a_ext, ext_drop in *. cbn [a_rgs] in H. apply in_map_iff in H as (R0 & <- & HR).
  exact (in_map (fun R => (rg_base R, rg_size R)) _ R0 (In_drop_nth i _ R0 HR)).
Qed.
Definition anil (a : ast) : bool := negb (a_on a).

(* [comment removed for export] *)
Fixpoint tree_eqb {A} (f : A -> A -> bool) (t u : tree A) : bool :=
  match t, u with
  | TEmpty, TEmpty => true
  | TNode l v r, TNode l' v' r' =>
      (tree_eqb f l l' && match v, v' with Some x, Some y => f x y | None, None => true | _, _ => false end && tree_eqb f r r')%bool
  | _, _ => false
  end.
Lemma tree_eqb_eq : forall {A} (f : A -> A -> bool), (forall x y, f x y = true -> x = y) -> forall t u, tree_eqb f t u = true -> t = u.
Proof.
  intros A f Hf t. induction t as [|l IHl v r IHr]; intros [|l' v' r'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hl Hv].
  rewrite (IHl l' Hl), (IHr r' Hr). destruct v as [x|], v' as [y|]; try discriminate; [rewrite (Hf x y Hv) | ]; reflexivity.
Qed.
Definition rkind_eqb (a b : rkind) : bool :=
  match a, b with RW, RW | RO, RO | RZ, RZ | RI, RI | RT, RT => true | _, _ => false end.
Lemma rkind_eqb_eq : forall a b, rkind_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition rg_eqb (R S : region) : bool :=
  (lin_eqb (rg_base R) (rg_base S) && lin_eqb (rg_size R) (rg_size S) && rkind_eqb (rg_kind R) (rg_kind S) &&
   tree_eqb bval_eqb (rg_cont R) (rg_cont S))%bool.
Lemma rg_eqb_eq : forall R S, rg_eqb R S = true -> R = S.
Proof.
  intros [b z k c] [b' z' k' c'] H. unfold rg_eqb in H. cbn [rg_base rg_size rg_kind rg_cont] in H.
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hz].
  rewrite (lin_eqb_eq _ _ Hb), (lin_eqb_eq _ _ Hz), (rkind_eqb_eq _ _ Hk), (tree_eqb_eq bval_eqb bval_eqb_eq _ _ Hc). reflexivity.
Qed.
Fixpoint list_eqb {A} (f : A -> A -> bool) (l m : list A) : bool :=
  match l, m with [], [] => true | x :: l', y :: m' => (f x y && list_eqb f l' m')%bool | _, _ => false end.
Lemma list_eqb_eq : forall {A} (f : A -> A -> bool), (forall x y, f x y = true -> x = y) -> forall l m, list_eqb f l m = true -> l = m.
Proof.
  intros A f Hf l. induction l as [|x l IH]; intros [|y m] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hf x y H1), (IH m H2). reflexivity.
Qed.
Definition pair_eqb (p q : lin * lin) : bool := (lin_eqb (fst p) (fst q) && lin_eqb (snd p) (snd q))%bool.
Lemma pair_eqb_eq : forall p q, pair_eqb p q = true -> p = q.
Proof. intros [a b] [c d] H. unfold pair_eqb in H. cbn in H. apply andb_prop in H as [H1 H2]. rewrite (lin_eqb_eq _ _ H1), (lin_eqb_eq _ _ H2). reflexivity. Qed.

Definition aeqb (x y : ast) : bool :=
  (Bool.eqb (a_on x) (a_on y) && list_eqb rg_eqb (a_rgs x) (a_rgs y) && list_eqb fact_eqb (a_fcts x) (a_fcts y) &&
   list_eqb pair_eqb (a_own x) (a_own y) && pair_eqb (a_dep x) (a_dep y) && lin_eqb (a_nl x) (a_nl y) &&
   list_eqb pair_eqb (a_live x) (a_live y) && list_eqb lin_eqb (a_pri x) (a_pri y))%bool.
Lemma aeqb_eq : forall x y, aeqb x y = true -> x = y.
Proof.
  intros [o r f w d n l p] [o' r' f' w' d' n' l' p'] H. unfold aeqb in H. cbn [a_on a_rgs a_fcts a_own a_dep a_nl a_live a_pri] in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?] end.
  repeat match goal with
         | H : Bool.eqb _ _ = true |- _ => apply eqb_prop in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
         | H : list_eqb rg_eqb _ _ = true |- _ => apply (list_eqb_eq rg_eqb rg_eqb_eq) in H
         | H : list_eqb fact_eqb _ _ = true |- _ => apply (list_eqb_eq fact_eqb fact_eqb_eq) in H
         | H : list_eqb pair_eqb _ _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in H
         | H : list_eqb lin_eqb _ _ = true |- _ => apply (list_eqb_eq lin_eqb lin_eqb_eq) in H
         | H : pair_eqb _ _ = true |- _ => apply pair_eqb_eq in H
         | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
         end.
  subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pwf (n : positive) (p : lin * lin) : bool := (lwf n (fst p) && lwf n (snd p))%bool.
Definition awf (n : positive) (a : ast) : bool :=
  (lwf n (a_nl a) && forallb (rwf n) (a_rgs a) && forallb (fwf n) (a_fcts a) && forallb (pwf n) (a_own a) && pwf n (a_dep a) &&
   forallb (pwf n) (a_live a) && forallb (lwf n) (a_pri a))%bool.

Lemma lwf_mono' : forall n n' l, (n <= n')%positive -> lwf n l = true -> lwf n' l = true.
Proof.
  intros n n' [c t] Hn H. unfold lwf in *. cbn [l_t] in *. rewrite forallb_forall in *. intros [x k] Hx.
  specialize (H _ Hx). apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.
Lemma pwf_mono : forall n n' p, (n <= n')%positive -> pwf n p = true -> pwf n' p = true.
Proof. intros n n' [a b] Hn H. unfold pwf in *. cbn in *. apply andb_prop in H as [H1 H2]. rewrite (lwf_mono' n n' a Hn H1), (lwf_mono' n n' b Hn H2). reflexivity. Qed.
Lemma bwf_mono : forall n n' v, (n <= n')%positive -> bwf n v = true -> bwf n' v = true.
Proof. intros n n' [b|l j] Hn H; [reflexivity | exact (lwf_mono' n n' l Hn H)]. Qed.
Lemma tforall_mono : forall {A} (f g : positive -> A -> bool) t, (forall p x, f p x = true -> g p x = true) -> tforall f t = true -> tforall g t = true.
Proof.
  intros A f g t Hfg. unfold tforall. generalize (fun p : positive => p). induction t as [|l IHl v r IHr]; intros k H; [reflexivity|].
  cbn [tforall_acc] in H |- *. apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hv Hl].
  rewrite (IHl _ Hl), (IHr _ Hr). destruct v; [rewrite (Hfg _ _ Hv) | ]; reflexivity.
Qed.
Lemma rwf_mono : forall n n' R, (n <= n')%positive -> rwf n R = true -> rwf n' R = true.
Proof.
  intros n n' R Hn H. unfold rwf in *. apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hb Hs].
  rewrite (lwf_mono' n n' _ Hn Hb), (lwf_mono' n n' _ Hn Hs). cbn. apply (tforall_mono (fun _ v => bwf n v)); [|exact Hc].
  intros p v Hv. exact (bwf_mono n n' v Hn Hv).
Qed.
Lemma forallb_mono' : forall {A} (f g : A -> bool) l, (forall x, f x = true -> g x = true) -> forallb f l = true -> forallb g l = true.
Proof. intros A f g l Hfg H. rewrite forallb_forall in *. intros x Hx. exact (Hfg x (H x Hx)). Qed.
Lemma fwf_mono : forall n n' f, (n <= n')%positive -> fwf n f = true -> fwf n' f = true.
Proof.
  intros n n' [c a b tk|l lo hi|l k r|l m v|x v j|x bs] Hn H; cbn [fwf] in *;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end;
    repeat (apply andb_true_intro; split); try (eapply lwf_mono'; eassumption).
  apply (forallb_mono' (fun p : lin * Z => lwf n (fst p)) (fun p : lin * Z => lwf n' (fst p)) bs); [|eassumption]. intros p Hp. eapply lwf_mono'; eassumption.
Qed.
Lemma forallb_mono : forall {A} (f g : A -> bool) l, (forall x, f x = true -> g x = true) -> forallb f l = true -> forallb g l = true.
Proof. intros A f g l Hfg H. rewrite forallb_forall in *. intros x Hx. exact (Hfg x (H x Hx)). Qed.
Lemma awf_mono : forall n n' a, (n <= n')%positive -> awf n a = true -> awf n' a = true.
Proof.
  intros n n' a Hn H. unfold awf in *.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  rewrite (lwf_mono' n n' _ Hn H0), (forallb_mono _ _ _ (fun R => rwf_mono n n' R Hn) H1), (forallb_mono _ _ _ (fun f => fwf_mono n n' f Hn) H2),
          (forallb_mono _ _ _ (fun p => pwf_mono n n' p Hn) H3), (pwf_mono n n' _ Hn H4), (forallb_mono _ _ _ (fun p => pwf_mono n n' p Hn) H5),
          (forallb_mono _ _ _ (fun l => lwf_mono' n n' l Hn) H6).
  reflexivity.
Qed.

Lemma awf_nl : forall n a, awf n a = true -> lwf n (a_nl a) = true.
Proof.
  intros n a H. unfold awf in H. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H _] end. exact H.
Qed.
