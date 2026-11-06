(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFRT.
Import AX2. Import AX2B.
Definition is_kdisj (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Lemma mk_rt_kdisj : forall fk, mk_rt (List.filter is_kdisj fk) = mk_rt fk.
Proof.
  induction fk as [|K rest IH]; [reflexivity|]. destruct K; cbn [List.filter is_kdisj mk_rt]; try exact IH. rewrite IH. reflexivity.
Qed.
Definition kd_eqb (x y : kentry) : bool :=
  match x, y with
  | KDisj a1 n1 a2 n2, KDisj b1 m1 b2 m2 =>
      if Z.eqb (a_off a1) (a_off b1) then if Z.eqb (a_off a2) (a_off b2) then
      if expr_eqb n1 m1 then if expr_eqb n2 m2 then
      if expr_eqb (a_base a1) (a_base b1) then expr_eqb (a_base a2) (a_base b2) else false else false else false else false else false
  | _, _ => false
  end.
Lemma kd_eqb_eq : forall x y, kd_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x as [| | | | | | |[b1 o1] n1 [b2 o2] n2| |]; try discriminate. destruct y as [| | | | | | |[c1 p1] m1 [c2 p2] m2| |]; try discriminate.
  cbn [kd_eqb a_off a_base] in H.
  destruct (Z.eqb_spec o1 p1) as [->|]; [|discriminate]. destruct (Z.eqb_spec o2 p2) as [->|]; [|discriminate].
  destruct (expr_eqb n1 m1) eqn:E1; [|discriminate]. destruct (expr_eqb n2 m2) eqn:E2; [|discriminate].
  destruct (expr_eqb b1 c1) eqn:E3; [|discriminate].
  apply p_expr_eqb_eq in E1, E2, E3, H. subst. reflexivity.
Qed.
Fixpoint kl_eqb (a b : list kentry) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if kd_eqb x y then kl_eqb a' b' else false
  | _, _ => false
  end.
Lemma kl_eqb_eq : forall a b, kl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  destruct (kd_eqb x y) eqn:E; [|discriminate]. apply kd_eqb_eq in E. subst. f_equal. apply IH. exact H.
Qed.

Definition rtc : Type := option (list kentry * rtab).
Definition rtc_ok (c : rtc) : Prop := match c with Some (kd, rt) => rt = mk_rt kd | None => True end.
Definition get_rt (c : rtc) (fk : list kentry) : rtab * rtc :=
  let kd := List.filter is_kdisj fk in
  match c with
  | Some (kd', rt) => if kl_eqb kd kd' then (rt, c) else let rt' := mk_rt kd in (rt', Some (kd, rt'))
  | None => let rt' := mk_rt kd in (rt', Some (kd, rt'))
  end.
Lemma get_rt_spec : forall c fk, rtc_ok c -> fst (get_rt c fk) = mk_rt fk /\ rtc_ok (snd (get_rt c fk)).
Proof.
  intros c fk H. unfold get_rt. destruct c as [[kd' rt]|].
  - destruct (kl_eqb (List.filter is_kdisj fk) kd') eqn:E; cbn [fst snd].
    + apply kl_eqb_eq in E. cbn [rtc_ok] in H. subst kd'. split; [rewrite H; apply mk_rt_kdisj | exact H].
    + split; [apply mk_rt_kdisj | reflexivity].
  - cbn [fst snd]. split; [apply mk_rt_kdisj | reflexivity].
Qed.
Definition mkbc_c (c : rtc) (fk : list kentry) : bctx * rtc :=
  let ffk := facts_of fk in let ri := mk_ri ffk in
  let rc := get_rt c fk in
  (BC fk ffk (sum_factsB (BC fk ffk [] ri (fst rc)) fk) ri (fst rc), snd rc).
Lemma mkbc_c_spec : forall c fk, rtc_ok c -> fst (mkbc_c c fk) = mkbc fk /\ rtc_ok (snd (mkbc_c c fk)).
Proof.
  intros c fk H. unfold mkbc_c. destruct (get_rt_spec c fk H) as [E1 E2]. cbn [fst snd]. rewrite E1. split; [reflexivity|exact E2].
Qed.
End CXFRT.
