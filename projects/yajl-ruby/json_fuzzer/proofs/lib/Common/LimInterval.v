(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad LimFitBase LimFitVm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition clear_of (lo hi : Z) (e : word * word) : Prop :=
  0 < bv_unsigned (snd e)
  /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= two_pow_64
  /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= lo \/ hi <= bv_unsigned (fst e)).

Lemma Z_to_bv_unsigned_id : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.

Lemma maps_subtract_all_cuts_app : forall c1 c2 Y,
  maps_subtract_all Y (c1 ++ c2) = maps_subtract_all (maps_subtract_all Y c1) c2.
Proof.
  induction c1 as [| [a n] r IH]; intros c2 Y; cbn [app maps_subtract_all]; [reflexivity |].
  apply IH.
Qed.

Lemma maps_subtract_app' : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [| [a s] r IH]; intros l2 lo hi; cbn [app maps_subtract]; [reflexivity |].
  rewrite IH. apply app_assoc.
Qed.

Lemma maps_subtract_all_app' : forall cuts l1 l2,
  maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
  induction cuts as [| [a n] r IH]; intros l1 l2; cbn [maps_subtract_all]; [reflexivity |].
  rewrite maps_subtract_app'. apply IH.
Qed.

(* [comment removed for export] *)
Ltac iv_cases :=
  repeat (first
    [ progress cbn [app maps_subtract maps_subtract_all fst snd]
    | progress (unfold iv_subtract; cbv zeta)
    | match goal with
      | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
          rewrite (unsigned_Z_to_bv_small z) by (unfold two_pow_64 in *; lia)
      end
    | match goal with
      | |- context [if ?c then _ else _] =>
          let E := fresh "E" in
          destruct c eqn:E;
          [ first [apply Z.ltb_lt in E | idtac] | first [apply Z.ltb_ge in E | idtac] ]
      end ]).

Ltac iv_close :=
  try (exfalso; unfold two_pow_64 in *; lia);
  repeat match goal with
         | |- ?l = ?l => reflexivity
         | |- _ :: _ = _ :: _ => f_equal
         | |- (_, _) = (_, _) => f_equal
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold two_pow_64 in *; lia
         | |- ?b = Z_to_bv 64 _ => rewrite <- (Z_to_bv_unsigned_id b) at 1; f_equal; unfold two_pow_64 in *; lia
         | |- Z_to_bv 64 _ = ?b => rewrite <- (Z_to_bv_unsigned_id b) at 2; f_equal; unfold two_pow_64 in *; lia
         end.

(* [comment removed for export] *)
Lemma iv_subtract_cut_clear : forall (b t a s : word) lo hi,
  0 <= lo -> lo <= hi -> hi < two_pow_64 ->
  clear_of lo hi (b, t) ->
  maps_subtract_all [(b, t)] (iv_subtract a s lo hi)
  = iv_subtract b t (bv_unsigned a) (bv_unsigned a + bv_unsigned s).
Proof.
  intros b t a s lo hi Hlo Hlh Hhi (Hnz & Hfit & Hmiss). cbn [fst snd] in *.
  pose proof (word_range a) as Ra. pose proof (word_range s) as Rs.
  pose proof (word_range b) as Rb. pose proof (word_range t) as Rt.
  destruct Hmiss as [Hmiss | Hmiss]; iv_cases; iv_close.
Qed.

(* [comment removed for export] *)
Lemma clear_of_iv_subtract : forall (b t : word) lo hi x y,
  clear_of lo hi (b, t) -> Forall (clear_of lo hi) (iv_subtract b t x y).
Proof.
  intros b t lo hi x y (Hnz & Hfit & Hmiss). cbn [fst snd] in *.
  pose proof (word_range b) as Rb. pose proof (word_range t) as Rt.
  unfold iv_subtract. cbv zeta. apply Forall_app. split.
  - destruct (bv_unsigned b <? x) eqn:E; [| constructor]. apply Z.ltb_lt in E.
    constructor; [| constructor]. unfold clear_of. cbn [fst snd].
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia).
    unfold two_pow_64 in *. lia.
  - destruct (y <? bv_unsigned b + bv_unsigned t) eqn:E; [| constructor]. apply Z.ltb_lt in E.
    constructor; [| constructor]. unfold clear_of. cbn [fst snd].
    rewrite (unsigned_Z_to_bv_small (Z.max (bv_unsigned b) y)) by (unfold two_pow_64 in *; lia).
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia).
    unfold two_pow_64 in *. lia.
Qed.

Lemma clear_of_maps_subtract : forall Y lo hi x y,
  Forall (clear_of lo hi) Y -> Forall (clear_of lo hi) (maps_subtract Y x y).
Proof.
  induction Y as [| [b t] r IH]; intros lo hi x y H; cbn [maps_subtract]; [constructor |].
  inversion H as [| e l He Hr]; subst. apply Forall_app. split.
  - apply clear_of_iv_subtract. exact He.
  - apply IH. exact Hr.
Qed.

Lemma clear_of_maps_subtract_all : forall cuts Y lo hi,
  Forall (clear_of lo hi) Y -> Forall (clear_of lo hi) (maps_subtract_all Y cuts).
Proof.
  induction cuts as [| [a n] r IH]; intros Y lo hi H; cbn [maps_subtract_all]; [exact H |].
  apply IH. apply clear_of_maps_subtract. exact H.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_cut_clear : forall Y (a s : word) lo hi,
  0 <= lo -> lo <= hi -> hi < two_pow_64 ->
  Forall (clear_of lo hi) Y ->
  maps_subtract_all Y (iv_subtract a s lo hi)
  = maps_subtract Y (bv_unsigned a) (bv_unsigned a + bv_unsigned s).
Proof.
  induction Y as [| [b t] r IH]; intros a s lo hi Hlo Hlh Hhi H.
  - cbn [maps_subtract]. clear. induction (iv_subtract a s lo hi) as [| [x y] l IHl]; cbn; [reflexivity | exact IHl].
  - inversion H as [| e l He Hr]; subst.
    change ((b, t) :: r) with ([(b, t)] ++ r).
    rewrite maps_subtract_all_app'. rewrite maps_subtract_app'.
    rewrite (iv_subtract_cut_clear b t a s lo hi Hlo Hlh Hhi He).
    rewrite (IH a s lo hi Hlo Hlh Hhi Hr).
    cbn [maps_subtract]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem maps_subtract_all_cut_clear : forall K Y lo hi,
  0 <= lo -> lo <= hi -> hi < two_pow_64 ->
  Forall (clear_of lo hi) Y ->
  maps_subtract_all Y (maps_subtract K lo hi) = maps_subtract_all Y K.
Proof.
  induction K as [| [a s] K0 IH]; intros Y lo hi Hlo Hlh Hhi H; cbn [maps_subtract maps_subtract_all];
    [reflexivity |].
  rewrite maps_subtract_all_cuts_app.
  rewrite (maps_subtract_cut_clear Y a s lo hi Hlo Hlh Hhi H).
  apply IH; try assumption.
  apply clear_of_maps_subtract. exact H.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_inside : forall (b t : word) lo hi,
  lo <= bv_unsigned b -> bv_unsigned b + bv_unsigned t <= hi -> iv_subtract b t lo hi = [].
Proof.
  intros b t lo hi H1 H2. unfold iv_subtract. cbv zeta.
  destruct (bv_unsigned b <? lo) eqn:E1; [apply Z.ltb_lt in E1; lia |].
  destruct (hi <? bv_unsigned b + bv_unsigned t) eqn:E2; [apply Z.ltb_lt in E2; lia |].
  reflexivity.
Qed.

Lemma maps_subtract_inside : forall Y lo hi,
  Forall (fun e => lo <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= hi) Y ->
  maps_subtract Y lo hi = [].
Proof.
  induction Y as [| [b t] r IH]; intros lo hi H; cbn [maps_subtract]; [reflexivity |].
  inversion H as [| e l [H1 H2] Hr]; subst. cbn [fst snd] in *.
  rewrite (iv_subtract_inside b t lo hi H1 H2). cbn [app]. apply IH. exact Hr.
Qed.
