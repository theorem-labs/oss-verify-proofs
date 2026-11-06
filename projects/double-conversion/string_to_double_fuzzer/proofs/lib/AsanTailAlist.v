(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.

Definition tt_of_alist (AL : list (nat * (acs * plan * shape))) : nat -> option (acs * plan * shape) :=
  fun t => match find (fun e : nat * (acs * plan * shape) => Nat.eqb (fst e) t) AL with Some e => Some (snd e) | None => None end.

Lemma tt_of_alist_nil : forall t, tt_of_alist [] t = None.
Proof. reflexivity. Qed.
Lemma tt_of_alist_in : forall AL t e, tt_of_alist AL t = Some e -> In (t, e) AL.
Proof.
  intros AL t e H. unfold tt_of_alist in H.
  destruct (find (fun e0 : nat * (acs * plan * shape) => Nat.eqb (fst e0) t) AL) as [[k x]|] eqn:F; [|discriminate].
  injection H as <-. apply find_some in F as [Hin Hk]. cbn [fst] in Hk. apply Nat.eqb_eq in Hk. subst k. exact Hin.
Qed.
Lemma tt_of_alist_app : forall AL1 AL2 t,
  tt_of_alist (AL1 ++ AL2) t = match tt_of_alist AL1 t with Some e => Some e | None => tt_of_alist AL2 t end.
Proof.
  intros AL1 AL2 t. unfold tt_of_alist. induction AL1 as [|[k x] r IH]; [reflexivity|].
  cbn [app find fst]. destruct (Nat.eqb k t); [reflexivity | exact IH].
Qed.
(* [comment removed for export] *)
Definition alist_keys_in (lo hi : nat) (AL : list (nat * (acs * plan * shape))) : bool :=
  forallb (fun e : nat * (acs * plan * shape) => (Nat.leb lo (fst e) && Nat.leb (fst e) hi)%bool) AL.
Lemma tt_of_alist_out : forall lo hi AL t, alist_keys_in lo hi AL = true -> (t < lo \/ hi < t)%nat -> tt_of_alist AL t = None.
Proof.
  intros lo hi AL t H Ht. destruct (tt_of_alist AL t) as [e|] eqn:E; [|reflexivity]. exfalso.
  apply tt_of_alist_in in E. pose proof (proj1 (forallb_forall _ _) H _ E) as X. cbn [fst] in X.
  apply andb_prop in X as [X1 X2]. apply Nat.leb_le in X1. apply Nat.leb_le in X2. lia.
Qed.

Section Tab.
  Variable SEGS : list Segment.
  Variable IT : itab.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable KC : nat.

  (* [comment removed for export] *)
  Lemma tails_ok_of_alist : forall AL,
    AP.tails_okb SEGS IT A nx0 LIMIT KC (map snd AL) = true -> AP.tails_ok SEGS IT A nx0 LIMIT (tt_of_alist AL) KC.
  Proof.
    intros AL H t T p s Ht Hnf. apply tt_of_alist_in in Ht.
    pose proof (proj1 (forallb_forall _ _) H (T, p, s) (in_map snd _ _ Ht)) as X. cbn beta iota in X. rewrite Hnf in X.
    destruct (AP.checkT SEGS IT A nx0 LIMIT KC T p) as [s'|]; [|discriminate]. apply APS.shape_eqb_eq in X. subst s'. reflexivity.
  Qed.
  Lemma tails_ok_alist_app : forall AL1 AL2,
    AP.tails_ok SEGS IT A nx0 LIMIT (tt_of_alist AL1) KC -> AP.tails_ok SEGS IT A nx0 LIMIT (tt_of_alist AL2) KC ->
    AP.tails_ok SEGS IT A nx0 LIMIT (tt_of_alist (AL1 ++ AL2)) KC.
  Proof.
    intros AL1 AL2 H1 H2 t T p s Ht Hnf. rewrite tt_of_alist_app in Ht.
    destruct (tt_of_alist AL1 t) as [e|] eqn:E1.
    - injection Ht as ->. exact (H1 t T p s E1 Hnf).
    - exact (H2 t T p s Ht Hnf).
  Qed.
End Tab.
