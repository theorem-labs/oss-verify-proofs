(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem LaStep LaCheck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAM LAI LAC.

Module LAU.

Definition hdr_ok (Un : unitT) : bool :=
  tables_validb (un_env Un) &&& forallb (template_okb (un_env Un)) (un_cuts Un).

Definition leaves_ok (r : list (nat * list leaf)) : bool :=
  forallb (fun il : nat * list leaf => forallb leaf_ok (snd il)) r.

(* [comment removed for export] *)
Definition coverb (n : nat) (bins : list (list nat)) : bool :=
  forallb (fun i => existsb (fun b => existsb (Nat.eqb i) b) bins) (seq 0 n).

Lemma forallb_app : forall {A} (f : A -> bool) (l1 l2 : list A),
  forallb f (l1 ++ l2) = true <-> forallb f l1 = true /\ forallb f l2 = true.
Proof.
  intros A f l1 l2. induction l1 as [|x r IH]; cbn.
  - tauto.
  - destruct (f x); cbn; [exact IH|]. split; [discriminate|]. intros [H _]; discriminate.
Qed.

Lemma run_some_cut : forall Un which cps i k cp,
  leaves_ok (run_some Un i cps which) = true ->
  nth_error cps k = Some cp -> existsb (Nat.eqb (i + k)) which = true ->
  forallb leaf_ok (run_cut Un (i + k) cp) = true.
Proof.
  intros Un which cps i k cp Hok. rewrite run_some_eq in Hok. revert i k cp Hok.   (* [comment removed for export] *)
  induction cps as [|c r IH]; intros i k cp Hok Hnth Hin.
  - destruct k; discriminate.
  - cbn [run_some_ref] in Hok. unfold leaves_ok in Hok. apply forallb_app in Hok. destruct Hok as [H1 H2].
    destruct k as [|k'].
    + cbn in Hnth. injection Hnth as ->. rewrite Nat.add_0_r in Hin |- *.
      rewrite Hin in H1. cbn in H1. destruct (forallb leaf_ok (run_cut Un i cp)); [reflexivity|discriminate].
    + cbn in Hnth. replace (i + S k')%nat with (S i + k')%nat by lia.
      apply (IH (S i) k' cp); [exact H2|exact Hnth|]. replace (S i + k')%nat with (i + S k')%nat by lia. exact Hin.
Qed.

Lemma run_cuts_ok : forall Un cps i,
  (forall k cp, nth_error cps k = Some cp -> forallb leaf_ok (run_cut Un (i + k) cp) = true) ->
  forallb (fun il : nat * list leaf => forallb leaf_ok (snd il)) (run_cuts Un i cps) = true.
Proof.
  intros Un cps. induction cps as [|c r IH]; intros i H; [reflexivity|].
  cbn [run_cuts forallb snd]. pose proof (H 0%nat c eq_refl) as H0. rewrite Nat.add_0_r in H0. cbn [snd]. rewrite H0.
  apply IH. intros k cp Hk. replace (S i + k)%nat with (i + S k)%nat by lia. apply H. exact Hk.
Qed.

Theorem check_unit_parts : forall Un bins,
  hdr_ok Un = true ->
  coverb (length (un_cuts Un)) bins = true ->
  (forall b, In b bins -> leaves_ok (run_some Un 0 (un_cuts Un) b) = true) ->
  check_unit Un = true.
Proof.
  intros Un bins Hh Hc Hp. unfold check_unit. unfold hdr_ok in Hh.
  destruct (tables_validb (un_env Un)); [|discriminate]. cbn in Hh |- *. rewrite Hh.
  unfold run_unit. apply run_cuts_ok. intros k cp Hk. cbn [Nat.add].
  assert (Hlt : (k < length (un_cuts Un))%nat). { apply (proj1 (nth_error_Some (un_cuts Un) k)). rewrite Hk. discriminate. }
  unfold coverb in Hc. rewrite forallb_forall in Hc.
  specialize (Hc k). assert (Hin : In k (seq 0 (length (un_cuts Un)))). { apply in_seq. lia. }
  specialize (Hc Hin). apply existsb_exists in Hc. destruct Hc as [b [Hb Hkb]].
  exact (run_some_cut Un b (un_cuts Un) 0 k cp (Hp b Hb) Hk Hkb).
Qed.

End LAU.
