(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [dodist dolen fast_trip inflate_fast].


Lemma iterZ_ind2 : forall {A B} (P : A -> Prop) (Q : B -> Prop) (step : A -> A + B) (dflt : A -> B),
  (forall a, P a -> match step a with inl a' => P a' | inr b => Q b end) ->
  (forall a, P a -> Q (dflt a)) ->
  forall n a, P a -> Q (iterZ n step dflt a).
Proof.
  intros A B P Q step dflt Hs Hd n a Ha. rewrite iterZ_nat.
  revert a Ha. generalize (Z.to_nat n) as k. induction k as [|k IH]; intros a Ha; cbn [iterK_nat].
  - exact (Hd a Ha).
  - pose proof (Hs a Ha) as H. destruct (step a) as [a'|b]; [exact (IH a' H) | exact H].
Qed.

Lemma loopZ_ind : forall {A} (P : A -> Prop) (step : A -> bool * A),
  (forall a, P a -> P (snd (step a))) ->
  forall n a, P a -> P (loopZ n step a).
Proof.
  intros A P step Hs n a Ha. unfold loopZ.
  apply (iterZ_ind2 P P); [|intros a0 H0; exact H0|exact Ha].
  intros a0 H0. pose proof (Hs a0 H0) as H1. destruct (step a0) as [c a1]. cbn [snd] in H1. destruct c; exact H1.
Qed.


Section Frame.
  Variable o0 : Z.
Variable ob0 : arr.

  Definition FR (f : ffs) : Prop :=
    o0 <= f_out f /\ arr_len (f_ob f) = arr_len ob0 /\
    (forall i, (i < o0 \/ f_out f <= i) -> arr_get (f_ob f) i = arr_get ob0 i).

  Definition FRs (st : fstep) : Prop :=
    match st with FCont f => FR f | FBreak f _ _ => FR f end.

  Lemma FR_scal : forall f g, f_out g = f_out f -> f_ob g = f_ob f -> FR f -> FR g.
  Proof. intros f g E1 E2 H. unfold FR in *. rewrite E1, E2. exact H. Qed.

  Lemma FR_if : forall (c : bool) a b, FR a -> FR b -> FR (if c then a else b).
  Proof. intros [] a b Ha Hb; assumption. Qed.
  Lemma FRs_if : forall (c : bool) a b, FRs a -> FRs b -> FRs (if c then a else b).
  Proof. intros [] a b Ha Hb; assumption. Qed.

  Lemma FR_cp1 : forall x f, FR f -> FR (cp1 x f).
  Proof.
    intros x f (H1 & H2 & H3). unfold cp1. destruct f as [fi fo fh fb fl fd fop ff fob]. unfold FR.
    cbn [f_out f_ob f_from fset_ob fset_out fset_from]. cbn [f_out f_ob] in H1, H2, H3.
    split; [lia|]. split; [rewrite arr_len_set; exact H2|].
    intros i Hi. rewrite arr_get_set_other by lia. apply H3. lia.
  Qed.

  Lemma FR_fpull : forall x f, FR f -> FR (fpull x f).
  Proof. intros x f H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fpull2_if : forall x f, FR f -> FR (fpull2_if x f).
  Proof. intros x f H. unfold fpull2_if. apply FR_if; [apply FR_fpull, FR_fpull, H|exact H]. Qed.
  Lemma FR_fdrop : forall f op, FR f -> FR (fdrop f op).
  Proof. intros f op H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_in : forall f v, FR f -> FR (fset_in f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_hold : forall f v, FR f -> FR (fset_hold f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_bits : forall f v, FR f -> FR (fset_bits f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_len : forall f v, FR f -> FR (fset_len f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_dist : forall f v, FR f -> FR (fset_dist f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_op : forall f v, FR f -> FR (fset_op f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.
  Lemma FR_fset_from : forall f v, FR f -> FR (fset_from f v).
  Proof. intros f v H. apply (FR_scal f); [destruct f; reflexivity|destruct f; reflexivity|exact H]. Qed.

  Lemma FR_copy_op : forall x f, FR f -> FR (copy_op x f).
  Proof.
    intros x f H. unfold copy_op. apply loopZ_ind; [|exact H].
    intros a Ha. cbn [snd]. apply FR_fset_op, FR_cp1, Ha.
  Qed.

  Lemma FR_copy_while3 : forall x f, FR f -> FR (copy_while3 x f).
  Proof.
    intros x f H. unfold copy_while3. apply loopZ_ind; [|exact H].
    intros a Ha. destruct (2 <? f_len a); cbn [snd]; [|exact Ha].
    apply FR_fset_len. apply FR_cp1, FR_cp1, FR_cp1, Ha.
  Qed.

  Lemma FR_copy_do3 : forall x f, FR f -> FR (copy_do3 x f).
  Proof.
    intros x f H. unfold copy_do3. apply loopZ_ind; [|exact H].
    intros a Ha. cbn [snd]. apply FR_fset_len. apply FR_cp1, FR_cp1, FR_cp1, Ha.
  Qed.

  Lemma FR_copy_tail : forall x f, FR f -> FR (copy_tail x f).
  Proof.
    intros x f H. unfold copy_tail.
    apply FR_if; [|exact H]. apply FR_if; [apply FR_cp1|]; apply FR_cp1, H.
  Qed.

  Ltac frgo :=
    lazymatch goal with
    | |- FRs (if _ then _ else _) => apply FRs_if; frgo
    | |- FR (if _ then _ else _) => apply FR_if; frgo
    | |- FRs (FCont _) => cbn [FRs]; frgo
    | |- FRs (FBreak _ _ _) => cbn [FRs]; frgo
    | |- FR (fpull _ _) => apply FR_fpull; frgo
    | |- FR (fpull2_if _ _) => apply FR_fpull2_if; frgo
    | |- FR (fdrop _ _) => apply FR_fdrop; frgo
    | |- FR (fset_in _ _) => apply FR_fset_in; frgo
    | |- FR (fset_hold _ _) => apply FR_fset_hold; frgo
    | |- FR (fset_bits _ _) => apply FR_fset_bits; frgo
    | |- FR (fset_len _ _) => apply FR_fset_len; frgo
    | |- FR (fset_dist _ _) => apply FR_fset_dist; frgo
    | |- FR (fset_op _ _) => apply FR_fset_op; frgo
    | |- FR (fset_from _ _) => apply FR_fset_from; frgo
    | |- FR (cp1 _ _) => apply FR_cp1; frgo
    | |- FR (copy_op _ _) => apply FR_copy_op; frgo
    | |- FR (copy_while3 _ _) => apply FR_copy_while3; frgo
    | |- FR (copy_do3 _ _) => apply FR_copy_do3; frgo
    | |- FR (copy_tail _ _) => apply FR_copy_tail; frgo
    | |- _ => idtac
    end.

  Lemma FR_dodist : forall k x s here f, FR f -> FRs (dodist k x s here f).
  Proof.
    induction k as [|k IH]; intros x s here f H.
    - cbn [dodist FRs]. exact H.
    - cbn [dodist]. cbv zeta. frgo; try exact H.
      apply IH. frgo. exact H.
  Qed.

  Lemma FR_literal : forall f v, FR f -> FR (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) v)) (f_out (fset_ob f (arr_set (f_ob f) (f_out f) v)) + 1)).
  Proof.
    intros f v (H1 & H2 & H3). destruct f as [fi fo fh fb fl fd fop ff fob]. unfold FR.
    cbn [f_out f_ob fset_ob fset_out]. cbn [f_out f_ob] in H1, H2, H3.
    split; [lia|]. split; [rewrite arr_len_set; exact H2|].
    intros i Hi. rewrite arr_get_set_other by lia. apply H3. lia.
  Qed.

  Lemma FR_dolen : forall k x s here f, FR f -> FRs (dolen k x s here f).
  Proof.
    induction k as [|k IH]; intros x s here f H.
    - cbn [dolen FRs]. exact H.
    - cbn [dolen]. cbv zeta. frgo; try exact H.
      + apply FR_literal. frgo. exact H.
      + apply FR_dodist. frgo; exact H.
      + apply IH. frgo. exact H.
  Qed.

  Lemma FR_fast_trip : forall x s f, FR f -> FRs (fast_trip x s f).
  Proof. intros x s f H. unfold fast_trip. apply FR_dolen. apply FR_fpull2_if. exact H. Qed.
End Frame.


Theorem inflate_fast_frame_proof : inflate_fast_frame_stmt.
Proof.
  intros s c r. cbv zeta. unfold inflate_fast. cbn [w_s w_c w_r]. cbv zeta.
  set (o0 := ic_next_out c). set (ob0 := ic_outbuf c).
  lazymatch goal with |- context [iterZ ?n ?st ?d ?a] =>
    assert (HL : FR o0 ob0 (fst (iterZ n st d a)));
    [ apply (iterZ_ind2 (FR o0 ob0) (fun p => FR o0 ob0 (fst p)));
      [ intros f Hf; pose proof (FR_fast_trip o0 ob0 (mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
          (o0 - wrap32 (ir_out r - ic_avail_out c)) (o0 + wrap32 (ic_avail_out c - 257)) (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
          (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s)) s f Hf) as T;
        lazymatch goal with |- context [fast_trip ?x ?s ?f] => destruct (fast_trip x s f) as [f'|f' md mg] end;
        cbn [FRs] in T; [destruct (_ && _); cbn [fst]; exact T | cbn [fst]; exact T]
      | intros f Hf; cbn [fst]; exact Hf
      | split; [cbn [f_out]; lia|]; split; [reflexivity|]; intros i _; reflexivity ]
    | generalize dependent (iterZ n st d a); intros [f mm] HL ]
  end.
  cbn [fst] in HL.
  assert (HL2 : forall g, f_out g = f_out f -> f_ob g = f_ob f ->
    forall c', ic_next_out c' = f_out g -> ic_outbuf c' = f_ob g ->
    o0 <= ic_next_out c' /\ arr_len (ic_outbuf c') = arr_len ob0 /\
    (forall i, i < o0 \/ ic_next_out c' <= i -> arr_get (ic_outbuf c') i = arr_get ob0 i)).
  { intros g E1 E2 c' E3 E4. rewrite E3, E4, E1, E2. exact HL. }
  destruct mm as [[md [mg|]]|]; cbn [w_c];
    lazymatch goal with |- context [icset_outbuf c (f_ob ?G)] =>
      apply (HL2 G); [destruct f; reflexivity | destruct f; reflexivity | destruct c; reflexivity | destruct c; reflexivity] end.
Qed.
