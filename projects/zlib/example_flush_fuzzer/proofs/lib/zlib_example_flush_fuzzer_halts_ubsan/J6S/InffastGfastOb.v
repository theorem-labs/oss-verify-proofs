(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast InflateGarbBase InflateGarbFast.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GOB.
  Variable x : ffx.
  Variable s : inflate_state.
  Variable ON : Z.

  Local Ltac ff_comm' :=
    intros; repeat match goal with f : ffs |- _ => destruct f end;
    cbv beta iota zeta delta [cp1 fdrop fpull fpull2_if fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
                             f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.

  Lemma loopZ_shapeN : forall (step : ffs -> bool * ffs),
    (forall f ob, step (fset_ob f ob) = (fst (step f), fset_ob (snd (step f)) (f_ob (snd (step (fset_ob f ob)))))) ->
    forall k f ob, exists ob1, loopZ (Z.of_nat k) step (fset_ob f ob) = fset_ob (loopZ (Z.of_nat k) step f) ob1.
  Proof.
    intros step Hshape. induction k as [|k IH]; intros f ob.
    - rewrite !loopZ_le0 by lia. exists ob. reflexivity.
    - rewrite !(loopZ_step (Z.of_nat (S k))) by lia. rewrite Hshape. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
      destruct (step f) as [c f1]; cbn [fst snd]. destruct c; [apply IH | eexists; reflexivity].
  Qed.
  Lemma loopZ_shape : forall (step : ffs -> bool * ffs),
    (forall f ob, step (fset_ob f ob) = (fst (step f), fset_ob (snd (step f)) (f_ob (snd (step (fset_ob f ob)))))) ->
    forall n f ob, exists ob1, loopZ n step (fset_ob f ob) = fset_ob (loopZ n step f) ob1.
  Proof.
    intros step Hshape n f ob. destruct (Z.le_gt_cases n 0) as [L|L].
    - rewrite !loopZ_le0 by lia. exists ob. reflexivity.
    - rewrite <- (Z2Nat.id n) by lia. apply loopZ_shapeN. exact Hshape.
  Qed.
  Lemma loop_okN_ob : forall (step : ffs -> bool * ffs) (ok : ffs -> bool),
    (forall f ob, step (fset_ob f ob) = (fst (step f), fset_ob (snd (step f)) (f_ob (snd (step (fset_ob f ob)))))) ->
    (forall f ob, ok (fset_ob f ob) = ok f) ->
    forall k f ob, loop_okN k step ok (fset_ob f ob) = loop_okN k step ok f.
  Proof.
    intros step ok Hshape Hok. induction k as [|k IH]; intros f ob; [reflexivity|].
    cbn [loop_okN]. rewrite Hok, Hshape. destruct (step f) as [c f1]; cbn [fst snd]. destruct c; [| reflexivity]. rewrite IH. reflexivity.
  Qed.

  Lemma copy_op_step_shape : forall f ob, copy_op_step x (fset_ob f ob) = (fst (copy_op_step x f), fset_ob (snd (copy_op_step x f)) (f_ob (snd (copy_op_step x (fset_ob f ob))))).
  Proof. intros f ob. unfold copy_op_step. rewrite cp1_shape. ff_comm'. Qed.
  Lemma copy_do3_step_shape : forall f ob, copy_do3_step x (fset_ob f ob) = (fst (copy_do3_step x f), fset_ob (snd (copy_do3_step x f)) (f_ob (snd (copy_do3_step x (fset_ob f ob))))).
  Proof. intros f ob. unfold copy_do3_step. rewrite cp3_shape. ff_comm'. Qed.
  Lemma copy_while3_step_shape : forall f ob, copy_while3_step x (fset_ob f ob) = (fst (copy_while3_step x f), fset_ob (snd (copy_while3_step x f)) (f_ob (snd (copy_while3_step x (fset_ob f ob))))).
  Proof. intros f ob. unfold copy_while3_step. rewrite f_len_ob. destruct (2 <? f_len f); [rewrite cp3_shape|]; ff_comm'. Qed.
  Lemma copy_opG_ob : forall f ob, copy_opG x ON (fset_ob f ob) = copy_opG x ON f.
  Proof. intros f ob. unfold copy_opG, loopZ_ok. rewrite f_op_ob. apply loop_okN_ob; [apply copy_op_step_shape | apply cp1_ok_ob]. Qed.
  Lemma ok3_ob : forall f ob, ok3 x ON (fset_ob f ob) = ok3 x ON f.
  Proof. intros [fi fo fh fb fl fd fop ffr fob] ob. unfold ok3, cp1_ok, cp1. cbn [f_ob f_out f_from fset_ob fset_out fset_from f_in f_hold f_bits f_len f_dist f_op]. reflexivity. Qed.
  Lemma copy_do3G_ob : forall f ob, copy_do3G x ON (fset_ob f ob) = copy_do3G x ON f.
  Proof. intros f ob. unfold copy_do3G, loopZ_ok. rewrite f_len_ob. apply loop_okN_ob; [apply copy_do3_step_shape | apply ok3_ob]. Qed.
  Lemma copy_while3G_ob : forall f ob, copy_while3G x ON (fset_ob f ob) = copy_while3G x ON f.
  Proof.
    intros f ob. unfold copy_while3G, loopZ_ok. rewrite f_len_ob. apply loop_okN_ob; [apply copy_while3_step_shape |].
    intros g ob'. rewrite f_len_ob, ok3_ob. reflexivity.
  Qed.
  Lemma copy_tailG_ob : forall f ob, copy_tailG x ON (fset_ob f ob) = copy_tailG x ON f.
  Proof. intros f ob. unfold copy_tailG. rewrite f_len_ob, cp1_ok_ob, cp1_shape, f_len_ob, cp1_ok_ob. reflexivity. Qed.

  Lemma copy_op_shape : forall f ob, exists ob1, copy_op x (fset_ob f ob) = fset_ob (copy_op x f) ob1.
  Proof.
    intros f ob. unfold copy_op. rewrite f_op_ob.
    change (fun f0 : ffs => let f1 := cp1 x f0 in let f2 := fset_op f1 (wrap32 (f_op f1 - 1)) in (negb (f_op f2 =? 0), f2)) with (copy_op_step x).
    apply loopZ_shape. apply copy_op_step_shape.
  Qed.
  Lemma copy_while3_shape : forall f ob, exists ob1, copy_while3 x (fset_ob f ob) = fset_ob (copy_while3 x f) ob1.
  Proof.
    intros f ob. unfold copy_while3. rewrite f_len_ob.
    change (fun f0 : ffs => if 2 <? f_len f0 then let f1 := cp1 x (cp1 x (cp1 x f0)) in (true, fset_len f1 (wrap32 (f_len f1 - 3))) else (false, f0)) with (copy_while3_step x).
    apply loopZ_shape. apply copy_while3_step_shape.
  Qed.
  Lemma copy_do3_shape : forall f ob, exists ob1, copy_do3 x (fset_ob f ob) = fset_ob (copy_do3 x f) ob1.
  Proof.
    intros f ob. unfold copy_do3. rewrite f_len_ob.
    change (fun f0 : ffs => let f1 := cp1 x (cp1 x (cp1 x f0)) in let f2 := fset_len f1 (wrap32 (f_len f1 - 3)) in (2 <? f_len f2, f2)) with (copy_do3_step x).
    apply loopZ_shape. apply copy_do3_step_shape.
  Qed.
  Local Ltac fobn' :=
    cbn -[copy_op copy_while3 copy_do3 copy_tail cp1 place wrap32 zmask Z.sub Z.add Z.ltb Z.eqb Z.leb Z.land Z.shiftr Z.mul copy_opG] in *;
    repeat first [ rewrite !fdrop_ob in * | rewrite !fpull_ob in * | rewrite !fpull2_if_ob in * | rewrite !fset_dist_ob in *
                 | rewrite !fset_len_ob in * | rewrite !fset_op_ob in * | rewrite !fset_from_ob in *
                 | rewrite !f_in_ob in * | rewrite !f_out_ob in * | rewrite !f_hold_ob in * | rewrite !f_bits_ob in *
                 | rewrite !f_len_ob in * | rewrite !f_dist_ob in * | rewrite !f_op_ob in * | rewrite !f_from_ob in * | rewrite !copy_opG_ob in * ].
  Lemma placeG_ob : forall f ob, placeG x ON (fset_ob f ob) = placeG x ON f.
  Proof.
    intros f ob. unfold placeG. fobn'.
    destruct (x_wnext x =? 0); [reflexivity|]. destruct (x_wnext x <? f_op f); [| reflexivity].
    destruct (_ <? f_len f); [| reflexivity]. f_equal.
    edestruct (copy_op_shape) as [ob1 E]; rewrite E. fobn'. reflexivity.
  Qed.
  Lemma place_shape : forall f ob, exists ob1, place x (fset_ob f ob) = fset_ob (place x f) ob1.
  Proof.
    intros f ob. unfold place. fobn'.
    destruct (x_wnext x =? 0).
    { destruct (_ <? f_len f); [| eexists; reflexivity].
      edestruct (copy_op_shape) as [ob1 E]; rewrite E. fobn'. eexists; reflexivity. }
    destruct (x_wnext x <? f_op f).
    { destruct (_ <? f_len f); [| eexists; reflexivity].
      edestruct (copy_op_shape) as [ob1 E]; rewrite E. fobn'.
      destruct (x_wnext x <? _); [| eexists; reflexivity].
      edestruct (copy_op_shape) as [ob2 E2]; rewrite E2. fobn'. eexists; reflexivity. }
    destruct (_ <? f_len f); [| eexists; reflexivity].
    edestruct (copy_op_shape) as [ob1 E]; rewrite E. fobn'. eexists; reflexivity.
  Qed.

  Lemma dodistG_ob : forall k here f ob, dodistG x s ON k here (fset_ob f ob) = dodistG x s ON k here f.
  Proof.
    induction k as [|k IH]; intros here f ob; [reflexivity|].
    rewrite !dodistG_S. cbv zeta. rewrite !dist_pre_ob, !f_out_ob, !f_dist_ob, !fdrop_ob, !f_hold_ob, !IH.
    destruct (negb _); [| reflexivity]. destruct (_ <? _).
    - destruct (_ && _); [reflexivity|]. rewrite !fset_op_ob, !placeG_ob. f_equal.
      edestruct (place_shape) as [ob1 E]; rewrite E, copy_while3G_ob. f_equal.
      edestruct (copy_while3_shape) as [ob2 E2]; rewrite E2, copy_tailG_ob. reflexivity.
    - rewrite !fset_from_ob, !copy_do3G_ob. f_equal.
      edestruct (copy_do3_shape) as [ob1 E]; rewrite E, copy_tailG_ob. reflexivity.
  Qed.
  Lemma dolenG_ob : forall k here f ob, dolenG x s ON k here (fset_ob f ob) = dolenG x s ON k here f.
  Proof.
    induction k as [|k IH]; intros here f ob; [reflexivity|].
    rewrite !dolenG_S. cbv zeta. rewrite fdrop_ob, f_out_ob, len_pre_ob, f_hold_ob, dodistG_ob, f_hold_ob, IH. reflexivity.
  Qed.
  Lemma fast_tripG_ob : forall f ob, fast_tripG x s ON (fset_ob f ob) = fast_tripG x s ON f.
  Proof. intros f ob. unfold fast_tripG. rewrite fpull2_if_ob, f_hold_ob, dolenG_ob. reflexivity. Qed.

  Lemma fast_loopN_ob : forall n f ob, FR ON f ob -> fast_loopN x s ON n (fset_ob f ob) = fast_loopN x s ON n f.
  Proof.
    induction n as [|n IH]; intros f ob HF; [reflexivity|].
    cbn [fast_loopN]. rewrite fast_tripG_ob. destruct (fast_tripG x s ON f) eqn:G; [| reflexivity]. cbn [andb].
    destruct (fast_trip_rel x s ON f ob HF ltac:(rewrite fast_tripG_ob; exact G)) as (ob1 & E & HF1). rewrite E.
    destruct (fast_trip x s f) as [f'|f' m g]; cbn [fsmap fsf] in HF1 |- *; [| reflexivity].
    rewrite f_in_ob, f_out_ob. destruct (_ && _); [apply IH; exact HF1 | reflexivity].
  Qed.
End GOB.

Theorem gfast_ob : forall s c ob r, arr_len ob = arr_len (ic_outbuf c) ->
  (forall i, 0 <= i < ic_next_out c -> arr_get ob i = arr_get (ic_outbuf c) i) ->
  ffG (mkW s (icset_outbuf c ob) r) = ffG (mkW s c r).
Proof.
  intros s c ob r HL HA. unfold ffG. cbn [w_s w_c w_r]. rewrite ffx_of'_ob, ff0_of'_ob, ffuel_ob.
  replace (arr_len (ic_outbuf (icset_outbuf c ob))) with (arr_len (ic_outbuf c)) by (destruct c; cbn; symmetry; exact HL).
  apply fast_loopN_ob. split; [| destruct c; reflexivity]. split; [destruct c; cbn in *; exact HL | destruct c; cbn in *; exact HA].
Qed.
