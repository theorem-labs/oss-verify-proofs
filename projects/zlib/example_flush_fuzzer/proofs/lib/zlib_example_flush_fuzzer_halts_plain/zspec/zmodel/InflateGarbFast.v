(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateGarbBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.



Definition cp1_ok (ON : Z) (f : ffs) : bool :=
  (0 <=? f_out f) && (f_out f <? ON)
  && match f_from f with FWin _ => true | FOut i => (0 <=? i) && (i <? f_out f) end.

Fixpoint loop_okN {A} (n : nat) (step : A -> bool * A) (ok : A -> bool) (a : A) : bool :=
  match n with
  | O => true
  | S n' => ok a && (let '(c, a') := step a in if c then loop_okN n' step ok a' else true)
  end.
Definition loopZ_ok {A} (n : Z) (step : A -> bool * A) (ok : A -> bool) (a : A) : bool :=
  loop_okN (Z.to_nat n) step ok a.

Definition copy_op_step (x : ffx) (f : ffs) : bool * ffs :=
  let f := cp1 x f in let f := fset_op f (wrap32 (f_op f - 1)) in (negb (f_op f =? 0), f).
Definition copy_opG (x : ffx) (ON : Z) (f : ffs) : bool := loopZ_ok (f_op f) (copy_op_step x) (cp1_ok ON) f.

Definition ok3 (x : ffx) (ON : Z) (f : ffs) : bool := cp1_ok ON f && cp1_ok ON (cp1 x f) && cp1_ok ON (cp1 x (cp1 x f)).
Definition copy_while3_step (x : ffx) (f : ffs) : bool * ffs :=
  if 2 <? f_len f then let f := cp1 x (cp1 x (cp1 x f)) in (true, fset_len f (wrap32 (f_len f - 3))) else (false, f).
Definition copy_while3G (x : ffx) (ON : Z) (f : ffs) : bool :=
  loopZ_ok (f_len f) (copy_while3_step x) (fun f => if 2 <? f_len f then ok3 x ON f else true) f.
Definition copy_do3_step (x : ffx) (f : ffs) : bool * ffs :=
  let f := cp1 x (cp1 x (cp1 x f)) in let f := fset_len f (wrap32 (f_len f - 3)) in (2 <? f_len f, f).
Definition copy_do3G (x : ffx) (ON : Z) (f : ffs) : bool := loopZ_ok (f_len f + 1) (copy_do3_step x) (ok3 x ON) f.
Definition copy_tailG (x : ffx) (ON : Z) (f : ffs) : bool :=
  if negb (f_len f =? 0) then cp1_ok ON f && (if 1 <? f_len (cp1 x f) then cp1_ok ON (cp1 x f) else true) else true.

Definition place (x : ffx) (f : ffs) : ffs :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        let f := copy_op x f in
        fset_from f (FOut (f_out f - f_dist f))
      else f
    else f
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f.
Definition placeG (x : ffx) (ON : Z) (f : ffs) : bool :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then copy_opG x ON (fset_len f (wrap32 (f_len f - f_op f))) else true
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      copy_opG x ON f &&
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        copy_opG x ON f
      else true
    else true
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then copy_opG x ON (fset_len f (wrap32 (f_len f - f_op f))) else true.

Fixpoint dodistG (x : ffx) (s : inflate_state) (ON : Z) (k : nat) (here : Z) (f : ffs) : bool :=
  match k with
  | O => true
  | S k' =>
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let f := fset_dist f (code_val here) in
      let op := Z.land op 15 in
      let f := if f_bits f <? op then
                 let f := fpull x f in
                 if f_bits f <? op then fpull x f else f
               else f in
      let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
      let f := fdrop f op in
      let op := wrap32 (f_out f - x_beg x) in
      if op <? f_dist f then
        let op := wrap32 (f_dist f - op) in
        if (x_whave x <? op) && negb (x_sane x =? 0) then true
        else
          let f := fset_op f op in
          placeG x ON f &&
          let f := place x f in
          copy_while3G x ON f && copy_tailG x ON (copy_while3 x f)
      else
        let f := fset_from f (FOut (f_out f - f_dist f)) in
        copy_do3G x ON f && copy_tailG x ON (copy_do3 x f)
    else if Z.land op 64 =? 0 then
      dodistG x s ON k' (code_at s (is_distcode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else true
  end.

Fixpoint dolenG (x : ffx) (s : inflate_state) (ON : Z) (k : nat) (here : Z) (f : ffs) : bool :=
  match k with
  | O => true
  | S k' =>
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then (0 <=? f_out f) && (f_out f <? ON)
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      let f := if negb (op =? 0) then
                 let f := if f_bits f <? op then fpull x f else f in
                 let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
                 fdrop f op
               else f in
      let f := fpull2_if x f in
      dodistG x s ON 4 (code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask x))) f
    else if Z.land op 64 =? 0 then
      dolenG x s ON k' (code_at s (is_lencode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else true
  end.

Definition fast_tripG (x : ffx) (s : inflate_state) (ON : Z) (f : ffs) : bool :=
  let f := fpull2_if x f in
  dolenG x s ON 4 (code_at s (is_lencode s) (Z.land (f_hold f) (x_lmask x))) f.

Fixpoint fast_loopN (x : ffx) (s : inflate_state) (ON : Z) (n : nat) (f : ffs) : bool :=
  match n with
  | O => true
  | S n' => fast_tripG x s ON f &&
            match fast_trip x s f with
            | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then fast_loopN x s ON n' f' else true
            | FBreak _ _ _ => true
            end
  end.

Definition ffx_of' (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  let in_ := ic_next_in c in
  let last := in_ + wrap32 (ic_avail_in c - 5) in
  let out := ic_next_out c in
  let beg := out - wrap32 (ir_out r - ic_avail_out c) in
  let end_ := out + wrap32 (ic_avail_out c - 257) in
  mkFX (ic_input c) last beg end_ (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0_of' (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).
Definition ffuel (c : icall) : nat := Z.to_nat (8 * ic_avail_in c + ic_avail_out c + 80).

Definition ffG (w : iw) : bool :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  fast_loopN (ffx_of' s c r) s (arr_len (ic_outbuf c)) (ffuel c) (ff0_of' s c).


Section FastRel.
  Variable x : ffx.
  Variable s : inflate_state.
  Variable ON : Z.

  Definition FR (f : ffs) (ob' : arr) : Prop := agree_below (f_out f) (f_ob f) ob' /\ arr_len (f_ob f) = ON.

  Lemma fset_ob_ob : forall f ob, f_ob (fset_ob f ob) = ob. Proof. intros [] ob; reflexivity. Qed.
  Lemma fset_ob_twice : forall f a b, fset_ob (fset_ob f a) b = fset_ob f b. Proof. intros [] a b; reflexivity. Qed.

  Ltac ff_red := cbv beta iota zeta delta [cp1 fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
                                            f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob].
  Ltac ff_red_in H := cbv beta iota zeta delta [cp1 fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
                                            f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob] in H.
  Ltac ff_comm :=
    intros; repeat match goal with f : ffs |- _ => destruct f end;
    cbv beta iota zeta delta [cp1 fdrop fpull fpull2_if fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
                             f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.

  Lemma fdrop_ob : forall f ob n, fdrop (fset_ob f ob) n = fset_ob (fdrop f n) ob. Proof. ff_comm. Qed.
  Lemma fpull_ob : forall f ob, fpull x (fset_ob f ob) = fset_ob (fpull x f) ob. Proof. ff_comm. Qed.
  Lemma fpull2_if_ob : forall f ob, fpull2_if x (fset_ob f ob) = fset_ob (fpull2_if x f) ob. Proof. ff_comm. Qed.
  Lemma fset_dist_ob : forall f ob v, fset_dist (fset_ob f ob) v = fset_ob (fset_dist f v) ob. Proof. ff_comm. Qed.
  Lemma fset_len_ob : forall f ob v, fset_len (fset_ob f ob) v = fset_ob (fset_len f v) ob. Proof. ff_comm. Qed.
  Lemma fset_op_ob : forall f ob v, fset_op (fset_ob f ob) v = fset_ob (fset_op f v) ob. Proof. ff_comm. Qed.
  Lemma fset_from_ob : forall f ob v, fset_from (fset_ob f ob) v = fset_ob (fset_from f v) ob. Proof. ff_comm. Qed.
  Lemma fset_out_ob : forall f ob v, fset_out (fset_ob f ob) v = fset_ob (fset_out f v) ob. Proof. ff_comm. Qed.
  Lemma f_in_ob : forall f ob, f_in (fset_ob f ob) = f_in f. Proof. ff_comm. Qed.
  Lemma f_out_ob : forall f ob, f_out (fset_ob f ob) = f_out f. Proof. ff_comm. Qed.
  Lemma f_hold_ob : forall f ob, f_hold (fset_ob f ob) = f_hold f. Proof. ff_comm. Qed.
  Lemma f_bits_ob : forall f ob, f_bits (fset_ob f ob) = f_bits f. Proof. ff_comm. Qed.
  Lemma f_len_ob : forall f ob, f_len (fset_ob f ob) = f_len f. Proof. ff_comm. Qed.
  Lemma f_dist_ob : forall f ob, f_dist (fset_ob f ob) = f_dist f. Proof. ff_comm. Qed.
  Lemma f_op_ob : forall f ob, f_op (fset_ob f ob) = f_op f. Proof. ff_comm. Qed.
  Lemma f_from_ob : forall f ob, f_from (fset_ob f ob) = f_from f. Proof. ff_comm. Qed.
  Lemma f_ob_len : forall f v, f_ob (fset_len f v) = f_ob f. Proof. ff_comm. Qed.
  Lemma f_out_len : forall f v, f_out (fset_len f v) = f_out f. Proof. ff_comm. Qed.
  Lemma f_out_pull : forall f, f_out (fpull x f) = f_out f. Proof. ff_comm. Qed.
  Lemma f_ob_pull : forall f, f_ob (fpull x f) = f_ob f. Proof. ff_comm. Qed.
  Lemma f_ob_op : forall f v, f_ob (fset_op f v) = f_ob f. Proof. ff_comm. Qed.
  Lemma f_out_op : forall f v, f_out (fset_op f v) = f_out f. Proof. ff_comm. Qed.
  Lemma f_ob_out : forall f v, f_ob (fset_out f v) = f_ob f. Proof. ff_comm. Qed.
  Lemma f_out_out : forall f v, f_out (fset_out f v) = v. Proof. ff_comm. Qed.
  Lemma f_ob_drop : forall f n, f_ob (fdrop f n) = f_ob f. Proof. ff_comm. Qed.
  Lemma f_out_drop : forall f n, f_out (fdrop f n) = f_out f. Proof. ff_comm. Qed.
  Lemma f_ob_pull2 : forall f, f_ob (fpull2_if x f) = f_ob f. Proof. unfold fpull2_if. ff_comm. Qed.
  Lemma f_out_pull2 : forall f, f_out (fpull2_if x f) = f_out f. Proof. unfold fpull2_if. ff_comm. Qed.

  Lemma cp1_rel : forall f ob', FR f ob' -> cp1_ok ON (fset_ob f ob') = true ->
    exists ob1, cp1 x (fset_ob f ob') = fset_ob (cp1 x f) ob1 /\ FR (cp1 x f) ob1.
  Proof.
    intros f ob' [AG L] C. unfold cp1_ok, FR in *. destruct f as [fin fout fhold fbits flen fdist fop ffrom fob]. ff_red_in AG. ff_red_in L. ff_red_in C. ff_red.
    apply andb_prop in C as [C CF]. apply andb_prop in C as [C0 C1]. apply Z.leb_le in C0. apply Z.ltb_lt in C1.
    assert (Hv : match ffrom with FWin i => arr_get (x_window x) i | FOut i => arr_get ob' i end
               = match ffrom with FWin i => arr_get (x_window x) i | FOut i => arr_get fob i end).
    { destruct ffrom as [i|i]; [reflexivity|]. apply andb_prop in CF as [CF0 CF1]. apply Z.leb_le in CF0. apply Z.ltb_lt in CF1.
      apply (proj2 AG). lia. }
    rewrite Hv. set (v := match ffrom with FWin i => _ | FOut i => _ end).
    eexists. split; [reflexivity|]. split; [| rewrite arr_len_set; exact L].
    apply (agree_below_set fout); [exact AG | lia | lia].
  Qed.

  Lemma loopZ_rel : forall (step : ffs -> bool * ffs) (ok : ffs -> bool),
    (forall f ob, step (fset_ob f ob) = (fst (step f), fset_ob (snd (step f)) (f_ob (snd (step (fset_ob f ob)))))) ->
    (forall f ob', FR f ob' -> ok (fset_ob f ob') = true -> FR (snd (step f)) (f_ob (snd (step (fset_ob f ob'))))) ->
    forall k f ob', FR f ob' -> loop_okN k step ok (fset_ob f ob') = true ->
    exists ob1, loopZ (Z.of_nat k) step (fset_ob f ob') = fset_ob (loopZ (Z.of_nat k) step f) ob1 /\ FR (loopZ (Z.of_nat k) step f) ob1.
  Proof.
    intros step ok Hshape Hstep. induction k as [|k IH]; intros f ob' HF C.
    - rewrite !loopZ_le0 by lia. exists ob'. split; [reflexivity | exact HF].
    - cbn [loop_okN] in C. apply andb_prop in C as [C0 C]. rewrite Hshape in C.
      rewrite !(loopZ_step (Z.of_nat (S k))) by lia. rewrite Hshape.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
      pose proof (Hstep f ob' HF C0) as HF1.
      destruct (step f) as [c f1] eqn:Es; cbn [fst snd] in *.
      destruct c; [| eexists; split; [reflexivity | exact HF1]].
      apply IH; [exact HF1 | exact C].
  Qed.

  Lemma cp1_shape : forall f ob, cp1 x (fset_ob f ob) = fset_ob (cp1 x f) (f_ob (cp1 x (fset_ob f ob))).
  Proof. intros [fin fout fhold fbits flen fdist fop ffrom fob] ob; reflexivity. Qed.

  Lemma cp1_rel' : forall f ob', FR f ob' -> cp1_ok ON (fset_ob f ob') = true -> FR (cp1 x f) (f_ob (cp1 x (fset_ob f ob'))).
  Proof.
    intros f ob' HF C. destruct (cp1_rel f ob' HF C) as (ob1 & E & HF1). rewrite E, fset_ob_ob. exact HF1.
  Qed.

  Lemma cp1_ok_ob : forall f ob, cp1_ok ON (fset_ob f ob) = cp1_ok ON f.
  Proof. intros [] ob; reflexivity. Qed.

  Lemma copy_op_rel : forall f ob', FR f ob' -> copy_opG x ON (fset_ob f ob') = true ->
    exists ob1, copy_op x (fset_ob f ob') = fset_ob (copy_op x f) ob1 /\ FR (copy_op x f) ob1.
  Proof.
    intros f ob' HF C. unfold copy_op, copy_opG, loopZ_ok in *. rewrite f_op_ob in C |- *.
    destruct (Z.le_gt_cases (f_op f) 0) as [Hle|Hgt].
    { rewrite !loopZ_le0 by lia. exists ob'. split; [reflexivity | exact HF]. }
    rewrite <- (Z2Nat.id (f_op f)) by lia.
    apply (loopZ_rel (copy_op_step x) (cp1_ok ON)); [| | exact HF | exact C].
    - intros f0 ob. unfold copy_op_step. rewrite cp1_shape. cbn [fst snd].
      rewrite !f_op_ob, !fset_op_ob, fset_ob_ob. reflexivity.
    - intros f0 ob0 HF0 C0. unfold copy_op_step. cbn [snd]. rewrite cp1_shape.
      rewrite !f_op_ob, !fset_op_ob, fset_ob_ob.
      pose proof (cp1_rel' f0 ob0 HF0 C0) as HF1. unfold FR in *. rewrite f_ob_op, f_out_op. exact HF1.
  Qed.

  Lemma cp3_shape : forall f ob, cp1 x (cp1 x (cp1 x (fset_ob f ob))) = fset_ob (cp1 x (cp1 x (cp1 x f))) (f_ob (cp1 x (cp1 x (cp1 x (fset_ob f ob))))).
  Proof. intros f ob. rewrite (cp1_shape f ob), (cp1_shape (cp1 x f)), (cp1_shape (cp1 x (cp1 x f))). rewrite !fset_ob_ob. reflexivity. Qed.
  Lemma cp3_rel' : forall f ob', FR f ob' -> ok3 x ON (fset_ob f ob') = true ->
    FR (cp1 x (cp1 x (cp1 x f))) (f_ob (cp1 x (cp1 x (cp1 x (fset_ob f ob'))))).
  Proof.
    intros f ob' HF C. unfold ok3 in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
    pose proof (cp1_rel' f ob' HF C1) as HF1. rewrite (cp1_shape f ob') in C2, C3 |- *.
    pose proof (cp1_rel' _ _ HF1 C2) as HF2. rewrite (cp1_shape (cp1 x f)) in C3 |- *.
    pose proof (cp1_rel' _ _ HF2 C3) as HF3. rewrite (cp1_shape (cp1 x (cp1 x f))). rewrite fset_ob_ob. exact HF3.
  Qed.

  Lemma copy_while3_rel : forall f ob', FR f ob' -> copy_while3G x ON (fset_ob f ob') = true ->
    exists ob1, copy_while3 x (fset_ob f ob') = fset_ob (copy_while3 x f) ob1 /\ FR (copy_while3 x f) ob1.
  Proof.
    intros f ob' HF C. unfold copy_while3, copy_while3G, loopZ_ok in *. rewrite f_len_ob in C |- *.
    destruct (Z.le_gt_cases (f_len f) 0) as [Hle|Hgt].
    { rewrite !loopZ_le0 by lia. exists ob'. split; [reflexivity | exact HF]. }
    rewrite <- (Z2Nat.id (f_len f)) by lia.
    apply (loopZ_rel (copy_while3_step x) (fun f => if 2 <? f_len f then ok3 x ON f else true)); [| | exact HF | exact C].
    - intros f0 ob. unfold copy_while3_step. rewrite f_len_ob.
      destruct (2 <? f_len f0); cbn [fst snd]; [| rewrite fset_ob_ob; reflexivity].
      rewrite cp3_shape. set (X := cp1 x (cp1 x (cp1 x f0))). set (OB := f_ob (cp1 x (cp1 x (cp1 x (fset_ob f0 ob))))).
      rewrite !f_len_ob, !fset_len_ob, fset_ob_ob. reflexivity.
    - intros f0 ob0 HF0 C0. unfold copy_while3_step. rewrite f_len_ob in C0 |- *.
      destruct (2 <? f_len f0); cbn [snd]; [| rewrite fset_ob_ob; exact HF0].
      pose proof (cp3_rel' f0 ob0 HF0 C0) as HF1. rewrite cp3_shape.
      set (X := cp1 x (cp1 x (cp1 x f0))) in *. set (OB := f_ob (cp1 x (cp1 x (cp1 x (fset_ob f0 ob0))))) in *.
      rewrite !f_len_ob, !fset_len_ob, fset_ob_ob. unfold FR in *. rewrite f_ob_len, f_out_len. exact HF1.
  Qed.

  Lemma copy_do3_rel : forall f ob', FR f ob' -> copy_do3G x ON (fset_ob f ob') = true ->
    exists ob1, copy_do3 x (fset_ob f ob') = fset_ob (copy_do3 x f) ob1 /\ FR (copy_do3 x f) ob1.
  Proof.
    intros f ob' HF C. unfold copy_do3, copy_do3G, loopZ_ok in *. rewrite f_len_ob in C |- *.
    destruct (Z.le_gt_cases (f_len f + 1) 0) as [Hle|Hgt].
    { rewrite !loopZ_le0 by lia. exists ob'. split; [reflexivity | exact HF]. }
    rewrite <- (Z2Nat.id (f_len f + 1)) by lia.
    apply (loopZ_rel (copy_do3_step x) (ok3 x ON)); [| | exact HF | exact C].
    - intros f0 ob. unfold copy_do3_step. rewrite cp3_shape. cbn [fst snd].
      set (X := cp1 x (cp1 x (cp1 x f0))). set (OB := f_ob (cp1 x (cp1 x (cp1 x (fset_ob f0 ob))))).
      rewrite !f_len_ob, !fset_len_ob, !f_len_ob, fset_ob_ob. reflexivity.
    - intros f0 ob0 HF0 C0. unfold copy_do3_step. cbn [snd]. pose proof (cp3_rel' f0 ob0 HF0 C0) as HF1. rewrite cp3_shape.
      set (X := cp1 x (cp1 x (cp1 x f0))) in *. set (OB := f_ob (cp1 x (cp1 x (cp1 x (fset_ob f0 ob0))))) in *.
      rewrite !f_len_ob, !fset_len_ob, fset_ob_ob. unfold FR in *. rewrite f_ob_len, f_out_len. exact HF1.
  Qed.

  Lemma copy_tail_rel : forall f ob', FR f ob' -> copy_tailG x ON (fset_ob f ob') = true ->
    exists ob1, copy_tail x (fset_ob f ob') = fset_ob (copy_tail x f) ob1 /\ FR (copy_tail x f) ob1.
  Proof.
    intros f ob' HF C. unfold copy_tail, copy_tailG in *. rewrite f_len_ob in C |- *.
    destruct (negb (f_len f =? 0)); [| exists ob'; split; [reflexivity | exact HF]].
    apply andb_prop in C as [C1 C2]. pose proof (cp1_rel' f ob' HF C1) as HF1. rewrite (cp1_shape f ob') in C2 |- *.
    rewrite f_len_ob in C2 |- *.
    destruct (1 <? f_len (cp1 x f)); [| eexists; split; [reflexivity | exact HF1]].
    pose proof (cp1_rel' _ _ HF1 C2) as HF2. rewrite (cp1_shape (cp1 x f)). eexists; split; [reflexivity | exact HF2].
  Qed.

  Ltac fobn :=
    cbn -[copy_op copy_while3 copy_do3 copy_tail cp1 place wrap32 zmask Z.sub Z.add Z.ltb Z.eqb Z.leb Z.land Z.shiftr Z.mul] in *;
    repeat first [ rewrite !fdrop_ob in * | rewrite !fpull_ob in * | rewrite !fpull2_if_ob in * | rewrite !fset_dist_ob in *
                 | rewrite !fset_len_ob in * | rewrite !fset_op_ob in * | rewrite !fset_from_ob in *
                 | rewrite !f_in_ob in * | rewrite !f_out_ob in * | rewrite !f_hold_ob in * | rewrite !f_bits_ob in *
                 | rewrite !f_len_ob in * | rewrite !f_dist_ob in * | rewrite !f_op_ob in * | rewrite !f_from_ob in * ].

  Lemma FR_eq : forall f g ob', f_out g = f_out f -> f_ob g = f_ob f -> FR f ob' -> FR g ob'.
  Proof. intros f g ob' E1 E2 HF. unfold FR in *. rewrite E1, E2. exact HF. Qed.
  Ltac rel_on lem HF C ob1 E1 HF1 :=
    lazymatch type of C with
    | ?g (fset_ob ?f0 ?o) = true => destruct (lem f0 o (FR_eq _ _ _ eq_refl eq_refl HF) C) as (ob1 & E1 & HF1)
    end.

  Lemma place_rel : forall f ob', FR f ob' -> placeG x ON (fset_ob f ob') = true ->
    exists ob1, place x (fset_ob f ob') = fset_ob (place x f) ob1 /\ FR (place x f) ob1.
  Proof.
    intros f ob' HF C. unfold place, placeG in *. fobn.
    destruct (x_wnext x =? 0).
    - destruct (f_op f <? f_len f); [| eexists; split; [reflexivity | exact HF]].
      rel_on copy_op_rel HF C ob1 E1 HF1. rewrite E1. fobn.
      eexists; split; [reflexivity | apply (FR_eq _ _ _ eq_refl eq_refl HF1)].
    - destruct (x_wnext x <? f_op f).
      + destruct (_ <? f_len f); [| eexists; split; [reflexivity | exact HF]].
        apply andb_prop in C as [C1 C2].
        rel_on copy_op_rel HF C1 ob1 E1 HF1. rewrite E1 in C2 |- *. fobn.
        destruct (x_wnext x <? _); [| eexists; split; [reflexivity | apply (FR_eq _ _ _ eq_refl eq_refl HF1)]].
        rel_on copy_op_rel HF1 C2 ob2 E2 HF2. rewrite E2. fobn.
        eexists; split; [reflexivity | apply (FR_eq _ _ _ eq_refl eq_refl HF2)].
      + destruct (_ <? f_len f); [| eexists; split; [reflexivity | exact HF]].
        rel_on copy_op_rel HF C ob1 E1 HF1. rewrite E1. fobn.
        eexists; split; [reflexivity | apply (FR_eq _ _ _ eq_refl eq_refl HF1)].
  Qed.

  Definition dist_pre (here : Z) (f : ffs) : ffs :=
    let f := fdrop f (code_bits here) in
    let f := fset_dist f (code_val here) in
    let op := Z.land (code_op here) 15 in
    let f := if f_bits f <? op then let f := fpull x f in if f_bits f <? op then fpull x f else f else f in
    let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
    fdrop f op.
  Lemma dist_pre_ob : forall here f ob, dist_pre here (fset_ob f ob) = fset_ob (dist_pre here f) ob.
  Proof. unfold dist_pre. ff_comm. Qed.
  Lemma dist_pre_out : forall here f, f_out (dist_pre here f) = f_out f.
  Proof. unfold dist_pre. ff_comm. Qed.
  Lemma dist_pre_obf : forall here f, f_ob (dist_pre here f) = f_ob f.
  Proof. unfold dist_pre. ff_comm. Qed.

  Lemma dodist_S : forall k here f, dodist (S k) x s here f =
    if negb (Z.land (code_op here) 16 =? 0) then
      let f1 := dist_pre here f in
      let opb := wrap32 (f_out f1 - x_beg x) in
      if opb <? f_dist f1 then
        let opw := wrap32 (f_dist f1 - opb) in
        if (x_whave x <? opw) && negb (x_sane x =? 0) then FBreak (fset_op f1 opw) BAD (Some MSG_invalid_distance_too_far_back)
        else FCont (copy_tail x (copy_while3 x (place x (fset_op f1 opw))))
      else FCont (copy_tail x (copy_do3 x (fset_from f1 (FOut (f_out f1 - f_dist f1)))))
    else if Z.land (code_op here) 64 =? 0 then
      dodist k x s (code_at s (is_distcode s) (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))) (fdrop f (code_bits here))
    else FBreak (fdrop f (code_bits here)) BAD (Some MSG_invalid_distance_code).
  Proof. reflexivity. Qed.

  Lemma dodistG_S : forall k here f, dodistG x s ON (S k) here f =
    if negb (Z.land (code_op here) 16 =? 0) then
      let f1 := dist_pre here f in
      let opb := wrap32 (f_out f1 - x_beg x) in
      if opb <? f_dist f1 then
        let opw := wrap32 (f_dist f1 - opb) in
        if (x_whave x <? opw) && negb (x_sane x =? 0) then true
        else placeG x ON (fset_op f1 opw) && (copy_while3G x ON (place x (fset_op f1 opw)) && copy_tailG x ON (copy_while3 x (place x (fset_op f1 opw))))
      else copy_do3G x ON (fset_from f1 (FOut (f_out f1 - f_dist f1))) && copy_tailG x ON (copy_do3 x (fset_from f1 (FOut (f_out f1 - f_dist f1))))
    else if Z.land (code_op here) 64 =? 0 then
      dodistG x s ON k (code_at s (is_distcode s) (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))) (fdrop f (code_bits here))
    else true.
  Proof. reflexivity. Qed.

  Definition fsmap (ob : arr) (st : fstep) : fstep :=
    match st with FCont f => FCont (fset_ob f ob) | FBreak f m g => FBreak (fset_ob f ob) m g end.
  Definition fsf (st : fstep) : ffs := match st with FCont f => f | FBreak f _ _ => f end.

  Lemma dodist_rel : forall k here f ob', FR f ob' -> dodistG x s ON k here (fset_ob f ob') = true ->
    exists ob1, dodist k x s here (fset_ob f ob') = fsmap ob1 (dodist k x s here f) /\ FR (fsf (dodist k x s here f)) ob1.
  Proof.
    induction k as [|k IH]; intros here f ob' HF C.
    - cbn. exists ob'. split; [reflexivity | exact HF].
    - rewrite !dodist_S. rewrite dodistG_S in C. rewrite !dist_pre_ob, !fdrop_ob, !f_hold_ob in C |- *.
      destruct (negb (Z.land (code_op here) 16 =? 0)).
      + set (f1 := dist_pre here f) in *.
        assert (HF1 : FR f1 ob') by (apply (FR_eq f); [apply dist_pre_out | apply dist_pre_obf | exact HF]).
        cbv zeta in C |- *. rewrite !f_out_ob, !f_dist_ob, !fset_op_ob, !fset_from_ob in C |- *.
        destruct (_ <? f_dist f1).
        * destruct (_ && _); [exists ob'; split; [reflexivity | apply (FR_eq _ _ _ eq_refl eq_refl HF1)]|].
          apply andb_prop in C as [C1 C]. apply andb_prop in C as [C2 C3].
          rel_on place_rel HF1 C1 ob1 E1 HG1. rewrite E1 in C2, C3 |- *.
          rel_on copy_while3_rel HG1 C2 ob2 E2 HG2. rewrite E2 in C3 |- *.
          rel_on copy_tail_rel HG2 C3 ob3 E3 HG3. rewrite E3. exists ob3. split; [reflexivity | exact HG3].
        * apply andb_prop in C as [C2 C3].
          rel_on copy_do3_rel HF1 C2 ob2 E2 HG2. rewrite E2 in C3 |- *.
          rel_on copy_tail_rel HG2 C3 ob3 E3 HG3. rewrite E3. exists ob3. split; [reflexivity | exact HG3].
      + destruct (Z.land (code_op here) 64 =? 0).
        * apply IH; [apply (FR_eq f); [ff_comm | ff_comm | exact HF] | exact C].
        * exists ob'. split; [reflexivity | apply (FR_eq f); [ff_comm | ff_comm | exact HF]].
  Qed.

  Definition len_pre (here : Z) (f : ffs) : ffs :=
    let f := fdrop f (code_bits here) in
    let f := fset_len f (code_val here) in
    let op := Z.land (code_op here) 15 in
    let f := if negb (op =? 0) then
               let f := if f_bits f <? op then fpull x f else f in
               let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
               fdrop f op
             else f in
    fpull2_if x f.
  Lemma len_pre_ob : forall here f ob, len_pre here (fset_ob f ob) = fset_ob (len_pre here f) ob.
  Proof.
    intros here f ob. unfold len_pre. rewrite fdrop_ob, fset_len_ob, f_bits_ob.
    destruct (negb _); [| apply fpull2_if_ob].
    destruct (_ <? _); rewrite ?fpull_ob, f_len_ob, f_hold_ob, fset_len_ob, fdrop_ob, fpull2_if_ob; reflexivity.
  Qed.
  Lemma len_pre_out : forall here f, f_out (len_pre here f) = f_out f.
  Proof.
    intros here f. unfold len_pre. rewrite f_out_pull2.
    destruct (negb _); [destruct (_ <? _)|]; rewrite ?f_out_drop, ?f_out_len, ?f_out_pull, ?f_out_len, ?f_out_drop; reflexivity.
  Qed.
  Lemma len_pre_obf : forall here f, f_ob (len_pre here f) = f_ob f.
  Proof.
    intros here f. unfold len_pre. rewrite f_ob_pull2.
    destruct (negb _); [destruct (_ <? _)|]; rewrite ?f_ob_drop, ?f_ob_len, ?f_ob_pull, ?f_ob_len, ?f_ob_drop; reflexivity.
  Qed.

  Lemma dolen_S : forall k here f, dolen (S k) x s here f =
    (let f0 := fdrop f (code_bits here) in
     if code_op here =? 0 then
       FCont (fset_out (fset_ob f0 (arr_set (f_ob f0) (f_out f0) (wrap8 (code_val here)))) (f_out (fset_ob f0 (arr_set (f_ob f0) (f_out f0) (wrap8 (code_val here)))) + 1))
     else if negb (Z.land (code_op here) 16 =? 0) then
       let f1 := len_pre here f in
       dodist 4 x s (code_at s (is_distcode s) (Z.land (f_hold f1) (x_dmask x))) f1
     else if Z.land (code_op here) 64 =? 0 then
       dolen k x s (code_at s (is_lencode s) (code_val here + Z.land (f_hold f0) (zmask (code_op here)))) f0
     else if negb (Z.land (code_op here) 32 =? 0) then FBreak f0 TYPE None
     else FBreak f0 BAD (Some MSG_invalid_literal_length_code)).
  Proof. reflexivity. Qed.

  Lemma dolenG_S : forall k here f, dolenG x s ON (S k) here f =
    (let f0 := fdrop f (code_bits here) in
     if code_op here =? 0 then (0 <=? f_out f0) && (f_out f0 <? ON)
     else if negb (Z.land (code_op here) 16 =? 0) then
       let f1 := len_pre here f in
       dodistG x s ON 4 (code_at s (is_distcode s) (Z.land (f_hold f1) (x_dmask x))) f1
     else if Z.land (code_op here) 64 =? 0 then
       dolenG x s ON k (code_at s (is_lencode s) (code_val here + Z.land (f_hold f0) (zmask (code_op here)))) f0
     else true).
  Proof. reflexivity. Qed.

  Lemma dolen_rel : forall k here f ob', FR f ob' -> dolenG x s ON k here (fset_ob f ob') = true ->
    exists ob1, dolen k x s here (fset_ob f ob') = fsmap ob1 (dolen k x s here f) /\ FR (fsf (dolen k x s here f)) ob1.
  Proof.
    induction k as [|k IH]; intros here f ob' HF C.
    - cbn. exists ob'. split; [reflexivity | exact HF].
    - rewrite !dolen_S. rewrite dolenG_S in C. cbv zeta in C |- *.
      rewrite ?len_pre_ob, ?fdrop_ob, ?f_hold_ob, ?f_out_ob, ?fset_ob_ob, ?fset_ob_twice in C. rewrite ?len_pre_ob, ?fdrop_ob, ?f_hold_ob, ?f_out_ob, ?fset_ob_ob, ?fset_ob_twice.
      destruct (code_op here =? 0).
      +
        apply andb_prop in C as [C0 C1]. apply Z.leb_le in C0. apply Z.ltb_lt in C1.
        set (f0 := fdrop f (code_bits here)) in *.
        assert (HF0 : FR f0 ob') by (apply (FR_eq f); [apply f_out_drop | apply f_ob_drop | exact HF]).
        exists (arr_set ob' (f_out f0) (wrap8 (code_val here))).
        rewrite fset_out_ob. split; [reflexivity|]. cbn [fsf].
        destruct HF0 as [AG L]. unfold FR. rewrite f_out_out, f_ob_out, fset_ob_ob, arr_len_set. split; [|exact L].
        apply (agree_below_set (f_out f0)); [exact AG | lia | lia].
      + destruct (negb (Z.land (code_op here) 16 =? 0)).
        * apply dodist_rel; [| exact C]. apply (FR_eq f); [apply len_pre_out | apply len_pre_obf | exact HF].
        * destruct (Z.land (code_op here) 64 =? 0).
          -- apply IH; [apply (FR_eq f); [apply f_out_drop | apply f_ob_drop | exact HF] | exact C].
          -- destruct (negb (Z.land (code_op here) 32 =? 0)); exists ob'; (split; [reflexivity|]); cbn [fsf];
               apply (FR_eq f); first [apply f_out_drop | apply f_ob_drop | exact HF].
  Qed.

  Lemma fast_trip_rel : forall f ob', FR f ob' -> fast_tripG x s ON (fset_ob f ob') = true ->
    exists ob1, fast_trip x s (fset_ob f ob') = fsmap ob1 (fast_trip x s f) /\ FR (fsf (fast_trip x s f)) ob1.
  Proof.
    intros f ob' HF C. unfold fast_trip, fast_tripG in *. rewrite !fpull2_if_ob, !f_hold_ob in C |- *.
    apply dolen_rel; [| exact C]. apply (FR_eq f); [apply f_out_pull2 | apply f_ob_pull2 | exact HF].
  Qed.

  Definition floop_step (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
    | FBreak f' mode msg => inr (f', Some (mode, msg))
    end.
  Definition floop_n (n : nat) (f : ffs) : ffs * option (Z * option Z) :=
    match iterK_nat n floop_step f with inl f' => (f', None) | inr b => b end.

  Lemma floop_n_S : forall n f, floop_n (S n) f =
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then floop_n n f' else (f', None)
    | FBreak f' mode msg => (f', Some (mode, msg))
    end.
  Proof.
    intros n f. unfold floop_n. cbn [iterK_nat]. unfold floop_step at 1.
    destruct (fast_trip x s f) as [f'|f' mode msg]; [|reflexivity].
    destruct (_ && _); reflexivity.
  Qed.

  Lemma floop_rel : forall n f ob', FR f ob' -> fast_loopN x s ON n (fset_ob f ob') = true ->
    exists ob1, floop_n n (fset_ob f ob') = (fset_ob (fst (floop_n n f)) ob1, snd (floop_n n f)) /\ FR (fst (floop_n n f)) ob1.
  Proof.
    induction n as [|n IH]; intros f ob' HF C.
    - exists ob'. split; [reflexivity | exact HF].
    - cbn [fast_loopN] in C. apply andb_prop in C as [C0 C]. rewrite !floop_n_S.
      destruct (fast_trip_rel f ob' HF C0) as (ob1 & E1 & HF1). rewrite E1 in C |- *.
      destruct (fast_trip x s f) as [f'|f' mode msg]; cbn [fsmap fsf] in C, HF1 |- *.
      + rewrite f_in_ob, f_out_ob in C |- *. destruct (_ && _); [exact (IH f' ob1 HF1 C)|].
        exists ob1. split; [reflexivity | exact HF1].
      + exists ob1. split; [reflexivity | exact HF1].
  Qed.
End FastRel.


Lemma ffx_of'_ob : forall s c ob r, ffx_of' s (icset_outbuf c ob) r = ffx_of' s c r.
Proof. intros s [] ob r; reflexivity. Qed.
Lemma ff0_of'_ob : forall s c ob, ff0_of' s (icset_outbuf c ob) = fset_ob (ff0_of' s c) ob.
Proof. intros s [] ob; reflexivity. Qed.
Lemma ffuel_ob : forall c ob, ffuel (icset_outbuf c ob) = ffuel c.
Proof. intros [] ob; reflexivity. Qed.

Definition ifast_fin (s : inflate_state) (c : icall) (r : iregs) (fm : ffs * option (Z * option Z)) : iw :=
  let x := ffx_of' s c r in
  let '(f, mm) := fm in
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  let f := fset_hold f (Z.land (f_hold f) (zmask (f_bits f))) in
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Lemma inflate_fast_floop : forall s c r,
  inflate_fast (mkW s c r) = ifast_fin s c r (floop_n (ffx_of' s c r) s (ffuel c) (ff0_of' s c)).
Proof.
  intros s c r. unfold inflate_fast, ifast_fin, floop_n, floop_step, ffx_of', ff0_of', ffuel. cbn [w_s w_c w_r].
  rewrite iterZ_nat. reflexivity.
Qed.

Definition ceq (c c' : icall) : Prop :=
  c' = icset_outbuf c (ic_outbuf c') /\ agree_below (ic_next_out c) (ic_outbuf c) (ic_outbuf c').


Theorem inflate_fast_rel : forall s c c' r,
  ceq c c' -> ffG (mkW s c' r) = true ->
  w_s (inflate_fast (mkW s c' r)) = w_s (inflate_fast (mkW s c r))
  /\ w_r (inflate_fast (mkW s c' r)) = w_r (inflate_fast (mkW s c r))
  /\ ceq (w_c (inflate_fast (mkW s c r))) (w_c (inflate_fast (mkW s c' r)))
  /\ arr_len (ic_outbuf (w_c (inflate_fast (mkW s c r)))) = arr_len (ic_outbuf c).
Proof.
  intros s c c' r [Ec AG] C. rewrite Ec in C |- *.
  set (ob' := ic_outbuf c') in *. clearbody ob'. clear Ec c'.
  unfold ffG in C. cbn [w_s w_c w_r] in C. rewrite ffx_of'_ob, ff0_of'_ob, ffuel_ob, ic_outbuf_set in C.
  rewrite !inflate_fast_floop. rewrite ffx_of'_ob, ff0_of'_ob, ffuel_ob.
  assert (HF : FR (arr_len (ic_outbuf c)) (ff0_of' s c) ob').
  { split; [| destruct c; reflexivity]. destruct c; cbn in *. exact AG. }
  rewrite (proj1 AG) in C.
  destruct (floop_rel (ffx_of' s c r) s (arr_len (ic_outbuf c)) (ffuel c) (ff0_of' s c) ob' HF C) as (ob1 & E1 & [AG1 L1]).
  rewrite E1. destruct (floop_n (ffx_of' s c r) s (ffuel c) (ff0_of' s c)) as [f mm]. cbn [fst snd] in *.
  unfold ifast_fin, ceq. rewrite !ffx_of'_ob.
  destruct f as [fin fout fhold fbits flen fdist fop ffrom fob]; destruct c; cbn -[Z.shiftr wrap32 Z.sub Z.add Z.ltb zmask Z.land Z.shiftl] in *.
  destruct mm as [[mode [msg|]]|]; cbn -[Z.shiftr wrap32 Z.sub Z.add Z.ltb zmask Z.land Z.shiftl];
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [split; [reflexivity | exact AG1] | exact L1]).
Qed.


Definition gFAST (w : iw) : bool := ffG (RESTORE w).



