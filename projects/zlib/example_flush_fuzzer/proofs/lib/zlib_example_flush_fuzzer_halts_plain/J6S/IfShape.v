(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InffastModel InffastCtx.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Lemma iterZ_inv : forall {A B} (P : B -> Prop) n (step : A -> A + B) dflt,
  (forall a b, step a = inr b -> P b) -> (forall a, P (dflt a)) -> forall a, P (iterZ n step dflt a).
Proof.
  intros A B P n step dflt Hs Hd.
  assert (G : forall k a, P (match iterK_nat k step a with inl a' => dflt a' | inr b => b end)).
  { induction k as [|k IH]; intros a; cbn [iterK_nat]; [apply Hd|].
    destruct (step a) as [a'|b] eqn:E; [apply IH | exact (Hs _ _ E)]. }
  intros a. rewrite iterZ_nat. apply G.
Qed.



Definition lf_loop (s : inflate_state) (c : icall) (r : iregs) : ffs * option (Z * option Z) :=
  iterZ (8 * ic_avail_in c + ic_avail_out c + 80)
    (fun f => match fast_trip (ffx_of s c r) s f with
              | FCont f' => if (f_in f' <? x_last (ffx_of s c r)) && (f_out f' <? x_end (ffx_of s c r)) then inl f'
                            else inr (f', None)
              | FBreak f' mode msg => inr (f', Some (mode, msg))
              end)
    (fun f => (f, None)) (ff0_of s c).
Definition lf_fin (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).
Definition lf_post (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
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
Lemma lf_eq : forall s c r, inflate_fast (mkW s c r) = let '(f, mm) := lf_loop s c r in lf_post s c r (ffx_of s c r) (lf_fin f) mm.
Proof. intros. reflexivity. Qed.





Definition lf_msg_ok (mg : option Z) : Prop :=
  mg = None \/ mg = Some MSG_invalid_literal_length_code \/ mg = Some MSG_invalid_distance_code \/ mg = Some MSG_invalid_distance_too_far_back.

Lemma dodist_break_msg : forall k x s here f f' md mg, dodist k x s here f = FBreak f' md mg -> md = BAD /\ lf_msg_ok mg.
Proof.
  induction k as [|k IH]; intros x s here f f' md mg H; [discriminate H|].
  cbn [dodist] in H. cbv zeta in H.
  destruct (negb (Z.land (code_op here) 16 =? 0)).
  - cbv zeta in H.
    match type of H with (if ?b then _ else _) = _ => destruct b end.
    + match type of H with (if ?b then _ else _) = _ => destruct b end; [injection H; intros; subst; split; [reflexivity | right; right; right; reflexivity] | discriminate H].
    + discriminate H.
  - destruct (Z.land (code_op here) 64 =? 0); [exact (IH _ _ _ _ _ _ _ H) | injection H; intros; subst; split; [reflexivity | right; right; left; reflexivity]].
Qed.

Lemma dolen_break_msg : forall k x s here f f' md mg, dolen k x s here f = FBreak f' md mg -> (md = TYPE \/ md = BAD) /\ lf_msg_ok mg.
Proof.
  induction k as [|k IH]; intros x s here f f' md mg H; [discriminate H|].
  cbn [dolen] in H. cbv zeta in H.
  destruct (code_op here =? 0); [discriminate H|].
  destruct (negb (Z.land (code_op here) 16 =? 0)); [destruct (dodist_break_msg _ _ _ _ _ _ _ _ H) as [-> M]; split; [right; reflexivity | exact M]|].
  destruct (Z.land (code_op here) 64 =? 0); [exact (IH _ _ _ _ _ _ _ H)|].
  destruct (negb (Z.land (code_op here) 32 =? 0)); injection H; intros; subst; (split; [| first [left; reflexivity | right; left; reflexivity]]); [left | right]; reflexivity.
Qed.

Lemma lf_loop_msg : forall s c r, match snd (lf_loop s c r) with Some (md, mg) => (md = TYPE \/ md = BAD) /\ lf_msg_ok mg | None => True end.
Proof.
  intros s c r. unfold lf_loop.
  apply (iterZ_inv (fun p : ffs * option (Z * option Z) => match snd p with Some (md, mg) => (md = TYPE \/ md = BAD) /\ lf_msg_ok mg | None => True end)).
  - intros a b H. destruct (fast_trip (ffx_of s c r) s a) as [f'|f' mode msg] eqn:E.
    + destruct (_ && _); [discriminate H|]. injection H as <-. exact I.
    + injection H as <-. cbn [snd]. unfold fast_trip in E. exact (dolen_break_msg _ _ _ _ _ _ _ _ E).
  - intros a. exact I.
Qed.

Lemma lf_shape_msg : forall s c r,
  exists fh fb (om : option Z) ob fi fo ai ao (omsg : option Z),
    (om = None \/ om = Some TYPE \/ om = Some BAD) /\ lf_msg_ok omsg
    /\ w_s (inflate_fast (mkW s c r)) = match om with Some md => iset_mode (iset_bits (iset_hold s fh) fb) md | None => iset_bits (iset_hold s fh) fb end
    /\ w_r (inflate_fast (mkW s c r)) = r
    /\ w_c (inflate_fast (mkW s c r)) =
         let c1 := icset_avail_out (icset_avail_in (icset_next_out (icset_next_in (icset_outbuf c ob) fi) fo) ai) ao in
         match omsg with Some mg => icset_msg c1 mg | None => c1 end.
Proof.
  intros s c r. pose proof (lf_loop_msg s c r) as X. rewrite lf_eq. destruct (lf_loop s c r) as [f mm]. cbn [snd] in X.
  unfold lf_post.
  set (ai := wrap32 (if f_in (lf_fin f) <? x_last (ffx_of s c r) then 5 + (x_last (ffx_of s c r) - f_in (lf_fin f)) else 5 - (f_in (lf_fin f) - x_last (ffx_of s c r)))).
  set (ao := wrap32 (if f_out (lf_fin f) <? x_end (ffx_of s c r) then 257 + (x_end (ffx_of s c r) - f_out (lf_fin f)) else 257 - (f_out (lf_fin f) - x_end (ffx_of s c r)))).
  destruct mm as [[md mg]|].
  - destruct X as [Xmd Xmg].
    exists (f_hold (lf_fin f)), (f_bits (lf_fin f)), (Some md), (f_ob (lf_fin f)), (f_in (lf_fin f)), (f_out (lf_fin f)), ai, ao, mg.
    split; [destruct Xmd as [-> | ->]; [right; left | right; right]; reflexivity|]. split; [exact Xmg|].
    destruct mg as [mg|]; cbn [w_s w_r w_c]; (split; [reflexivity|]); (split; [reflexivity|]); destruct c; reflexivity.
  - exists (f_hold (lf_fin f)), (f_bits (lf_fin f)), (@None Z), (f_ob (lf_fin f)), (f_in (lf_fin f)), (f_out (lf_fin f)), ai, ao, (@None Z).
    split; [left; reflexivity|]. split; [left; reflexivity|]. cbn [w_s w_r w_c]. split; [reflexivity|]. split; [reflexivity|]. destruct c; reflexivity.
Qed.
End FXG.
