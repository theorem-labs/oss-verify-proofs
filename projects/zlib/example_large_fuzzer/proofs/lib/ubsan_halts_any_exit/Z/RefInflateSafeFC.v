(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeFF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [dodist dolen fast_trip dodist_ok dolen_ok trip_ok].


Definition obrel (out : Z) (a b : arr) : Prop :=
  arr_len b = arr_len a /\ forall i, 0 <= i < out -> arr_get b i = arr_get a i.


Lemma fpull_ob : forall x f ob, fpull x (fset_ob f ob) = fset_ob (fpull x f) ob. Proof. intros x [] ob; reflexivity. Qed.
Lemma fpull2_if_ob : forall x f ob, fpull2_if x (fset_ob f ob) = fset_ob (fpull2_if x f) ob.
Proof. intros x f ob. unfold fpull2_if. cbn [f_bits fset_ob]. destruct f as [a1 a2 a3 a4 a5 a6 a7 a8 a9]; cbn [f_bits]. destruct (a4 <? 15); [rewrite !fpull_ob|]; reflexivity. Qed.
Lemma fdrop_ob : forall f op ob, fdrop (fset_ob f ob) op = fset_ob (fdrop f op) ob. Proof. intros [] op ob; reflexivity. Qed.
Lemma fset_len_ob : forall f v ob, fset_len (fset_ob f ob) v = fset_ob (fset_len f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_dist_ob : forall f v ob, fset_dist (fset_ob f ob) v = fset_ob (fset_dist f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_op_ob : forall f v ob, fset_op (fset_ob f ob) v = fset_ob (fset_op f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_from_ob : forall f v ob, fset_from (fset_ob f ob) v = fset_ob (fset_from f v) ob. Proof. intros [] v ob; reflexivity. Qed.
Lemma fset_ob_ob : forall f a b, fset_ob (fset_ob f a) b = fset_ob f b. Proof. intros [] a b; reflexivity. Qed.
Lemma f_ob_fset_ob : forall f ob, f_ob (fset_ob f ob) = ob. Proof. intros [] ob; reflexivity. Qed.
Lemma scal_ob : forall f ob,
  f_in (fset_ob f ob) = f_in f /\ f_out (fset_ob f ob) = f_out f /\ f_hold (fset_ob f ob) = f_hold f /\ f_bits (fset_ob f ob) = f_bits f
  /\ f_len (fset_ob f ob) = f_len f /\ f_dist (fset_ob f ob) = f_dist f /\ f_op (fset_ob f ob) = f_op f /\ f_from (fset_ob f ob) = f_from f.
Proof. intros [] ob; repeat split; reflexivity. Qed.

Ltac obn := rewrite ?fpull_ob, ?fpull2_if_ob, ?fdrop_ob, ?fset_len_ob, ?fset_dist_ob, ?fset_op_ob, ?fset_from_ob, ?fset_ob_ob, ?f_ob_fset_ob.
Ltac obs f ob := let H := fresh in pose proof (scal_ob f ob) as H;
  rewrite ?(proj1 H), ?(proj1 (proj2 H)), ?(proj1 (proj2 (proj2 H))), ?(proj1 (proj2 (proj2 (proj2 H)))),
          ?(proj1 (proj2 (proj2 (proj2 (proj2 H))))), ?(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))),
          ?(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))), ?(proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) in *; clear H.


Definition fromOK (f : ffs) : Prop := forall i, f_from f = FOut i -> 0 <= i < f_out f.

Definition OBR (f : ffs) (g : ffs) : Prop := exists ob, g = fset_ob f ob /\ obrel (f_out f) (f_ob f) ob.
Definition OBRF (f : ffs) (g : ffs) : Prop := OBR f g /\ fromOK f.







Definition RREL (ON lo : Z) (r1 r2 : InflateFast.fstep) : Prop :=
  match r1, r2 with
  | FCont f1, FCont f2 => OBR f1 f2 /\ lo <= f_out f1 /\ arr_len (f_ob f1) = ON
  | FBreak f1 m1 g1, FBreak f2 m2 g2 => OBR f1 f2 /\ lo <= f_out f1 /\ arr_len (f_ob f1) = ON /\ m2 = m1 /\ g2 = g1
  | _, _ => False
  end.

Definition dpulls (x : ffx) (e : Z) (f : ffs) : ffs :=
  if f_bits f <? e then (if f_bits (fpull x f) <? e then fpull x (fpull x f) else fpull x f) else f.
Definition dext (x : ffx) (e : Z) (f : ffs) : ffs :=
  let f := dpulls x e f in
  fdrop (fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask e)))) e.

Section B.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

End B.


Section B2.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

End B2.


Section CheckerOb.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.

End CheckerOb.


Section Loop.
  Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis HON : ON < 2 ^ 32.

  Let mstep := fun f => match fast_trip x s f with
                        | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', @None (Z * option Z))
                        | FBreak f' mode msg => inr (f', Some (mode, msg))
                        end.
  Let cstep := fun f => if trip_ok x s IN ON WN f then
                          match fast_trip x s f with
                          | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (exit_ok f')
                          | FBreak f' _ _ => inr (exit_ok f')
                          end
                        else inr false.

End Loop.


Definition ffloop (x : ffx) (s : inflate_state) (fuel : Z) (f0 : ffs) : ffs * option (Z * option Z) :=
  iterZ fuel
    (fun f => match fast_trip x s f with
              | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
              | FBreak f' mode msg => inr (f', Some (mode, msg))
              end)
    (fun f => (f, None)) f0.
Definition fffin (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).
Definition ffpost (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
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

