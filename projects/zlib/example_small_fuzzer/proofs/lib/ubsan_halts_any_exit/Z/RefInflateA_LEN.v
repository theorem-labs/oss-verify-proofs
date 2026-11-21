(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1.

Module RefInflateA_LEN2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma iterZ_inv : forall {A B} (P : B -> Prop) n (step : A -> A + B) dflt,
  (forall a b, step a = inr b -> P b) -> (forall a, P (dflt a)) -> forall a, P (iterZ n step dflt a).
Proof.
  intros A B P n step dflt Hs Hd.
  assert (G : forall k a, P (match iterK_nat k step a with inl a' => dflt a' | inr b => b end)).
  { induction k as [|k IH]; intros a; cbn [iterK_nat]; [apply Hd|].
    destruct (step a) as [a'|b] eqn:E; [apply IH | exact (Hs _ _ E)]. }
  intros a. rewrite iterZ_nat. apply G.
Qed.

Lemma dodist_break : forall k x s here f f' md mg, dodist k x s here f = FBreak f' md mg -> md = BAD.
Proof.
  induction k as [|k IH]; intros x s here f f' md mg H; [discriminate H|].
  cbn [dodist] in H. cbv zeta in H.
  destruct (negb (Z.land (code_op here) 16 =? 0)).
  - cbv zeta in H.
    match type of H with (if ?b then _ else _) = _ => destruct b end.
    + match type of H with (if ?b then _ else _) = _ => destruct b end; [injection H; intros; subst; reflexivity | discriminate H].
    + discriminate H.
  - destruct (Z.land (code_op here) 64 =? 0); [exact (IH _ _ _ _ _ _ _ H) | injection H; intros; subst; reflexivity].
Qed.

Lemma dolen_break : forall k x s here f f' md mg, dolen k x s here f = FBreak f' md mg -> md = TYPE \/ md = BAD.
Proof.
  induction k as [|k IH]; intros x s here f f' md mg H; [discriminate H|].
  cbn [dolen] in H. cbv zeta in H.
  destruct (code_op here =? 0); [discriminate H|].
  destruct (negb (Z.land (code_op here) 16 =? 0)); [right; exact (dodist_break _ _ _ _ _ _ _ _ H)|].
  destruct (Z.land (code_op here) 64 =? 0); [exact (IH _ _ _ _ _ _ _ H)|].
  destruct (negb (Z.land (code_op here) 32 =? 0)); injection H; intros; subst; [left | right]; reflexivity.
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

Lemma lf_loop_mode : forall s c r, match snd (lf_loop s c r) with Some (md, _) => md = TYPE \/ md = BAD | None => True end.
Proof.
  intros s c r. unfold lf_loop.
  apply (iterZ_inv (fun p : ffs * option (Z * option Z) => match snd p with Some (md, _) => md = TYPE \/ md = BAD | None => True end)).
  - intros a b H. destruct (fast_trip (ffx_of s c r) s a) as [f'|f' mode msg] eqn:E.
    + destruct (_ && _); [discriminate H|]. injection H as <-. exact I.
    + injection H as <-. cbn [snd]. unfold fast_trip in E. exact (dolen_break _ _ _ _ _ _ _ _ E).
  - intros a. exact I.
Qed.

Lemma lf_shape : forall s c r,
  exists fh fb (om : option Z) ob fi fo ai ao (omsg : option Z),
    (om = None \/ om = Some TYPE \/ om = Some BAD)
    /\ w_s (inflate_fast (mkW s c r)) = match om with Some md => iset_mode (iset_bits (iset_hold s fh) fb) md | None => iset_bits (iset_hold s fh) fb end
    /\ w_r (inflate_fast (mkW s c r)) = r
    /\ w_c (inflate_fast (mkW s c r)) =
         let c1 := icset_avail_out (icset_avail_in (icset_next_out (icset_next_in (icset_outbuf c ob) fi) fo) ai) ao in
         match omsg with Some mg => icset_msg c1 mg | None => c1 end.
Proof.
  intros s c r. pose proof (lf_loop_mode s c r) as X. rewrite lf_eq. destruct (lf_loop s c r) as [f mm]. cbn [snd] in X.
  unfold lf_post.
  set (ai := wrap32 (if f_in (lf_fin f) <? x_last (ffx_of s c r) then 5 + (x_last (ffx_of s c r) - f_in (lf_fin f)) else 5 - (f_in (lf_fin f) - x_last (ffx_of s c r)))).
  set (ao := wrap32 (if f_out (lf_fin f) <? x_end (ffx_of s c r) then 257 + (x_end (ffx_of s c r) - f_out (lf_fin f)) else 257 - (f_out (lf_fin f) - x_end (ffx_of s c r)))).
  destruct mm as [[md mg]|].
  - exists (f_hold (lf_fin f)), (f_bits (lf_fin f)), (Some md), (f_ob (lf_fin f)), (f_in (lf_fin f)), (f_out (lf_fin f)), ai, ao, mg.
    split; [destruct X as [-> | ->]; [right; left | right; right]; reflexivity|].
    destruct mg as [mg|]; cbn [w_s w_r w_c]; (split; [reflexivity|]); (split; [reflexivity|]); destruct c; reflexivity.
  - exists (f_hold (lf_fin f)), (f_bits (lf_fin f)), (@None Z), (f_ob (lf_fin f)), (f_in (lf_fin f)), (f_out (lf_fin f)), ai, ao, (@None Z).
    split; [left; reflexivity|]. cbn [w_s w_r w_c]. split; [reflexivity|]. split; [reflexivity|]. destruct c; reflexivity.
Qed.
End RefInflateA_LEN2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LEN2.

Module RefInflateA_LENF.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LEN2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lf_shape' : forall s c r,
  exists fh fb md ob fi fo ai ao (omsg : option Z),
    (md = is_mode s \/ md = TYPE \/ md = BAD)
    /\ w_s (inflate_fast (mkW s c r)) = iset_mode (iset_bits (iset_hold s fh) fb) md
    /\ w_r (inflate_fast (mkW s c r)) = r
    /\ w_c (inflate_fast (mkW s c r)) =
         let c1 := icset_avail_out (icset_avail_in (icset_next_out (icset_next_in (icset_outbuf c ob) fi) fo) ai) ao in
         match omsg with Some mg => icset_msg c1 mg | None => c1 end.
Proof.
  intros s c r. destruct (lf_shape s c r) as (fh & fb & om & ob & fi & fo & ai & ao & omsg & Hom & Es & Er & Ec).
  destruct om as [md|].
  - exists fh, fb, md, ob, fi, fo, ai, ao, omsg. split; [destruct Hom as [X|[X|X]]; [discriminate X | injection X as ->; right; left; reflexivity | injection X as ->; right; right; reflexivity]|].
    split; [exact Es|]. split; [exact Er | exact Ec].
  - exists fh, fb, (is_mode s), ob, fi, fo, ai, ao, omsg. split; [left; reflexivity|].
    split; [rewrite Es; destruct s; reflexivity|]. split; [exact Er | exact Ec].
Qed.

Lemma icset5_facts : forall c ob fi fo ai ao,
  let c1 := icset_avail_out (icset_avail_in (icset_next_out (icset_next_in (icset_outbuf c ob) fi) fo) ai) ao in
  ic_next_in c1 = fi /\ ic_avail_in c1 = ai /\ ic_next_out c1 = fo /\ ic_avail_out c1 = ao
  /\ ic_input c1 = ic_input c /\ ic_outbuf c1 = ob /\ zstrm_of_icall c1 = zstrm_of_icall c
  /\ ic_total_in c1 = ic_total_in c /\ ic_total_out c1 = ic_total_out c /\ ic_adler c1 = ic_adler c /\ ic_data_type c1 = ic_data_type c.
Proof. intros. destruct c. repeat split; reflexivity. Qed.


Lemma icm_facts : forall (c5 : icall) (omsg : option Z),
  let c1 := match omsg with Some mg => icset_msg c5 mg | None => c5 end in
  ic_next_in c1 = ic_next_in c5 /\ ic_avail_in c1 = ic_avail_in c5 /\ ic_next_out c1 = ic_next_out c5 /\ ic_avail_out c1 = ic_avail_out c5
  /\ ic_input c1 = ic_input c5 /\ ic_outbuf c1 = ic_outbuf c5
  /\ ic_total_in c1 = ic_total_in c5 /\ ic_total_out c1 = ic_total_out c5 /\ ic_adler c1 = ic_adler c5 /\ ic_data_type c1 = ic_data_type c5.
Proof. intros c5 omsg. destruct omsg; destruct c5; repeat split; reflexivity. Qed.

Section ArmLENcall.
  Hypothesis HCONGR : inflate_fast_congr_stmt.
  Hypothesis HFRAME : inflate_fast_frame_stmt.

  Definition rL_of (s1 : inflate_state) (c1 : icall) (r : iregs) : iregs :=
    mkIR (ic_next_in c1) (ic_avail_in c1) (ic_next_out c1) (ic_avail_out c1) (is_hold s1) (is_bits s1) (ir_in r) (ir_out r) (ir_ret r).
End ArmLENcall.
End RefInflateA_LENF.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LENF.

Module RefInflateA_LEN3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition len_tail2 (c : icall) (op : Z) (s' : inflate_state) (r' : iregs) : ares unit :=
  if negb (Z.land op 32 =? 0) then ARun tt (mkW (iset_mode (iset_back s' (-1)) TYPE) c r')
  else if negb (Z.land op 64 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_invalid_literal_length_code) r')
  else arm_LENEXT ivar_ref (mkW (iset_mode (iset_extra s' (Z.land op 15)) LENEXT) c r').
Definition ltab (s : inflate_state) : Z -> Z := code_at s (is_lencode s).
Definition lN (s : inflate_state) : Z := ctab_len (is_lencode s).

Section ArmLEN3.
End ArmLEN3.

Section ArmLENtail.
  Variable arm_ok : Z -> iw -> bool.

End ArmLENtail.
End RefInflateA_LEN3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LEN3.

Module RefInflateA_LEN4.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateArmLib3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateA_DIST2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LEN3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lreg_in := cbn; repeat (first [ left; reflexivity | right ]).

Section ArmLEN4.
End ArmLEN4.
End RefInflateA_LEN4.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN.RefInflateA_LEN4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma addback0 : forall s0 hb, is_back s0 = 0 -> 0 <= hb < 256 -> addback s0 hb = iset_back s0 hb.
Proof.
  intros s0 hb H0 Hhb. unfold addback. rewrite H0, Z.add_0_l, swrap32_small by lia. reflexivity.
Qed.
Lemma addback00 : forall s0 lb hb, is_back s0 = 0 -> 0 <= lb < 256 -> 0 <= hb < 256 ->
  addback (addback s0 lb) hb = iset_back s0 (hb + lb).
Proof.
  intros s0 lb hb H0 Hlb Hhb. unfold addback. rewrite H0, Z.add_0_l, (swrap32_small lb) by lia.
  destruct s0; cbn. rewrite swrap32_small by lia. rewrite (Z.add_comm lb hb). reflexivity.
Qed.

Lemma len_tail_0 : forall c here r sb, code_op here = 0 ->
  len_tail c here r sb = ARun tt (mkW (iset_mode (iset_length (addback sb (code_bits here)) (code_val here)) LIT) c (ddrop r (code_bits here))).
Proof. intros c here r sb H. unfold len_tail. rewrite H. reflexivity. Qed.
Lemma len_tail_ne0 : forall c here r sb, code_op here <> 0 ->
  len_tail c here r sb = len_tail2 c (code_op here) (iset_length (addback sb (code_bits here)) (code_val here)) (ddrop r (code_bits here)).
Proof. intros c here r sb H. unfold len_tail, len_tail2. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.


Section ArmLEN.
  Variable arm_ok : Z -> iw -> bool.
  Hypothesis OK_LEN : forall flush w, is_mode (w_s w) = LEN -> arm_ok flush w = true ->
    leave_okb (w_s w) = true /\ len_okb w = true.
  Hypothesis OK_LEN_ : forall flush s c r, is_mode s = LEN_ -> arm_ok flush (mkW s c r) = true ->
    arm_ok flush (mkW (iset_mode s LEN) c r) = true.
  Hypothesis OK_LEN_next : forall flush w w2, is_mode (w_s w) = LEN -> arm_ok flush w = true ->
    len_next w = Some w2 -> arm_ok flush w2 = true.
  Hypothesis HCONGR : inflate_fast_congr_stmt.
  Hypothesis HFRAME : inflate_fast_frame_stmt.
End ArmLEN.
