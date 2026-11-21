(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Checker.
Variable x : ffx.
Variable s : inflate_state.
Variable IN : Z.
Variable ON : Z.
Variable WN : Z.   (* [comment removed for export] *)
Let LCN := ctab_len (is_lencode s).
Let DCN := ctab_len (is_distcode s).

Definition pull2_ok (f : ffs) : bool :=
  if f_bits f <? 15 then f_in f + 2 <=? IN else true.

(* [comment removed for export] *)
Definition window_ok (f : ffs) : bool :=
  let opw := f_op f in let len := f_len f in let out := f_out f in
  (out + len <=? ON) &&
  if x_wnext x =? 0 then
    (opw <=? x_wsize x) &&
    (if opw <? len then x_wsize x - opw + opw <=? WN else x_wsize x - opw + len <=? WN)
  else if x_wnext x <? opw then
    (opw <=? x_wsize x + x_wnext x) &&
    let opp := opw - x_wnext x in
    (if opp <? len
     then (x_wsize x + x_wnext x - opw + opp <=? WN) &&
          (if x_wnext x <? len - opp then x_wnext x <=? WN else len - opp <=? WN)
     else x_wsize x + x_wnext x - opw + len <=? WN)
  else
    (if opw <? len then x_wnext x - opw + opw <=? WN else x_wnext x - opw + len <=? WN).

Fixpoint dodist_ok (k : nat) (here : Z) (f : ffs) : bool :=
  match k with
  | O => false
  | S k' =>
    let op := code_bits here in
    (op <=? f_bits f) &&
    let f := fdrop f op in
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let f := fset_dist f (code_val here) in
      let op := Z.land op 15 in
      (if f_bits f <? op then (f_in f + 1 <=? IN) && (if f_bits f + 8 <? op then f_in f + 2 <=? IN else true) else true) &&
      let f := if f_bits f <? op then
                 let f := fpull x f in
                 if f_bits f <? op then fpull x f else f
               else f in
      (op <=? f_bits f) &&
      let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
      let f := fdrop f op in
      (1 <=? f_dist f) && (3 <=? f_len f) && (f_out f + f_len f <=? ON) &&
      let op := wrap32 (f_out f - x_beg x) in
      if op <? f_dist f then
        let op := wrap32 (f_dist f - op) in
        if (x_whave x <? op) && negb (x_sane x =? 0) then true
        else window_ok (fset_op f op)
      else true
    else if Z.land op 64 =? 0 then
      (op <? 16) &&
      let i := code_val here + Z.land (f_hold f) (zmask op) in
      (i <? DCN) && dodist_ok k' (code_at s (is_distcode s) i) f
    else true
  end.

Fixpoint dolen_ok (k : nat) (here : Z) (f : ffs) : bool :=
  match k with
  | O => false
  | S k' =>
    let op := code_bits here in
    (op <=? f_bits f) &&
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then f_out f <? ON
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      (if negb (op =? 0) then if f_bits f <? op then (f_in f + 1 <=? IN) && (op <=? f_bits f + 8) else true else true) &&
      let f := if negb (op =? 0) then
                 let f := if f_bits f <? op then fpull x f else f in
                 let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
                 fdrop f op
               else f in
      pull2_ok f &&
      let f := fpull2_if x f in
      let i := Z.land (f_hold f) (x_dmask x) in
      (i <? DCN) && dodist_ok 4 (code_at s (is_distcode s) i) f
    else if Z.land op 64 =? 0 then
      (op <? 16) &&
      let i := code_val here + Z.land (f_hold f) (zmask op) in
      (i <? LCN) && dolen_ok k' (code_at s (is_lencode s) i) f
    else true
  end.

Definition trip_ok (f : ffs) : bool :=
  pull2_ok f &&
  let f := fpull2_if x f in
  let i := Z.land (f_hold f) (x_lmask x) in
  (i <? LCN) && dolen_ok 4 (code_at s (is_lencode s) i) f.

(* [comment removed for export] *)
Definition exit_ok (f : ffs) : bool := Z.shiftr (f_bits f) 3 <=? f_in f.

(* [comment removed for export] *)
Definition loop_ok (fuel : Z) (f0 : ffs) : bool :=
  iterZ fuel
    (fun f => if trip_ok f then
                match fast_trip x s f with
                | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (exit_ok f')
                | FBreak f' _ _ => inr (exit_ok f')
                end
              else inr false)
    (fun _ => false) f0.
End Checker.

(* [comment removed for export] *)
Definition ff_ok (s : inflate_state) (c : icall) (r : iregs) : bool :=
  loop_ok (ffx_of s c r) s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s))
          (8 * ic_avail_in c + ic_avail_out c + 80) (ff0_of s c).
