(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zmask (n : Z) : Z := wrap32 (Z.shiftl 1 n - 1).

Inductive fromptr : Set := FWin (i : Z) | FOut (i : Z).
Definition from_succ (f : fromptr) : fromptr :=
  match f with FWin i => FWin (i + 1) | FOut i => FOut (i + 1) end.

Record ffs : Type := mkF {
  f_in : Z; f_out : Z; f_hold : Z; f_bits : Z;
  f_len : Z; f_dist : Z; f_op : Z;
  f_from : fromptr;
  f_ob : arr
}.
Definition fset_in (f : ffs) v := mkF v (f_out f) (f_hold f) (f_bits f) (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Definition fset_out (f : ffs) v := mkF (f_in f) v (f_hold f) (f_bits f) (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Definition fset_hold (f : ffs) v := mkF (f_in f) (f_out f) v (f_bits f) (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Definition fset_bits (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) v (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Definition fset_len (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) (f_bits f) v (f_dist f) (f_op f) (f_from f) (f_ob f).
Definition fset_dist (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) (f_bits f) (f_len f) v (f_op f) (f_from f) (f_ob f).
Definition fset_op (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) (f_bits f) (f_len f) (f_dist f) v (f_from f) (f_ob f).
Definition fset_from (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) (f_bits f) (f_len f) (f_dist f) (f_op f) v (f_ob f).
Definition fset_ob (f : ffs) v := mkF (f_in f) (f_out f) (f_hold f) (f_bits f) (f_len f) (f_dist f) (f_op f) (f_from f) v.

Record ffx : Type := mkFX {
  x_input : arr; x_last : Z; x_beg : Z; x_end : Z;
  x_wsize : Z; x_whave : Z; x_wnext : Z; x_window : arr;
  x_lmask : Z; x_dmask : Z; x_sane : Z
}.

Definition fpull (x : ffx) (f : ffs) : ffs :=
  let b := arr_get (x_input x) (f_in f) in
  let f := fset_hold f (wrap64 (f_hold f + shl64 b (f_bits f))) in
  let f := fset_bits f (wrap32 (f_bits f + 8)) in
  fset_in f (f_in f + 1).

Definition fpull2_if (x : ffx) (f : ffs) : ffs :=
  if f_bits f <? 15 then fpull x (fpull x f) else f.

Definition fdrop (f : ffs) (op : Z) : ffs :=
  fset_bits (fset_hold f (Z.shiftr (f_hold f) op)) (wrap32 (f_bits f - op)).

Definition cp1 (x : ffx) (f : ffs) : ffs :=
  let v := match f_from f with
           | FWin i => arr_get (x_window x) i
           | FOut i => arr_get (f_ob f) i
           end in
  let f := fset_ob f (arr_set (f_ob f) (f_out f) v) in
  let f := fset_out f (f_out f + 1) in
  fset_from f (from_succ (f_from f)).

Definition copy_op (x : ffx) (f : ffs) : ffs :=
  loopZ (f_op f)
    (fun f => let f := cp1 x f in
              let f := fset_op f (wrap32 (f_op f - 1)) in
              (negb (f_op f =? 0), f)) f.

Definition copy_while3 (x : ffx) (f : ffs) : ffs :=
  loopZ (f_len f)
    (fun f => if 2 <? f_len f then
                let f := cp1 x (cp1 x (cp1 x f)) in
                (true, fset_len f (wrap32 (f_len f - 3)))
              else (false, f)) f.

Definition copy_do3 (x : ffx) (f : ffs) : ffs :=
  loopZ (f_len f + 1)
    (fun f => let f := cp1 x (cp1 x (cp1 x f)) in
              let f := fset_len f (wrap32 (f_len f - 3)) in
              (2 <? f_len f, f)) f.

Definition copy_tail (x : ffx) (f : ffs) : ffs :=
  if negb (f_len f =? 0) then
    let f := cp1 x f in
    if 1 <? f_len f then cp1 x f else f
  else f.

Inductive fstep : Type :=
  | FCont (f : ffs)
  | FBreak (f : ffs) (mode : Z) (msg : option Z).

Fixpoint dodist (k : nat) (x : ffx) (s : inflate_state) (here : Z) (f : ffs) : fstep :=
  match k with
  | O => FCont f
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
        if (x_whave x <? op) && negb (x_sane x =? 0) then
          FBreak (fset_op f op) BAD (Some MSG_invalid_distance_too_far_back)
        else
        let f := fset_op f op in
        let f :=
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
            else f in
        let f := copy_while3 x f in
        FCont (copy_tail x f)
      else
        let f := fset_from f (FOut (f_out f - f_dist f)) in
        let f := copy_do3 x f in
        FCont (copy_tail x f)
    else if Z.land op 64 =? 0 then
      let here := code_at s (is_distcode s) (code_val here + Z.land (f_hold f) (zmask op)) in
      dodist k' x s here f
    else
      FBreak f BAD (Some MSG_invalid_distance_code)
  end.

Fixpoint dolen (k : nat) (x : ffx) (s : inflate_state) (here : Z) (f : ffs) : fstep :=
  match k with
  | O => FCont f
  | S k' =>
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then
      let f := fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val here))) in
      FCont (fset_out f (f_out f + 1))
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      let f := if negb (op =? 0) then
                 let f := if f_bits f <? op then fpull x f else f in
                 let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
                 fdrop f op
               else f in
      let f := fpull2_if x f in
      let here := code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask x)) in
      dodist 4 x s here f
    else if Z.land op 64 =? 0 then
      let here := code_at s (is_lencode s) (code_val here + Z.land (f_hold f) (zmask op)) in
      dolen k' x s here f
    else if negb (Z.land op 32 =? 0) then
      FBreak f TYPE None
    else
      FBreak f BAD (Some MSG_invalid_literal_length_code)
  end.

Definition fast_trip (x : ffx) (s : inflate_state) (f : ffs) : fstep :=
  let f := fpull2_if x f in
  let here := code_at s (is_lencode s) (Z.land (f_hold f) (x_lmask x)) in
  dolen 4 x s here f.

Definition inflate_fast (w : iw) : iw :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  let in_ := ic_next_in c in
  let last := in_ + wrap32 (ic_avail_in c - 5) in
  let out := ic_next_out c in
  let beg := out - wrap32 (ir_out r - ic_avail_out c) in
  let end_ := out + wrap32 (ic_avail_out c - 257) in
  let x := mkFX (ic_input c) last beg end_ (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
                (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s) in
  let f0 := mkF in_ out (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c) in
  let '(f, mm) :=
    iterZ (8 * ic_avail_in c + ic_avail_out c + 80)
      (fun f => match fast_trip x s f with
                | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f'
                              else inr (f', None)
                | FBreak f' mode msg => inr (f', Some (mode, msg))
                end)
      (fun f => (f, None)) f0 in
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
