(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition lbase_l : list Z :=
  [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
   35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258; 0; 0].
Definition lext_l : list Z :=
  [16; 16; 16; 16; 16; 16; 16; 16; 17; 17; 17; 17; 18; 18; 18; 18;
   19; 19; 19; 19; 20; 20; 20; 20; 21; 21; 21; 21; 16; 71; 77].
Definition dbase_l : list Z :=
  [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
   257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145;
   8193; 12289; 16385; 24577; 0; 0].
Definition dext_l : list Z :=
  [16; 16; 16; 16; 17; 17; 18; 18; 19; 19; 20; 20; 21; 21; 22; 22;
   23; 23; 24; 24; 25; 25; 26; 26; 27; 27; 28; 28; 29; 29; 64; 64].
Definition lbase_a : arr := arr_of_list lbase_l.
Definition lext_a : arr := arr_of_list lext_l.
Definition dbase_a : arr := arr_of_list dbase_l.
Definition dext_a : arr := arr_of_list dext_l.

Definition codetype_eqb (a b : codetype) : bool :=
  match a, b with CODES, CODES | LENS, LENS | DISTS, DISTS => true | _, _ => false end.

Definition it_match (ty : codetype) : Z :=
  match ty with CODES => 20 | LENS => 257 | DISTS => 0 end.
Definition it_base (ty : codetype) (work : arr) (i : Z) : Z :=
  match ty with CODES => arr_get work i | LENS => arr_get lbase_a i | DISTS => arr_get dbase_a i end.
Definition it_extra (ty : codetype) (work : arr) (i : Z) : Z :=
  match ty with CODES => arr_get work i | LENS => arr_get lext_a i | DISTS => arr_get dext_a i end.

Definition it_not_enough (ty : codetype) (used : Z) : bool :=
  match ty with
  | LENS => Z.ltb ENOUGH_LENS used
  | DISTS => Z.ltb ENOUGH_DISTS used
  | CODES => false
  end.


Definition it_zero_count (count : arr) : arr :=
  forZ 0 (MAXBITS + 1) (fun len cnt => arr_set cnt len 0) count.

Definition it_count (lens : arr) (lens_ofs codes : Z) (count : arr) : arr :=
  forZ 0 codes (fun sym cnt =>
    let l := arr_get lens (lens_ofs + sym) in
    arr_set cnt l (wrap16 (arr_get cnt l + 1))) count.

Definition it_find_max (count : arr) : Z :=
  loopZ 16 (fun max => if (1 <=? max) && (arr_get count max =? 0) then (true, max - 1) else (false, max)) MAXBITS.

Definition it_find_min (count : arr) (max : Z) : Z :=
  loopZ 16 (fun min => if (min <? max) && (arr_get count min =? 0) then (true, min + 1) else (false, min)) 1.

Definition it_left_check (count : arr) : option Z :=
  iterZ 16
    (fun st : Z * Z => let '(len, lft) := st in
       if len <=? MAXBITS then
         let lft := Z.shiftl lft 1 in
         let lft := lft - arr_get count len in
         if lft <? 0 then inr None else inl (len + 1, lft)
       else inr (Some lft))
    (fun st => Some (snd st)) (1, 1).

Definition it_offs (count : arr) (offs : arr) : arr :=
  let offs := arr_set offs 1 0 in
  forZ 1 MAXBITS (fun len o => arr_set o (len + 1) (wrap16 (arr_get o len + arr_get count len))) offs.

Definition it_sort (lens : arr) (lens_ofs codes : Z) (ow : arr * arr) : arr * arr :=
  forZ 0 codes (fun sym ow =>
    let '(offs, work) := ow in
    let l := arr_get lens (lens_ofs + sym) in
    if negb (l =? 0) then
      let o := arr_get offs l in
      (arr_set offs l (wrap16 (o + 1)), arr_set work o (wrap16 sym))
    else (offs, work)) ow.


Record ItCtx : Type := mkItCtx {
  x_ty : codetype;
  x_lens : arr; x_lens_ofs : Z;
  x_table : Z ;
  x_root : Z; x_max : Z; x_mask : Z
}.

Record ItSt : Type := mkItSt {
  t_huff : Z; t_sym : Z; t_len : Z;
  t_next : Z ;
  t_curr : Z; t_drop : Z; t_low : Z; t_used : Z;
  t_min : Z ;
  t_count : arr; t_tbl : arr; t_work : arr
}.

Inductive ItStep : Type :=
  | ItCont (st : ItSt)
  | ItBreak (st : ItSt)
  | ItFail (st : ItSt).

Definition it_fill (here incr : Z) (huff drop next : Z) (fill : Z) (tbl : arr) : arr :=
  snd (loopZ fill
         (fun ft : Z * arr => let '(fill, tbl) := ft in
            let fill := wrap32 (fill - incr) in
            let tbl := arr_set tbl (next + (Z.shiftr huff drop + fill)) here in
            if negb (fill =? 0) then (true, (fill, tbl)) else (false, (fill, tbl)))
         (fill, tbl)).

Definition it_incr_back (huff len : Z) : Z :=
  loopZ 32 (fun incr => if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr))
        (shl32 1 (len - 1)).

Definition it_subtable_curr (count : arr) (len drop max : Z) : Z :=
  let curr := wrap32 (len - drop) in
  let lft := swrap32 (Z.shiftl 1 curr) in
  fst (loopZ 16
         (fun cl : Z * Z => let '(curr, lft) := cl in
            if wrap32 (curr + drop) <? max then
              let lft := lft - arr_get count (wrap32 (curr + drop)) in
              if lft <=? 0 then (false, (curr, lft))
              else (true, (wrap32 (curr + 1), Z.shiftl lft 1))
            else (false, (curr, lft)))
         (curr, lft)).

Definition it_step (x : ItCtx) (st : ItSt) : ItStep :=
  let ty := x_ty x in
  let here_bits := wrap8 (t_len st - t_drop st) in
  let w := arr_get (t_work st) (t_sym st) in
  let '(here_op, here_val) :=
    if w + 1 <? it_match ty then (0, w)
    else if it_match ty <=? w then
      (wrap8 (it_extra ty (t_work st) (w - it_match ty)), it_base ty (t_work st) (w - it_match ty))
    else (96, 0) in
  let here := code_pack here_op here_bits here_val in
  let incr := shl32 1 (t_len st - t_drop st) in
  let fill := shl32 1 (t_curr st) in
  let min := fill in
  let tbl := it_fill here incr (t_huff st) (t_drop st) (t_next st) fill (t_tbl st) in
  let incr := it_incr_back (t_huff st) (t_len st) in
  let huff := if negb (incr =? 0) then Z.land (t_huff st) (incr - 1) + incr else 0 in
  let sym := wrap32 (t_sym st + 1) in
  let c := wrap16 (arr_get (t_count st) (t_len st) - 1) in
  let count := arr_set (t_count st) (t_len st) c in
  let brk := (c =? 0) && (t_len st =? x_max x) in
  let len := if (c =? 0) && negb (t_len st =? x_max x)
             then arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) sym)
             else t_len st in
  let st := mkItSt huff sym len (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st)
                   min count tbl (t_work st) in
  if brk then ItBreak st
  else
  if (x_root x <? len) && negb (Z.land huff (x_mask x) =? t_low st) then
    let drop := if t_drop st =? 0 then x_root x else t_drop st in
    let next := t_next st + t_min st in
    let curr := it_subtable_curr count len drop (x_max x) in
    let used := wrap32 (t_used st + Z.shiftl 1 curr) in
    let st := mkItSt huff sym len next curr drop (t_low st) used (t_min st) count tbl (t_work st) in
    if it_not_enough ty used then ItFail st
    else
      let low := Z.land huff (x_mask x) in
      let tbl := arr_set tbl (x_table x + low) (code_pack curr (x_root x) (next - x_table x)) in
      ItCont (mkItSt huff sym len next curr drop low used (t_min st) count tbl (t_work st))
  else ItCont st.

Definition it_loop (x : ItCtx) (codes : Z) (st : ItSt) : ItSt + ItSt :=
  iterZ (codes + 1)
    (fun st => match it_step x st with
               | ItCont st' => inl st'
               | ItBreak st' => inr (inl st')
               | ItFail st' => inr (inr st')
               end)
    (fun st => inl st) st.


Definition inflate_table (ty : codetype) (lens : arr) (lens_ofs codes : Z)
           (tbl : arr) (table bits : Z) (work : arr)
  : Z * arr * Z * Z * arr :=
  let count := it_count lens lens_ofs codes (it_zero_count (arr_make 16 0)) in
  let root := bits in
  let max := it_find_max count in
  let root := if max <? root then max else root in
  if max =? 0 then
    let here := code_pack 64 1 0 in
    let tbl := arr_set tbl table here in
    let tbl := arr_set tbl (table + 1) here in
    (0, tbl, table + 2, 1, work)
  else
  let min := it_find_min count max in
  let root := if root <? min then min else root in
  match it_left_check count with
  | None => (-1, tbl, table, bits, work)
  | Some lft =>
  if (0 <? lft) && (codetype_eqb ty CODES || negb (max =? 1)) then (-1, tbl, table, bits, work)
  else
  let offs := it_offs count (arr_make 16 0) in
  let '(_, work) := it_sort lens lens_ofs codes (offs, work) in
  let used := shl32 1 root in
  let mask := used - 1 in
  if it_not_enough ty used then (1, tbl, table, bits, work)
  else
  let x := mkItCtx ty lens lens_ofs table root max mask in
  let st0 := mkItSt 0 0 min table root 0 4294967295 used 0 count tbl work in
  match it_loop x codes st0 with
  | inr st => (1, t_tbl st, table, bits, t_work st)
  | inl st =>
    let tbl := if negb (t_huff st =? 0)
               then arr_set (t_tbl st) (t_next st + t_huff st)
                            (code_pack 64 (t_len st - t_drop st) 0)
               else t_tbl st in
    (0, tbl, table + t_used st, root, t_work st)
  end end.
