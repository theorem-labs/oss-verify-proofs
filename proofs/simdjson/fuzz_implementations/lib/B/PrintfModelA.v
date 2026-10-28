(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

Definition ALT_FORM : Z := 8.
Definition ZERO_PAD : Z := 65536.
Definition LEFT_ADJ : Z := 8192.
Definition PAD_POS  : Z := 1.
Definition MARK_POS : Z := 2048.
Definition INT_MAX  : Z := 2147483647.
Definition INTMAX_MAX : Z := 9223372036854775807.

Inductive parg : Type := PA_s (s : list Z) | PA_sn | PA_i (i : Z) | PA_u (u : Z) | PA_z (u : Z) | PA_g (d : Z).

Definition NULLSTR : list Z := str "(null)".

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

Definition T_PTR : Z := 9.  Definition T_INT : Z := 10.  Definition T_UINT : Z := 11.  Definition T_SIZET : Z := 20.  Definition T_DBL : Z := 25.
Definition ZTPRE : Z := 6.

Definition FLAGMASK : Z := 75913.

Fixpoint digits_aux (fuel : nat) (base : Z) (dig : Z -> Z) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' => if x =? 0 then acc else digits_aux fuel' base dig (x / base) (dig (x mod base) :: acc)
  end.

Definition dec_digits (x : Z) : list Z := digits_aux 20 10 (fun v => 48 + v) x [].

Definition XDIGITS : list Z := [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70].
Definition hex_digits (lower : Z) (x : Z) : list Z := digits_aux 16 16 (fun v => Z.lor (znth XDIGITS v) lower) x [].

Fixpoint lit_run (s : list Z) : list Z :=
  match s with
  | [] => []
  | c :: s' => if (c =? 0) || (c =? 37) then [] else c :: lit_run s'
  end.

Definition flag_bit (c : Z) : option Z :=
  if (32 <=? c) && (c <? 64) && negb (Z.land FLAGMASK (Z.shiftl 1 (c - 32)) =? 0)
  then Some (Z.shiftl 1 (c - 32)) else None.
Fixpoint parse_flags (s : list Z) (fl : Z) {struct s} : Z * list Z :=
  match s with
  | [] => (fl, s)
  | c :: s' => match flag_bit c with
               | Some b => parse_flags s' (Z.lor fl b)
               | None => (fl, s)
               end
  end.

Fixpoint getint (s : list Z) (i : Z) {struct s} : option (Z * list Z) :=
  match s with
  | [] => Some (i, s)
  | c :: s' => if is_digit c then
                 if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None
                 else getint s' (10 * i + (c - 48))
               else Some (i, s)
  end.

Definition conv_type (t : Z) : option Z :=
  if t =? 115 then Some T_PTR
  else if (t =? 100) || (t =? 105) then Some T_INT
  else if (t =? 117) || (t =? 120) || (t =? 88) then Some T_UINT
  else None.

Definition conv_type_z (t : Z) : option Z :=
  if t =? 117 then Some T_SIZET else None.

Definition conv_state (s : list Z) : option (Z * Z * nat) :=
  match s with
  | [] => None
  | t :: s' =>
      if t =? 122 then
        match s' with
        | [] => None
        | t2 :: _ => let? ty := conv_type_z t2 in Some (ty, ZTPRE, 2%nat)
        end
      else let? ty := conv_type t in Some (ty, 0, 1%nat)
  end.

Record dir : Type := mkDir { d_fl : Z; d_w : Z; d_p : Z; d_xp : bool; d_t : Z; d_ty : Z }.

Definition dir_ps (d : dir) : Z := if d_ty d =? T_SIZET then ZTPRE else 0.

Definition parse_dir (s : list Z) : option (dir * list Z) :=
  let positional := match s with
                    | c1 :: c2 :: _ => is_digit c1 && (c2 =? 36)
                    | [c1] => is_digit c1
                    | [] => false
                    end in
  if positional then None else
  let '(fl, s1) := parse_flags s 0 in
  match s1 with
  | [] => None
  | c1 :: _ =>
    if c1 =? 42 then None else
    let? (w, s2) := getint s1 0 in
    match s2 with
    | [] => None
    | c2 :: s2' =>
      let pxs : option (Z * bool * list Z) :=
        if c2 =? 46 then
          match s2' with
          | [] => None
          | c3 :: _ => if c3 =? 42 then None
                       else let? (p, s3) := getint s2' 0 in Some (p, true, s3)
          end
        else Some (-1, false, s2) in
      match pxs with
      | None => None
      | Some (p, xp, s3) =>
        let? (ty, ps, n) := conv_state s3 in
        Some (mkDir fl w p xp (nth (n - 1)%nat s3 0) ty, skipn n s3)
      end
    end
  end.

Section PrintfModel.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  Definition mpad (c w l fl : Z) : M St unit :=
    if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then mret tt
    else if 256 <=? w - l then munr
    else OUT (zrepeat c (w - l)).

  Definition conv_tail (cnt fl w p : Z) (prefix body : list Z) : M St Z :=
    let pl := zlength prefix in
    let n := zlength body in
    let p := Z.max p n in
    if INT_MAX - pl <? p then munr else
    let w := Z.max w (pl + p) in
    if INT_MAX - cnt <? w then munr else
    mpad 32 w (pl + p) fl ;;;
    OUT prefix ;;;
    mpad 48 w (pl + p) (Z.lxor fl ZERO_PAD) ;;;
    mpad 48 p n 0 ;;;
    OUT body ;;;
    mpad 32 w (pl + p) (Z.lxor fl LEFT_ADJ) ;;;
    mret (cnt + w).

  Definition conv_int (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : M St Z :=
    if xp && (p <? 0) then munr else
    let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
    if (argi =? 0) && (p =? 0) then conv_tail cnt fl w p prefix []
    else conv_tail cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

  Definition conv (cnt : Z) (d : dir) (a : parg) : M St Z :=
    let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
    let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
    match a with
    | PA_s s =>
        if negb (d_ty d =? T_PTR) then munr else

        if (p <? 0) && (INT_MAX <=? zlength s) then munr else
        let n := if p <? 0 then zlength s else Z.min (zlength s) p in
        conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
    | PA_sn =>
        if negb (d_ty d =? T_PTR) then munr else
        let s := NULLSTR in
        if (p <? 0) && (INT_MAX <=? zlength s) then munr else
        let n := if p <? 0 then zlength s else Z.min (zlength s) p in
        conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
    | PA_i i =>
        if negb (d_ty d =? T_INT) then munr else
        let argi := i mod 2^64 in

        let '(argi, prefix) :=
          if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
          else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
          else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
          else (argi, []) in
        conv_int cnt fl w p xp argi prefix (dec_digits argi)
    | PA_u u =>
        if negb (d_ty d =? T_UINT) then munr else
        if t =? 117 then conv_int cnt fl w p xp u [] (dec_digits u)
        else

          let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                        then (if t =? 120 then [48; 120] else [48; 88]) else [] in
          conv_int cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
    | PA_z u =>
        if negb (d_ty d =? T_SIZET) then munr else
        if t =? 117 then conv_int cnt fl w p xp u [] (dec_digits u) else munr
    | PA_g dd =>
        if negb (d_ty d =? T_DBL) then munr else
        if xp && (p <? 0) then munr else
        if (1 <? w) || (2^20 <=? p) then munr else
        r <- OUTFP dd w p fl t ;;
        if (r <? 0) || (INT_MAX - cnt <? r) then munr else mret (cnt + r)
    end.

  Fixpoint printf_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel} : M St Z :=
    match fuel with
    | O => munr
    | S fuel' =>
      match s with
      | [] => munr
      | c :: _ =>
        if c =? 0 then mret cnt else
        let lit := lit_run s in
        let l := zlength lit in
        let s1 := skipn (Datatypes.length lit) s in
        match s1 with
        | [] => munr
        | c1 :: s2 =>
          if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end
          then munr
          else if 0 <? l then
            (if INT_MAX - cnt <? l then munr
             else OUT lit ;;; printf_loop fuel' s1 args (cnt + l))
          else
            match parse_dir s2, args with
            | Some (d, s3), a :: args' =>
                OUT [] ;;;
                cnt' <- conv cnt d a ;;
                printf_loop fuel' s3 args' cnt'
            | _, _ => munr
            end
        end
      end
    end.

  Definition printf_model (fmt : list Z) (args : list parg) : M St Z :=
    printf_loop (Datatypes.length fmt) fmt args 0.
End PrintfModel.

Arguments mpad {St} OUT _ _ _ _.
Arguments conv_tail {St} OUT _ _ _ _ _ _.
Arguments conv_int {St} OUT _ _ _ _ _ _ _ _.
Arguments conv {St} OUT OUTFP _ _ _.
Arguments printf_loop {St} OUT OUTFP _ _ _ _.
Arguments printf_model {St} OUT OUTFP _ _.

Fixpoint fp_calls (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (Z * Z * Z * Z * Z) :=
  match fuel with
  | O => []
  | S fuel' =>
    match s with
    | [] => []
    | c :: _ =>
      if c =? 0 then [] else
      let lit := lit_run s in
      let s1 := skipn (Datatypes.length lit) s in
      if 0 <? zlength lit then fp_calls fuel' s1 args
      else match s1 with
           | _ :: s2 =>
             match parse_dir s2, args with
             | Some (d, s3), a :: args' =>
                 match a with
                 | PA_g dd =>
                     let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
                     (dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel' s3 args'
                 | _ => fp_calls fuel' s3 args'
                 end
             | _, _ => []
             end
           | _ => []
           end
    end
  end.

Definition pass1_ok (fmt : list Z) : bool :=
  let lit := lit_run fmt in
  (zlength lit <=? INT_MAX) &&
  match skipn (Datatypes.length lit) fmt with
  | [] => false
  | c1 :: s2 =>
      if c1 =? 0 then true
      else match s2 with
           | [] => false
           | c2 :: _ => negb (c2 =? 37) && match parse_dir s2 with Some _ => true | None => false end
           end
  end.

Definition pad_pieces (c w l fl : Z) : option (list (list Z)) :=
  if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some []
  else if 256 <=? w - l then None
  else Some [zrepeat c (w - l)].

Definition tail_pieces (cnt fl w p : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
  let pl := zlength prefix in
  let n := zlength body in
  let p := Z.max p n in
  if INT_MAX - pl <? p then None else
  let w := Z.max w (pl + p) in
  if INT_MAX - cnt <? w then None else
  let? p1 := pad_pieces 32 w (pl + p) fl in
  let? p2 := pad_pieces 48 w (pl + p) (Z.lxor fl ZERO_PAD) in
  let? p3 := pad_pieces 48 p n 0 in
  let? p4 := pad_pieces 32 w (pl + p) (Z.lxor fl LEFT_ADJ) in
  Some (p1 ++ [prefix] ++ p2 ++ p3 ++ [body] ++ p4, cnt + w).

Definition int_pieces (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
  if xp && (p <? 0) then None else
  let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
  if (argi =? 0) && (p =? 0) then tail_pieces cnt fl w p prefix []
  else tail_pieces cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

Definition conv_pieces (cnt : Z) (d : dir) (a : parg) : option (list (list Z) * Z) :=
  let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
  let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
  match a with
  | PA_s s =>
      if negb (d_ty d =? T_PTR) then None else
      if (p <? 0) && (INT_MAX <=? zlength s) then None else
      let n := if p <? 0 then zlength s else Z.min (zlength s) p in
      tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
  | PA_sn =>
      if negb (d_ty d =? T_PTR) then None else
      let s := NULLSTR in
      if (p <? 0) && (INT_MAX <=? zlength s) then None else
      let n := if p <? 0 then zlength s else Z.min (zlength s) p in
      tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
  | PA_i i =>
      if negb (d_ty d =? T_INT) then None else
      let argi := i mod 2^64 in
      let '(argi, prefix) :=
        if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
        else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
        else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
        else (argi, []) in
      int_pieces cnt fl w p xp argi prefix (dec_digits argi)
  | PA_u u =>
      if negb (d_ty d =? T_UINT) then None else
      if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
      else
        let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                      then (if t =? 120 then [48; 120] else [48; 88]) else [] in
        int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
  | PA_z u =>
      if negb (d_ty d =? T_SIZET) then None else
      if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u) else None
  | PA_g _ => None
  end.

Fixpoint printf_pieces_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel}
    : option (list (list Z) * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then Some ([], cnt) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if INT_MAX - cnt <? l then None
           else let? (ps, r) := printf_pieces_loop fuel' s1 args (cnt + l) in Some (lit :: ps, r))
        else
          match parse_dir s2, args with
          | Some (d, s3), a :: args' =>
              let? (ps1, cnt') := conv_pieces cnt d a in
              let? (ps, r) := printf_pieces_loop fuel' s3 args' cnt' in
              Some ([] :: ps1 ++ ps, r)
          | _, _ => None
          end
      end
    end
  end.

Definition printf_pieces (fmt : list Z) (args : list parg) : option (list (list Z) * Z) :=
  printf_pieces_loop (Datatypes.length fmt) fmt args 0.
