(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import Uint63 PrimString.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LZ.

Definition B : int := 16384%uint63.      (* [comment removed for export] *)
Definition C : int := 512%uint63.

Inductive st : Type := ST (i : int) (cur mid : string) (blocks : list string).

Definition dg (s : string) (i : int) : int := PrimInt63.sub (PrimString.get s i) 35%uint63.

Definition flush (i : int) (cur mid : string) (blocks : list string) : st :=
  if PrimInt63.ltb (PrimString.length cur) C then ST i cur mid blocks
  else
    let m := PrimString.cat mid cur in
    let n := PrimString.length m in
    if PrimInt63.ltb n B then ST i ""%pstring m blocks
    else ST i ""%pstring (PrimString.sub m B (PrimInt63.sub n B)) (cons (PrimString.sub m 0%uint63 B) blocks).

Fixpoint nthb (l : list string) (k : int) : string :=
  match l with
  | nil => ""%pstring
  | cons x r => if PrimInt63.eqb k 0%uint63 then x else nthb r (PrimInt63.sub k 1%uint63)
  end.

(* [comment removed for export] *)
Fixpoint fromb (f : nat) (blocks : list string) (b n : int) : string :=
  let k := PrimInt63.lsr (PrimInt63.sub b 1%uint63) 14%uint63 in
  let o := PrimInt63.sub b (PrimInt63.lsl k 14%uint63) in
  let blk := nthb blocks k in
  if PrimInt63.leb n o then PrimString.sub blk (PrimInt63.sub B o) n
  else match f with
       | O => PrimString.sub blk (PrimInt63.sub B o) o
       | S f' => PrimString.cat (PrimString.sub blk (PrimInt63.sub B o) o) (fromb f' blocks (PrimInt63.sub b o) (PrimInt63.sub n o))
       end.

(* [comment removed for export] *)
Definition copy (cur mid : string) (blocks : list string) (dist len : int) : string :=
  let lc := PrimString.length cur in
  if PrimInt63.leb dist lc then PrimString.sub cur (PrimInt63.sub lc dist) len
  else
    let a := PrimInt63.sub dist lc in
    let lm := PrimString.length mid in
    if PrimInt63.leb a lm then
      if PrimInt63.leb len a then PrimString.sub mid (PrimInt63.sub lm a) len
      else PrimString.cat (PrimString.sub mid (PrimInt63.sub lm a) a) (PrimString.sub cur 0%uint63 (PrimInt63.sub len a))
    else
      let b := PrimInt63.sub a lm in
      if PrimInt63.leb len b then fromb 64 blocks b len
      else
        let hd := fromb 64 blocks b b in
        let r := PrimInt63.sub len b in
        if PrimInt63.leb r lm then PrimString.cat hd (PrimString.sub mid 0%uint63 r)
        else PrimString.cat (PrimString.cat hd mid) (PrimString.sub cur 0%uint63 (PrimInt63.sub r lm)).

Definition dq : string := PrimString.make 1%uint63 34%uint63.

(* [comment removed for export] *)
Definition mtch (s : string) (j : int) (len : int) (cur mid : string) (blocks : list string) : st :=
  let e := dg s j in
  let f := dg s (PrimInt63.add j 1%uint63) in
  if PrimInt63.ltb e 14%uint63 then
    let d := PrimInt63.add 1%uint63 (PrimInt63.add (PrimInt63.mul e 30%uint63) f) in
    flush (PrimInt63.add j 2%uint63) (PrimString.cat cur (copy cur mid blocks d len)) mid blocks
  else
    let g := dg s (PrimInt63.add j 2%uint63) in
    if PrimInt63.ltb e 26%uint63 then
      let d := PrimInt63.add (PrimInt63.add 421%uint63 (PrimInt63.mul (PrimInt63.sub e 14%uint63) 900%uint63))
                             (PrimInt63.add (PrimInt63.mul f 30%uint63) g) in
      flush (PrimInt63.add j 3%uint63) (PrimString.cat cur (copy cur mid blocks d len)) mid blocks
    else
      let h := dg s (PrimInt63.add j 3%uint63) in
      if PrimInt63.ltb e 29%uint63 then
        let d := PrimInt63.add (PrimInt63.add 11221%uint63 (PrimInt63.mul (PrimInt63.sub e 26%uint63) 27000%uint63))
                               (PrimInt63.add (PrimInt63.mul f 900%uint63) (PrimInt63.add (PrimInt63.mul g 30%uint63) h)) in
        flush (PrimInt63.add j 4%uint63) (PrimString.cat cur (copy cur mid blocks d len)) mid blocks
      else
        let k := dg s (PrimInt63.add j 4%uint63) in
        let d := PrimInt63.add (PrimInt63.add 92221%uint63 (PrimInt63.mul f 27000%uint63))
                               (PrimInt63.add (PrimInt63.mul g 900%uint63) (PrimInt63.add (PrimInt63.mul h 30%uint63) k)) in
        flush (PrimInt63.add j 5%uint63) (PrimString.cat cur (copy cur mid blocks d len)) mid blocks.

Definition step (s : string) (n : int) (x : st) : st :=
  match x with
  | ST i cur mid blocks =>
      if PrimInt63.leb n i then x else
      let t := dg s i in
      let i1 := PrimInt63.add i 1%uint63 in
      if PrimInt63.ltb t 10%uint63 then
        let k := PrimInt63.add t 1%uint63 in
        flush (PrimInt63.add i1 k) (PrimString.cat cur (PrimString.sub s i1 k)) mid blocks
      else if PrimInt63.ltb t 29%uint63 then
        if PrimInt63.eqb t 10%uint63 then
          let k := PrimInt63.add 11%uint63 (PrimInt63.add (PrimInt63.mul (dg s i1) 30%uint63) (dg s (PrimInt63.add i 2%uint63))) in
          let i3 := PrimInt63.add i 3%uint63 in
          flush (PrimInt63.add i3 k) (PrimString.cat cur (PrimString.sub s i3 k)) mid blocks
        else mtch s i1 (PrimInt63.sub t 7%uint63) cur mid blocks
      else if PrimInt63.eqb t 29%uint63 then
        mtch s (PrimInt63.add i 3%uint63)
             (PrimInt63.add 22%uint63 (PrimInt63.add (PrimInt63.mul (dg s i1) 30%uint63) (dg s (PrimInt63.add i 2%uint63)))) cur mid blocks
      else flush i1 (PrimString.cat cur dq) mid blocks
  end.

(* [comment removed for export] *)
Fixpoint iter (f : nat) (s : string) (n : int) (x : st) : st :=
  match f with
  | O => step s n x
  | S f' =>
      let y := iter f' s n x in
      match y with ST i _ _ _ => if PrimInt63.leb n i then y else iter f' s n y end
  end.

(* [comment removed for export] *)
Fixpoint pairs (l : list string) : list string :=
  match l with
  | cons a (cons b r) => cons (PrimString.cat b a) (pairs r)
  | _ => l
  end.
Fixpoint cat_all (l : list string) : string :=
  match l with
  | nil => ""%pstring
  | cons a r => PrimString.cat (cat_all r) a
  end.
Fixpoint glue (f : nat) (l : list string) : string :=
  match f with
  | O => cat_all l
  | S f' => match l with
            | nil => ""%pstring
            | cons a nil => a
            | _ => glue f' (pairs l)
            end
  end.

(* [comment removed for export] *)
Fixpoint chunk (f : nat) (d : string) (n : int) (p : int) (blocks : list string) : int * list string :=
  match f with
  | O => if PrimInt63.leb (PrimInt63.add p B) n then (PrimInt63.add p B, cons (PrimString.sub d p B) blocks) else (p, blocks)
  | S f' =>
      match chunk f' d n p blocks with
      | (q, bl) => if PrimInt63.leb (PrimInt63.add q B) n then chunk f' d n q bl else (q, bl)
      end
  end.

Definition run (dict s : string) : string :=
  let nd := PrimString.length dict in
  match chunk 40 dict nd 0%uint63 nil with
  | (p, bl) =>
      match iter 48 s (PrimString.length s) (ST 0%uint63 ""%pstring (PrimString.sub dict p (PrimInt63.sub nd p)) bl) with
      | ST _ cur mid blocks => glue 64 (cons (PrimString.cat mid cur) blocks)
      end
  end.

End LZ.

Definition lz_dec (s : string) : string := LZ.run ""%pstring s.

(* [comment removed for export] *)
Definition lz_decd (dict s : string) : string :=
  let full := LZ.run dict s in
  let k := PrimString.length dict in
  PrimString.sub full k (PrimInt63.sub (PrimString.length full) k).
