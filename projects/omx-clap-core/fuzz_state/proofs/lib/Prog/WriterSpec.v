From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Definition special (c : Z) : bool := (c =? 34) || (c =? 92) || (c <? 32).

Definition hexd (x : Z) : Z := if x <? 10 then 48 + x else 87 + x.

Definition esc (c : Z) : list Z :=
  if c =? 34 then [92; 34]
  else if c =? 92 then [92; 92]
  else if c =? 10 then [92; 110]
  else if c =? 9 then [92; 116]
  else if c =? 13 then [92; 114]
  else [92; 117; 48; 48; hexd (c / 16); hexd (c mod 16)].

Fixpoint spieces_run (run : list Z) (bs : list Z) : list (list Z) :=
  match bs with
  | [] => [run]
  | c :: rest =>
      if special c then run :: esc c :: spieces_run [] rest
      else spieces_run (run ++ [c]) rest
  end.

Definition spieces (bs : list Z) : list (list Z) := [34] :: spieces_run [] bs ++ [[34]].

Definition wstr (bs : list Z) : list Z := concat (spieces bs).

Fixpoint dbl (fuel : nat) (c need : Z) : Z :=
  match fuel with
  | O => c
  | S f => if need <=? c then c else dbl f (2 * c) need
  end.

Definition newcap (c need : Z) : Z := dbl 64 (if c =? 0 then 4096 else c) need.

Fixpoint grow_calls (x c : Z) (ls : list Z) : list Z :=
  match ls with
  | [] => []
  | l :: rest =>
      if c <? x + l + 1 then newcap c (x + l + 1) :: grow_calls (x + l) (newcap c (x + l + 1)) rest
      else grow_calls (x + l) c rest
  end.

Fixpoint grow_cap (x c : Z) (ls : list Z) : Z :=
  match ls with
  | [] => c
  | l :: rest =>
      if c <? x + l + 1 then grow_cap (x + l) (newcap c (x + l + 1)) rest
      else grow_cap (x + l) c rest
  end.

Definition piece_lens (P : list (list Z)) : list Z := map (fun b => Z.of_nat (length b)) P.

Definition b64c (v : Z) : Z :=
  if v <? 26 then 65 + v
  else if v <? 52 then 71 + v
  else if v <? 62 then v - 4
  else if v =? 62 then 43
  else 47.

Definition b64_table : list Z := map b64c (map Z.of_nat (seq 0 64)) ++ [0].

Fixpoint b64_enc (bs : list Z) : list Z :=
  match bs with
  | b0 :: b1 :: b2 :: rest =>
      b64c (b0 / 4) :: b64c ((b0 mod 4) * 16 + b1 / 16) :: b64c ((b1 mod 16) * 4 + b2 / 64)
        :: b64c (b2 mod 64) :: b64_enc rest
  | [b0; b1] => [b64c (b0 / 4); b64c ((b0 mod 4) * 16 + b1 / 16); b64c ((b1 mod 16) * 4); 61]
  | [b0] => [b64c (b0 / 4); b64c ((b0 mod 4) * 16); 61; 61]
  | [] => []
  end.

Definition b64_ws (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 10) || (c =? 13).

Definition b64v (c : Z) : option Z :=
  if (65 <=? c) && (c <=? 90) then Some (c - 65)
  else if (97 <=? c) && (c <=? 122) then Some (c - 71)
  else if (48 <=? c) && (c <=? 57) then Some (c + 4)
  else if c =? 43 then Some 62
  else if c =? 47 then Some 63
  else None.

Fixpoint b64_scan (pad : Z) (six : list Z) (tb : list Z) : option (list Z * Z) :=
  match tb with
  | [] => Some (six, pad)
  | c :: rest =>
      if b64_ws c then b64_scan pad six rest
      else if c =? 61 then b64_scan (pad + 1) six rest
      else match b64v c with
           | Some v => if pad =? 0 then b64_scan pad (six ++ [v]) rest else None
           | None => None
           end
  end.

Fixpoint six_bytes (six : list Z) : list Z :=
  match six with
  | s0 :: s1 :: s2 :: s3 :: rest =>
      (s0 * 4 + s1 / 16) :: ((s1 mod 16) * 16 + s2 / 4) :: ((s2 mod 4) * 64 + s3) :: six_bytes rest
  | [s0; s1; s2] => [s0 * 4 + s1 / 16; (s1 mod 16) * 16 + s2 / 4]
  | [s0; s1] => [s0 * 4 + s1 / 16]
  | _ => []
  end.

Definition six_tail_ok (six : list Z) : bool :=
  let r := Z.of_nat (length six) mod 4 in
  let l := last six 0 in
  negb (r =? 1) && (negb (r =? 2) || (l mod 16 =? 0)) && (negb (r =? 3) || (l mod 4 =? 0)).

Definition b64_dec (tb : list Z) : option (list Z) :=
  match b64_scan 0 [] tb with
  | Some (six, pad) => if (pad <=? 2) && six_tail_ok six then Some (six_bytes six) else None
  | None => None
  end.

Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Definition no_zero (bs : list Z) : Prop := Forall (fun b => b <> 0) bs.
