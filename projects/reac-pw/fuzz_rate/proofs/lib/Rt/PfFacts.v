(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_vsnprintf.v, with its module paths and module names changed; 710 of its 816 lines of code are new or changed and 1295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GX/Printf_text.v; 3 of its 76 lines of code are new or changed and 743 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/Rt/PfFacts.v at 2d2ff01bb6f2; module paths changed. *)
(* Copied from lib/Prog/printf_facts_c.v, with the address-dependent parts left out. *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.

Inductive pf_piece : Type := PLit (b : Z) | Pd | Pc | Px04 | Px02 | Pllu | Ps | Pps.
Inductive pf_arg : Type := AInt (v : Z) | AU64 (u : Z) | APtr (s : list Z).

Fixpoint pf_parse (f : list Z) : option (list pf_piece) :=
  match f with
  | [] => Some []
  | b :: r =>
    if b =? 37 then
      match r with
      | c :: r1 =>
        if c =? 100 then option_map (cons Pd) (pf_parse r1)
        else if c =? 99 then option_map (cons Pc) (pf_parse r1)
        else if c =? 115 then option_map (cons Ps) (pf_parse r1)
        else if c =? 48 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 52) && (c3 =? 120) then option_map (cons Px04) (pf_parse r3)
              else if (c2 =? 50) && (c3 =? 120) then option_map (cons Px02) (pf_parse r3)
              else None
          | _ => None
          end
        else if c =? 108 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 108) && (c3 =? 117) then option_map (cons Pllu) (pf_parse r3) else None
          | _ => None
          end
        else if c =? 46 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 42) && (c3 =? 115) then option_map (cons Pps) (pf_parse r3) else None
          | _ => None
          end
        else None
      | [] => None
      end
    else if (0 <? b) && (b <? 256) then option_map (cons (PLit b)) (pf_parse r)
    else None
  end.

Fixpoint pf_digits (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 10 then (48 + x) :: acc else pf_digits f (x / 10) ((48 + x mod 10) :: acc)
  end.

Definition pf_dec (v : Z) : list Z := if v <? 0 then 45 :: pf_digits 11 (- v) [] else pf_digits 11 v [].

Definition pf_hexd (d : Z) : Z := if d <? 10 then 48 + d else 87 + d.

Fixpoint pf_hexs (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 16 then pf_hexd x :: acc else pf_hexs f (x / 16) (pf_hexd (x mod 16) :: acc)
  end.

Definition pf_hex4 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (4 - length h) ++ h.

Definition pf_hex2 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (2 - length h) ++ h.

Definition pf_udec (u : Z) : list Z := pf_digits 20 u [].

Fixpoint pf_text (ps : list pf_piece) (args : list pf_arg) : option (list Z) :=
  match ps with
  | [] => match args with [] => Some [] | _ :: _ => None end
  | PLit b :: ps' => option_map (cons b) (pf_text ps' args)
  | Pd :: ps' => match args with AInt v :: a' => option_map (app (pf_dec v)) (pf_text ps' a') | _ => None end
  | Pc :: ps' => match args with AInt v :: a' => option_map (cons (v mod 256)) (pf_text ps' a') | _ => None end
  | Px04 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex4 v)) (pf_text ps' a') | _ => None end
  | Px02 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex2 v)) (pf_text ps' a') | _ => None end
  | Pllu :: ps' => match args with AU64 u :: a' => option_map (app (pf_udec u)) (pf_text ps' a') | _ => None end
  | Ps :: ps' => match args with APtr s :: a' => option_map (app s) (pf_text ps' a') | _ => None end
  | Pps :: ps' =>
      match args with
      | AInt k :: APtr s :: a' =>
          if (0 <=? k) && (k <=? Z.of_nat (length s)) then option_map (app (firstn (Z.to_nat k) s)) (pf_text ps' a')
          else None
      | _ => None
      end
  end.

Definition pf_disco_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pd | Px02 | Pllu | Ps => True | _ => False end.
