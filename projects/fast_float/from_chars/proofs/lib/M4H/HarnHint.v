(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HarnHintTbl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive hmode : Type := HReal | HRec | HReplay.
(* [comment removed for export] *)
Record hst : Type := HST { h_bits : positive; h_hull : list Z; h_ok : bool; h_rbits : list bool; h_rhull : list Z }.
Definition hst0 : hst := HST xH [] true [] [].
Definition hst_replay (bits : positive) (hull : list Z) : hst := HST bits hull true [] [].
(* [comment removed for export] *)
Definition ask_b (m : hmode) (st : hst) (real : unit -> bool) : bool * hst :=
  match m with
  | HReal => (real tt, st)
  | HRec => let b := real tt in (b, HST (h_bits st) (h_hull st) (h_ok st) (b :: h_rbits st) (h_rhull st))
  | HReplay => match h_bits st with
               | xI p => (true, HST p (h_hull st) (h_ok st) [] [])
               | xO p => (false, HST p (h_hull st) (h_ok st) [] [])
               | xH => (false, HST xH (h_hull st) false [] [])
               end
  end.
(* [comment removed for export] *)
Definition ask_h (m : hmode) (st : hst) (l : lin) (real : unit -> list fact) : list fact * hst :=
  match m with
  | HReal => (real tt, st)
  | HRec => match real tt with
            | [FRange g lo hi] => ([FRange g lo hi], HST (h_bits st) (h_hull st) (h_ok st) (true :: h_rbits st) (hi :: lo :: h_rhull st))
            | r => (r, HST (h_bits st) (h_hull st) (h_ok st) (false :: h_rbits st) (h_rhull st))
            end
  | HReplay => match h_bits st with
               | xI p => match h_hull st with
                         | lo :: hi :: r => ([FRange l lo hi], HST p r (h_ok st) [] [])
                         | _ => ([], HST p [] false [] [])
                         end
               | xO p => ([], HST p (h_hull st) (h_ok st) [] [])
               | xH => ([], HST xH (h_hull st) false [] [])
               end
  end.
(* [comment removed for export] *)
Definition hst_done (st : hst) : bool := (h_ok st && match h_bits st with xH => true | _ => false end && match h_hull st with [] => true | _ => false end)%bool.
(* [comment removed for export] *)
Fixpoint filter_h {A} (f : hst -> A -> bool * hst) (l : list A) (st : hst) : list A * hst :=
  match l with
  | [] => ([], st)
  | x :: r => let '(b, st1) := f st x in let '(r', st2) := filter_h f r st1 in (if b then x :: r' else r', st2)
  end.
Fixpoint flat_map_h {A B} (f : hst -> A -> list B * hst) (l : list A) (st : hst) : list B * hst :=
  match l with
  | [] => ([], st)
  | x :: r => let '(y, st1) := f st x in let '(r', st2) := flat_map_h f r st1 in (y ++ r', st2)
  end.
(* [comment removed for export] *)
Fixpoint key_eqb (a b : list Z) : bool := match a, b with [], [] => true | x :: a', y :: b' => if Z.eqb x y then key_eqb a' b' else false | _, _ => false end.
Fixpoint hint_find (T : list (list Z * positive * list Z)) (k : list Z) : option (positive * list Z) :=
  match T with [] => None | (k', bits, hull) :: r => if key_eqb k k' then Some (bits, hull) else hint_find r k end.
Definition hint_lookup (k : list Z) : option (positive * list Z) := hint_find HINTS k.
Definition HINT_REC : bool := Z.eqb HINT_MODE 1.
Definition HINT_STRICT : bool := Z.eqb HINT_MODE 2.
(* [comment removed for export] *)
Definition HMAGIC : Z := 7777777777.
Definition hmarker (k : list Z) (st : hst) : fact :=
  FBytes (lconst HMAGIC) (List.map (fun z => (lconst 0, z)) (k ++ [-1] ++ List.map (fun b : bool => if b then 1 else 0) (List.rev (h_rbits st)) ++ [-1] ++ List.rev (h_rhull st))).
Definition is_hmarker (f : fact) : bool := match f with FBytes (LIN c []) _ => Z.eqb c HMAGIC | _ => false end.
Definition hmarker_codes (f : fact) : list Z := match f with FBytes _ bs => List.map snd bs | _ => [] end.
