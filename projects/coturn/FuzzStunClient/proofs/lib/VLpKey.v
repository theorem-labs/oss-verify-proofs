(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition hM : int := 1099511628211%uint63.
Definition hstep (h x : int) : int := PrimInt63.mul (PrimInt63.lxor h x) hM.

(* [comment removed for export] *)
Fixpoint hpos (p : positive) (acc : int) : int :=
  match p with
  | xH => acc
  | xO q => hpos q (PrimInt63.add acc acc)
  | xI q => hpos q (PrimInt63.add (PrimInt63.add acc acc) 1%uint63)
  end.

Definition hz (z : Z) : int :=
  match z with Z0 => 0%uint63 | Zpos p => hpos p 2%uint63 | Zneg p => hpos p 3%uint63 end.

Definition hn (n : N) : int := match n with N0 => 0%uint63 | Npos p => hpos p 1%uint63 end.

Definition ho (o : option Z) : int := match o with None => 1%uint63 | Some z => hz z end.

Fixpoint hterms (l : list term) (h : int) : int :=
  match l with
  | [] => hstep h 7%uint63
  | (s, k) :: t => hterms t (hstep (hstep h (hpos s 1%uint63)) (hz k))
  end.

Definition hlin (e : lin) (h : int) : int := hterms (lt e) (hstep h (hz (lc e))).

Fixpoint hgs (gs : list (N * lin)) (h : int) : int :=
  match gs with
  | [] => hstep h 5%uint63
  | (i, g) :: t => hgs t (hlin g (hstep h (hn i)))
  end.

(* [comment removed for export] *)
Fixpoint hbox (ss : pmap unit) (bx : pmap itv) (h : int) : int :=
  match ss with
  | PLeaf => h
  | PNode l o r =>
      match bx with
      | PLeaf =>
          let h1 := match o with None => h | Some _ => hstep (hstep h 1%uint63) 1%uint63 end in
          hbox r PLeaf (hbox l PLeaf h1)
      | PNode bl bo br =>
          let h1 := match o with
                    | None => h
                    | Some _ => match bo with
                                | Some i => hstep (hstep h (ho (fst i))) (ho (snd i))
                                | None => hstep (hstep h 1%uint63) 1%uint63
                                end
                    end in
          hbox r br (hbox l bl h1)
      end
  end.

Definition lp_key (St : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) : int :=
  hbox symset (sbox St) (hgs gs (hlin a 3%uint63)).
