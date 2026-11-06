(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition OFF_PARENT : Z := 0.
Definition OFF_LEFT   : Z := 8.
Definition OFF_RIGHT  : Z := 16.
Definition OFF_COLOR  : Z := 24.   (* [comment removed for export] *)
Definition NODE_SIZE  : Z := 32.
Definition RED   : Z := 0.
Definition BLACK : Z := 1.
(* [comment removed for export] *)
Definition ELEM_TO_NODE : Z := 16.
Definition NODE_TO_VALUE : Z := 32.

(* [comment removed for export] *)
Definition OFF_NEXT : Z := 0.
Definition OFF_PREV : Z := 8.
Definition LNODE_SIZE : Z := 16.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record node := mkNode { n_par : Z ; n_lft : Z ; n_rgt : Z ; n_col : Z }.

Definition set_par (v : Z) (nd : node) : node := mkNode v (n_lft nd) (n_rgt nd) (n_col nd).
Definition set_lft (v : Z) (nd : node) : node := mkNode (n_par nd) v (n_rgt nd) (n_col nd).
Definition set_rgt (v : Z) (nd : node) : node := mkNode (n_par nd) (n_lft nd) v (n_col nd).
Definition set_col (v : Z) (nd : node) : node := mkNode (n_par nd) (n_lft nd) (n_rgt nd) v.

Abbreviation NS := (gmap Z node).

(* [comment removed for export] *)
Definition get_field (off : Z) (nd : node) : Z :=
  if off =? OFF_PARENT then n_par nd
  else if off =? OFF_LEFT then n_lft nd
  else if off =? OFF_RIGHT then n_rgt nd
  else n_col nd.

Definition set_field (off v : Z) (nd : node) : node :=
  if off =? OFF_PARENT then set_par v nd
  else if off =? OFF_LEFT then set_lft v nd
  else if off =? OFF_RIGHT then set_rgt v nd
  else set_col v nd.

(* [comment removed for export] *)
Definition load (ns : NS) (a off : Z) : option Z :=
  nd ← ns !! a ; Some (get_field off nd).

Definition store (ns : NS) (a off v : Z) : option NS :=
  nd ← ns !! a ; Some (<[ a := set_field off v nd ]> ns).

(* [comment removed for export] *)
Definition get_parent (ns : NS) (a : Z) : option Z := load ns a OFF_PARENT.
Definition get_left   (ns : NS) (a : Z) : option Z := load ns a OFF_LEFT.
Definition get_right  (ns : NS) (a : Z) : option Z := load ns a OFF_RIGHT.
Definition get_color  (ns : NS) (a : Z) : option Z := load ns a OFF_COLOR.
Definition set_parent (ns : NS) (a v : Z) : option NS := store ns a OFF_PARENT v.
Definition set_left   (ns : NS) (a v : Z) : option NS := store ns a OFF_LEFT v.
Definition set_right  (ns : NS) (a v : Z) : option NS := store ns a OFF_RIGHT v.
Definition set_color  (ns : NS) (a v : Z) : option NS := store ns a OFF_COLOR v.

(* [comment removed for export] *)
Fixpoint oloop {X R : Type} (fuel : nat) (body : X -> option (X + R)) (x : X) : option R :=
  match fuel with
  | O => None
  | S fuel' =>
      s ← body x ;
      match s with
      | inl x' => oloop fuel' body x'
      | inr r => Some r
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_header (ns : NS) (p : Z) : option bool :=
  ppar ← get_parent ns p ;
  if ppar =? 0 then Some true                                  (* [comment removed for export] *)
  else
    pl ← get_left ns p ;
    if pl =? 0 then Some false                                 (* [comment removed for export] *)
    else
      pr ← get_right ns p ;
      if pr =? 0 then Some false                               (* [comment removed for export] *)
      else if pl =? pr then Some true                          (* [comment removed for export] *)
      else
        lp ← get_parent ns pl ;                                (* [comment removed for export] *)
        if negb (lp =? p) then Some true                       (* [comment removed for export] *)
        else
          rp ← get_parent ns pr ;                              (* [comment removed for export] *)
          if negb (rp =? p) then Some true else Some false.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition maximum_step (ns : NS) (n : Z) : option (Z + Z) :=
  r ← get_right ns n ;
  Some (if r =? 0 then inr n else inl r).
Definition maximum (fuel : nat) (ns : NS) (n : Z) : option Z := oloop fuel (maximum_step ns) n.

Definition minimum_step (ns : NS) (n : Z) : option (Z + Z) :=
  l ← get_left ns n ;
  Some (if l =? 0 then inr n else inl l).
Definition minimum (fuel : nat) (ns : NS) (n : Z) : option Z := oloop fuel (minimum_step ns) n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prev_climb_step (ns : NS) (cur : Z) : option (Z + Z) :=
  x ← get_parent ns cur ;
  xl ← get_left ns x ;
  Some (if cur =? xl then inl x else inr x).

Definition prev_node (fuel : nat) (ns : NS) (p : Z) : option Z :=
  ih ← is_header ns p ;
  if (ih : bool) then get_right ns p                                    (* [comment removed for export] *)
  else
    pl ← get_left ns p ;                                       (* [comment removed for export] *)
    if negb (pl =? 0) then maximum fuel ns pl                  (* [comment removed for export] *)
    else oloop fuel (prev_climb_step ns) p.                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition next_climb_step (ns : NS) (np : Z * Z) : option ((Z * Z) + (Z * Z)) :=
  let '(n, p) := np in
  pr ← get_right ns p ;
  if n =? pr then (pp ← get_parent ns p ; Some (inl (p, pp))) else Some (inr (n, p)).

Definition next_node (fuel : nat) (ns : NS) (n : Z) : option Z :=
  nr ← get_right ns n ;
  if negb (nr =? 0) then minimum fuel ns nr
  else
    p ← get_parent ns n ;
    np ← oloop fuel (next_climb_step ns) (n, p) ;
    let '(n', p') := np in
    nr' ← get_right ns n' ;
    Some (if negb (nr' =? p') then p' else n').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition upper_bound_step (cmpU : Z -> bool) (ns : NS) (xy : Z * Z) : option ((Z * Z) + Z) :=
  let '(x, y) := xy in
  let c := cmpU x in
  x' ← load ns x (if c then OFF_LEFT else OFF_RIGHT) ;
  let y' := if c then x else y in
  Some (if x' =? 0 then inr y' else inl (x', y')).

(* [comment removed for export] *)
Definition upper_bound_loop (fuel : nat) (cmpU : Z -> bool) (ns : NS) (x y : Z) : option Z :=
  if x =? 0 then Some y else oloop fuel (upper_bound_step cmpU ns) (x, y).

(* [comment removed for export] *)
Definition upper_bound (fuel : nat) (cmpU : Z -> bool) (ns : NS) (h : Z) : option Z :=
  root ← get_parent ns h ;
  upper_bound_loop fuel cmpU ns root h.

(* [comment removed for export] *)
Definition lower_bound_step (cmpL : Z -> bool) (ns : NS) (xy : Z * Z) : option ((Z * Z) + Z) :=
  let '(x, y) := xy in
  let c := cmpL x in
  x' ← load ns x (if c then OFF_RIGHT else OFF_LEFT) ;
  let y' := if c then y else x in
  Some (if x' =? 0 then inr y' else inl (x', y')).

Definition lower_bound_loop (fuel : nat) (cmpL : Z -> bool) (ns : NS) (x y : Z) : option Z :=
  if x =? 0 then Some y else oloop fuel (lower_bound_step cmpL ns) (x, y).

Definition lower_bound (fuel : nat) (cmpL : Z -> bool) (ns : NS) (h : Z) : option Z :=
  root ← get_parent ns h ;
  lower_bound_loop fuel cmpL ns root h.

(* [comment removed for export] *)
Definition find (fuel : nat) (cmpL cmpU : Z -> bool) (ns : NS) (h : Z) : option Z :=
  root ← get_parent ns h ;                                     (* [comment removed for export] *)
  y ← lower_bound_loop fuel cmpL ns root h ;                   (* [comment removed for export] *)
  if y =? h then Some h                                        (* [comment removed for export] *)
  else if cmpU y then Some h else Some y.                      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition insert_commit (ns : NS) (h new_node : Z) (link_left : bool) (nd : Z) : option NS :=
  if nd =? 0 then None                                         (* [comment removed for export] *)
  else
  ns3 ←
    (if nd =? h then                                           (* [comment removed for export] *)
       ns1 ← set_parent ns h new_node ;
       ns2 ← set_left ns1 h new_node ;
       set_right ns2 h new_node                                (* [comment removed for export] *)
     else if link_left then                                    (* [comment removed for export] *)
       ns1 ← set_left ns nd new_node ;
       hl ← get_left ns1 h ;                                   (* [comment removed for export] *)
       if nd =? hl then set_left ns1 h new_node else Some ns1  (* [comment removed for export] *)
     else                                                      (* [comment removed for export] *)
       ns1 ← set_right ns nd new_node ;
       hr ← get_right ns1 h ;                                  (* [comment removed for export] *)
       if nd =? hr then set_right ns1 h new_node else Some ns1 (* [comment removed for export] *)) ;
  ns4 ← set_parent ns3 new_node nd ;                           (* [comment removed for export] *)
  ns5 ← set_left ns4 new_node 0 ;                              (* [comment removed for export] *)
  set_right ns5 new_node 0.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition insert_before_check (fuel : nat) (ns : NS) (h pos : Z) : option (bool * Z) :=
  hl ← get_left ns h ;
  prev ← (if pos =? hl then Some pos else prev_node fuel ns pos) ;
  hp ← get_parent ns h ;
  if hp =? 0 then Some (true, pos)
  else
    pl ← get_left ns pos ;
    Some (if pl =? 0 then (true, pos) else (false, prev)).

(* [comment removed for export] *)
Definition bst_insert_before (fuel : nat) (ns : NS) (h pos new_node : Z) : option NS :=
  cd ← insert_before_check fuel ns h pos ;
  let '(link_left, nd) := cd in
  insert_commit ns h new_node link_left nd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rb_entry (ns : NS) (h p : Z) : option (NS * ((Z * Z) + unit)) :=
  pp ← get_parent ns p ;
  ns1 ← set_color ns p RED ;
  Some (ns1, if pp =? h then inr tt else inl (p, pp)).

(* [comment removed for export] *)
Definition rb_rot_left_npf (ns : NS) (pp p : Z) : option NS :=
  prl ← get_left ns p ;
  ns1 ← set_right ns pp prl ;
  ns2 ← (if prl =? 0 then Some ns1 else set_parent ns1 prl pp) ;
  ns3 ← set_left ns2 p pp ;
  set_parent ns3 pp p.

(* [comment removed for export] *)
Definition rb_rot_right_npf (ns : NS) (pp p : Z) : option (NS * Z) :=
  plr ← get_right ns p ;
  ns1 ← set_left ns pp plr ;
  ns2 ← (if plr =? 0 then Some ns1 else set_parent ns1 plr pp) ;
  c ← get_left ns2 p ;
  ns3 ← set_right ns2 p pp ;
  ns4 ← set_parent ns3 pp p ;
  Some (ns4, c).

(* [comment removed for export] *)
Definition rb_set_child_black (ns : NS) (h q a3 : Z) (p_was_left : bool) : option NS :=
  ns1 ← (if a3 =? h then set_parent ns h q                     (* [comment removed for export] *)
         else if p_was_left then set_left ns a3 q              (* [comment removed for export] *)
         else set_right ns a3 q) ;                             (* [comment removed for export] *)
  set_color ns1 q BLACK.                                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rb_rotate_left_full (ns : NS) (h gp q c : Z) : option NS :=
  a3 ← get_parent ns gp ;
  a5 ← get_left ns a3 ;
  ns1 ← set_right ns gp c ;
  ns2 ← (if c =? 0 then Some ns1 else set_parent ns1 c gp) ;
  ns3 ← set_parent ns2 gp q ;
  ns4 ← set_parent ns3 q a3 ;
  ns5 ← set_left ns4 q gp ;
  rb_set_child_black ns5 h q a3 (a5 =? gp).

(* [comment removed for export] *)
Definition rb_rotate_right_full (ns : NS) (h gp q : Z) : option NS :=
  a3 ← get_parent ns gp ;
  a5 ← get_right ns q ;
  a4 ← get_left ns a3 ;
  ns1 ← set_left ns gp a5 ;
  ns2 ← (if a5 =? 0 then Some ns1 else set_parent ns1 a5 gp) ;
  ns3 ← set_parent ns2 gp q ;
  ns4 ← set_parent ns3 q a3 ;
  ns5 ← set_right ns4 q gp ;
  rb_set_child_black ns5 h q a3 (a4 =? gp).

(* [comment removed for export] *)
Definition rb_final (ns : NS) (h p pp gp gpl : Z) : option NS :=
  ppl ← get_left ns pp ;
  if pp =? gpl then
    nq ← (if ppl =? p then Some (ns, pp)
          else ns1 ← rb_rot_left_npf ns pp p ; Some (ns1, p)) ;
    let '(ns1, q) := nq in
    rb_rotate_right_full ns1 h gp q
  else
    nqc ← (if ppl =? p then r ← rb_rot_right_npf ns pp p ; Some (fst r, p, snd r)
           else Some (ns, pp, ppl)) ;
    let '(ns1, q, c) := nqc in
    rb_rotate_left_full ns1 h gp q c.

(* [comment removed for export] *)
Definition rb_body (h : Z) (st : NS * (Z * Z)) : option ((NS * (Z * Z)) + NS) :=
  let '(ns, (p, pp)) := st in
  gp ← get_parent ns pp ;
  if gp =? h then Some (inr ns)
  else
    ppc ← get_color ns pp ;
    if ppc =? BLACK then Some (inr ns)
    else
      gpl ← get_left ns gp ;
      ns1 ← set_color ns gp RED ;
      x ← (if negb (pp =? gpl) then Some gpl else get_right ns1 gp) ;
      red ← (if x =? 0 then Some false
             else xc ← get_color ns1 x ; Some (xc =? RED)) ;
      if (red : bool) then
        ns2 ← set_color ns1 x BLACK ;
        ns3 ← set_color ns2 pp BLACK ;
        pp' ← get_parent ns3 gp ;
        Some (if pp' =? h then inr ns3 else inl (ns3, (gp, pp')))
      else
        ns2 ← rb_final ns1 h p pp gp gpl ;
        Some (inr ns2).

(* [comment removed for export] *)
Definition rb_end (ns : NS) (h : Z) : option NS :=
  root ← get_parent ns h ;
  set_color ns root BLACK.

Definition rebalance_after_insertion (fuel : nat) (ns : NS) (h p : Z) : option NS :=
  e ← rb_entry ns h p ;
  let '(ns1, k) := e in
  ns2 ← match k with
        | inr _ => Some ns1
        | inl st => oloop fuel (rb_body h) (ns1, st)
        end ;
  rb_end ns2 h.

(* [comment removed for export] *)
Definition rb_insert_before (fuel : nat) (ns : NS) (h pos new_node : Z) : option NS :=
  ns1 ← bst_insert_before fuel ns h pos new_node ;
  rebalance_after_insertion fuel ns1 h new_node.

(* [comment removed for export] *)
Definition init_header_node (h : Z) : node := mkNode 0 h h RED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record lnode := mkLNode { l_next : Z ; l_prev : Z }.
Definition l_set_next (v : Z) (n : lnode) : lnode := mkLNode v (l_prev n).
Definition l_set_prev (v : Z) (n : lnode) : lnode := mkLNode (l_next n) v.
Abbreviation LS := (gmap Z lnode).

Definition lget_field (off : Z) (n : lnode) : Z := if off =? OFF_NEXT then l_next n else l_prev n.
Definition lset_field (off v : Z) (n : lnode) : lnode :=
  if off =? OFF_NEXT then l_set_next v n else l_set_prev v n.
Definition lload (ls : LS) (a off : Z) : option Z := n ← ls !! a ; Some (lget_field off n).
Definition lstore (ls : LS) (a off v : Z) : option LS :=
  n ← ls !! a ; Some (<[ a := lset_field off v n ]> ls).

Definition get_next (ls : LS) (a : Z) := lload ls a OFF_NEXT.
Definition get_prev (ls : LS) (a : Z) := lload ls a OFF_PREV.
Definition set_next (ls : LS) (a v : Z) := lstore ls a OFF_NEXT v.
Definition set_prev (ls : LS) (a v : Z) := lstore ls a OFF_PREV v.

Definition init_lheader_node (hL : Z) : lnode := mkLNode hL hL.

(* [comment removed for export] *)
Definition link_before (ls : LS) (nxt this : Z) : option LS :=
  prev ← get_prev ls nxt ;
  ls1 ← set_next ls this nxt ;
  ls2 ← set_prev ls1 this prev ;
  ls3 ← set_prev ls2 nxt this ;
  set_next ls3 prev this.

Definition push_back (ls : LS) (hL this : Z) : option LS := link_before ls hL this.

(* [comment removed for export] *)
Definition link_after (ls : LS) (prv this : Z) : option LS :=
  nxt ← get_next ls prv ;
  ls1 ← set_prev ls this prv ;
  ls2 ← set_next ls1 this nxt ;
  ls3 ← set_next ls2 prv this ;
  set_prev ls3 nxt this.

(* [comment removed for export] *)
Definition unlink (ls : LS) (this : Z) : option (LS * Z) :=
  nxt ← get_next ls this ;
  prv ← get_prev ls this ;
  ls1 ← set_next ls prv nxt ;
  ls2 ← set_prev ls1 nxt prv ;
  Some (ls2, nxt).

(* [comment removed for export] *)
Definition iterator_to (ls : LS) (e : Z) : option Z :=
  n ← get_next ls e ;
  if n =? 0 then None else Some e.

(* [comment removed for export] *)
Definition iter_next (ls : LS) (it : Z) : option Z := get_next ls it.

(* [comment removed for export] *)
Definition iter_step (ls : LS) (hL : Z) (st : Z * list Z) : option ((Z * list Z) + list Z) :=
  let '(it, acc) := st in
  if it =? hL then Some (inr (rev acc))
  else nxt ← get_next ls it ; Some (inl (nxt, it :: acc)).

Definition iterate (fuel : nat) (ls : LS) (hL : Z) : option (list Z) :=
  first ← get_next ls hL ;
  oloop fuel (iter_step ls hL) (first, []).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ie_path := IE_begin | IE_newname | IE_dup.

(* [comment removed for export] *)
Definition fields_find (fuel : nat) (cmpL cmpU : Z -> bool) (ns : NS) (ls : LS) (bf : Z) : option Z :=
  let h := bf in let hL := bf + 32 in
  y ← find fuel cmpL cmpU ns h ;                               (* [comment removed for export] *)
  if y =? h then Some hL                                       (* [comment removed for export] *)
  else iterator_to ls (if y =? 0 then 0 else y - ELEM_TO_NODE). (* [comment removed for export] *)

(* [comment removed for export] *)
Definition assert_not_contains (fuel : nat) (cmpL cmpU : Z -> bool) (ns : NS) (ls : LS) (bf : Z) : option unit :=
  r ← fields_find fuel cmpL cmpU ns ls bf ;                    (* [comment removed for export] *)
  if r =? bf + 32 then Some tt else None.                      (* [comment removed for export] *)

Definition insert_element (fuel : nat) (cmpL cmpU : Z -> bool) (ieq : Z -> bool)
           (ns : NS) (ls : LS) (bf e : Z) : option (NS * LS * ie_path) :=
  let h := bf in let hL := bf + 32 in let n := e + ELEM_TO_NODE in
  before ← upper_bound fuel cmpU ns h ;                        (* [comment removed for export] *)
  hl ← get_left ns h ;                                         (* [comment removed for export] *)
  if before =? hl then                                         (* [comment removed for export] *)
    _ ← assert_not_contains fuel cmpL cmpU ns ls bf ;          (* [comment removed for export] *)
    ns' ← rb_insert_before fuel ns h before n ;                (* [comment removed for export] *)
    ls' ← push_back ls hL e ;                                  (* [comment removed for export] *)
    Some (ns', ls', IE_begin)
  else
    lastn ← prev_node fuel ns before ;                         (* [comment removed for export] *)
    let last := (if lastn =? 0 then 0 else lastn - ELEM_TO_NODE) in   (* [comment removed for export] *)
    if negb (ieq last) then                                    (* [comment removed for export] *)
      _ ← assert_not_contains fuel cmpL cmpU ns ls bf ;        (* [comment removed for export] *)
      ns' ← rb_insert_before fuel ns h before n ;              (* [comment removed for export] *)
      ls' ← push_back ls hL e ;                                (* [comment removed for export] *)
      Some (ns', ls', IE_newname)
    else                                                       (* [comment removed for export] *)
      ns' ← rb_insert_before fuel ns h before n ;              (* [comment removed for export] *)
      it ← iterator_to ls last ;                               (* [comment removed for export] *)
      nxt ← iter_next ls it ;                                  (* [comment removed for export] *)
      ls' ← link_before ls nxt e ;                             (* [comment removed for export] *)
      Some (ns', ls', IE_dup).
