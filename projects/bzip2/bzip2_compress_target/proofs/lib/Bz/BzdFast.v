(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Frame.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Module BF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 is_op (h : constr) : bool :=
    if Constr.equal h '@Z.add then true else if Constr.equal h '@Z.sub then true
    else if Constr.equal h '@Z.mul then true else if Constr.equal h '@Z.opp then true
    else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
    else if Constr.equal h '@or then true else if Constr.equal h '@and then true
    else if Constr.equal h '@not then true else if Constr.equal h '@Z.of_nat then true
    else if Constr.equal h '@id then true else false.
  Ltac2 is_lit_head (h : constr) : bool :=
    if Constr.equal h '@Zpos then true else if Constr.equal h '@Zneg then true else false.
  Ltac2 rec mem_c (c : constr) (l : constr list) : bool :=
    match l with [] => false | x :: r => if Constr.equal c x then true else mem_c c r end.
  Ltac2 rec atoms (acc : constr list) (c : constr) : constr list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h args =>
        if is_lit_head h then acc
        else if is_op h then Array.fold_left atoms acc args
        else (if mem_c c acc then acc else c :: acc)
    | Constr.Unsafe.Constructor _ _ => acc      (* [comment removed for export] *)
    | Constr.Unsafe.Ind _ _ => acc              (* [comment removed for export] *)
    | Constr.Unsafe.Sort _ => acc
    | _ => if mem_c c acc then acc else c :: acc
    end.
  Ltac2 rec count_shared (l : constr list) (g : constr list) (sh : int) (un : int) : int * int :=
    match l with
    | [] => (sh, un)
    | x :: r => if mem_c x g then count_shared r g (Int.add sh 1) un else count_shared r g sh (Int.add un 1)
    end.
  (* [comment removed for export] *)
  Ltac2 candidates () : ident list :=
    let g := atoms [] (Control.goal ()) in
    let scored := List.map_filter (fun h => let (id, _, ty) := h in
        lazy_match! ty with
        | id (_ \/ _) => let (sh, un) := count_shared (atoms [] ty) g 0 0 in
                         if Int.equal sh 0 then None else Some (id, sh, un)
        | _ => None
        end) (Control.hyps ()) in
    let better (a : ident * int * int) (b : ident * int * int) : int :=
      let (_, s1, u1) := a in let (_, s2, u2) := b in
      if Int.gt s1 s2 then -1 else if Int.lt s1 s2 then 1 else Int.compare u1 u2 in
    List.map (fun x => let (id, _, _) := x in id) (List.sort better scored).
  Ltac2 rec try_each (ids : ident list) (k : ident -> unit) : unit :=
    match ids with
    | [] => Control.zero (Tactic_failure None)
    | id :: r => Control.plus (fun () => k id) (fun _ => try_each r k)
    end.
  Ltac2 rec firstn (n : int) (l : ident list) : ident list :=
    if Int.le n 0 then [] else match l with [] => [] | x :: r => x :: firstn (Int.sub n 1) r end.
  Ltac2 targeted () : unit :=
    let ids := firstn 3 (candidates ()) in
    Control.once (fun () => try_each ids (fun id =>
      let h := Control.hyp id in
      ltac1:(h |- unfold id in h; first [ solve [ destruct h as [h|h]; lia ] | lia ]) (Ltac1.of_constr h))).
End BF.
Ltac dlia_targeted := ltac2:(Control.enter BF.targeted).
Ltac dlia_rest := match goal with H : id (_ \/ _) |- _ => unfold id in H;
                    first [ lia | match goal with H' : id (_ \/ _) |- _ => unfold id in H'; lia end ] end.
Ltac dlia_fast := first [ lia | dlia_targeted | dlia_rest ].

(* [comment removed for export] *)
Ltac dj_conj_lia :=
  first [ solve [ repeat match goal with D : (_ \/ _) |- _ => destruct D as [D|D] end; lia ] | lia ].
Ltac dj_conjs_lia :=
  lazymatch goal with
  | |- _ /\ _ => split; [ dj_conj_lia | dj_conjs_lia ]
  | |- True => exact I
  | |- _ => dj_conj_lia
  end.
(* [comment removed for export] *)
Ltac dj_seplin := cbn [Frame.disjoint_from]; SepLinT.sl_tslia ltac:(idtac; lia).
Ltac cbn_lia := first [ solve [ dj_seplin ] | solve [ cbn; dj_conjs_lia ] | cbn; lia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac subfp_neg OX :=
  lazymatch type of OX with
  | ?A /\ ?B => first [ solve [ let O := fresh "O" in pose proof (proj1 OX) as O; clear OX; first [ exact O | lia ] ]
                      | let R := fresh "OXr" in pose proof (proj2 OX) as R; clear OX; subfp_neg R ]
  | _ => fail
  end.
Ltac subfp_fast :=
  unfold Frame.sub_fp; cbn [Frame.outside app]; let xo := fresh "xo" in let OX := fresh "OX" in intros xo OX;
  repeat split; try exact I; first [ subfp_neg OX | dlia_fast ].
