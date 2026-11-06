(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TL.
  Import Ltac2.
  Ltac2 is_and (h : constr) : bool :=
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Ind i _ => (match reference:(and) with Std.IndRef i' => Ind.equal i i' | _ => false end)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 exact_hyp () : unit :=
    let g := Control.goal () in
    let rec go (hs : (ident * constr option * constr) list) : unit :=
      match hs with
      | [] => Control.zero (Tactic_failure None)
      | h :: r =>
          let (id, _, ty) := h in
          if Constr.equal ty g then Std.exact_no_check (Control.hyp id)
          else
            match Constr.Unsafe.kind ty with
            | Constr.Unsafe.App hd args =>
                if Int.equal (Array.length args) 2 then
                  (if is_and hd then
                     (if Constr.equal (Array.get args 0) g then (let hh := Control.hyp id in Std.exact_no_check constr:(proj1 $hh))
                      else if Constr.equal (Array.get args 1) g then (let hh := Control.hyp id in Std.exact_no_check constr:(proj2 $hh))
                      else go r)
                   else go r)
                else go r
            | _ => go r
            end
      end in
    go (Control.hyps ()).
End TL.
Ltac exact_hyp := ltac2:(Control.enter TL.exact_hyp).

(* [comment removed for export] *)
Ltac zlit_pos p := lazymatch p with xH => idtac | xO ?q => zlit_pos q | xI ?q => zlit_pos q end.
Ltac zlit z := lazymatch z with Z0 => idtac | Zpos ?p => zlit_pos p | Zneg ?p => zlit_pos p end.

Ltac lia_triv1 :=
  lazymatch goal with
  | |- Z.le ?a ?b => first [ constr_eq a b; exact (Z.le_refl a)
                           | zlit a; zlit b; exact (proj1 (Z.leb_le a b) (@eq_refl bool true))
                           | exact_hyp ]
  | |- Z.lt ?a ?b => first [ zlit a; zlit b; exact (proj1 (Z.ltb_lt a b) (@eq_refl bool true)) | exact_hyp ]
  | |- @eq Z ?a ?b => first [ constr_eq a b; exact (@eq_refl Z a) | exact_hyp ]
  | |- @eq nat _ _ => exact_hyp
  | |- le _ _ => exact_hyp
  | |- lt _ _ => exact_hyp
  end.
Ltac lia_triv :=
  lazymatch goal with
  | |- _ /\ _ => first [ exact_hyp | split; lia_triv1 ]
  | |- _ => lia_triv1
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
