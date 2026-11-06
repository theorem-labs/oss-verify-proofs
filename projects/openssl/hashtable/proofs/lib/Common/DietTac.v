(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac diet_injection H :=
  lazymatch type of H with
  | ?l = ?r =>
      let l' := eval hnf in l in
      let r' := eval hnf in r in
      lazymatch l' with
      | Some ?a =>
          lazymatch r' with
          | Some ?b =>
              first
                [ is_var b;
                  change (Some a = Some b) in H;
                  apply (f_equal (fun o => match o with Some x => x | None => a end)) in H;
                  change (a = b) in H; subst b
                | is_var a;
                  change (Some a = Some b) in H;
                  apply (f_equal (fun o => match o with Some x => x | None => b end)) in H;
                  change (a = b) in H; subst a
                | injection H as <- ]
          | _ => injection H as <-
          end
      | _ => injection H as <-
      end
  | _ => injection H as <-
  end.

(* [comment removed for export] *)
Ltac diet_eassumption :=
  first
    [ lazymatch goal with
      | |- ?f ?l ?e =>
          match goal with
          | H : ?g ?l2 ?e2 |- _ => constr_eq l l2; constr_eq e e2; exact H
          end
      end
    | eassumption ].
