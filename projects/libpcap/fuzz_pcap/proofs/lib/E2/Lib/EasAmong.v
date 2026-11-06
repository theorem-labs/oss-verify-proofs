(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1.
#[local] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 ea_of_ltac1 (l : Ltac1.t) : ident list :=
  match Ltac1.to_list l with
  | Some xs => List.map (fun x => match Ltac1.to_ident x with Some i => i | None => Control.throw (Invalid_argument (Some (Message.of_string "eas_among: not an identifier"))) end) xs
  | None => Control.throw (Invalid_argument (Some (Message.of_string "eas_among: not a list")))
  end.
Ltac2 ea_among (ids : ident list) : unit :=
  Control.once (fun () =>
    let rec go l := match l with
      | [] => Control.zero (Tactic_failure (Some (Message.of_string "eas_among: no listed hypothesis applies")))
      | h :: r => let (id, _, _) := h in
          if List.exist (Ident.equal id) ids
          then Control.plus (fun () => ltac1:(x |- eexact x) (Ltac1.of_ident id)) (fun _ => go r)
          else go r
      end in
    go (List.rev (Control.hyps ()))).
Tactic Notation "eas_among" ne_ident_list(l) :=
  let f := ltac2:(l |- Control.enter (fun () => ea_among (ea_of_ltac1 l))) in f l.
