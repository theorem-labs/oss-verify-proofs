(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1.
#[local] Set Default Proof Mode "Classic".
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac2 kh_keep_only (ids : ident list) : unit :=
  Control.once (fun () => List.iter (fun (h, _, _) =>
      if List.exist (Ident.equal h) ids then ()
      else Control.plus (fun () => Std.clear [h]) (fun _ => ()))
    (List.rev (Control.hyps ()))).
Ltac2 kh_of_ltac1 (l : Ltac1.t) : ident list :=
  match Ltac1.to_list l with
  | Some xs => List.map (fun x => match Ltac1.to_ident x with Some i => i | None => Control.throw (Invalid_argument (Some (Message.of_string "keep_hyps: not an identifier"))) end) xs
  | None => Control.throw (Invalid_argument (Some (Message.of_string "keep_hyps: not a list")))
  end.
(* [comment removed for export] *)
Ltac2 kh_keep_only_s (ids : ident list) : unit :=
  Control.once (fun () => List.iter (fun (h, _, _) =>
      if List.exist (Ident.equal h) ids then ()
      else match Env.get [h] with
           | Some _ => ()
           | None => Control.plus (fun () => Std.clear [h]) (fun _ => ())
           end)
    (List.rev (Control.hyps ()))).
Tactic Notation "keep_hyps_s" ne_ident_list(l) :=
  let f := ltac2:(l |- Control.enter (fun () => kh_keep_only_s (kh_of_ltac1 l))) in f l.
Tactic Notation "keep_hyps" ne_ident_list(l) :=
  let f := ltac2:(l |- Control.enter (fun () => kh_keep_only (kh_of_ltac1 l))) in f l.
