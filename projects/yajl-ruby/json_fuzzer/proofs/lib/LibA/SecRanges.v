(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".

Ltac2 sr_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.

Ltac2 force_section_ranges0 () : unit :=
  List.iter (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => ()
    | None =>
        if sr_is_local id then () else
        lazy_match! ty with
        | (0 <= _ < _)%Z => let c := Control.hyp id in Std.pose None c
        | _ => ()
        end
    end) (Control.hyps ()).
Ltac force_section_ranges := ltac2:(Control.enter force_section_ranges0).
