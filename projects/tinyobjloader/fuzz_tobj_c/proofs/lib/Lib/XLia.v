(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Ltac2 slia_keep_prop (t : constr) : bool :=
  lazy_match! t with
  | @eq Z _ _ => true | @eq nat _ _ => true | @eq N _ _ => true | @eq positive _ _ => true
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | N.le _ _ => true | N.lt _ _ => true | N.ge _ _ => true | N.gt _ _ => true
  | Pos.le _ _ => true | Pos.lt _ _ => true | Pos.ge _ _ => true | Pos.gt _ _ => true
  | _ /\ _ => true | _ \/ _ => true | ~ _ => true | _ <-> _ => true | False => true
  | _ -> _ => true
  | _ => false
  end.

Ltac2 slia_keep (t : constr) : bool :=
  let s := Constr.type t in
  if Constr.equal s constr:(Prop) then slia_keep_prop t
  else lazy_match! t with
       | Z => true | nat => true | N => true | positive => true
       | _ => false
       end.

Ltac2 slia_clear0 () : unit :=
  List.iter (fun (h : ident * constr option * constr) =>
               let (id, _, t) := h in
               if slia_keep t then ()
               else match Control.case (fun () => Std.clear [id]) with
                    | Val _ => () | Err _ => ()
                    end)
            (List.rev (Control.hyps ())).

Ltac slia_clear := ltac2:(slia_clear0 ()).

Ltac slia := first [ solve [ slia_clear; lia ] | lia ].
Ltac snia := first [ solve [ slia_clear; nia ] | nia ].

Ltac slia_dbg := first [ solve [ slia_clear; lia ] | match goal with |- ?g => first [ solve [lia]; idtac "SLIA-TRUE-FALLBACK" g | idtac "SLIA-BOTH-FAIL" g; fail ] end ].
