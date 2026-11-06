(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 rec inst_go (c : constr) (ty : constr) : constr :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod b body =>
      match Constr.Binder.name b with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val p => let (h, _) := p in
                     inst_go (Constr.Unsafe.make (Constr.Unsafe.App c [|h|])) (Constr.Unsafe.substnl [h] 0 body)
          | Err _ => c
          end
      | None => c
      end
  | Constr.Unsafe.Cast ty' _ _ => inst_go c ty'
  | _ => c
  end.

Ltac2 inst_sec (c : constr) := let r := inst_go c (Constr.type c) in exact $r.
