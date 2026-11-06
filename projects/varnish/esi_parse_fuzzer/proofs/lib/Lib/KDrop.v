(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.

Inductive kd_mark : Prop := KdMark : kd_mark.

Ltac2 mutable kd_debug : bool := false.
Ltac2 kd_note (s : string) (n : ident) : unit :=
  if kd_debug then Message.print (Message.concat (Message.of_string s) (Message.of_ident n)) else ().

Ltac2 kd_try_clear (n : ident) : unit :=
  match Control.case (fun () => Std.clear [n]) with
  | Val _ => kd_note "note: KDROP cleared " n
  | Err _ => kd_note "note: KDROP could not clear " n
  end.

Ltac2 kd_hyp_names () : ident list := List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()).

Ltac2 kdrop_ids (names : ident list) : unit :=
  let hs := kd_hyp_names () in
  List.iter (fun n => if List.exist (fun h => Ident.equal h n) hs then kd_try_clear n else ()) names.

Ltac2 kd_is_mark (ty : constr) : bool :=
  lazy_match! ty with
  | kd_mark => true
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 kdrop_marked () : unit :=
  let marks := List.map_filter (fun h => let (id, _, ty) := h in if kd_is_mark ty then Some id else None) (Control.hyps ()) in
  match marks with
  | [] => ()
  | _ :: _ =>
      List.iter kd_try_clear marks;
      let ms := List.map Ident.to_string marks in
      List.iter (fun h =>
          let key := String.app "kdm_" (Ident.to_string h) in
          if List.exist (String.equal key) ms then kd_try_clear h else ())
        (kd_hyp_names ())
  end.
