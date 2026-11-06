(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Zify Lia.
From Ltac2 Require Import Ltac2 Constr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac fl_zify := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (zify_iter_specs); zify_saturate; Zify.zify_post_hook.
Ltac lia_nodiv := fl_zify; xlia zchecker.

(* [comment removed for export] *)
Ltac2 fl_max (a : int) (b : int) : int := if Int.lt a b then b else a.
Ltac2 rec fl_level (t : constr) : int :=
  lazy_match! t with
  | Z.le _ _ => 1 | Z.lt _ _ => 1 | Z.ge _ _ => 1 | Z.gt _ _ => 1 | @eq Z _ _ => 1
  | le _ _ => 1 | lt _ _ => 1 | ge _ _ => 1 | gt _ _ => 1 | @eq nat _ _ => 1
  | N.le _ _ => 1 | N.lt _ _ => 1 | @eq N _ _ => 1
  | @eq positive _ _ => 1 | Pos.le _ _ => 1 | Pos.lt _ _ => 1 | @eq bool _ _ => 3
  | ?a /\ ?b => fl_max (fl_level a) (fl_level b)
  | ?a \/ ?b => let la := fl_level a in let lb := fl_level b in
                if Int.equal (fl_max la lb) 0 then 0 else if Int.le (fl_max la lb) 1 then 2 else 3
  | ~ ?a => let la := fl_level a in
            if Int.equal la 0 then 0 else
            lazy_match! a with | _ /\ _ => 3 | _ \/ _ => 3 | _ => la end
  | ?a <-> ?b => if Int.equal (fl_max (fl_level a) (fl_level b)) 0 then 0 else 3
  | ?a -> ?b => if Int.equal (fl_max (fl_level a) (fl_level b)) 0 then 0 else 3
  | _ => 0
  end.
Ltac2 fl_is_prop (t : constr) : bool := Constr.equal (Constr.type t) 'Prop.
(* [comment removed for export] *)
Ltac2 fl_filter (lvl : int) : unit :=
  let hs := Control.hyps () in
  let bad := List.fold_right (fun (id, _, ty) acc =>
               if fl_is_prop ty then (let l := fl_level ty in if Int.equal l 0 then id :: acc else if Int.lt lvl l then id :: acc else acc) else acc) hs [] in
  Control.once (fun () => Control.plus (fun () => Std.clear bad)
    (fun _ => List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) bad)).
Ltac fl_keep1 := ltac2:(fl_filter 1).
Ltac fl_keep2 := ltac2:(fl_filter 2).
Ltac fl_keepP := ltac2:(fl_filter 3).

Ltac flia := first [ solve [fl_keep1; lia_nodiv] | solve [fl_keep2; lia_nodiv] | solve [fl_keepP; Lia.lia] ].
Ltac lia := flia.
