(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Cells Step.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module JN.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec root_is_junk (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var id =>
        let s := Ident.to_string id in
        let pre (p : string) : bool :=
          if Int.lt (String.length s) (String.length p) then false else
          (let rec go (i : int) : bool := if Int.ge i (String.length p) then true else if Int.equal (Char.to_int (String.get s i)) (Char.to_int (String.get p i)) then go (Int.add i 1) else false in go 0) in
        if pre "junk" then true else pre "jk"
    | Constr.Unsafe.App h args =>
        if Int.equal (Array.length args) 3 then
          (if (if Constr.equal h '@firstn then true else Constr.equal h '@skipn) then root_is_junk (Array.get args 2) else false)
        else false
    | _ => false
    end.
  Ltac2 check (t : constr) : unit :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var _ => Control.zero (Tactic_failure None)        (* [comment removed for export] *)
    | _ => if root_is_junk t then () else Control.zero (Tactic_failure None)
    end.
End JN.
Ltac jn_is_junk bs := let f := ltac2:(bs |- JN.check (Option.get (Ltac1.to_constr bs))) in f bs.
Ltac jn_name_junk H :=
  repeat match type of H with
         | context [CB ?n ?bs] => jn_is_junk bs; let j := fresh "jk" in set (j := bs) in H; clearbody j
         end.
(* [comment removed for export] *)
Ltac split_for_access_jn H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                   | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
             [ jn_name_junk H | exact_no_check (@eq_refl bool true) | exact_no_check (@eq_refl (list cell) cs2) ]
      end
  end.
