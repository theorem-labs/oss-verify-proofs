(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bx X1bw X1c3.

Ltac lia_tuned :=
first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_prune; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ].

Module PLiaL2.
Import Ltac2.

Ltac2 revert_nonsec () : unit :=
List.iter (fun (h : ident * constr option * constr) => let (id, _, ty) := h in
if Bool.and (Bool.neg (X1bx.zt_is_local id)) (X1bx.zt_is_prop ty) then ()
else (match Control.case (fun () => Std.revert [id]) with Val _ => () | Err _ => () end)) (List.rev (Control.hyps ())).

Ltac2 vars_in (c : constr) : ident list :=
let acc := Ref.ref [] in
let rec go (t : constr) : unit :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Var id => if List.exist (Ident.equal id) (Ref.get acc) then () else Ref.set acc (id :: Ref.get acc)
| _ => Constr.Unsafe.iter go t
end in
go c; Ref.get acc.

Ltac2 clear_sec_props (pf : constr option) : unit :=
let used := match pf with Some c => vars_in c | None => [] end in
List.iter (fun (h : ident * constr option * constr) => let (id, _, ty) := h in
if X1bx.zt_is_local id then ()
else if X1bx.zt_is_prop ty then
(if List.exist (Ident.equal id) used then ()
else (match Control.case (fun () => Std.clear [id]) with Val _ => () | Err _ => () end))
else ()) (List.rev (Control.hyps ())).
Ltac2 revert_nonsec1 () : unit := Control.enter revert_nonsec.
Ltac2 lean_keep1 () : unit := Control.enter (fun () => LL2.lean_keep_n 1).
Ltac2 clear_all1 () : unit := Control.enter (fun () => clear_sec_props None).
Ltac2 clear_except1 (pf : constr) : unit := Control.enter (fun () => clear_sec_props (Some pf)).
End PLiaL2.
Ltac revert_nonsec := ltac2:(PLiaL2.revert_nonsec1 ()).
Ltac lean_keep1 := ltac2:(PLiaL2.lean_keep1 ()).
Ltac clear_sec_props := ltac2:(PLiaL2.clear_all1 ()).
Ltac clear_sec_props_except pf := let f := ltac2:(pf |- PLiaL2.clear_except1 (Option.get (Ltac1.to_constr pf))) in f pf.

Ltac plia_ne := zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac plia_eu := Zify.zify; xlia zchecker.

Module PLiaL5.
Import Ltac2.
Ltac2 rec lits (gf : constr list) (acc : constr list) (t : constr) : constr list :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f constr:(Z.of_nat)) (Int.equal (Array.length args) 1) then
(if OffL2.ground gf (Array.get args 0) then (if List.exist (Constr.equal t) acc then acc else t :: acc)
else lits gf acc (Array.get args 0))
else Array.fold_left (lits gf) acc args
| Constr.Unsafe.Prod b body => lits gf (lits gf acc (Constr.Binder.type b)) body
| Constr.Unsafe.Cast c _ _ => lits gf acc c
| _ => acc
end.

Ltac2 chg_goal (t : constr) : unit :=
let v := Std.eval_vm None t in ltac1:(t v |- change t with v) (Ltac1.of_constr t) (Ltac1.of_constr v).
Ltac2 chg_hyp (id : ident) (t : constr) : unit :=
let v := Std.eval_vm None t in ltac1:(t v h |- change t with v in h) (Ltac1.of_constr t) (Ltac1.of_constr v) (Ltac1.of_ident id).
Ltac2 simp_ofnat (hyps : bool) : unit :=
let gf := OffL2.gfuns () in
List.iter chg_goal (lits gf [] (Control.goal ()));
if hyps then
List.iter (fun (h : ident * constr option * constr) => let (id, _, ty) := h in
if Bool.and (X1bx.zt_is_local id) (X1bx.zt_is_prop ty) then List.iter (chg_hyp id) (lits gf [] ty) else ()) (Control.hyps ())
else ().
Ltac2 simp_goal1 () : unit := Control.enter (fun () => simp_ofnat false).
Ltac2 simp_all1 () : unit := Control.enter (fun () => simp_ofnat true).
End PLiaL5.
Ltac simp_ofnat_goal := ltac2:(PLiaL5.simp_goal1 ()).
Ltac simp_ofnat_all := ltac2:(PLiaL5.simp_all1 ()).

Ltac clear_unused pf := repeat match goal with H : _ |- _ => lazymatch pf with context [H] => fail | _ => clear H end end.
Ltac min_closed tail :=
simp_ofnat_all;
lazymatch goal with |- ?G =>
let pf := constr:(ltac:(tail) : G) in
clear_unused pf; revert_nonsec; intros;
first [ exact pf | tail ]
end.

Ltac lean_core :=
first [ timeout 10 (solve [ os_lia ])   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
| timeout 90 (solve [ lean_clear; simp_ofnat_goal; revert_nonsec; intros; plia_ne ])   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
| timeout 90 (solve [ lean_keep1; min_closed ltac:(plia_ne) ])   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
| timeout 90 (solve [ lean_keep; min_closed ltac:(plia_ne) ])   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
| timeout 90 (solve [ lean_keep6; min_closed ltac:(plia_ne) ])   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
| timeout 90 (solve [ lean_keep6; min_closed ltac:(plia_eu) ]) ].   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)

Module PLiaL6.
Import Ltac2.

Ltac2 uses_sec_prop (pf : constr) : bool :=
let used := PLiaL2.vars_in pf in
List.exist (fun (h : ident * constr option * constr) => let (id, _, ty) := h in
if X1bx.zt_is_local id then false
else if X1bx.zt_is_prop ty then List.exist (Ident.equal id) used else false) (Control.hyps ()).
Ltac2 check_uses_sec (pf : constr) : unit := Control.enter (fun () => if uses_sec_prop pf then () else Control.zero Not_found).
End PLiaL6.
Ltac pf_uses_sec pf := let f := ltac2:(pf |- PLiaL6.check_uses_sec (Option.get (Ltac1.to_constr pf))) in f pf.
Ltac os_tier := timeout 10 (solve [ os_lia ]).   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
Ltac lean_tier := goal_has_atoms; timeout 90 (solve [ lean_keep; min_closed ltac:(plia_ne) ]).   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)

Ltac plia_size stock :=
first [ solve [ goal_liable; clear_sec_props; lean_core ]
| lazymatch goal with |- ?G =>
let pf0 := constr:(ltac:(stock) : G) in
first [ solve [ clear_sec_props_except pf0; first [ goal_liable; lean_core | timeout 90 false_lia ] ] | exact pf0 ] end ].   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
Ltac plia_fast0 stock := first [ solve [ goal_liable; clear_sec_props; os_tier ] | stock ].
Ltac plia_mid0 stock := first [ solve [ goal_liable; clear_sec_props; first [ os_tier | lean_tier ] ] | stock ].
Ltac plia_midB stock :=
first [ solve [ goal_liable; clear_sec_props; first [ os_tier | lean_tier ] ]
| lazymatch goal with |- ?G =>
let pf0 := constr:(ltac:(stock) : G) in
first [ solve [ goal_liable; pf_uses_sec pf0; clear_sec_props_except pf0; os_tier ] | exact pf0 ] end ].

Ltac plia_gen stock := plia_mid0 stock.

Ltac plia := plia_gen ltac:(lia_tuned).
Ltac lia ::= plia.
