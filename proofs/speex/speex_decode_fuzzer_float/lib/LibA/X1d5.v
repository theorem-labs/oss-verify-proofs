(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1ct X1d6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module OLia2.
Import Ltac2.
Ltac2 rec codomain (t : constr) : constr :=
match Constr.Unsafe.kind t with Constr.Unsafe.Prod _ b => codomain b | _ => t end.
Ltac2 rec head (t : constr) : constr :=
match Constr.Unsafe.kind t with Constr.Unsafe.App f _ => head f | Constr.Unsafe.Cast c _ _ => head c | _ => t end.
Ltac2 sort_is_prop (ty : constr) : bool := lazy_match! codomain ty with Prop => true | _ => false end.

Ltac2 is_prop (ty : constr) : bool :=
let h := head (codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => sort_is_prop (Constr.type h)
| Constr.Unsafe.Ind _ _ => sort_is_prop (Constr.type h)
| Constr.Unsafe.Var _ => sort_is_prop (Constr.type h)
| _ => false
end.

Ltac2 clear_sec_except (pf0 : constr) : unit :=
let used := LDce2.secvars pf0 in
List.iter (fun (h : ident * constr option * constr) => let (id, _, ty) := h in
if LDce2.is_secvar id then
(if List.exist (Ident.equal id) used then ()
else if is_prop ty then (match Control.case (fun () => Std.clear [id]) with _ => () end) else ())
else ()) (List.rev (Control.hyps ())).
Ltac2 clear_sec_except1 (pf0 : constr) : unit := Control.enter (fun () => clear_sec_except pf0).

Ltac2 has_sec_props () : bool :=
List.exist (fun (h : ident * constr option * constr) => let (id, b, ty) := h in
match b with Some _ => false | None => if LDce2.is_secvar id then is_prop ty else false end) (Control.hyps ()).
Ltac2 no_sec_props () : unit := if has_sec_props () then Control.zero Not_found else ().
End OLia2.
Ltac olia_no_sec_props := ltac2:(OLia2.no_sec_props ()).
Ltac olia_clear_sec_except pf0 := let f := ltac2:(p |- OLia2.clear_sec_except1 (Option.get (Ltac1.to_constr p))) in f pf0.
Ltac olia_os pf0 :=
lazymatch goal with |- ?G =>
let pf1 := constr:(ltac:(olia_clear_sec_except pf0; timeout 30 (solve [ os_lia ])) : G) in   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
ldce_keep_install pf0 pf1
end.

Ltac olia_direct stock :=
first [ timeout 30 (solve [ os_lia ]) | ldce stock ].   (* timeout-ok: tiered lia: expiry takes the next tier, and every caller catches a failure of the last one *)
Ltac olia stock := idtac;
lazymatch goal with
| |- ?G => tryif has_evar G then stock
else tryif ldce_no_ctx_evar then (tryif olia_no_sec_props then olia_direct stock
else let pf0 := constr:(ltac:(stock) : G) in
first [ olia_os pf0 | ldce_install pf0 ])
else stock
end.

