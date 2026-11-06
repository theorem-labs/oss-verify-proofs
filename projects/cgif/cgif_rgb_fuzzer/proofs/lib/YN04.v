(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2 Init Constr FSet Control Std List Array Bool Ident Int Env.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YN03.
Module LF2.
Import Ltac2.Init.
Ltac2 rec has_or (ty : constr) : bool :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Constr.equal f '@or then true
else if List.exist (fun c => Constr.equal f c) ['@and; '@iff; '@not] then Array.exist has_or args
else false
| Constr.Unsafe.Prod b c =>
if Constr.Unsafe.noccurn 1 c then (if has_or (Constr.Binder.type b) then true else has_or c) else false
| _ => false
end.
Ltac2 hide_or () : unit :=
let hs := Control.hyps () in
let ids := List.fold_left
(fun acc h => let (id, _, ty) := h in
if YN03.lf_is_section id then acc else if has_or ty then id :: acc else acc) [] hs in
match ids with
| [] => Control.zero (Tactic_failure None)
| _ :: _ => let m := YN03.lf_clear_list ids in if Int.lt m 1 then Control.zero (Tactic_failure None) else ()
end.
Ltac2 goal_closed () : unit := if YN03.lf_has_var (Control.goal ()) then Control.zero (Tactic_failure None) else ().
End LF2.
Ltac lf2_hide_or := ltac2:(Control.enter LF2.hide_or).
Ltac lf2_goal_closed := ltac2:(Control.enter LF2.goal_closed).
Ltac lia_full := Zify.zify; xlia zchecker.
Ltac lia_cheap :=
first [ solve [YN03.lf_prune0; lia_full] | solve [YN03.lf_prune1; lia_full] | solve [lf2_hide_or; lia_full] ].
Ltac YN03.lf_lia_orig ::=
tryif YN03.lf_arith_goal
then (tryif lf2_goal_closed
then first [ solve [YN03.lf_prune0; lia_full]
| solve [lf2_hide_or; lia_full]
| tryif lf2_hide_or then fail else lia_full ]
else first [ solve [lf2_hide_or; lia_full] | lia_full ])
else first [ solve [lf2_hide_or; lia_full] | lia_full ].
