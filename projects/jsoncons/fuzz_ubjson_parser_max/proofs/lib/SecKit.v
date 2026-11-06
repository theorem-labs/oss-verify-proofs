(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Ltac2 Require Import Ltac2.
From Stdlib Require Import BinNums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac sec_inst T vs :=
lazymatch vs with
| tt => T
| (?v, ?vs2) => lazymatch T with forall x : _, @?B x => let T2 := eval cbv beta in (B v) in sec_inst T2 vs2 end
end.
Ltac sec_ty T vs := let T1 := sec_inst T vs in lazymatch T1 with forall x : ?A, _ => exact A end.
Ltac sec_stmt T vs := let T1 := sec_inst T vs in exact T1.
Ltac2 rec sec_subst (t : constr) (hs : constr list) : constr :=
match hs with
| [] => t
| h :: hs' =>
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ body => sec_subst (Constr.Unsafe.substnl [h] 0 body) hs'
| _ => Control.throw (Invalid_argument (Some (Message.of_string "sec_subst: not a product")))
end
end.
Ltac2 sec_hyps (k : int) (s : int) : constr list :=
let hs := Control.hyps () in
let n := List.length hs in
List.map (fun (id, _, _) => Control.hyp id) (List.firstn k (List.skipn (Int.sub (Int.sub n s) k) hs)).
Ltac2 sec_inst2_ (t : constr) (k : int) (s : int) : constr := sec_subst t (sec_hyps k s).
Ltac2 sec_ty2_ (t : constr) (k : int) (s : int) : constr :=
match Constr.Unsafe.kind (sec_inst2_ t k s) with
| Constr.Unsafe.Prod b _ => Constr.Binder.type b
| _ => Control.throw (Invalid_argument (Some (Message.of_string "sec_ty2: no binder left")))
end.
Ltac2 rec sec_nat (c : constr) : int := lazy_match! c with | O => 0 | S ?n => Int.add 1 (sec_nat n) end.
Ltac2 rec sec_pos (c : constr) : int :=
lazy_match! c with | xH => 1 | xO ?p => Int.mul 2 (sec_pos p) | xI ?p => Int.add 1 (Int.mul 2 (sec_pos p)) end.
Ltac2 sec_numc (c : constr) : int :=
lazy_match! c with | O => 0 | S ?n => Int.add 1 (sec_nat n) | Z0 => 0 | Zpos ?p => sec_pos p end.
Ltac2 sec_num (v : Ltac1.t) : int :=
match Ltac1.to_int v with Some i => i | None => sec_numc (Option.get (Ltac1.to_constr v)) end.
Set Default Proof Mode "Classic".
Ltac sec_ty2 T k s := let f := ltac2:(t k s |- let a := sec_ty2_ (Option.get (Ltac1.to_constr t)) (sec_num k) (sec_num s) in exact $a) in f T k s.
Ltac sec_stmt2 T k s := let f := ltac2:(t k s |- let a := sec_inst2_ (Option.get (Ltac1.to_constr t)) (sec_num k) (sec_num s) in exact $a) in f T k s.
Ltac sec_inst2 T k s := constr:(ltac:(sec_stmt2 T k s)).
