(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Ltac2 Require Import Ltac2 Constr Control Message.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Create Rewrite HintDb gw_eqs.

Ltac2 gw_try_exact (t : constr) : unit := ltac1:(t |- exact t) (Ltac1.of_constr t).

Ltac2 gw_next (t : constr) (ty : constr) (e : exn) (k : constr -> constr -> 'a) : 'a :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in

k constr:($t $h) (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => Control.zero e
end
| None => Control.zero e
end
| Constr.Unsafe.LetIn _ body rest => k t (Constr.Unsafe.substnl [body] 0 rest)
| Constr.Unsafe.Cast c _ _ => k t c
| _ => Control.zero e
end.

Ltac2 rec gw_go (t : constr) (ty : constr) : unit :=
Control.plus (fun () => gw_try_exact t) (fun e => gw_next t ty e gw_go).

Ltac2 gw_exact0 (t : constr) : unit := gw_go t (Constr.type t).
Ltac gw_exact t := let f := ltac2:(t |- gw_exact0 (Option.get (Ltac1.to_constr t))) in f t.

Ltac2 rec gw_term_go (target : constr) (t : constr) (ty : constr) : constr :=
match Control.case (fun () => Std.unify ty target) with
| Val _ => t
| Err e => gw_next t ty e (gw_term_go target)
end.
Ltac2 gw_term0 (t : constr) (d : constr) : unit :=
let r := gw_term_go (Constr.type d) t (Constr.type t) in gw_try_exact r.
Ltac gw_term t d := let f := ltac2:(t d |- gw_term0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr d))) in f t d.

Ltac gw_hyp_of t :=
let T := type of t in
lazymatch T with
| forall _ : ?A, _ => exact A
| _ => let T' := eval hnf in T in lazymatch T' with forall _ : ?A, _ => exact A end
end.
