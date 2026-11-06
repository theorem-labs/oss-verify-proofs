(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LK.
  Import Ltac2.
  Ltac2 k1 (ids : ident list) : unit :=
    let hs := List.map (fun (h : ident * constr option * constr) => let (id, _, _) := h in id) (Control.hyps ()) in
    Std.keep (List.filter (fun id => List.mem Ident.equal id hs) ids).
  Ltac2 k (ids : ident list) : unit := Control.enter (fun () => k1 ids).
End LK.

Module LiaKeepSelfTest.
  Local Open Scope Z_scope.
  Goal forall (x y z : Z) (l : list Z), length l = 3%nat -> x < y -> y < z -> z mod 8 = 0 -> x < z.
  Proof. intros x y z l HL Hxy Hyz Hm. ltac2:(LK.k [@Hxy; @Hyz; @Habsent]); lia. Qed.
End LiaKeepSelfTest.
