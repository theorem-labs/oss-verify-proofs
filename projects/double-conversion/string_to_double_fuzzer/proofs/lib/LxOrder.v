(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Wellfounded.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module LXO.

(* [comment removed for export] *)
Fixpoint lex_lt (cur start : list Z) : Prop :=
  match cur, start with
  | c :: cr, s :: sr => (0 <= c /\ c < s /\ length cr = length sr /\ Forall (fun z => 0 <= z) cr)
                        \/ (0 <= c /\ c = s /\ lex_lt cr sr)
  | _, _ => False
  end.

Definition mu_lt (cur start : list Z) : Prop :=
  (start = [] /\ cur <> [] /\ Forall (fun z => 0 <= z) cur) \/ lex_lt cur start.

(* [comment removed for export] *)
(* [comment removed for export] *)

End LXO.
