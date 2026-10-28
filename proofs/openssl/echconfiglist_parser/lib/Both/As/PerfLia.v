(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : ~ _ |- _ => clear H end.
Ltac keep_only_disj H :=
  repeat match goal with
  | H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H'
  | H' : ~ _ |- _ => tryif constr_eq H' H then fail else clear H'
  end.
(* [comment removed for export] *)
Ltac fastlia := dle_wrap ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker).
Ltac tlia :=
  first [ solve [ clear_disj; fastlia ]
        | match goal with
          | H : _ \/ _ |- _ => solve [ keep_only_disj H; fastlia ]
          | H : ~ _ |- _ => solve [ keep_only_disj H; fastlia ]
          end
        | lia ].

(* [comment removed for export] *)
Ltac split_conjs := repeat match goal with H : _ /\ _ |- _ => let A := fresh H in destruct H as [A H] end.
Ltac tliac :=
  first [ solve [ split_conjs; clear_disj; fastlia ]
        | solve [ split_conjs;
                  match goal with
                  | H : _ \/ _ |- _ => solve [ keep_only_disj H; fastlia ]
                  | H : ~ _ |- _ => solve [ keep_only_disj H; fastlia ]
                  end ]
        | tlia ].
