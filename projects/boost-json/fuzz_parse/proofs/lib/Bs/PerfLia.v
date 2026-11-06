(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : ~ _ |- _ => clear H end.
Ltac keep_only_disj H :=
  repeat match goal with
  | H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H'
  | H' : ~ _ |- _ => tryif constr_eq H' H then fail else clear H'
  end.
(* [comment removed for export] *)
Ltac fastlia := zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
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
