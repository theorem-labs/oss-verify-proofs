(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLiaTuning.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : ~ _ |- _ => clear H end.
Ltac keep_only_disj H :=
  repeat match goal with
  | H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H'
  | H' : ~ _ |- _ => tryif constr_eq H' H then fail else clear H'
  end.

Ltac fastlia := zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac tlia :=
  first [ solve [ clear_disj; fastlia ]
        | match goal with
          | H : _ \/ _ |- _ => solve [ keep_only_disj H; fastlia ]
          | H : ~ _ |- _ => solve [ keep_only_disj H; fastlia ]
          end
        | lia ].

Ltac split_conjs := repeat match goal with H : _ /\ _ |- _ => let A := fresh H in destruct H as [A H] end.
Ltac tliac :=
  first [ solve [ split_conjs; clear_disj; fastlia ]
        | solve [ split_conjs;
                  match goal with
                  | H : _ \/ _ |- _ => solve [ keep_only_disj H; fastlia ]
                  | H : ~ _ |- _ => solve [ keep_only_disj H; fastlia ]
                  end ]
        | tlia ].
