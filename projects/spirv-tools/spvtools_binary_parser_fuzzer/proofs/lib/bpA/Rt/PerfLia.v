(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HLiaTuning.
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
