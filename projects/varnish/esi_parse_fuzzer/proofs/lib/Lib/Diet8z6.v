(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import DietDL3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac dl_first := DietDL3.dl_solve.
(* [comment removed for export] *)
Ltac dlia_nc :=
  first [ dl_first
        | tryif PropExec.noncert_goal_has_var then (Zify.zify; xlia zchecker)
          else first [ solve [PropExec.noncert_clear_all; Zify.zify; xlia zchecker]
                     | Zify.zify; xlia zchecker ] ].

Local Open Scope Z_scope.
Goal forall a b c : Z, a + 8 <= b -> b <= c -> a + 4 <= c /\ a <= a + 4.
Proof. intros. dlia_nc. Qed.
Goal forall a b : Z, a * b = b * a.
Proof. intros. Fail dl_first. dlia_nc. Qed.
