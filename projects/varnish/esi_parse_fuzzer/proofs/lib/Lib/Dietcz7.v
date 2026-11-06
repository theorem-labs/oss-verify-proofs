(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import LiaTwx2 Tran6di DietDL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac dl_tf_lia :=
  DietDL3.dl_first_r ltac:(idtac;
    first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
          | zify_prune; Zify.zify; xlia zchecker
          | Zify.zify; xlia zchecker ]).
Ltac dl_tf_cfree_lia := first [ DietDL3.dl_solve0 | solve [ Tran6di.tf_clear_props; Zify.zify; xlia zchecker ] ].

Local Open Scope Z_scope.
Goal forall a : Z, a + 8 <= a + 16.
Proof. intros. dl_tf_cfree_lia. Qed.
