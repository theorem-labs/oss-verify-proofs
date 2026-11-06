(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac wf_clear_bignat :=
  repeat match goal with
         | H : context [ (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ] |- _ => clear H
         end.

Ltac lia_nobignat :=
  first [ solve [ wf_clear_bignat; Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac wf_conj_vm :=
  lazymatch goal with
  | |- _ /\ _ => split; [ wf_conj_vm | wf_conj_vm ]
  | |- @eq ?T _ ?b => vm_cast_no_check (@eq_refl T b)
  end.
