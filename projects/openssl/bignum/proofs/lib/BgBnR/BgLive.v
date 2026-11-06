(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgInv BgLib BgArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma bn_live_run : forall {ptr A} rs (k : BM (M := btree ptr) (ptr := ptr) A) (bs : bstate ptr),
  bn_live (tree_ops ptr) rs k bs = if live_refs (st_ctx bs) rs then k bs else TUnr.
Proof.
  intros ptr A rs k bs. unfold bn_live, bbind, bgetctx, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
  destruct (live_refs (st_ctx bs) rs); reflexivity.
Qed.

Lemma live_refs_true_iff : forall {ptr} (c : bg_ctx ptr) rs,
  live_refs c rs = true <-> Forall (fun r => (r < NFIX + gx_used c)%nat) rs.
Proof.
  intros ptr c rs. unfold live_refs. rewrite forallb_forall, Forall_forall.
  split; intros H r Hr; [apply Nat.ltb_lt | apply Nat.ltb_lt]; exact (H r Hr).
Qed.

