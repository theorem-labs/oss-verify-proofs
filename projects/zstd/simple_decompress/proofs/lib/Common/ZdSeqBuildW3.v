(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition skip_cover (tl : Z) : bool :=
  let size := 2^tl in let step := fse_tablestep size in
  forallb (fun q => existsb (fun j => (q + j * step) mod size =? 0) (zseq (Z.to_nat size) 0)) (zseq (Z.to_nat size) 0).

Lemma skip_cover_ok : forall tl, 5 <= tl <= 9 -> skip_cover tl = true.
Proof.
  intros tl H. assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9) by lia.
  destruct C as [->|[->|[->|[->| ->]]]]; vm_compute; reflexivity.
Qed.

Lemma skip_low_reach : forall size step high, 0 < size -> 0 <= high ->
  forall (j : nat) (fuel : nat) q, (j < fuel)%nat -> 0 <= q < size -> (q + Z.of_nat j * step) mod size = 0 ->
  skip_low fuel size step high q <= high.
Proof.
  intros size step high Hs Hh. induction j as [|j IH]; intros fuel q Hj Hq E.
  - destruct fuel as [|f]; [lia|]. cbn [skip_low].
    rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small in E by lia. subst q.
    destruct (Z.ltb_spec high 0); lia.
  - destruct fuel as [|f]; [lia|]. cbn [skip_low].
    destruct (Z.ltb_spec high q); [|lia].
    apply IH; [lia| apply Z.mod_pos_bound; lia|].
    rewrite Z.add_mod_idemp_l by lia. rewrite <- E. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

Lemma skip_low_term : forall tl high q, 5 <= tl <= 9 -> 0 <= high -> 0 <= q < 2^tl ->
  skip_low (Z.to_nat (2^tl)) (2^tl) (fse_tablestep (2^tl)) high q <= high.
Proof.
  intros tl high q Htl Hh Hq. pose proof (skip_cover_ok tl Htl) as C. unfold skip_cover in C. cbv zeta in C.
  rewrite forallb_forall in C. specialize (C q ltac:(apply zseq_In_iff; lia)).
  rewrite existsb_exists in C. destruct C as (j & Hj & E). apply zseq_In_iff in Hj. apply Z.eqb_eq in E.
  assert (0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  apply (skip_low_reach (2^tl) _ high ltac:(lia) Hh (Z.to_nat j)); [lia| exact Hq|].
  rewrite Z2Nat.id by lia. exact E.
Qed.
