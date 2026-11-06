(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI01.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09 YI04 YI08 YI0t YI00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b.
Variable segs : list Segment.
Lemma val_mem1_of_mbyte : forall mem a v, 0 <= v < 256 -> mbyte segs mem a = Some (Z_to_bv 8 v) -> val_mem segs mem a 1 v.
Proof.
intros mem a v Hv Hb k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma garr8_intro : forall mem base l,
(forall j, (j < length l)%nat -> mbyte segs mem (base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)) /\ 0 <= nth j l 0 < 256) -> garr8 segs mem base l.
Proof. intros mem base l H j Hj. destruct (H j Hj) as [Hb Hr]. split; [apply val_mem1_of_mbyte; assumption | exact Hr]. Qed.
Lemma garr8_copy : forall mem mem' src dst l, garr8 segs mem src l ->
(forall i, 0 <= i < Z.of_nat (length l) -> mbyte segs mem' (dst + i) = mbyte segs mem (src + i)) -> garr8 segs mem' dst l.
Proof.
intros mem mem' src dst l H Hc. apply garr8_intro. intros j Hj. split; [|exact (proj2 (H j Hj))].
rewrite (Hc (Z.of_nat j)) by lia. apply (garr8_mbyte segs mem src l j H Hj).
Qed.
Lemma garr8_sub : forall mem base l (a n : nat), garr8 segs mem base l -> garr8 segs mem (base + Z.of_nat a) (firstn n (skipn a l)).
Proof.
intros mem base l a n H j Hj. rewrite length_firstn, length_skipn in Hj.
rewrite nth_firstn. replace (Nat.ltb j n) with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn.
specialize (H (a + j)%nat ltac:(lia)). replace (base + Z.of_nat (a + j)) with (base + Z.of_nat a + Z.of_nat j) in H by lia. exact H.
Qed.
Lemma garr8_one : forall mem a v, val_mem segs mem a 1 v -> 0 <= v < 256 -> garr8 segs mem a [v].
Proof. intros mem a v Hv Hr [|j] Hj; cbn in Hj; [|lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; assumption. Qed.
Lemma garr8_cons : forall mem a v l, val_mem segs mem a 1 v -> 0 <= v < 256 -> garr8 segs mem (a + 1) l -> garr8 segs mem a (v :: l).
Proof.
intros mem a v l Hv Hr Hl. apply (proj2 (garr8_app segs mem a [v] l)). split; [apply garr8_one; assumption|].
cbn [length Z.of_nat]. change (Z.pos (Pos.of_succ_nat 0)) with 1. exact Hl.
Qed.
End b.
