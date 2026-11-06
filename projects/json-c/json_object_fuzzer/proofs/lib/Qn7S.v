(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl.
Import ListNotations. Import AX2. Import AX2S. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section Sub.
Variable segs : list Segment.

Lemma bytes_at_sub : forall (m : word -> option byte) A bs k n,
QZDE.bytes_at segs m A bs -> (k + n <= length bs)%nat ->
QZDE.bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros m A bs k n (H0 & H1 & H) Hk. split; [lia|]. rewrite length_firstn, length_skipn. split; [lia|].
intros i Hi.
replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
rewrite nth_error_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
Qed.

Lemma wr_at_sub : forall (m : word -> option byte) A n k l,
QZDE.wr_at segs m A n -> 0 <= k -> 0 <= l -> k + l <= n -> QZDE.wr_at segs m (A + k) l.
Proof.
intros m A n k l (H0 & H1 & H) Hk Hl Hkl. split; [lia|]. split; [lia|]. intros i Hi.
replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

Lemma firstn_repeat_le : forall {X} (x : X) n N, (n <= N)%nat -> firstn n (repeat x N) = repeat x n.
Proof. intros X x n. induction n as [|n IH]; intros [|N] H; cbn [firstn repeat]; try reflexivity; try lia. f_equal. apply IH. lia. Qed.
Lemma firstn_skipn_repeat : forall {X} (x : X) N k n, (k + n <= N)%nat -> firstn n (skipn k (repeat x N)) = repeat x n.
Proof.
intros X x N k. revert N. induction k as [|k IH]; intros N n H; cbn [skipn].
- apply firstn_repeat_le. lia.
- destruct N as [|N]; [lia|]. cbn [repeat]. apply IH. lia.
Qed.

Lemma zero_cells : forall (m : word -> option byte) A N k (cs : list QbVh.cell),
QZDE.bytes_at segs m A (repeat (Z_to_bv 8 0) N) -> QZDE.wr_at segs m A (Z.of_nat N) ->
QbVh.cells_wf cs -> QbVh.cells_bytes cs = repeat (Z_to_bv 8 0) (QbVh.cells_size cs) -> (k + QbVh.cells_size cs <= N)%nat ->
QlEo_c1.rw_cells segs m (A + Z.of_nat k) cs.
Proof.
intros m A N k cs BA WR WF EQ Hk. split; [split; [exact WF|]|].
- rewrite EQ, <- (firstn_skipn_repeat (Z_to_bv 8 0) N k (QbVh.cells_size cs) Hk). apply bytes_at_sub; [exact BA | rewrite repeat_length; exact Hk].
- apply (wr_at_sub m A (Z.of_nat N)); [exact WR | lia | lia | lia].
Qed.

Definition lit_byte (w : nat) (z : Z) (i : nat) : Z := (z / 2 ^ (8 * Z.of_nat i)) mod 256.
Fixpoint sc_lit_byte (cs : list scell) (o : nat) : option Z :=
match cs with
| [] => None
| SCw w (ELit z) :: r => if (o <? w)%nat then (if (0 <=? z) && (z <? 2^64) then Some (lit_byte w z o) else None) else sc_lit_byte r (o - w)
| SCw w _ :: r => if (o <? w)%nat then None else sc_lit_byte r (o - w)
| SCz n :: r => if (o <? n)%nat then Some 0 else sc_lit_byte r (o - n)
| SCi n :: r => if (o <? n)%nat then None else sc_lit_byte r (o - n)
end.

Lemma nth_error_le_bytes : forall w u i, (i < w)%nat -> 0 <= u ->
nth_error (Z_to_le_bytes w u) i = Some (Z_to_bv 8 ((u / 2 ^ (8 * Z.of_nat i)) mod 256)).
Proof.
induction w as [|w IH]; intros u i Hi Hu; [lia|]. cbn [Z_to_le_bytes]. destruct i as [|i].
- cbn [nth_error]. change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. apply f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
- cbn [nth_error]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite IH by (try lia; apply Z.div_pos; lia). f_equal. f_equal.
replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
rewrite Z.div_div by lia. reflexivity.
Qed.

Lemma sc_lit_byte_sound : forall E cs A o v, sc_lit_byte cs o = Some v ->
nth_error (sc_bytes segs E A cs) o = Some (Z_to_bv 8 v).
Proof.
intros E cs. induction cs as [|c r IH]; intros A o v H; [discriminate|].
destruct c as [w e|n|n]; cbn [sc_lit_byte] in H; cbn [sc_bytes].
- destruct (Nat.ltb_spec o w) as [L|G].
+ destruct e as [z| | | | | | |]; try discriminate.
destruct ((0 <=? z) && (z <? 2 ^ 64)) eqn:R; [|discriminate]. injection H as <-.
apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
rewrite nth_error_app1 by (rewrite length_N_to_le_bytes; exact L).
unfold word_to_le_bytes. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
apply nth_error_le_bytes; [exact L | exact R1].
+ rewrite nth_error_app2 by (rewrite length_N_to_le_bytes; lia). rewrite length_N_to_le_bytes.
destruct e; apply IH; exact H.
- destruct (Nat.ltb_spec o n) as [L|G].
+ injection H as <-. rewrite nth_error_app1 by (rewrite repeat_length; exact L). apply nth_error_repeat. exact L.
+ rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length. apply IH. exact H.
- destruct (Nat.ltb_spec o n) as [L|G]; [discriminate|].
rewrite nth_error_app2 by (rewrite rom_bytes_length; lia). rewrite rom_bytes_length. apply IH. exact H.
Qed.

Lemma bytes_at_nth : forall (m : word -> option byte) A bs o b,
QZDE.bytes_at segs m A bs -> nth_error bs o = Some b -> QZDE.bytes_at segs m (A + Z.of_nat o) [b].
Proof.
intros m A bs o b BA Hn. assert (Ho : (o < length bs)%nat) by (apply nth_error_Some; congruence).
pose proof (bytes_at_sub m A bs o 1 BA ltac:(lia)) as S.
replace (firstn 1 (skipn o bs)) with [b] in S; [exact S|].
rewrite <- (firstn_skipn o bs) in Hn. rewrite nth_error_app2 in Hn by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hn by lia. destruct (skipn o bs) as [|x t]; [discriminate|]. cbn in Hn. injection Hn as ->. reflexivity.
Qed.
End Sub.
