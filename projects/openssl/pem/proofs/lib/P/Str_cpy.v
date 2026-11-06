(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_split_at : forall segs m A n bs k, (k <= n)%nat ->
  rw_cells segs m A [CB n bs] ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k)%nat (skipn k bs)].
Proof.
  intros segs m A n bs k Hk H.
  pose proof (rw_cells_CB_length segs m A n bs H) as L.
  pose proof (rw_cells_split_CB segs m A [] n bs [] [k; (n - k)%nat] H ltac:(cbn; lia)) as H2.
  cbn [mk_CB_cells app] in H2.
  apply (proj1 (rw_cells_app segs m A [_] _)) in H2. destruct H2 as [Ha Hb].
  cbn [cells_size csize Nat.add] in Hb. rewrite Nat.add_0_r in Hb.
  split; [exact Ha|].
  replace (skipn k bs) with (firstn (n - k) (skipn k bs)); [exact Hb|].
  apply firstn_all2. rewrite skipn_length. lia.
Qed.

Lemma rw_cells_CB_join : forall segs m A k1 bs1 k2 bs2,
  rw_cells segs m A [CB k1 bs1] -> rw_cells segs m (A + Z.of_nat k1) [CB k2 bs2] ->
  rw_cells segs m A [CB (k1 + k2)%nat (bs1 ++ bs2)].
Proof.
  intros segs m A k1 bs1 k2 bs2 H1 H2.
  pose proof (rw_cells_CB_length segs m A k1 bs1 H1) as L1.
  pose proof (rw_cells_CB_length segs m _ k2 bs2 H2) as L2.
  assert (H : rw_cells segs m A ([CB k1 bs1] ++ [CB k2 bs2])).
  { apply (proj2 (rw_cells_app segs m A [_] [_])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge segs m A [] ([CB k1 bs1] ++ [CB k2 bs2]) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size cells_bytes csize cbytes] in M.
  rewrite app_nil_r, Nat.add_0_r in M. apply M. exact H.
Qed.

(* [comment removed for export] *)
Lemma le8_ld : forall w : list byte, length w = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word w)) = w.
Proof.
  intros w Hl. unfold le8, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (le_val_range (map bv_unsigned w) (bytes_ok_map w)) as Hr. rewrite length_map, Hl in Hr.
  rewrite bytes_le_to_Z_le_val in *.
  change (256 ^ Z.of_nat 8) with (bv_modulus 64) in Hr.
  rewrite !(bv_wrap_small 64 (le_val _)) by lia.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma firstn_add_split : forall {X} (l : list X) p k, firstn (p + k) l = firstn p l ++ firstn k (skipn p l).
Proof.
  intros X l p k. revert l. induction p as [|p IH]; intros [|x l]; cbn; try reflexivity.
  - now destruct k.
  - rewrite IH. reflexivity.
Qed.

Lemma upd_bytes_prefix : forall (bs buf xs : list byte) (p : nat),
  firstn p bs = firstn p buf -> firstn (length xs) (skipn p buf) = xs -> (p + length xs <= length bs)%nat ->
  (p + length xs <= length buf)%nat ->
  firstn (p + length xs) (upd_bytes bs p xs) = firstn (p + length xs) buf.
Proof.
  intros bs buf xs p Hp Hx Hl Hlb. unfold upd_bytes.
  assert (Lp : length (firstn p bs) = p) by (rewrite firstn_length; lia).
  rewrite firstn_app, Lp, firstn_all2 by lia. replace (p + length xs - p)%nat with (length xs) by lia.
  rewrite firstn_app_exact.
  rewrite firstn_add_split, Hp, Hx. reflexivity.
Qed.
