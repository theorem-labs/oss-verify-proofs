(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
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

Lemma rwc_eq : forall segs m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros segs m A A' cs H <-. exact H. Qed.

Lemma rw_CB_length : forall segs m A n (bs : list byte), rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros segs m A n bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_of_rw_cells : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ B] _]. exact B. Qed.

Lemma bytes_at_prefix : forall segs m A (l1 l2 : list byte), bytes_at segs m A (l1 ++ l2) -> bytes_at segs m A l1.
Proof. intros segs m A l1 l2 H. apply bytes_at_app in H. tauto. Qed.

(* [comment removed for export] *)

Lemma firstn_app_le : forall {X} (n : nat) (l1 l2 : list X), (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof. intros X n l1 l2 H. rewrite firstn_app. replace (n - length l1)%nat with 0%nat by lia. cbn. apply app_nil_r. Qed.

(* [comment removed for export] *)
Lemma upd_app_mid : forall {X} (l1 l2 : list X) (y x : X) i,
  i = length l1 -> upd (l1 ++ y :: l2) i x = l1 ++ x :: l2.
Proof.
  intros X l1 l2 y x i ->. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma upd_after_prefix : forall (dlv jd : list byte) (x : byte) k,
  k = length dlv -> (k < length jd)%nat ->
  upd (dlv ++ skipn k jd) k x = dlv ++ x :: skipn (S k) jd.
Proof.
  intros dlv jd x k Hk Hlt.
  destruct (skipn k jd) as [|y r] eqn:E.
  { exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia. }
  rewrite (upd_app_mid dlv r y x k Hk). f_equal. f_equal.
  replace (S k) with (1 + k)%nat by lia. rewrite <- skipn_skipn, E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_split3 : forall segs m A n (l : list byte) (i j : nat),
  rw_cells segs m A [CB n l] -> (i + j <= n)%nat ->
  rw_cells segs m A [CB i (firstn i l)]
  /\ rw_cells segs m (A + Z.of_nat i) [CB j (firstn j (skipn i l))]
  /\ rw_cells segs m (A + Z.of_nat i + Z.of_nat j) [CB (n - i - j) (skipn (i + j) l)].
Proof.
  intros segs m A n l i j H Hij.
  pose proof (rw_CB_length _ _ _ _ _ H) as L.
  apply (rw_cells_split_CB segs m A [] n l [] [i; j; n - i - j]%nat) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  apply (proj1 (rw_cells_app segs m A [_] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H.
  apply (proj1 (rw_cells_app segs m _ [_] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3.
  rewrite skipn_skipn, (Nat.add_comm j i) in H3. rewrite firstn_all2 in H3 by (rewrite length_skipn; lia).
  rewrite !Nat.add_0_r in H2. rewrite !Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Lemma rw_cells_CB_join3 : forall segs m A (i j k : nat) (l1 l2 l3 : list byte),
  rw_cells segs m A [CB i l1] ->
  rw_cells segs m (A + Z.of_nat i) [CB j l2] ->
  rw_cells segs m (A + Z.of_nat i + Z.of_nat j) [CB k l3] ->
  rw_cells segs m A [CB (i + j + k) (l1 ++ l2 ++ l3)].
Proof.
  intros segs m A i j k l1 l2 l3 H1 H2 H3.
  pose proof (rw_CB_length _ _ _ _ _ H1) as L1. pose proof (rw_CB_length _ _ _ _ _ H2) as L2. pose proof (rw_CB_length _ _ _ _ _ H3) as L3.
  assert (J : rw_cells segs m A ([] ++ [CB i l1; CB j l2; CB k l3] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app segs m A [_] _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply (proj2 (rw_cells_app segs m _ [_] _)). split; [exact H2|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H3. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite app_nil_r, Nat.add_0_r in J.
  replace (i + (j + k))%nat with (i + j + k)%nat in J by lia. exact J.
Qed.

Lemma skipn_app_exact : forall {X} (l1 l2 : list X) (a b : nat),
  length l1 = a -> skipn (a + b) (l1 ++ skipn a l2) = skipn (a + b) l2.
Proof.
  intros X l1 l2 a b H. rewrite skipn_app, H. replace (a + b - a)%nat with b by lia.
  rewrite skipn_all2 by lia. cbn. rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma skipn_app_exact2 : forall {X} (l1 l2 : list X) (a b : nat),
  length l1 = a -> skipn (a + b) (l1 ++ l2) = skipn b l2.
Proof.
  intros X l1 l2 a b H. rewrite skipn_app, H. replace (a + b - a)%nat with b by lia.
  rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma mod_mod_mul : forall a k m, (0 < k -> 0 < m -> (a mod (k * m)) mod m = a mod m)%Z.
Proof.
  intros a k m Hk Hm.
  assert (E : (a mod (k * m) = a - (a / (k * m)) * (k * m))%Z) by (rewrite Zmod_eq_full by nia; reflexivity).
  rewrite E. replace (a - a / (k * m) * (k * m))%Z with (a + (- (a / (k * m) * k)) * m)%Z by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_mod256 : forall v : word, (bv_unsigned (sx32 v) mod 256 = bv_unsigned v mod 256)%Z.
Proof.
  intros v. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N N.sub Z.sub].
  set (x := bv_unsigned v).
  change (2^64)%Z with (72057594037927936 * 256)%Z. rewrite mod_mod_mul by lia.
  change (2 ^ 32 / 2)%Z with 2147483648%Z. change (2^32)%Z with (16777216 * 256)%Z.
  rewrite <- Zminus_mod_idemp_l. rewrite mod_mod_mul by lia.
  rewrite Zminus_mod_idemp_l.
  replace (x + 2147483648 - 2147483648)%Z with x by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_read4_C8 : forall segs m A cs k v a,
  rw_cells segs m A cs -> cell_at cs k = Some (C8 v) -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a 4 = Some (le4 v).
Proof.
  intros segs m A cs k v a H Hc ->.
  destruct H as [[Hwf Hb] _].
  destruct (cell_at_split cs k (C8 v) (C8 v) Hc) as (pre & post & E & Hsz & _).
  rewrite E in Hb, Hwf. rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 _].
  pose proof (cells_bytes_length pre W1) as L. rewrite Hsz in L.
  rewrite <- L. rewrite (bytes_at_ov_read segs m A _ (length (cells_bytes pre)) 4 Hb).
  2:{ rewrite !length_app, length_le8. lia. }
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn].
  match goal with |- Some (firstn 4 ?l) = _ => change (firstn 4 l) with (firstn 4 (le8 v ++ cells_bytes post)) end.
  rewrite firstn_app, length_le8. replace (4 - 8)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes_at_cell : forall segs m A cs k c,
  rw_cells segs m A cs -> cell_at cs k = Some c ->
  bytes_at segs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros segs m A cs k c H Hc.
  destruct H as [[Hwf Hb] _].
  destruct (cell_at_split cs k c c Hc) as (pre & post & E & Hsz & _).
  rewrite E in Hb, Hwf. rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 _].
  pose proof (cells_bytes_length pre W1) as L. rewrite Hsz in L.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite L in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
