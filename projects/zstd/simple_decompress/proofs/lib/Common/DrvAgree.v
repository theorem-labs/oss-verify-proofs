(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zbytes_length : forall l, length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_app : forall l1 l2, zbytes (l1 ++ l2) = zbytes l1 ++ zbytes l2.
Proof. intros. unfold zbytes. apply map_app. Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.
Lemma zbytes_map_unsigned : forall bs : list byte, zbytes (map bv_unsigned bs) = bs.
Proof. exact zbytes_map_unsigned'. Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
  - apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition magree (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma magree_refl : forall P m, magree P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma magree_trans : forall P m1 m2 m3, magree P m1 m2 -> magree P m2 m3 -> magree P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma magree_mono : forall (P P' : Z -> Prop) m m', magree P m m' -> (forall a, P' a -> P a) -> magree P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_magree : forall P m m' A bs,
  magree P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at segs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_magree : forall P m m' A n,
  magree P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_magree : forall P m m' A cs,
  magree P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_magree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_magree; eauto.
Qed.

Lemma stk_magree : forall P m m' lo hi,
  magree P m m' -> stk segs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk segs m' lo hi.
Proof.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HS a Ha) as [W [b R]]. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W'].
  split; [apply W'; exact W|]. exists b. unfold mrd in *. rewrite E. exact R.
Qed.

(* [comment removed for export] *)
Lemma magree_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> magree (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

(* [comment removed for export] *)
Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End WithSegs.
