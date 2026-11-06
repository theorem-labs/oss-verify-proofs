(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Exec Step Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Fixpoint u32s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.

Lemma u32s_length : forall ws, length (u32s ws) = (4 * length ws)%nat.
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. lia. Qed.
Lemma u64s_length : forall ws, length (u64s ws) = (8 * length ws)%nat.
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. lia. Qed.

Lemma u32s_app : forall a b, u32s (a ++ b) = u32s a ++ u32s b.
Proof. induction a; intros; cbn -[le4]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma u64s_app : forall a b, u64s (a ++ b) = u64s a ++ u64s b.
Proof. induction a; intros; cbn -[le8]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint upd {X} (l : list X) (i : nat) (x : X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: upd l' i' x
  end.

Lemma upd_length : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

Lemma upd_app_split : forall {X} (l : list X) i x, (i < length l)%nat ->
  exists pre y post, l = pre ++ y :: post /\ length pre = i /\ upd l i x = pre ++ x :: post.
Proof.
  induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
  destruct i as [|i].
  - exists [], z, l. repeat split; reflexivity.
  - destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
    cbn. rewrite Hupd. reflexivity.
Qed.

Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
  exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
  induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
  - inversion H; subst. exists [], l. split; reflexivity.
  - destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. split; [reflexivity| cbn; lia].
Qed.

Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma upd_bytes_mid : forall (a b c bs : list byte), length bs = length b ->
  upd_bytes (a ++ b ++ c) (length a) bs = a ++ bs ++ c.
Proof.
  intros a b c bs H. unfold upd_bytes.
  rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
  rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length a + length bs - length a)%nat with (length b) by lia.
  rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition u8arr (m : word -> option byte) (A : Z) (bs : list byte) : Prop :=
  bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat (length bs)).
Definition u32arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
  bytes_at segs m A (u32s ws) /\ wr_at segs m A (4 * Z.of_nat (length ws)).
Definition u64arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
  bytes_at segs m A (u64s ws) /\ wr_at segs m A (8 * Z.of_nat (length ws)).

(* [comment removed for export] *)
Definition u8ro (m : word -> option byte) (A : Z) (bs : list byte) : Prop := bytes_at segs m A bs.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_read : forall m A bs (i : Z) b a,
  u8arr m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs i b a [Hb _] Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

#[using="Type"] Lemma u8ro_read : forall m A bs (i : Z) b a,
  u8ro m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs i b a Hb Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

#[using="Type"] Lemma u8arr_store_ok : forall m A bs (i : Z) a,
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a 1 = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u8arr_write : forall m A bs (i : Z) (b : byte),
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z ->
  u8arr (write_to_mem m (wa (A + i)) [b]) A (upd bs (Z.to_nat i) b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs i b [Hb Hw] Hi. split.
  - eapply bytes_at_ext. { apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
    destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
    rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
    rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
    replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u32s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u32s ws = u32s pre ++ le4 w ++ u32s post /\ length (u32s pre) = (4 * i)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u32arr_read : forall m A ws (i : Z) w a,
  u32arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma u32arr_store_ok : forall m A ws (i : Z) a,
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
  store_ok segs m a 4 = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u32arr_write : forall m A ws (i : Z) (v : word),
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u32arr (write_to_mem m (wa (A + 4 * i)) (le4 v)) A (upd ws (Z.to_nat i) v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le4 v) Hb); [lia|].
      rewrite length_le4, u32s_length. lia. }
    rewrite Hupd, E, !u32s_app. cbn [u32s].
    replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
    apply upd_bytes_mid. rewrite !length_le4. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u64s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u64s ws = u64s pre ++ le8 w ++ u64s post /\ length (u64s pre) = (8 * i)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u64arr_read : forall m A ws (i : Z) w a,
  u64arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes segs m a 8 = Some (le8 w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma u64arr_store_ok : forall m A ws (i : Z) a,
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 8 * i) ->
  store_ok segs m a 8 = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u64arr_write : forall m A ws (i : Z) (v : word),
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u64arr (write_to_mem m (wa (A + 8 * i)) (le8 v)) A (upd ws (Z.to_nat i) v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
      rewrite length_le8, u64s_length. lia. }
    rewrite Hupd, E, !u64s_app. cbn [u64s].
    replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
    apply upd_bytes_mid. rewrite !length_le8. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_frame : forall m A bs a xs,
  u8arr m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8arr (write_to_mem m (wa a) xs) A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.

#[using="Type"] Lemma u32arr_frame : forall m A ws a xs,
  u32arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u32arr (write_to_mem m (wa a) xs) A ws.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u32s_length. lia.
Qed.

#[using="Type"] Lemma u64arr_frame : forall m A ws a xs,
  u64arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u64arr (write_to_mem m (wa a) xs) A ws.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u64s_length. lia.
Qed.

#[using="Type"] Lemma u8arr_bound : forall m A bs, u8arr m A bs -> (0 <= A /\ A + Z.of_nat (length bs) <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
#[using="Type"] Lemma u32arr_bound : forall m A ws, u32arr m A ws -> (0 <= A /\ A + 4 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.
#[using="Type"] Lemma u64arr_bound : forall m A ws, u64arr m A ws -> (0 <= A /\ A + 8 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. lia. Qed.

#[using="Type"] Lemma u8ro_frame : forall m A bs a xs,
  u8ro m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8ro (write_to_mem m (wa a) xs) A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_of_rw_cells : forall m A n bs,
  rw_cells segs m A [CB n bs] -> u8arr m A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
  split; assumption.
Qed.

#[using="Type"] Lemma rw_cells_of_u8arr : forall m A bs,
  u8arr m A bs -> rw_cells segs m A [CB (length bs) bs].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs [Hb Hw]. split.
  - split. { cbn. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma upd_firstn_skipn : forall {X} (l : list X) i x, (i < length l)%nat ->
  upd l i x = firstn i l ++ x :: skipn (S i) l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat ->
  nth_error (upd l i x) i = Some x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

#[using="Type"] Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j ->
  nth_error (upd l i x) j = nth_error l j.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [lia|].
  apply IH. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_transport : forall W m m' A bs,
  u8arr m A bs -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr m' A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A bs [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u32arr_transport : forall W m m' A ws,
  u32arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr m' A ws.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u64arr_transport : forall W m m' A ws,
  u64arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr m' A ws.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u8ro_transport : forall W m m' A bs,
  u8ro m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8ro m' A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma testbit_small_high : forall b i, (0 <= b < 256)%Z -> (8 <= i)%Z -> Z.testbit b i = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b i Hb Hi. destruct (Z.eq_dec b 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 8%Z; [apply Z.log2_lt_pow2; lia| lia].
Qed.

#[using="Type"] Lemma lor_shiftl8_bound : forall b r k, (0 <= b < 256)%Z -> (0 <= r < 2 ^ k)%Z -> (0 <= k)%Z ->
  (0 <= Z.lor b (Z.shiftl r 8) < 2 ^ (k + 8))%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b r k Hb Hr Hk.
  assert (D : Z.land (Z.shiftl r 8) b = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (testbit_small_high b i) by lia. apply andb_false_r. }
  assert (E : Z.lor b (Z.shiftl r 8) = (Z.shiftl r 8 + b)%Z).
  { rewrite Z.lor_comm. rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D. }
  rewrite E, Z.shiftl_mul_pow2, Z.pow_add_r by lia. change (2 ^ 8)%Z with 256%Z. nia.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_bound : forall bs, (0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length].
  - cbn. lia.
  - pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
    replace (8 * Z.of_nat (S (length bs)))%Z with (8 * Z.of_nat (length bs) + 8)%Z by lia.
    apply lor_shiftl8_bound; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (bytes_le_to_Z_bound bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.ones_spec_low, Z.shiftl_spec_low, orb_false_r, andb_true_r by lia. reflexivity.
    + rewrite Z.ones_spec_high, andb_false_r by lia. symmetry. apply testbit_small_high; lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    replace (Z.shiftr (bv_unsigned b) 8) with 0%Z; [rewrite Z.lor_0_l; exact IH|].
    symmetry. apply Z.shiftr_eq_0; [lia|].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [rewrite E; cbn; lia|].
    apply Z.log2_lt_pow2; lia.
Qed.

Fixpoint words_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7] :: words_of_bytes rest
  | _ => []
  end.

#[using="Type"] Lemma le8_le_bytes_to_word8 : forall b0 b1 b2 b3 b4 b5 b6 b7,
  le8 (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7]) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3; b4; b5; b6; b7]) as Hr. cbn [length] in Hr.
  change (8 * Z.of_nat 8)%Z with 64%Z in Hr.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; exact Hr).
  exact (Z_to_le_bytes_to_Z [b0; b1; b2; b3; b4; b5; b6; b7]).
Qed.

#[using="Type"] Lemma u64s_words_of_bytes : forall n bs, length bs = (8 * n)%nat -> u64s (words_of_bytes bs) = bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros bs Hl.
  - destruct bs; [reflexivity| cbn in Hl; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]]; cbn in Hl; try lia.
    cbn [words_of_bytes u64s flat_map map]. change (u64s (words_of_bytes rest)) with (u64s (words_of_bytes rest)).
    unfold u64s. cbn [flat_map]. fold (u64s (words_of_bytes rest)).
    rewrite le8_le_bytes_to_word8. cbn. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
    apply IH. lia.
Qed.

#[using="Type"] Lemma words_of_bytes_length : forall n bs, length bs = (8 * n)%nat -> length (words_of_bytes bs) = n.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros bs Hl.
  - destruct bs; [reflexivity| cbn in Hl; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]]; cbn in Hl; try lia.
    cbn. f_equal. apply IH. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_of_rw_cells : forall m A n bs,
  rw_cells segs m A [CB (8 * n) bs] ->
  exists ws, length ws = n /\ u64arr m A ws.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n bs H. pose proof (u8arr_of_rw_cells m A _ bs H) as [Hb Hw].
  destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hn _].
  exists (words_of_bytes bs). split; [apply words_of_bytes_length; lia|].
  split.
  - rewrite (u64s_words_of_bytes n) by lia. exact Hb.
  - rewrite (words_of_bytes_length n) by lia. replace (8 * Z.of_nat n)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr m A ws -> rw_cells segs m A [CB (8 * length ws) (u64s ws)].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws [Hb Hw]. split.
  - split. { cbn. rewrite u64s_length. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact Hw.
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma wr_at_app_split : forall m A n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hn & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i)%Z with (A + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hn & X1) & (Hb & Hm & X2)). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply X1. lia.
    + replace (A + i)%Z with (A + n1 + (i - n1))%Z by lia. apply X2. lia.
Qed.

#[using="Type"] Lemma u8arr_app : forall m A l1 l2,
  u8arr m A (l1 ++ l2) <-> u8arr m A l1 /\ u8arr m (A + Z.of_nat (length l1)) l2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A l1 l2. unfold u8arr. rewrite app_length, Nat2Z.inj_add.
  rewrite wr_at_app_split by lia. rewrite bytes_at_app. tauto.
Qed.

#[using="Type"] Lemma u64arr_app : forall m A ws1 ws2,
  u64arr m A (ws1 ++ ws2) <-> u64arr m A ws1 /\ u64arr m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws1 ws2. unfold u64arr. rewrite u64s_app, app_length, Nat2Z.inj_add, Z.mul_add_distr_l.
  rewrite wr_at_app_split by lia. rewrite bytes_at_app. rewrite u64s_length.
  replace (A + Z.of_nat (8 * length ws1))%Z with (A + 8 * Z.of_nat (length ws1))%Z by lia. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_write_all : forall m A old bs,
  u8arr m A old -> length old = length bs ->
  u8arr (write_to_mem m (wa A) bs) A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A old bs [B W] Hl. pose proof (bytes_at_bound segs _ _ _ B) as Hb. rewrite Hl in Hb.
  split.
  - apply bytes_at_write_same; lia.
  - rewrite <- Hl. apply wr_at_write. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma words_of_bytes_zero : forall k,
  words_of_bytes (repeat (Z_to_bv 8 0) (8 * k)) = repeat (Z_to_bv 64 0) k.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction k as [|k IH]; [reflexivity|].
  replace (8 * S k)%nat with (S (S (S (S (S (S (S (S (8 * k)))))))))%nat by lia.
  cbn [repeat words_of_bytes]. rewrite IH. f_equal.
Qed.

#[using="Type"] Lemma u64arr_of_u8arr : forall m A n bs,
  u8arr m A bs -> length bs = (8 * n)%nat -> u64arr m A (words_of_bytes bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n bs [B W] Hl. split.
  - rewrite (u64s_words_of_bytes n) by exact Hl. exact B.
  - rewrite (words_of_bytes_length n) by exact Hl. replace (8 * Z.of_nat n)%Z with (Z.of_nat (length bs)) by lia. exact W.
Qed.

#[using="Type"] Lemma u8arr_of_u64arr : forall m A ws, u64arr m A ws -> u8arr m A (u64s ws).
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws [B W]. split; [exact B|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact W. Qed.

End WithSegs.
