(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Import ListNotations.
Open Scope bv_scope.

Fixpoint u32s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.

Lemma u32s_length : forall ws, length (u32s ws) = (4 * length ws)%nat.
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62301877645.3000006S4IHws".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma u64s_length : forall ws, length (u64s ws) = (8 * length ws)%nat.
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62301877645.3000006S4IHws".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>43388999569.1345046962113.4 54927240279.7 00000900=00AS2Hi4HlenS2HiS2Hi".
induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
  destruct i as [|i].
  - exists [], z, l. repeat split; reflexivity.
  - destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
    cbn. rewrite Hupd. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
  exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
  induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
  - inversion H; subst. exists [], l. split; reflexivity.
  - destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. Local Ltac2 Set LiaHints.tbl := fun () => "0010=43389000731.9000006S4Hlen".
split; [reflexivity| cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma upd_bytes_mid : forall (a b c bs : list byte), length bs = length b ->
  upd_bytes (a ++ b ++ c) (length a) bs = a ++ bs ++ c.
Proof.
  intros a b c bs H. unfold upd_bytes.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=54293222055.554432257189.562800998352.568637344924.500000300600900<S1HS1HS1HS1H".
rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
  rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length a + length bs - length a)%nat with (length b) by lia.
  rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
Proof.
  intros m A bs i b a [Hb _] Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>10357883337.1014290935642.1038177583318.1400000600900AS2Hi1HS1HS1H4Hlen".
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u8ro_read : forall m A bs (i : Z) b a,
  u8ro m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros m A bs i b a Hb Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>10357883337.1014290935642.1038177583318.1400000600900AS2Hi1HS1HS1H4Hlen".
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u8arr_store_ok : forall m A bs (i : Z) a,
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a 1 = true.
Proof. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u8arr_write : forall m A bs (i : Z) (b : byte),
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z ->
  u8arr (write_to_mem m (wa (A + i)) [b]) A (upd bs (Z.to_nat i) b).
Proof.
  intros m A bs i b [Hb Hw] Hi. split.
  - eapply bytes_at_ext. { Local Ltac2 Set LiaHints.tbl := fun () => "0060>10351595562.9 14288834233.9 38177586012.1549309357387.1553585280128.9 55172881559.1500000400800>00D00H00NS2HiS2HiS4HlenS4HlenS2HiS4Hlen".
apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
    destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
    rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
    rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
    replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma u32s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u32s ws = u32s pre ++ le4 w ++ u32s post /\ length (u32s pre) = (4 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u32arr_read : forall m A ws (i : Z) w a,
  u32arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>12883073381.1525273904528.1546081068896.1561555382922.1500000=00G00Q00[S2Hi4Hlen3HluS4Hlen3HluS4Hlen3HluS4Hlen3Hlu".
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u32arr_store_ok : forall m A ws (i : Z) a,
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
  store_ok segs m a 4 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u32arr_write : forall m A ws (i : Z) (v : word),
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u32arr (write_to_mem m (wa (A + 4 * i)) (le4 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>1873198208.9  29066737278.1542878410424.1563378567340.1500000400=00F00LS2HiS2Hi4HlenS2Hi4HlenS4Hlen".
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le4 v) Hb); [lia|].
      rewrite length_le4, u32s_length. lia. }
    rewrite Hupd, E, !u32s_app. cbn [u32s].
    replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
    apply upd_bytes_mid. rewrite !length_le4. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma u64s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u64s ws = u64s pre ++ le8 w ++ u64s post /\ length (u64s pre) = (8 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u64arr_read : forall m A ws (i : Z) w a,
  u64arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>25273904528.1546081068896.1558870951973.1561555382922.1500000:00D00Q00[S4Hlen3HluS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u64arr_store_ok : forall m A ws (i : Z) a,
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 8 * i) ->
  store_ok segs m a 8 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u64arr_write : forall m A ws (i : Z) (v : word),
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u64arr (write_to_mem m (wa (A + 8 * i)) (le8 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>12332677112.151873198208.9  21911288428.1529066737278.1500000900=00C00LS2Hi4HlenS2HiS4HlenS2Hi4Hlen".
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
      rewrite length_le8, u64s_length. lia. }
    rewrite Hupd, E, !u64s_app. cbn [u64s].
    replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
    apply upd_bytes_mid. rewrite !length_le8. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_frame : forall m A bs a xs,
  u8arr m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8arr (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.

#[using="Type"] Lemma u32arr_frame : forall m A ws a xs,
  u32arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u32arr (write_to_mem m (wa a) xs) A ws.
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u32s_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010>42331852288.11000004S2H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u64arr_frame : forall m A ws a xs,
  u64arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u64arr (write_to_mem m (wa a) xs) A ws.
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u64s_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010>42331852288.11000004S2H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u8arr_bound : forall m A bs, u8arr m A bs -> (0 <= A /\ A + Z.of_nat (length bs) <= 2^64)%Z.
Proof. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
#[using="Type"] Lemma u32arr_bound : forall m A ws, u32arr m A ws -> (0 <= A /\ A + 4 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010<3225310955.6000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u64arr_bound : forall m A ws, u64arr m A ws -> (0 <= A /\ A + 8 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010<3225310955.6000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u8ro_frame : forall m A bs a xs,
  u8ro m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8ro (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_of_rw_cells : forall m A n bs,
  rw_cells segs m A [CB n bs] -> u8arr m A bs.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
  split; assumption.
Qed.

#[using="Type"] Lemma rw_cells_of_u8arr : forall m A bs,
  u8arr m A bs -> rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs [Hb Hw]. split.
  - split. { cbn. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma upd_firstn_skipn : forall {X} (l : list X) i x, (i < length l)%nat ->
  upd l i x = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros X l. Local Ltac2 Set LiaHints.tbl := fun () => "0050=31588438987.431588438987.543171128641.848179086344.754927240279.800000400800900:00>S2HiS2HiFFS2Hi".
induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat ->
  nth_error (upd l i x) i = Some x.
Proof.
  intros X l. Local Ltac2 Set LiaHints.tbl := fun () => "0050=1301109116.7 20317035747.420317035747.554927240279.865345226923.800000100500900=00>FS2HiS2HiS2HiF".
induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j ->
  nth_error (upd l i x) j = nth_error l j.
Proof.
  intros X l. Local Ltac2 Set LiaHints.tbl := fun () => "0020=1283617519.9 38759345692.700000500:S3HijS3Hij".
induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [lia|].
  apply IH. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma u8arr_transport : forall W m m' A bs,
  u8arr m A bs -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u32arr_transport : forall W m m' A ws,
  u32arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u64arr_transport : forall W m m' A ws,
  u64arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u8ro_transport : forall W m m' A bs,
  u8ro m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8ro m' A bs.
Proof. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.

End WithSegs.
