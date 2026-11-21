(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition bhole (m : word -> option byte) (A : Z) (bs : list byte) (k len : nat) : Prop :=
  (k + len <= length bs)%nat /\
  bytes_at segs m A (firstn k bs) /\
  bytes_at segs m (A + Z.of_nat (k + len)) (skipn (k + len) bs) /\
  wr_at segs m A (Z.of_nat (length bs)).

Lemma wr_at_sub' : forall m a n a' n', wr_at segs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) L1 L0 L2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma bhole_open : forall m A bs k len,
  bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) -> (k + len <= length bs)%nat ->
  bhole m A bs k len /\ bytes_at segs m (A + Z.of_nat k) (firstn len (skipn k bs)) /\ wr_at segs m (A + Z.of_nat k) (Z.of_nat len).
Proof.
  intros m A bs k len HB HW HK.
  assert (E : bs = firstn k bs ++ firstn len (skipn k bs) ++ skipn (k + len) bs).
  { rewrite <- (firstn_skipn k bs) at 1. f_equal. rewrite <- (firstn_skipn len (skipn k bs)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia. }
  pose proof HB as HB'. rewrite E in HB'.
  apply bytes_at_app in HB'. destruct HB' as [H1 H2]. apply bytes_at_app in H2. destruct H2 as [H2 H3].
  rewrite length_firstn in H2, H3. replace (Nat.min k (length bs)) with k in H2, H3 by lia.
  rewrite length_firstn, length_skipn in H3. replace (Nat.min len (length bs - k)) with len in H3 by lia.
  split; [|split].
  - split; [exact HK|]. split; [exact H1|]. split; [| exact HW].
    replace (A + Z.of_nat (k + len)) with (A + Z.of_nat k + Z.of_nat len) by lia. exact H3.
  - exact H2.
  - eapply wr_at_sub'; [exact HW| lia| lia| lia].
Qed.

Lemma bhole_close : forall m A bs k len mid,
  bhole m A bs k len -> bytes_at segs m (A + Z.of_nat k) mid -> length mid = len ->
  bytes_at segs m A (firstn k bs ++ mid ++ skipn (k + len) bs) /\ wr_at segs m A (Z.of_nat (length bs)).
Proof.
  intros m A bs k len mid (HK & H1 & H3 & HW) H2 L. split; [| exact HW].
  apply bytes_at_app. split; [exact H1|]. rewrite length_firstn. replace (Nat.min k (length bs)) with k by lia.
  apply bytes_at_app. split; [exact H2|]. rewrite L.
  replace (A + Z.of_nat k + Z.of_nat len) with (A + Z.of_nat (k + len)) by lia. exact H3.
Qed.

Lemma bhole_frame : forall m A bs k len a xs,
  bhole m A bs k len -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A
   \/ (A + Z.of_nat k <= a /\ a + Z.of_nat (length xs) <= A + Z.of_nat k + Z.of_nat len)) ->
  bhole (write_to_mem m (wa a) xs) A bs k len.
Proof.
  intros m A bs k len a xs (HK & H1 & H3 & HW) Ha Hl D.
  split; [exact HK|]. split; [|split].
  - apply bytes_at_write_other; [exact H1| exact Ha| exact Hl|]. rewrite length_firstn. lia.
  - apply bytes_at_write_other; [exact H3| exact Ha| exact Hl|]. rewrite length_skipn. lia.
  - apply wr_at_write. exact HW.
Qed.

Lemma djf_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' D L1 L2; [exact I|].
  destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
Qed.

Lemma bhole_transport : forall W m m' A bs k len,
  bhole m A bs k len -> munch W m m' -> wmono segs m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
  bhole m' A bs k len.
Proof.
  intros W m m' A bs k len (HK & H1 & H3 & HW) MU WM D.
  split; [exact HK|]. split; [|split].
  - eapply bytes_at_transport; [exact H1| exact MU|]. eapply djf_sub; [exact D| lia|]. rewrite length_firstn. lia.
  - eapply bytes_at_transport; [exact H3| exact MU|]. eapply djf_sub; [exact D| lia|]. rewrite length_skipn. lia.
  - eapply wr_at_transport; eauto.
Qed.


Lemma nth_error_ext' : forall {X} (l l' : list X), length l = length l' ->
  (forall k, (k < length l)%nat -> nth_error l k = nth_error l' k) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] HL HE; cbn in HL; try discriminate; [reflexivity|].
  pose proof (HE 0%nat ltac:(cbn; lia)) as E0. cbn in E0. inversion E0; subst y. f_equal.
  apply IH; [lia|]. intros k Hk. exact (HE (S k) ltac:(cbn; lia)).
Qed.

Lemma fws_fupd : forall f n i x, (i < n)%nat -> fws (fupd f (Z.of_nat i) x) n = upd (fws f n) i (Z_to_bv 64 x).
Proof.
  intros f n i x Hi. apply nth_error_ext'; [rewrite upd_length, !fws_length; reflexivity|].
  intros k Hk. rewrite fws_length in Hk. rewrite fws_nth by exact Hk.
  destruct (Nat.eq_dec k i) as [->|NE].
  - rewrite nth_error_upd_same by (rewrite fws_length; exact Hi). rewrite fupd_same. reflexivity.
  - rewrite nth_error_upd_other by (intros E; apply NE; symmetry; exact E). rewrite fws_nth by exact Hk.
    rewrite fupd_other by lia. reflexivity.
Qed.

Lemma u16s_around : forall ws i w, nth_error ws i = Some w ->
  firstn 2 (skipn (2 * i) (u16s ws)) = le2 w /\
  forall v, u16s (upd ws i v) = firstn (2 * i) (u16s ws) ++ le2 v ++ skipn (2 * i + 2) (u16s ws).
Proof.
  intros ws i w H. destruct (u16s_split _ _ _ H) as (pre & post & E & Hlen & Eu & Hlu).
  split.
  - rewrite Eu. rewrite skipn_app, (skipn_all2 (u16s pre)) by lia. rewrite Hlu, Nat.sub_diag, skipn_O, app_nil_l.
    rewrite firstn_app, (firstn_all2 (le2 w)) by (rewrite length_le2; lia). rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
  - intros v. rewrite upd_firstn_skipn by (eapply nth_error_lt; eauto).
    rewrite E. rewrite firstn_app, (firstn_all2 pre) by lia. rewrite Hlen, Nat.sub_diag, firstn_O, app_nil_r.
    replace (S i) with (length pre + 1)%nat by lia. rewrite skipn_app, (skipn_all2 pre) by lia.
    replace (length pre + 1 - length pre)%nat with 1%nat by lia. cbn [skipn app].
    rewrite u16s_app. cbn [u16s]. rewrite <- E, Eu.
    rewrite firstn_app, (firstn_all2 (u16s pre)) by lia. rewrite Hlu, Nat.sub_diag, firstn_O, app_nil_r.
    f_equal. f_equal. rewrite skipn_app, (skipn_all2 (u16s pre)) by lia.
    replace (2 * i + 2 - length (u16s pre))%nat with 2%nat by lia.
    rewrite skipn_app, (skipn_all2 (le2 w)) by (rewrite length_le2; lia). rewrite length_le2. cbn [Nat.sub skipn app]. reflexivity.
Qed.
Lemma u32s_around : forall ws i w, nth_error ws i = Some w ->
  firstn 4 (skipn (4 * i) (u32s ws)) = le4 w /\
  forall v, u32s (upd ws i v) = firstn (4 * i) (u32s ws) ++ le4 v ++ skipn (4 * i + 4) (u32s ws).
Proof.
  intros ws i w H. destruct (u32s_split _ _ _ H) as (pre & post & E & Hlen & Eu & Hlu).
  split.
  - rewrite Eu. rewrite skipn_app, (skipn_all2 (u32s pre)) by lia. rewrite Hlu, Nat.sub_diag, skipn_O, app_nil_l.
    rewrite firstn_app, (firstn_all2 (le4 w)) by (rewrite length_le4; lia). rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
  - intros v. rewrite upd_firstn_skipn by (eapply nth_error_lt; eauto).
    rewrite E. rewrite firstn_app, (firstn_all2 pre) by lia. rewrite Hlen, Nat.sub_diag, firstn_O, app_nil_r.
    replace (S i) with (length pre + 1)%nat by lia. rewrite skipn_app, (skipn_all2 pre) by lia.
    replace (length pre + 1 - length pre)%nat with 1%nat by lia. cbn [skipn app].
    rewrite u32s_app. cbn [u32s]. rewrite <- E, Eu.
    rewrite firstn_app, (firstn_all2 (u32s pre)) by lia. rewrite Hlu, Nat.sub_diag, firstn_O, app_nil_r.
    f_equal. f_equal. rewrite skipn_app, (skipn_all2 (u32s pre)) by lia.
    replace (4 * i + 4 - length (u32s pre))%nat with 4%nat by lia.
    rewrite skipn_app, (skipn_all2 (le4 w)) by (rewrite length_le4; lia). rewrite length_le4. cbn [Nat.sub skipn app]. reflexivity.
Qed.

Definition f16hole (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) (i : Z) : Prop :=
  bhole m A (u16s (fws f n)) (2 * Z.to_nat i) 2.
Definition f32hole (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) (i : Z) : Prop :=
  bhole m A (u32s (fws f n)) (4 * Z.to_nat i) 4.

Lemma f16_open : forall m A n f i,
  f16arr segs m A n f -> 0 <= i < Z.of_nat n ->
  f16hole m A n f i /\ rw_cells segs m (A + 2 * i) [C2 (Z_to_bv 64 (f i))].
Proof.
  intros m A n f i [HB HW] Hi. rewrite fws_length in HW.
  assert (NE : nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i))).
  { rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity. }
  destruct (u16s_around _ _ _ NE) as [EA _].
  destruct (bhole_open m A (u16s (fws f n)) (2 * Z.to_nat i) 2 HB) as (H1 & H2 & H3).
  { rewrite u16s_length, fws_length. replace (Z.of_nat (2 * n)) with (2 * Z.of_nat n) by lia. exact HW. }
  { rewrite u16s_length, fws_length. lia. }
  split; [exact H1|].
  replace (A + 2 * i) with (A + Z.of_nat (2 * Z.to_nat i)) by lia.
  split; [split; [cbn; split; exact I|] | exact H3].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, <- EA. exact H2.
Qed.

Lemma f16_close : forall m A n f i (w : word) x,
  f16hole m A n f i -> 0 <= i < Z.of_nat n -> rw_cells segs m (A + 2 * i) [C2 w] -> le2 w = le2 (Z_to_bv 64 x) ->
  f16arr segs m A n (fupd f i x).
Proof.
  intros m A n f i w x HH Hi [[_ HC] _] EW. cbn [cells_bytes cbytes] in HC. rewrite app_nil_r in HC.
  assert (NE : nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i))).
  { rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity. }
  destruct (u16s_around _ _ _ NE) as [_ EU].
  replace (A + 2 * i) with (A + Z.of_nat (2 * Z.to_nat i)) in HC by lia.
  destruct (bhole_close m A _ _ _ (le2 w) HH HC (length_le2 w)) as [HB HW].
  unfold f16arr, u16arr. replace i with (Z.of_nat (Z.to_nat i)) at 1 2 by lia.
  rewrite fws_fupd by lia. rewrite EU, <- EW. split; [exact HB|].
  rewrite upd_length, fws_length. rewrite u16s_length, fws_length in HW.
  replace (2 * Z.of_nat n) with (Z.of_nat (2 * n)) by lia. exact HW.
Qed.

Lemma f32_open : forall m A n f i,
  f32arr segs m A n f -> 0 <= i < Z.of_nat n ->
  f32hole m A n f i /\ rw_cells segs m (A + 4 * i) [CB 4 (le4 (Z_to_bv 64 (f i)))].
Proof.
  intros m A n f i [HB HW] Hi. rewrite fws_length in HW.
  assert (NE : nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i))).
  { rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity. }
  destruct (u32s_around _ _ _ NE) as [EA _].
  destruct (bhole_open m A (u32s (fws f n)) (4 * Z.to_nat i) 4 HB) as (H1 & H2 & H3).
  { rewrite u32s_length, fws_length. replace (Z.of_nat (4 * n)) with (4 * Z.of_nat n) by lia. exact HW. }
  { rewrite u32s_length, fws_length. lia. }
  split; [exact H1|].
  replace (A + 4 * i) with (A + Z.of_nat (4 * Z.to_nat i)) by lia.
  split; [split; [cbn [cells_wf cell_wf]; split; [apply length_le4| exact I]|] | exact H3].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, <- EA. exact H2.
Qed.

Lemma f32_close : forall m A n f i cs x,
  f32hole m A n f i -> 0 <= i < Z.of_nat n -> rw_cells segs m (A + 4 * i) cs -> cells_bytes cs = le4 (Z_to_bv 64 x) ->
  f32arr segs m A n (fupd f i x).
Proof.
  intros m A n f i cs x HH Hi [[_ HC] _] EW. rewrite EW in HC.
  assert (NE : nth_error (fws f n) (Z.to_nat i) = Some (Z_to_bv 64 (f i))).
  { rewrite fws_nth by lia. rewrite Z2Nat.id by lia. reflexivity. }
  destruct (u32s_around _ _ _ NE) as [_ EU].
  replace (A + 4 * i) with (A + Z.of_nat (4 * Z.to_nat i)) in HC by lia.
  destruct (bhole_close m A _ _ _ (le4 (Z_to_bv 64 x)) HH HC (length_le4 _)) as [HB HW].
  unfold f32arr, u32arr. replace i with (Z.of_nat (Z.to_nat i)) at 1 2 by lia.
  rewrite fws_fupd by lia. rewrite EU. split; [exact HB|].
  rewrite upd_length, fws_length. rewrite u32s_length, fws_length in HW.
  replace (4 * Z.of_nat n) with (Z.of_nat (4 * n)) by lia. exact HW.
Qed.

Lemma f16hole_frame : forall m A n f i a xs N,
  f16hole m A n f i -> N = 2 * Z.of_nat n -> 0 <= i -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A \/ (A + 2 * i <= a /\ a + Z.of_nat (length xs) <= A + 2 * i + 2)) ->
  f16hole (write_to_mem m (wa a) xs) A n f i.
Proof.
  intros m A n f i a xs N H -> Hi Ha Hl D. unfold f16hole in *. apply bhole_frame; [exact H| exact Ha| exact Hl|].
  rewrite u16s_length, fws_length. lia.
Qed.
Lemma f32hole_frame : forall m A n f i a xs N,
  f32hole m A n f i -> N = 4 * Z.of_nat n -> 0 <= i -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A \/ (A + 4 * i <= a /\ a + Z.of_nat (length xs) <= A + 4 * i + 4)) ->
  f32hole (write_to_mem m (wa a) xs) A n f i.
Proof.
  intros m A n f i a xs N H -> Hi Ha Hl D. unfold f32hole in *. apply bhole_frame; [exact H| exact Ha| exact Hl|].
  rewrite u32s_length, fws_length. lia.
Qed.
Lemma f16arr_frameN : forall m A n f a xs N,
  f16arr segs m A n f -> N = 2 * Z.of_nat n -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A) -> f16arr segs (write_to_mem m (wa a) xs) A n f.
Proof.
  intros m A n f a xs N H -> Ha Hl D. unfold f16arr in *. apply u16arr_frame; [exact H| exact Ha| exact Hl|].
  rewrite fws_length. exact D.
Qed.
Lemma f32arr_frameN : forall m A n f a xs N,
  f32arr segs m A n f -> N = 4 * Z.of_nat n -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A) -> f32arr segs (write_to_mem m (wa a) xs) A n f.
Proof.
  intros m A n f a xs N H -> Ha Hl D. unfold f32arr in *. apply u32arr_frame; [exact H| exact Ha| exact Hl|].
  rewrite fws_length. exact D.
Qed.
Lemma f8arr_frameN : forall m A n f a xs N,
  f8arr segs m A n f -> N = Z.of_nat n -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A) -> f8arr segs (write_to_mem m (wa a) xs) A n f.
Proof.
  intros m A n f a xs N H -> Ha Hl D. unfold f8arr in *. apply u8arr_frame; [exact H| exact Ha| exact Hl|].
  rewrite length_map, length_seq. exact D.
Qed.

Definition c2f (ws : list word) : Z -> Z := fun k => bv_unsigned (nth (Z.to_nat k) ws (Z_to_bv 64 0)).
Lemma cells_bytes_C2 : forall ws, cells_bytes (map C2 ws) = u16s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u16s]. rewrite IH. reflexivity. Qed.
Lemma cells_size_C2 : forall ws, cells_size (map C2 ws) = (2 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma cells_wf_C2 : forall ws, cells_wf (map C2 ws).
Proof. induction ws as [|w ws IH]; cbn; [exact I| split; [exact I| exact IH]]. Qed.
Lemma f16arr_to_cells : forall m A n f, f16arr segs m A n f -> rw_cells segs m A (map C2 (fws f n)).
Proof.
  intros m A n f [HB HW]. split; [split; [apply cells_wf_C2| rewrite cells_bytes_C2; exact HB]|].
  rewrite cells_size_C2. replace (Z.of_nat (2 * length (fws f n))) with (2 * Z.of_nat (length (fws f n))) by lia. exact HW.
Qed.
Lemma f16arr_of_cells_fws : forall m A n f, rw_cells segs m A (map C2 (fws f n)) -> f16arr segs m A n f.
Proof.
  intros m A n f [[_ HB] HW]. rewrite cells_bytes_C2 in HB. rewrite cells_size_C2 in HW.
  split; [exact HB|]. replace (2 * Z.of_nat (length (fws f n))) with (Z.of_nat (2 * length (fws f n))) by lia. exact HW.
Qed.
Lemma f16arr_of_cells : forall m A ws, rw_cells segs m A (map C2 ws) -> f16arr segs m A (length ws) (c2f ws).
Proof.
  intros m A ws [[_ HB] HW]. rewrite cells_bytes_C2 in HB. rewrite cells_size_C2 in HW.
  assert (E : fws (c2f ws) (length ws) = ws).
  { apply nth_error_ext'; [apply fws_length|]. intros k Hk. rewrite fws_length in Hk. rewrite fws_nth by exact Hk.
    unfold c2f. rewrite Nat2Z.id. rewrite Z_to_bv_bv_unsigned. symmetry. apply nth_error_nth'. exact Hk. }
  unfold f16arr, u16arr. rewrite E. split; [exact HB|].
  replace (2 * Z.of_nat (length ws)) with (Z.of_nat (2 * length ws)) by lia. exact HW.
Qed.

Lemma f16arr_bound : forall m A n f, f16arr segs m A n f -> 0 <= A /\ A + 2 * Z.of_nat n <= 2^64.
Proof. intros m A n f [_ (H0 & H1 & _)]. rewrite fws_length in H1. lia. Qed.
Lemma f32arr_bound : forall m A n f, f32arr segs m A n f -> 0 <= A /\ A + 4 * Z.of_nat n <= 2^64.
Proof. intros m A n f [_ (H0 & H1 & _)]. rewrite fws_length in H1. lia. Qed.

End WithSegs.

Ltac ita_side := first [ lia | simpl_sizes; slia ].
Ltac ita_zlit e := let v := eval vm_compute in e in v.

Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f16arr segs m ?A2 ?n2 ?f2 |- _ =>
      let N := ita_zlit (2 * Z.of_nat n2) in
      first [ apply (f16arr_frameN segs m A2 n2 f2 a bs N) in H; [ | reflexivity | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f32arr segs m ?A2 ?n2 ?f2 |- _ =>
      let N := ita_zlit (4 * Z.of_nat n2) in
      first [ apply (f32arr_frameN segs m A2 n2 f2 a bs N) in H; [ | reflexivity | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f8arr segs m ?A2 ?n2 ?f2 |- _ =>
      let N := ita_zlit (Z.of_nat n2) in
      first [ apply (f8arr_frameN segs m A2 n2 f2 a bs N) in H; [ | reflexivity | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f16hole segs m ?A2 ?n2 ?f2 ?i2 |- _ =>
      let N := ita_zlit (2 * Z.of_nat n2) in
      first [ apply (f16hole_frame segs m A2 n2 f2 i2 a bs N) in H; [ | reflexivity | lia | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f32hole segs m ?A2 ?n2 ?f2 ?i2 |- _ =>
      let N := ita_zlit (4 * Z.of_nat n2) in
      first [ apply (f32hole_frame segs m A2 n2 f2 i2 a bs N) in H; [ | reflexivity | lia | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac f16_open_at ARR idx C EC CH CC :=
  lazymatch type of ARR with
  | f16arr ?segs ?m ?A ?n ?f =>
      destruct (f16_open segs m A n f idx ARR ltac:(lia)) as [CH CC]; clear ARR;
      remember (A + 2 * idx) as C eqn:EC
  end.
Ltac f16_close_at CH CC EC x NEW :=
  lazymatch type of CH with
  | f16hole ?segs ?m ?A ?n ?f ?i =>
      rewrite EC in CC;
      lazymatch type of CC with
      | rw_cells _ _ _ [C2 ?w] =>
          assert (NEW : f16arr segs m A n (fupd f i x));
          [ apply (f16_close segs m A n f i w x CH); [lia | exact CC | ] | clear CH CC ]
      end
  end.
Ltac f32_open_at ARR idx C EC CH CC :=
  lazymatch type of ARR with
  | f32arr ?segs ?m ?A ?n ?f =>
      destruct (f32_open segs m A n f idx ARR ltac:(lia)) as [CH CC]; clear ARR;
      remember (A + 4 * idx) as C eqn:EC
  end.
Ltac f32_close_at CH CC EC x NEW :=
  lazymatch type of CH with
  | f32hole ?segs ?m ?A ?n ?f ?i =>
      rewrite EC in CC;
      lazymatch type of CC with
      | rw_cells _ _ _ ?cs =>
          assert (NEW : f32arr segs m A n (fupd f i x));
          [ apply (f32_close segs m A n f i cs x CH); [lia | exact CC | ] | clear CH CC ]
      end
  end.

Ltac zs := zstep; fix_neg_store; try pc_lit.
