From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  send_line_c gesture_end_c relay_event_c RelayFrame send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c
  RelayRep relay_finish_b_c KindB relay_finish_seg.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fi_firstn_S : forall {X : Type} (l : list X) i d, (i < length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros X l. induction l as [|x l IH]; intros i d H; cbn [length] in H; [lia|].
  destruct i as [|i]; [reflexivity|].
  change (firstn (S (S i)) (x :: l)) with (x :: firstn (S i) l).
  rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma fi_skipn_S : forall {X : Type} (l : list X) i d, (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros X l. induction l as [|x l IH]; intros i d H; cbn [length] in H; [lia|].
  destruct i as [|i]; [reflexivity|]. exact (IH i d ltac:(lia)).
Qed.

Lemma fi_kt_nonneg : forall ks, 0 <= keys_total ks.
Proof. intros ks. unfold keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.

Lemma fi_kt_zero : forall ks, keys_total ks = 0 -> ks = [].
Proof.
  intros [|k ks] H; [reflexivity|]. exfalso. pose proof (fi_kt_nonneg ks) as N.
  unfold keys_total in H, N. cbn [fold_right] in H. lia.
Qed.

Lemma fi_et_app : forall l1 l2, entries_total (l1 ++ l2) = entries_total l1 + entries_total l2.
Proof. intros l1 l2. unfold entries_total. induction l1 as [|e l1 IH]; cbn [app fold_right]; lia. Qed.

Lemma fi_et_nonneg : forall l, 0 <= entries_total l.
Proof.
  intros l. unfold entries_total. induction l as [|e l IH]; cbn [fold_right]; [lia|].
  pose proof (fi_kt_nonneg (re_keys e)). lia.
Qed.

Lemma fi_et_one : forall e, entries_total [e] = keys_total (re_keys e).
Proof. intros e. unfold entries_total. cbn [fold_right]. lia. Qed.

Lemma fi_et_firstn_le : forall l i, entries_total (firstn i l) <= entries_total l.
Proof.
  intros l i. rewrite <- (firstn_skipn i l) at 2. rewrite fi_et_app.
  pose proof (fi_et_nonneg (skipn i l)). lia.
Qed.

Lemma fi_eo_app : forall l1 l2, entries_out (l1 ++ l2) = entries_out l1 ++ entries_out l2.
Proof. intros l1 l2. unfold entries_out. rewrite map_app, concat_app. reflexivity. Qed.

Lemma fi_eo_one : forall e, entries_out [e] = keys_out (re_keys e).
Proof. intros e. unfold entries_out. cbn [map concat]. apply app_nil_r. Qed.

Lemma fi_et_zero : forall l, entries_total l = 0 -> entries_out l = [].
Proof.
  induction l as [|e l IH]; intros H; [reflexivity|].
  pose proof (fi_kt_nonneg (re_keys e)) as N1. pose proof (fi_et_nonneg l) as N2.
  change (entries_total (e :: l)) with (keys_total (re_keys e) + entries_total l) in H.
  change (e :: l) with ([e] ++ l). rewrite fi_eo_app, fi_eo_one, IH by lia.
  rewrite (fi_kt_zero (re_keys e)) by lia. reflexivity.
Qed.

Lemma fi_eb_app : forall l1 l2,
  concat (map entry_blocks (l1 ++ l2)) = concat (map entry_blocks l1) ++ concat (map entry_blocks l2).
Proof. intros l1 l2. rewrite map_app, concat_app. reflexivity. Qed.

Ltac fi_sd cl br dd T1 T2 Hc Hb Hd :=
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->];
  destruct (Z.eqb_spec T1 0) as [?E1|?E1]; destruct (Z.eqb_spec T2 0) as [?E2|?E2];
  destruct (Z.eqb_spec (T1 + T2) 0) as [?E3|?E3]; cbn.

Lemma fi_br_step : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  (if send_off cl (if send_off cl br T1 then br else dd) T2 then (if send_off cl br T1 then br else dd) else dd) =
  (if send_off cl br (T1 + T2) then br else dd).
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2. unfold send_off.
  fi_sd cl br dd T1 T2 Hc Hb Hd; first [reflexivity | lia].
Qed.

Lemma fi_ei_step : forall cl br dd ei T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  (if send_off cl (if send_off cl br T1 then br else dd) T2 then (if send_off cl br T1 then ei else 0) else 0) =
  (if send_off cl br (T1 + T2) then ei else 0).
Proof.
  intros cl br dd ei T1 T2 Hc Hb Hd H1 H2. unfold send_off.
  fi_sd cl br dd T1 T2 Hc Hb Hd; first [reflexivity | lia].
Qed.

Lemma fi_live_step : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl br dd (T1 + T2) = send_live cl br dd T1 || send_live cl (if send_off cl br T1 then br else dd) dd T2.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2. unfold send_live, send_off.
  fi_sd cl br dd T1 T2 Hc Hb Hd; first [reflexivity | lia].
Qed.

Lemma fi_live_t1 : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl (if send_off cl br T1 then br else dd) dd T2 = true -> send_live cl br dd T1 = false -> T1 = 0.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2. unfold send_live, send_off.
  fi_sd cl br dd T1 T2 Hc Hb Hd; intros; first [lia | discriminate].
Qed.

Lemma fi_live_t2 : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl (if send_off cl br T1 then br else dd) dd T2 = false -> send_live cl br dd (T1 + T2) = true -> T2 = 0.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2. unfold send_live, send_off.
  fi_sd cl br dd T1 T2 Hc Hb Hd; intros; first [lia | discriminate].
Qed.

Lemma fi_live_nz : forall cl br dd T, send_live cl br dd T = true -> T <> 0.
Proof.
  intros cl br dd T H E. subst T. unfold send_live, send_off in H. rewrite Z.eqb_refl, orb_true_r in H.
  cbn in H. discriminate H.
Qed.

Lemma fi_br_01 : forall cl br dd T, (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  (if send_off cl br T then br else dd) = 0 \/ (if send_off cl br T then br else dd) = 1.
Proof. intros cl br dd T Hb Hd. destruct (send_off cl br T); assumption. Qed.

Lemma fi_ei_01 : forall cl br ei T, (ei = 0 \/ ei = 1) ->
  (if send_off cl br T then ei else 0) = 0 \/ (if send_off cl br T then ei else 0) = 1.
Proof. intros cl br ei T He. destruct (send_off cl br T); [assumption | left; reflexivity]. Qed.

Lemma fi_pw : forall m a, present m a -> YP09.writable_at rsegs m a.
Proof. intros m a [b E]. unfold YP09.writable_at, wview. rewrite E. discriminate. Qed.

Lemma fi_bytes_blk : forall m1 m2 q k c bs, q <= c -> c + Z.of_nat (length bs) <= q + k ->
  (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j)) ->
  bytes_at rsegs m1 c bs -> bytes_at rsegs m2 c bs.
Proof.
  intros m1 m2 q k c bs H1 H2 HB HC. apply (bytes_at_transfer _ m1); [exact HC|].
  intros i Hi. replace (c + i) with (q + (c + i - q)) by lia. apply HB. lia.
Qed.

Lemma fi_rw_blk : forall m1 m2 q k c cs, q <= c -> c + Z.of_nat (cells_size cs) <= q + k ->
  (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j) /\ present m2 (q + j)) ->
  rw_cells rsegs m1 c cs -> rw_cells rsegs m2 c cs.
Proof.
  intros m1 m2 q k c cs H1 H2 HB HC. apply (rw_cells_transfer _ m1); [exact HC|].
  intros i Hi. replace (c + i) with (q + (c + i - q)) by lia.
  destruct (HB (c + i - q) ltac:(lia)) as [E P]. split; [exact E | intros _; exact (fi_pw _ _ P)].
Qed.

Lemma fi_rw_sub : forall m A n P cs S, rw_cells rsegs m A [CB n (P ++ cells_bytes cs ++ S)] -> cells_wf cs ->
  rw_cells rsegs m (A + Z.of_nat (length P)) cs.
Proof.
  intros m A n P cs S [[[Hl _] Hb] (H0 & H1 & Hw)] Hwf.
  cbn [cells_bytes cbytes cell_wf cells_size csize] in Hb, Hl, H1, Hw. rewrite app_nil_r in Hb.
  rewrite ?Nat.add_0_r in H1, Hw. rewrite <- Hl in H1, Hw. rewrite !length_app in H1, Hw.
  apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [split; [exact Hwf | exact Hb]|].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (length P) + i) with (A + (Z.of_nat (length P) + i)) by lia. apply Hw. lia.
Qed.

Lemma fi_cb_sub : forall m A n P Y S, rw_cells rsegs m A [CB n (P ++ Y ++ S)] ->
  rw_cells rsegs m (A + Z.of_nat (length P)) [CB (length Y) Y].
Proof.
  intros m A n P Y S H. apply (fi_rw_sub m A n P [CB (length Y) Y] S); [|cbn; split; [reflexivity | exact I]].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma fi_cb_bytes : forall m A n P Y S, rw_cells rsegs m A [CB n (P ++ Y ++ S)] ->
  bytes_at rsegs m (A + Z.of_nat (length P)) Y.
Proof.
  intros m A n P Y S H. destruct (fi_cb_sub m A n P Y S H) as [[_ B] _].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma fi_cb_c84 : forall m A n P v w S, rw_cells rsegs m A [CB n (P ++ (le8 v ++ le4 w) ++ S)] ->
  rw_cells rsegs m (A + Z.of_nat (length P)) [C8 v; C4 w].
Proof.
  intros m A n P v w S H. apply (fi_rw_sub m A n P [C8 v; C4 w] S); [|cbn; tauto].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma fi_rw_patch : forall m m' A n P Y Y' S,
  rw_cells rsegs m A [CB n (P ++ Y ++ S)] -> length Y' = length Y ->
  bytes_at rsegs m' (A + Z.of_nat (length P)) Y' ->
  (forall j, 0 <= j < Z.of_nat n -> ~ (Z.of_nat (length P) <= j < Z.of_nat (length P) + Z.of_nat (length Y)) ->
     YP09.mbyte rsegs m' (A + j) = YP09.mbyte rsegs m (A + j)) ->
  (forall j, 0 <= j < Z.of_nat n -> YP09.writable_at rsegs m' (A + j)) ->
  rw_cells rsegs m' A [CB n (P ++ Y' ++ S)].
Proof.
  intros m m' A n P Y Y' S [[[Hl _] Hb] (H0 & H1 & Hw)] LY HY HS HW.
  cbn [cells_bytes cbytes cell_wf cells_size csize] in Hb, Hl, H1, Hw. rewrite app_nil_r in Hb.
  rewrite ?Nat.add_0_r in H1, Hw. rewrite !length_app in Hl.
  apply bytes_at_app in Hb as [HP Hb]. apply bytes_at_app in Hb as [_ HSb].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite !length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + apply (bytes_at_transfer _ m); [exact HP|]. intros j Hj. apply HS; lia.
    + apply bytes_at_app. split; [exact HY|]. rewrite LY.
      apply (bytes_at_transfer _ m); [exact HSb|]. intros j Hj.
      replace (A + Z.of_nat (length P) + Z.of_nat (length Y) + j)
        with (A + (Z.of_nat (length P) + Z.of_nat (length Y) + j)) by lia.
      apply HS; lia.
  - cbn [cells_size csize]. rewrite ?Nat.add_0_r. split; [lia|]. split; [lia|]. exact HW.
Qed.

Lemma fi_rd8 : forall m A v, bytes_at rsegs m A (le8 v) -> ov_read_bytes rsegs m (wa A) 8 = Some (le8 v).
Proof.
  intros m A v H. replace (wa A) with (wa (A + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m A (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  rewrite firstn_all2 by (rewrite ?length_skipn, ?length_le8; lia). reflexivity.
Qed.

Lemma fi_rw_at : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma fi_by_at : forall m A A' bs, bytes_at rsegs m A bs -> A = A' -> bytes_at rsegs m A' bs.
Proof. intros m A A' bs H <-. exact H. Qed.

Definition fi_pads (e : rentry) : Prop := length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat.

Lemma fi_eb_len : forall e, fi_pads e -> length (entry_bytes e) = 56%nat.
Proof.
  intros e [P1 P2]. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, P1, P2. reflexivity.
Qed.

Lemma fi_ebs_len : forall l, Forall fi_pads l -> length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
  induction l as [|e l IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [He Hl].
  cbn [map concat length]. rewrite length_app, (fi_eb_len e He), (IH Hl). lia.
Qed.

Lemma fi_eb_split : forall e, entry_bytes e =
  (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e) ++
  le8 (Z_to_bv 64 (re_buf e)) ++ (le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e))) ++
  (le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e))) ++ re_pad2 e.
Proof. intros e. unfold entry_bytes. rewrite <- !app_assoc. reflexivity. Qed.

Lemma fi_rw_eq : forall m A n l l', rw_cells rsegs m A [CB n l] -> l = l' -> rw_cells rsegs m A [CB n l'].
Proof. intros m A n l l' H <-. exact H. Qed.

Lemma fi_tab_entry : forall m G l1 e l2 tail,
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes (l1 ++ e :: l2)) ++ tail)] ->
  Forall fi_pads l1 -> fi_pads e ->
  bytes_at rsegs m (G + 56 * Z.of_nat (length l1) + 16) (le8 (Z_to_bv 64 (re_buf e))) /\
  rw_cells rsegs m (G + 56 * Z.of_nat (length l1) + 40) [C8 (Z_to_bv 64 (re_hp e)); C4 (Z_to_bv 64 (re_nheld e))].
Proof.
  intros m G l1 e l2 tail H F1 [P1 P2].
  rewrite map_app, concat_app in H. cbn [map concat] in H. rewrite fi_eb_split in H.
  pose proof (fi_ebs_len l1 F1) as L1.
  set (X := concat (map entry_bytes l1)) in *.
  set (H16 := le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e) in *.
  assert (L16 : length H16 = 16%nat) by (unfold H16; rewrite !length_app, !length_le4, P1; reflexivity).
  set (U := le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e))) in *.
  assert (LU : length U = 16%nat) by (unfold U; rewrite !length_app, !length_le8; reflexivity).
  set (R := concat (map entry_bytes l2)) in *.
  split.
  - apply (fi_by_at m (G + Z.of_nat (length (X ++ H16)))).
    + apply (fi_cb_bytes m G 896 (X ++ H16) (le8 (Z_to_bv 64 (re_buf e)))
        (U ++ (le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e))) ++ re_pad2 e ++ R ++ tail)).
      apply (fi_rw_eq _ _ _ _ _ H). rewrite <- !app_assoc. reflexivity.
    + rewrite length_app, L1, L16. lia.
  - apply (fi_rw_at m (G + Z.of_nat (length (X ++ H16 ++ le8 (Z_to_bv 64 (re_buf e)) ++ U)))).
    + apply (fi_cb_c84 m G 896 (X ++ H16 ++ le8 (Z_to_bv 64 (re_buf e)) ++ U) _ _ (re_pad2 e ++ R ++ tail)).
      apply (fi_rw_eq _ _ _ _ _ H). rewrite <- !app_assoc. reflexivity.
    + rewrite !length_app, L1, L16, LU, length_le8. lia.
Qed.

Lemma fi_tab_upd : forall m m' G l1 e l2 tail,
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes (l1 ++ e :: l2)) ++ tail)] ->
  Forall fi_pads l1 -> fi_pads e ->
  rw_cells rsegs m' (G + 56 * Z.of_nat (length l1) + 40) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  (forall j, 0 <= j < 896 -> ~ (56 * Z.of_nat (length l1) + 40 <= j < 56 * Z.of_nat (length l1) + 52) ->
     YP09.mbyte rsegs m' (G + j) = YP09.mbyte rsegs m (G + j)) ->
  (forall j, 0 <= j < 896 -> YP09.writable_at rsegs m' (G + j)) ->
  rw_cells rsegs m' G [CB 896 (concat (map entry_bytes (l1 ++ entry_cleared e :: l2)) ++ tail)].
Proof.
  intros m m' G l1 e l2 tail H F1 [P1 P2] HC HS HW.
  pose proof (fi_ebs_len l1 F1) as L1.
  set (P := concat (map entry_bytes l1) ++ (le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++
            le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e) ++ le8 (Z_to_bv 64 (re_buf e)) ++
            (le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e)))).
  assert (LP : length P = (56 * length l1 + 40)%nat)
    by (unfold P; rewrite !length_app, !length_le4, !length_le8, L1, P1; lia).
  apply (fi_rw_eq m' G 896 (P ++ (le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)) ++
    (re_pad2 e ++ concat (map entry_bytes l2) ++ tail))).
  2: { unfold P. rewrite map_app, concat_app. cbn [map concat]. rewrite fi_eb_split.
       cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 entry_cleared].
       rewrite <- !app_assoc. reflexivity. }
  apply (fi_rw_patch m m' G 896 P (le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)))).
  - apply (fi_rw_eq _ _ _ _ _ H). unfold P. rewrite map_app, concat_app. cbn [map concat]. rewrite fi_eb_split.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !length_app, !length_le8, !length_le4. reflexivity.
  - destruct HC as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    apply (fi_by_at m' _ _ _ B). rewrite LP. lia.
  - intros j Hj Hn. apply HS; [lia|]. rewrite LP, !length_app, length_le8, length_le4 in Hn. lia.
  - exact HW.
Qed.

Lemma fi_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat length].
  rewrite length_app, length_le8, IH. lia.
Qed.

Lemma fi_ks_eq : forall ks ks', map key_addr ks' = map key_addr ks -> map key_text ks' = map key_text ks ->
  keys_total ks' = keys_total ks /\ keys_out ks' = keys_out ks /\ key_ptrs ks' = key_ptrs ks /\ length ks' = length ks.
Proof.
  induction ks as [|k ks IH]; intros [|k' ks'] HA HT; cbn [map] in HA, HT; try discriminate; [repeat split|].
  injection HA as HA1 HA2. injection HT as HT1 HT2.
  destruct (IH ks' HA2 HT2) as (E1 & E2 & E3 & E4).
  unfold keys_total, keys_out, key_ptrs in *. cbn [fold_right map concat length].
  rewrite E1, E2, E3, E4, HA1, HT1. repeat split.
Qed.

Lemma fi_ks_forall : forall (P : Z -> list byte -> Prop) ks ks',
  map key_addr ks' = map key_addr ks -> map key_text ks' = map key_text ks ->
  Forall (fun k => P (key_addr k) (key_text k)) ks -> Forall (fun k => P (key_addr k) (key_text k)) ks'.
Proof.
  intros P. induction ks as [|k ks IH]; intros [|k' ks'] HA HT HF; cbn [map] in HA, HT; try discriminate;
    [constructor|].
  injection HA as HA1 HA2. injection HT as HT1 HT2. apply Forall_cons_iff in HF as [H1 H2].
  constructor; [rewrite HA1, HT1; exact H1 | exact (IH ks' HA2 HT2 H2)].
Qed.

Lemma fi_bytes_of_mbytes : forall m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, YP09.mbyte rsegs m (a + i) = Some b) ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [reflexivity|]. split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Eb]. rewrite Z.add_0_r in Eb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Lb & Hb).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
    + cbn [length Z.of_nat]. exact Hb.
Qed.

Section FA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis AX : AllocExtra Bm (aa_MR API).

Definition fi_kst (L : layout) (A : astate) (m : word -> option byte) (e : rentry) : Prop :=
  (re_hp e <> 0 -> In (re_hp e, re_kh e) (blocks L A) /\ bytes_at rsegs m (re_hp e) (key_ptrs (re_keys e))) /\
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
                   bytes_at rsegs m (key_addr k) (key_text k ++ [Z_to_bv 8 0])) (re_keys e).

Definition fi_est (L : layout) (A : astate) (m : word -> option byte) (e : rentry) : Prop :=
  (0 < re_cap e -> In (re_buf e, re_cap e) (blocks L A)) /\ fi_kst L A m e.

Lemma fi_blocks_in : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof using.
  intros L A a n. unfold blocks. rewrite in_map_iff. split.
  - intros ([p k] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
  - intros (p & <- & Hin). exists (p, n). auto.
Qed.

Lemma fi_blk : forall L A mem md q k j, aa_MR API L A mem md -> In (q, k) (blocks L A) -> 0 <= j < k ->
  present mem (q + j) /\ 4096 <= q /\ q + k <= YM05.alloc_ceiling /\ ~ owned Bm L A (q + j).
Proof using.
  intros L A mem md q k j HM Hin Hj. apply fi_blocks_in in Hin as (p & <- & Hp).
  exact (mr_blocks Bm _ (aa_laws API) L A mem md p k j HM Hp Hj).
Qed.

Lemma fi_blk_eq : forall L A q k1 k2, List.NoDup (map fst (blocks L A)) ->
  In (q, k1) (blocks L A) -> In (q, k2) (blocks L A) -> k1 = k2.
Proof using.
  intros L A q k1 k2 ND H1 H2. exact (fi_nodup_fst _ q k1 k2 ND H1 H2).
Qed.

Lemma fi_blk_disj : forall L A mem md p n q k, aa_MR API L A mem md ->
  In (p, n) (blocks L A) -> In (q, k) (blocks L A) -> p <> q -> p + n <= q \/ q + k <= p.
Proof using. intros. eapply blocks_disjoint; eassumption. Qed.

Lemma fi_free_iff : forall L1 A1 L2 A2 a0 n0,
  List.NoDup (map fst (blocks L1 A1)) ->
  (exists b1 b2, blocks L1 A1 = b1 ++ (a0, n0) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  forall q m, In (q, m) (blocks L2 A2) <-> In (q, m) (blocks L1 A1) /\ q <> a0.
Proof using.
  intros L1 A1 L2 A2 a0 n0 N (b1 & b2 & E1 & E2) q m.
  rewrite E1, map_app in N. cbn [map fst] in N.
  apply List.NoDup_remove_2 in N. rewrite E1, E2. split.
  - intros H. split.
    + apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right; right; exact H].
    + intros ->. apply N. rewrite <- map_app. change a0 with (fst (a0, m)). apply in_map. exact H.
  - intros [H Hq]. apply in_app_or in H as [H|[H|H]]; apply in_or_app;
      [left; exact H | congruence | right; exact H].
Qed.

Lemma fi_free_keep : forall L1 A1 m1 L2 A2 m2 a0 n0 q k,
  (exists b1 b2, blocks L1 A1 = b1 ++ (a0, n0) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  blocks_kept Bm L1 A1 m1 m2 (fun a => a = a0) ->
  In (q, k) (blocks L1 A1) -> q <> a0 ->
  In (q, k) (blocks L2 A2) /\ (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j)).
Proof using SEGS.
  intros L1 A1 m1 L2 A2 m2 a0 n0 q k (b1 & b2 & E1 & E2) BK Hq Hne.
  split.
  - rewrite E2. rewrite E1 in Hq. apply in_app_or in Hq as [Hq|[Hq|Hq]]; apply in_or_app;
      [left; exact Hq | congruence | right; exact Hq].
  - intros j Hj. rewrite <- SEGS. exact (BK q k j Hq Hne Hj).
Qed.

Lemma fi_rp_keep : forall K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k,
  relay_post Bm API K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> 0 < k -> ~ F q -> (forall j, 0 <= j < k -> ~ E (q + j)) ->
  In (q, k) (blocks L2 A2) /\ (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j)).
Proof using SEGS.
  intros K E F L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k RP Hq Hk NF NE.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  destruct (proj1 (fi_blocks_in _ _ _ _) Hq) as (p & Ep & Hp).
  assert (NF' : ~ F (ptr_addr L1 p)) by (rewrite Ep; exact NF).
  pose proof (SV2 p k Hp Hk NF') as Hp2.
  pose proof (AD2 p k Hp Hp2 NF') as E2.
  split.
  { apply fi_blocks_in. exists p. split; [congruence | exact Hp2]. }
  intros j Hj. rewrite <- Ep, <- SEGS. apply (BY2 p k j Hp Hp2 NF' Hj). rewrite Ep. exact (NE j Hj).
Qed.

Lemma fi_cp_cells : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs,
  aa_MR API L1 A1 m1 md1 -> call_post Bm (aa_MR API) L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) ->
     (img_plain Bm (c + j) \/ YM05.alloc_ceiling <= c + j < 2 ^ 64) /\ ~ E' (c + j) /\ ~ scratch Bm R1 (c + j)) ->
  rw_cells rsegs m1 c cs -> rw_cells rsegs m2 c cs.
Proof using SEGS AX.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs M1 CP H HC.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply (rw_cells_transfer _ m1); [exact HC|]. intros j Hj. destruct (H j Hj) as (Hp & HE & HS).
  assert (R : YM05.alloc_ceiling <= c + j < 2 ^ 64 \/ in_img Bm (c + j))
    by (destruct Hp as [Hp|Hp]; [right; exact (proj1 Hp) | left; exact Hp]).
  assert (N1 : ~ owned Bm L1 A1 (c + j)).
  { destruct Hp as [Hp|Hp]; [exact (fi_not_owned_img Bm API AX _ _ _ _ _ M1 Hp)|].
    intros Ho. pose proof (fi_low Bm API _ _ _ _ _ M1 Ho). lia. }
  assert (N2 : ~ owned Bm L2 A2 (c + j)).
  { destruct Hp as [Hp|Hp]; [exact (fi_not_owned_img Bm API AX _ _ _ _ _ M2 Hp)|].
    intros Ho. pose proof (fi_low Bm API _ _ _ _ _ M2 Ho). lia. }
  destruct (FR2 (c + j) R N1 N2 HS HE) as [E W]. rewrite SEGS in E, W. split; [exact E | apply W].
Qed.

Lemma fi_rp_cells : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 c cs,
  aa_MR API L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) ->
     (img_plain Bm (c + j) \/ YM05.alloc_ceiling <= c + j < 2 ^ 64) /\ ~ E' (c + j) /\ ~ scratch_k Bm K' R1 (c + j)) ->
  rw_cells rsegs m1 c cs -> rw_cells rsegs m2 c cs.
Proof using SEGS AX.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 c cs M1 RP H HC.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply (rw_cells_transfer _ m1); [exact HC|]. intros j Hj. destruct (H j Hj) as (Hp & HE & HS).
  assert (R : YM05.alloc_ceiling <= c + j < 2 ^ 64 \/ in_img Bm (c + j))
    by (destruct Hp as [Hp|Hp]; [right; exact (proj1 Hp) | left; exact Hp]).
  assert (N1 : ~ owned Bm L1 A1 (c + j)).
  { destruct Hp as [Hp|Hp]; [exact (fi_not_owned_img Bm API AX _ _ _ _ _ M1 Hp)|].
    intros Ho. pose proof (fi_low Bm API _ _ _ _ _ M1 Ho). lia. }
  assert (N2 : ~ owned Bm L2 A2 (c + j)).
  { destruct Hp as [Hp|Hp]; [exact (fi_not_owned_img Bm API AX _ _ _ _ _ M2 Hp)|].
    intros Ho. pose proof (fi_low Bm API _ _ _ _ _ M2 Ho). lia. }
  destruct (FR2 (c + j) R N1 N2 HS HE) as [E W]. rewrite SEGS in E, W. split; [exact E | apply W].
Qed.

Lemma fi_kst_tr : forall L1 A1 m1 L2 A2 m2 e L0 A0 m0,
  entry_ok Bm L0 A0 m0 e -> fi_kst L1 A1 m1 e ->
  (forall q k, 0 < k -> In (q, k) (blocks L1 A1) -> In q (entry_blocks e) ->
     In (q, k) (blocks L2 A2) /\ (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j))) ->
  fi_kst L2 A2 m2 e.
Proof using.
  intros L1 A1 m1 L2 A2 m2 e L0 A0 m0 EOK [KH KS] TR.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPK & _ & _ & KF).
  split.
  - intros Hh. destruct (KH Hh) as [IN BY].
    destruct HPK as [(H0 & _) | (_ & _ & K8 & K8' & _)]; [contradiction|].
    assert (HB : In (re_hp e) (entry_blocks e)).
    { unfold entry_blocks. apply in_or_app. right. apply in_or_app. left.
      destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (TR (re_hp e) (re_kh e) ltac:(lia) IN HB) as [IN2 KEEP].
    split; [exact IN2|].
    apply (fi_bytes_blk m1 m2 (re_hp e) (re_kh e)); [lia | | exact KEEP | exact BY].
    rewrite fi_key_ptrs_len. unfold re_nheld in K8. lia.
  - rewrite Forall_forall in KS, KF |- *. intros k Hk. destruct (KS k Hk) as [IN BY].
    destruct (KF k Hk) as (_ & _ & _ & _ & HL & _).
    assert (HB : In (key_addr k) (entry_blocks e)).
    { unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
    destruct (TR (key_addr k) (Z.of_nat (length (key_text k)) + 1) ltac:(lia) IN HB) as [IN2 KEEP].
    split; [exact IN2|].
    apply (fi_bytes_blk m1 m2 (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [lia | | exact KEEP | exact BY].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma fi_est_tr : forall L1 A1 m1 L2 A2 m2 e L0 A0 m0,
  entry_ok Bm L0 A0 m0 e -> fi_est L1 A1 m1 e ->
  (forall q k, 0 < k -> In (q, k) (blocks L1 A1) -> In q (entry_blocks e) ->
     In (q, k) (blocks L2 A2) /\ (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j))) ->
  fi_est L2 A2 m2 e.
Proof using.
  intros L1 A1 m1 L2 A2 m2 e L0 A0 m0 EOK [BF KF] TR. split.
  - intros Hc. assert (HB : In (re_buf e) (entry_blocks e)).
    { unfold entry_blocks. apply in_or_app. left. destruct (Z.eqb_spec (re_cap e) 0) as [E|E]; [lia | left; reflexivity]. }
    exact (proj1 (TR _ _ Hc (BF Hc) HB)).
  - exact (fi_kst_tr L1 A1 m1 L2 A2 m2 e L0 A0 m0 EOK KF TR).
Qed.

Lemma fi_eok_est : forall L A m e, entry_ok Bm L A m e -> fi_est L A m e.
Proof using SEGS.
  intros L A m e EOK.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUF & _ & HPK & _ & _ & KF).
  rewrite SEGS in HPK, KF.
  split; [|split].
  - intros Hc. destruct BUF as [(C0 & _) | (_ & IN & _)]; [lia | exact IN].
  - intros Hh. destruct HPK as [(H0 & _) | (IN & _ & _ & _ & BY)]; [contradiction | split; assumption].
  - rewrite Forall_forall in KF |- *. intros k Hk. destruct (KF k Hk) as (IN & _ & BY & _).
    split; [exact IN|]. replace (key_text k ++ Z_to_bv 8 0 :: key_slack k) with
      ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k) in BY by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BY. exact (proj1 BY).
Qed.

Lemma fi_slack : block_slack_present Bm API -> forall L A mem md a XL, aa_MR API L A mem md ->
  In (a, XL + 1) (blocks L A) -> 0 <= a -> 0 <= XL -> a + XL + 1 + 8 <= 2 ^ 64 ->
  exists sl, Z.of_nat (length sl) = (- (a + XL + 1)) mod 8 /\ bytes_at rsegs mem (a + XL + 1) sl.
Proof using SEGS.
  intros SL L A mem md a XL HM Hin Ha HX Hb.
  pose proof (Z.mod_pos_bound (- (a + XL + 1)) 8 ltac:(lia)) as R8.
  destruct (fi_bytes_of_mbytes mem (a + XL + 1) (Z.to_nat ((- (a + XL + 1)) mod 8))) as (sl & Ls & Hs).
  - lia.
  - lia.
  - intros i Hi.
    assert (E : 8 * ((a + (XL + 1) + 7) / 8) = a + (XL + 1) + (- (a + (XL + 1))) mod 8)
      by (Z.div_mod_to_equations; lia).
    destruct (SL L A mem md a (XL + 1) (a + XL + 1 + i) HM Hin ltac:(lia)) as [b Eb].
    exists b. unfold YP09.mbyte. rewrite Eb. reflexivity.
  - exists sl. split; [lia | exact Hs].
Qed.

Lemma fi_keys_slack : block_slack_present Bm API -> forall L A mem md ks, aa_MR API L A mem md ->
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
                   bytes_at rsegs mem (key_addr k) (key_text k ++ [Z_to_bv 8 0])) ks ->
  exists ks', map key_addr ks' = map key_addr ks /\ map key_text ks' = map key_text ks /\
    Forall (fun k => bytes_at rsegs mem (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
       (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k))) ks'.
Proof using SEGS.
  intros SL L A mem md ks HM. induction ks as [|k ks IH]; intros HF.
  - exists []. split; [reflexivity|]. split; [reflexivity | constructor].
  - apply Forall_cons_iff in HF as [[IN BY] HF'].
    destruct (IH HF') as (ks' & E1 & E2 & F').
    destruct (fi_blk _ _ _ _ _ _ 0 HM IN ltac:(lia)) as (_ & Q1 & Q2 & _).
    pose proof YM05.alloc_ceiling_lt as ACL.
    destruct (fi_slack SL L A mem md (key_addr k) (Z.of_nat (length (key_text k))) HM IN ltac:(lia) ltac:(lia)
               ltac:(lia)) as (sl & Lsl & Bsl).
    exists ((key_addr k, key_text k, sl) :: ks'). cbn [map]. rewrite E1, E2.
    split; [reflexivity|]. split; [reflexivity|]. constructor; [|exact F']. cbv beta.
    change (key_addr (key_addr k, key_text k, sl)) with (key_addr k).
    change (key_text (key_addr k, key_text k, sl)) with (key_text k).
    change (key_slack (key_addr k, key_text k, sl)) with sl.
    split; [|lia].
    replace (key_text k ++ Z_to_bv 8 0 :: sl) with ((key_text k ++ [Z_to_bv 8 0]) ++ sl)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BY|]. rewrite length_app. cbn [length].
    replace (key_addr k + Z.of_nat (length (key_text k) + 1)) with
      (key_addr k + Z.of_nat (length (key_text k)) + 1) by lia. exact Bsl.
Qed.

Lemma fi_rp_id : forall K E F L A regs mem md,
  call_pre_k Bm (aa_MR API) K L A regs mem md -> relay_post Bm API K E F L A regs mem md L A regs mem md.
Proof using.
  intros K E F L A regs mem md PRE.
  destruct PRE as (HM & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [intros; reflexivity|]. split; [intros p n Hp _ _; exact Hp|].
  split; [intros p Hp; split; [exact Hp | reflexivity]|]. split; [intros a _ Ho; exact Ho|].
  split; [intros r _; reflexivity|]. split; [exists (m_vmmaps md); symmetry; apply fi_vm_id|].
  split; [intros a _ _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha].
Qed.

Lemma fi_rp_regs : forall K E F L A regs mem md L' A' R0 mem' md' regs',
  relay_post Bm API K E F L A regs mem md L' A' R0 mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof using.
  intros K E F L A regs mem md L' A' R0 mem' md' regs'
    (M & W & B & LE & RG & AD & SV & Z0 & IO & _ & VM & FR & BY & SW) RP.
  repeat (split; [eassumption|]). exact SW.
Qed.

End FA.

Section Regs.
Context {fx : YK11.FPState}.

Lemma fi_unpack : forall (Q : machine_state -> Prop) mem ms',
  (exists can, (exists s0, Q s0 /\ ms_rel rsegs can s0 /\ ro_same rsegs mem (ms_mem can)) /\
     Regs6ss.ms_eqv can ms') ->
  exists s0 R' m', Q s0 /\
    ms' = {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0; ms_svc_pending := ms_svc_pending s0;
             ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0; ms_mem := m'; ms_rom := ms_rom s0 |} /\
    Regs6ss.xregs_eqv (ms_regs s0) R' /\ mem_rel rsegs m' (ms_mem s0) /\ ro_same rsegs mem m'.
Proof.
  intros Q mem ms' (can & (s0 & HQ & HR & HO) & HE).
  destruct ms' as [r f p sv rv c mm o], can as [cr cf cp csv crv cc cmm co], s0 as [zr zf zp zsv zrv zc zmm zo].
  destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct HE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *. subst.
  do 3 eexists. split; [exact HQ|]. split; [reflexivity|]. split; [exact E1|]. split; [exact R8 | exact HO].
Qed.

End Regs.
