(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths, module names, addresses and numbers changed; 521 of its 718 lines of code are new or changed and 461 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
Import ListNotations.
Local Open Scope Z_scope.

Ltac p1_nt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota
      | symmetry;
        first [ solve [unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
              | solve [vm_compute; reflexivity] ] ]
  end.

Ltac p1_land :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) with 0
        by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia;
            first [symmetry; assumption | lia])
  end.

Lemma op3_run : forall (S : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 < S < 2 ^ 64 -> S mod 8 = 0 ->
  store_ok rsegs m (Z_to_bv 64 (S + 8)) 4 = true ->
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
      (write_to_mem m (Z_to_bv 64 (S + 8)) (le4 (Z_to_bv 64 1))) ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143a0) fc None m ro).
Proof.
  intros. step. p1_nt. step. p1_land. step. p1_nt. step. step. apply evt_done. reflexivity.
Qed.

Lemma op6_run : forall (S : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 < S < 2 ^ 64 -> S mod 8 = 0 ->
  store_ok rsegs m (Z_to_bv 64 (S + 12)) 4 = true ->
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
      (write_to_mem m (Z_to_bv 64 (S + 12)) (le4 (Z_to_bv 64 1))) ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143f4) fc None m ro).
Proof.
  intros. step. p1_nt. step. p1_land. step. p1_nt. step. step. apply evt_done. reflexivity.
Qed.

Lemma op8_run : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b : byte),
  0 <= K <= N -> N < 2 ^ 26 ->
  (K < N -> 0 < P + K < 2 ^ 64 - 1) ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b]) ->
  store_ok rsegs m (Z_to_bv 64 0x318b0) 1 = true ->
  store_ok rsegs (write_to_mem m (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x318d8) 8 = true ->
  evt rsegs (fun ms => exists (s0 s10 a0 a1 : word) (K' : Z),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 x9 a0 a1 x12 x13 x14 x15 x16 x17 x18 x19
        (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 s10 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
        (write_to_mem (write_to_mem m (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x318d8) (le8 a0)) ro /\
      s0 = Z_to_bv 64 (P + K') /\ s10 = Z_to_bv 64 (N - K') /\
      ((K < N /\ K' = K + 1 /\ a0 = zxb b) \/ (K = N /\ K' = K /\ a0 = Z_to_bv 64 0)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14408) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m ro b HK HN HP RB S1 S2.
  step. if_cases HC.
  - assert (HKN : K = N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia. }
    step. step. step. step.
    apply evt_done. do 4 eexists. exists K. split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. right. split; [exact HKN|]. split; reflexivity.
  - assert (HKN : K < N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_neq in HC. lia. }
    specialize (RB HKN). specialize (HP HKN).
    step. step. p1_nt. step. step. step. step. step. step. step.
    apply evt_done. do 4 eexists. exists (K + 1). split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. left. split; [exact HKN|]. split; reflexivity.
Qed.

Lemma sp_ro_glob : forall a, 0x318a0 <= a < 0x31aa0 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  assert (C : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x318a0 + Z.of_nat i)))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat (a - 0x318a0))).
  rewrite Z2Nat.id in C by lia. replace (0x318a0 + (a - 0x318a0)) with a in C by lia.
  apply negb_true_iff. apply C. apply in_seq. lia.
Qed.

Lemma cells_writable : forall segs m A cs a, rw_cells segs m A cs ->
  A <= a < A + Z.of_nat (cells_size cs) -> writable_at segs m a.
Proof. intros segs m A cs a (_ & _ & _ & WR) Ha. replace a with (A + (a - A)) by lia. apply WR. lia. Qed.

Definition hs_flags (h : hsrc) (c e : Z) : hsrc :=
  HS (hs_fd h) (hs_open h) c e (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h) (hs_npartial h)
     (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).

Definition set_flag (off : Z) (h : hsrc) : hsrc :=
  if off =? 8 then hs_flags h 1 (hs_eintr h) else hs_flags h (hs_closed h) 1.

Definition upd_src (off : Z) (i : nat) (hj : list (hsrc * nat)) : list (hsrc * nat) :=
  map (fun p => if Nat.eqb (snd p) i then (set_flag off (fst p), snd p) else p) hj.

Lemma upd_snd : forall off i hj, map snd (upd_src off i hj) = map snd hj.
Proof.
  intros off i hj. unfold upd_src. rewrite map_map. apply map_ext. intros [h q]. cbn.
  destruct (Nat.eqb q i); reflexivity.
Qed.

Lemma upd_open : forall off i hj q, slot_open (upd_src off i hj) q = slot_open hj q.
Proof. intros off i hj q. unfold slot_open. rewrite upd_snd. reflexivity. Qed.

Lemma upd_blocks : forall off i hj,
  map (fun p => hs_blocks (fst p)) (upd_src off i hj) = map (fun p => hs_blocks (fst p)) hj.
Proof.
  intros off i hj. unfold upd_src. rewrite map_map. apply map_ext. intros [h q]. cbn.
  destruct (Nat.eqb q i); [|reflexivity]. unfold set_flag. destruct (off =? 8); reflexivity.
Qed.

Lemma upd_target : forall off i G OUT es hj, target_addrs G OUT es (upd_src off i hj) = target_addrs G OUT es hj.
Proof. intros off i G OUT es hj. unfold target_addrs. rewrite upd_blocks. reflexivity. Qed.

Lemma upd_cost : forall off i es hj, slot_cost es (upd_src off i hj) = slot_cost es hj.
Proof.
  intros off i es. induction es as [|e es IH]; intros [|[h q] hj]; try reflexivity.
  change (pair_cost e (if Nat.eqb q i then (set_flag off h, q) else (h, q)) + slot_cost es (upd_src off i hj) =
    pair_cost e (h, q) + slot_cost es hj).
  rewrite IH. destruct (Nat.eqb q i); [|reflexivity]. unfold pair_cost, set_flag. destruct (off =? 8); reflexivity.
Qed.

Lemma upd_view : forall off i G OUT es hj, view_of G OUT es (upd_src off i hj) = view_of G OUT es hj.
Proof.
  intros off i G OUT es hj.
  assert (K : forall (X : Type) (f : hsrc * nat -> X), (forall h q, f (set_flag off h, q) = f (h, q)) ->
    map f (upd_src off i hj) = map f hj).
  { intros X f Hf. unfold upd_src. rewrite map_map. apply map_ext. intros [h q]. cbn [fst snd].
    destruct (Nat.eqb q i); [apply Hf|reflexivity]. }
  assert (W : AllocBound.zsum (fun p => nw_src (fst p)) (upd_src off i hj) =
              AllocBound.zsum (fun p => nw_src (fst p)) hj).
  { unfold upd_src. clear K. induction hj as [|[h q] hj IH]; [reflexivity|]. cbn [map].
    rewrite !AllocBound.zsum_cons, IH. f_equal. cbn [fst snd]. destruct (Nat.eqb q i); [|reflexivity].
    unfold set_flag. destruct (off =? 8); reflexivity. }
  unfold view_of, pend_view, nc_wt, ek_view.
  rewrite W, (K _ (fun p => map snd (hl_recs (hs_pending (fst p))))), (K _ (fun p => src_nc (fst p))),
    (K _ (fun p => ekeys_hl (hs_expected (fst p)))).
  all: try (intros h q; unfold set_flag; destruct (off =? 8); reflexivity).
  unfold upd_src. rewrite length_map. reflexivity.
Qed.

Section GStore.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variables (m m' : word -> option byte) (lo hi : Z).
Hypothesis MU : munch [(lo, hi)] m m'.
Hypothesis WM : wmono (ms_segs B) m m'.
Hypothesis IMG : forall a, 0x318a0 <= a < 0x31aa0 -> in_img B a.
Hypothesis WLO : 0x318a7 <= lo.
Hypothesis WHI : hi <= 0x31aa0.

Lemma gs_apart : forall a n, fresh_block B a n -> 0 < n -> a + n + 7 <= lo \/ hi <= a.
Proof.
  intros a n (_ & _ & NI) HN.
  destruct (Z_le_gt_dec (a + n + 7) lo) as [H|H]; [left; exact H|right].
  destruct (Z_le_gt_dec hi a) as [HA|HA]; [exact HA|exfalso].
  destruct (Z_le_gt_dec 0x318a0 a) as [A0|A0].
  - apply (NI 0 ltac:(lia)), IMG. lia.
  - apply (NI (0x318a0 - a) ltac:(lia)), IMG. lia.
Qed.

Lemma gs_bytes : forall a bs,
  bytes_at (ms_segs B) m a bs -> a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at (ms_segs B) m' a bs.
Proof. intros a bs H D. eapply bytes_at_transport; [exact H|exact MU|]. cbn [disjoint_from]. tauto. Qed.
Lemma gs_cells : forall a cs,
  rw_cells (ms_segs B) m a cs -> a + Z.of_nat (cells_size cs) <= lo \/ hi <= a -> rw_cells (ms_segs B) m' a cs.
Proof. intros a cs H D. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn [disjoint_from]. tauto. Qed.
Lemma gs_fresh_bytes : forall a n bs, fresh_block B a n -> 0 < n ->
  Z.of_nat (length bs) <= n + 7 -> bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a bs.
Proof. intros a n bs FR HN HL HB. apply gs_bytes; [exact HB|]. pose proof (gs_apart a n FR HN). lia. Qed.
Lemma gs_fresh_cells : forall a n cs, fresh_block B a n -> 0 < n ->
  Z.of_nat (cells_size cs) <= n -> rw_cells (ms_segs B) m a cs -> rw_cells (ms_segs B) m' a cs.
Proof. intros a n cs FR HN HL HB. apply gs_cells; [exact HB|]. pose proof (gs_apart a n FR HN). lia. Qed.

Lemma gs_entry : forall L A e, RelayRep.entry_ok B L A m e -> RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    eapply gs_fresh_cells; [exact FR|exact C|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|exact BC]. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply gs_fresh_bytes; [exact FR|lia| |exact HB].
      rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { eapply gs_fresh_bytes; [exact FR|lia| |].
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length]. rewrite length_firstn. lia.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt))
        (firstn 8 (Z_to_bv 8 0 :: slack))). apply bytes_at_prefix. exact HT. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma gs_list : forall L A LA l lines,
  LA + 16 <= lo \/ hi <= LA -> list_at B L A m LA l lines -> list_at B L A m' LA l lines.
Proof.
  intros L A LA l lines HLA (C & HN & AR & ND1 & ND2 & RS).
  split; [apply gs_cells; [exact C|cbn; lia]|]. split; [exact HN|]. split.
  { destruct AR as [AR|(HC & IN & FR & HJ & HA)]; [left; exact AR|right].
    split; [exact HC|]. split; [exact IN|]. split; [exact FR|]. split; [exact HJ|].
    eapply gs_fresh_cells; [exact FR|lia| |exact HA]. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  split; [exact ND1|]. split; [exact ND2|]. eapply Forall_impl; [|exact RS].
  intros r (IN & FR & CR & H1 & H2). split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply gs_fresh_cells; [exact FR|lia|cbn; lia|exact CR].
Qed.

Lemma gs_src : forall L A HA h,
  HA + 96 <= lo \/ hi <= HA -> src_at B L A m HA h -> src_at B L A m' HA h.
Proof.
  intros L A HA h HHA (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND).
  split; [apply gs_cells; [exact C1|cbn; lia]|].
  do 4 (split; [assumption|]). split; [apply gs_list; [lia|exact LP]|].
  split; [apply gs_cells; [exact C2|cbn; lia]|]. do 6 (split; [assumption|]). split.
  { eapply gs_fresh_cells; [exact FR|lia|cbn; lia|exact C3]. }
  split; [exact NZ|]. split; [apply gs_list; [lia|exact LE]|]. split; [apply gs_list; [lia|exact LH]|exact ND].
Qed.

Lemma gs_src_flag : forall L A HA h c e,
  HA + 8 <= lo -> hi <= HA + 16 -> src_at B L A m HA h ->
  rw_cells (ms_segs B) m' HA [C4 (Z_to_bv 64 (hs_fd h)); C4 (Z_to_bv 64 (hs_open h)); C4 (Z_to_bv 64 c);
                              C4 (Z_to_bv 64 e)] ->
  (c = 0 \/ c = 1) -> (e = 0 \/ e = 1) -> src_at B L A m' HA (hs_flags h c e).
Proof.
  intros L A HA h c e H8 H16 (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND)
    CH Hc He.
  split; [exact CH|]. split; [exact Hc|]. split; [exact He|]. split; [exact H3|]. split; [exact H4|].
  split; [apply gs_list; [lia|exact LP]|].
  split; [apply gs_cells; [exact C2|cbn; lia]|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact IN|]. split; [exact FR|]. split; [exact HJ|].
  split; [eapply gs_fresh_cells; [exact FR|lia|cbn; lia|exact C3]|].
  split; [exact NZ|]. split; [apply gs_list; [lia|exact LE]|]. split; [apply gs_list; [lia|exact LH]|exact ND].
Qed.

Lemma gs_src_set : forall L A HA h off,
  (off = 8 \/ off = 12) -> lo = HA + off -> hi = HA + off + 4 ->
  m' = write_to_mem m (wa (HA + off)) (le4 (Z_to_bv 64 1)) ->
  src_at B L A m HA h -> src_at B L A m' HA (set_flag off h).
Proof.
  intros L A HA h off HOFF ELO EHI EM SRC.
  pose proof SRC as (CH & HC & HE & _).
  destruct HOFF as [-> | ->].
  - change (set_flag 8 h) with (hs_flags h 1 (hs_eintr h)).
    apply gs_src_flag; [lia|lia|exact SRC| |right; reflexivity|exact HE].
    rewrite EM. exact (rw_cells_write _ _ _ _ 8%nat (C4 (Z_to_bv 64 (hs_closed h))) (C4 (Z_to_bv 64 1)) CH eq_refl eq_refl I).
  - change (set_flag 12 h) with (hs_flags h (hs_closed h) 1).
    apply gs_src_flag; [lia|lia|exact SRC| |exact HC|right; reflexivity].
    rewrite EM. exact (rw_cells_write _ _ _ _ 12%nat (C4 (Z_to_bv 64 (hs_eintr h))) (C4 (Z_to_bv 64 1)) CH eq_refl eq_refl I).
Qed.

Lemma gs_output : forall L A no cap out, output_at (rc := rc) B L A m no cap out ->
  output_at (rc := rc) B L A m' no cap out.
Proof.
  intros L A no cap out ((O & junk & H) & CAP). split; [|exact CAP]. exists O, junk.
  destruct H as [H|(HC & HN & IN & FR & BY & LO & LJ)]; [left; exact H|right].
  split; [exact HC|]. split; [exact HN|]. split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply gs_fresh_bytes; [exact FR|exact HC|rewrite length_app; lia|exact BY].
Qed.

Lemma gs_relay : forall L A t nfd G OUT es hj,
  hi <= G_S -> relay_at (rc := rc) B L A m t nfd G OUT es hj ->
  relay_at (rc := rc) B L A m' t nfd G OUT (map short_entry es) hj.
Proof.
  intros L A t nfd G OUT es hj HG ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA).
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply short_entry_bytes. }
    rewrite EB. eapply gs_fresh_cells; [exact FR|unfold SRC_TABLE, SRC_ENTRY; lia|cbn; unfold SRC_TABLE, SRC_ENTRY; lia|exact TC]. }
  split; [exact IN|]. split; [exact FR|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact ES]. intros e HE. exact (gs_entry L A e HE). }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { clear HT TC IN FR ES ND FD NDH ZH NDA.
    induction PA as [|e p es hj HE HP IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
    unfold pair_ok in *. cbv zeta in *. cbn [short_entry re_keys re_fd re_skip re_used re_eof re_U].
    rewrite short_keys_texts. destruct HE as (SRC & HI & REST).
    split; [apply gs_src; [unfold G_S, SRC_SIZE in *; lia|exact SRC]|]. split; assumption. }
  split; [exact NDH|]. split.
  { intros i HI HZ. apply gs_cells; [exact (ZH i HI HZ)|]. right. unfold G_S, SRC_SIZE in *. lia. }
  rewrite short_target. exact NDA.
Qed.

Lemma gs_relay_flag : forall L A t nfd G OUT es hj i off,
  (off = 8 \/ off = 12) -> (i < 4)%nat -> slot_open hj i = true ->
  lo = G_S + SRC_SIZE * Z.of_nat i + off -> hi = G_S + SRC_SIZE * Z.of_nat i + off + 4 ->
  m' = write_to_mem m (wa (G_S + SRC_SIZE * Z.of_nat i + off)) (le4 (Z_to_bv 64 1)) ->
  relay_at (rc := rc) B L A m t nfd G OUT es hj ->
  relay_at (rc := rc) B L A m' t nfd G OUT (map short_entry es) (upd_src off i hj).
Proof.
  intros L A t nfd G OUT es hj i off HOFF HI OI ELO EHI EM
    ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA).
  assert (OFR : 8 <= off <= 12) by lia.
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply short_entry_bytes. }
    rewrite EB. eapply gs_fresh_cells; [exact FR|unfold SRC_TABLE, SRC_ENTRY; lia|cbn; unfold SRC_TABLE, SRC_ENTRY; lia|exact TC]. }
  split; [exact IN|]. split; [exact FR|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact ES]. intros e HE. exact (gs_entry L A e HE). }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { clear HT TC IN FR ES ND FD NDH ZH NDA OI. unfold upd_src.
    induction PA as [|e p es hj HE HP IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
    destruct p as [h q]. cbn [fst snd].
    unfold pair_ok in *. cbv zeta in *. cbn [fst snd short_entry re_keys re_fd re_skip re_used re_eof re_U] in *.
    rewrite short_keys_texts. destruct HE as (SRC & HQ & REST).
    destruct (Nat.eqb_spec q i) as [->|NE].
    - cbn [fst snd]. split; [eapply gs_src_set; [exact HOFF|exact ELO|exact EHI|exact EM|exact SRC]|].
      split; [exact HQ|]. destruct HOFF as [-> | ->]; exact REST.
    - cbn [fst snd]. split; [|split; assumption]. apply gs_src; [|exact SRC].
      rewrite ELO, EHI. unfold G_S, SRC_SIZE. lia. }
  split; [rewrite upd_snd; exact NDH|]. split.
  { intros q HQ HZ. rewrite upd_open in HZ. apply gs_cells; [exact (ZH q HQ HZ)|].
    destruct (Nat.eq_dec q i) as [->|NE]; [congruence|]. cbn. rewrite ELO, EHI. unfold G_S, SRC_SIZE. lia. }
  rewrite short_target, upd_target. exact NDA.
Qed.

End GStore.

Lemma gs_keep : forall B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA lo hi,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  munch [(lo, hi)] mem mem' -> wmono (ms_segs B) mem mem' ->
  0x318a0 <= lo -> hi <= 0x31aa0 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) ->
  aa_MR (API rc) L A mem md -> ro_agree (ms_segs B) mem -> image_kept (rc := rc) B E mem ->
  stack_mid B E mem -> driver_kept B E TA L A mem ->
  aa_MR (API rc) L A mem' md /\ ro_agree (ms_segs B) mem' /\ image_kept (rc := rc) B E mem' /\
  stack_mid B E mem' /\ driver_kept B E TA L A mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA lo hi HF MU WM HLO HHI MWR HMR HRO HIK HST HDK.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 27 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  pose proof FF as FFA. do 31 (destruct FFA as [_ FFA]). specialize (FFA rc fx).
  do 12 (destruct FFA as [_ FFA]). destruct FFA as (AX & UNG & _).
  assert (GA : forall a, 0x318a0 <= a < 0x31aa0 -> in_globals frame_G a).
  { intros a Ha. apply in_G_bss. lia. }
  assert (IMG : forall a, 0x318a0 <= a < 0x31aa0 -> in_img B a).
  { intros a Ha. exact (proj1 (FG a (GA a Ha))). }
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPB : 0x31aa0 < slot_sp E /\ slot_sp E < 2 ^ 64).
  { unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> outside [(lo, hi)] a ->
    mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha HO. split; [exact (munch_mbyte _ _ _ _ a MU Ha HO)|exact (munch_writable _ _ _ _ a MU Ha HO)]. }
  assert (BX : forall L0 A0 m0 md0 p n i,
    aa_MR (API rc) L0 A0 m0 md0 -> In (p, n) (user_blocks A0) -> 0 <= i < n ->
    0 <= ptr_addr L0 p + i < 2 ^ 64 /\ outside [(lo, hi)] (ptr_addr L0 p + i)).
  { intros L0 A0 m0 md0 p n i HM HP HI.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HM HP HI) as (_ & B0 & B1 & _).
    split; [lia|]. cbn [outside]. split; [|exact I]. intro HX.
    apply (ax_blocks_img AX L0 A0 m0 md0 p n i HM HP HI), IMG. lia. }
  split.
  { apply (mr_frame _ _ (aa_laws (API rc)) L A mem mem' md md HMR).
    - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      apply EQ; [lia|]. cbn [outside]. split; [|exact I]. intro HX. exact (UNG L A mem md a HMR (GA a ltac:(lia)) HO).
    - intros a HO HP. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      eapply munch_present; [exact MU|lia| |exact HP]. cbn [outside]. split; [|exact I]. intro HX.
      exact (UNG L A mem md a HMR (GA a ltac:(lia)) HO).
    - intros p n i HP HI. destruct (BX L A mem md p n i HMR HP HI) as [HR HO].
      eapply munch_present; [exact MU|exact HR|exact HO|].
      exact (proj1 (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HMR HP HI)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split.
  { intros a HA. unfold mrd. rewrite (MU a); [apply HRO; exact HA|]. cbn [outside]. split; [|exact I]. intro HX.
    pose proof (sp_ro_glob (bv_unsigned a) ltac:(lia)) as HNRO.
    rewrite Z_to_bv_bv_unsigned, <- SEG in HNRO. congruence. }
  split.
  { destruct HIK as (I1 & I2 & I3 & I4). split.
    - intros a HA H1 H2 H3 H4. destruct (I1 a HA H1 H2 H3 H4) as [EA WA].
      pose proof (in_img_low B SEG a HA) as AR.
      assert (HO : outside [(lo, hi)] a) by (cbn [outside]; split; [intro HX; apply H4, GA; lia|exact I]).
      destruct (EQ a ltac:(lia) HO) as [EB WB]. split; [congruence|tauto].
    - split.
      + intros a HA. pose proof (I2 a HA) as WA.
        assert (AR : 0 <= a < 2 ^ 64).
        { unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EE|[EE|[]]] & HR); inversion EE; subst; lia. }
        destruct (Z_le_gt_dec lo a) as [L1|L1]; [destruct (Z_lt_ge_dec a hi) as [L2|L2]|].
        * pose proof (MWR a ltac:(lia)) as W0. pose proof (WM (Z_to_bv 64 a) W0) as W1. tauto.
        * destruct (EQ a AR ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. tauto.
        * destruct (EQ a AR ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. tauto.
      + split.
        * intros a HA HNS. destruct (I3 a HA HNS) as [EA WA].
          destruct (EQ a ltac:(lia) ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. split; [congruence|tauto].
        * intros a HA. apply WM. exact (I4 a HA). }
  split.
  { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [eapply gs_cells; [exact MU|exact WM|exact ST1|right; lia]|].
    split; eapply gs_cells; [exact MU|exact WM|exact ST2|right; lia|exact MU|exact WM|exact ST3|right; lia]. }
  destruct HDK as (D1 & D2 & D3 & D4). split; [exact D1|]. split.
  - intros p n i HP HNT HNP HI. destruct (BX _ _ _ _ p n i MR0 HP HI) as [AR AO].
    rewrite (proj1 (EQ _ AR AO)). exact (D2 p n i HP HNT HNP HI).
  - split; [|exact D4]. intros i HI.
    destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
    destruct PIN as [(HN & _)|(HN & p & HP & EP)]; [lia|].
    destruct (BX _ _ _ _ p (ss_n E) i MR0 HP HI) as [AR AO]. rewrite EP in AR, AO.
    rewrite (proj1 (EQ _ AR AO)). exact (D3 i HI).
Qed.

Lemma gs_globals_src : forall B m m' lo hi cl br gn dd ei N G nfd mx no cap out,
  munch [(lo, hi)] m m' -> wmono (ms_segs B) m m' -> G_S <= lo -> errno_addr B = 0x31acc -> hi <= 0x31aa0 ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out -> globals_at B m' cl br gn dd ei N G nfd mx no cap out.
Proof.
  intros B m m' lo hi cl br gn dd ei N G nfd mx no cap out MU WM HLO ERR HHI
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & REST).
  unfold G_S in HLO. unfold globals_at.
  do 13 (split; [eapply gs_cells; [exact MU|exact WM|eassumption|
    left; match goal with |- ?a <= _ => let z := eval vm_compute in a in change (z <= lo); lia end]|]).
  split; [|exact REST]. destruct ER as [ev ER]. exists ev.
  eapply gs_cells; [exact MU|exact WM|exact ER|right; rewrite ERR; lia].
Qed.

Lemma globals_op8 : forall B m cl br gn dd ei N G nfd mx no cap out (a0 : word),
  errno_addr B = 0x31acc -> bv_unsigned a0 <= 255 ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out ->
  globals_at B (write_to_mem (write_to_mem m (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x318d8) (le8 a0))
    cl br gn dd 1 N G nfd a0 no cap out.
Proof.
  intros B m cl br gn dd ei N G nfd mx no cap out a0 ERR HA0
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & HCL & HBR & HGN & HDD & HEI & HGG & HMX).
  set (m1 := write_to_mem m (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))).
  assert (W1 : forall A cs, rw_cells (ms_segs B) m A cs ->
    (A + Z.of_nat (cells_size cs) <=? 0x318b0) || (0x318b1 <=? A) = true -> rw_cells (ms_segs B) m1 A cs).
  { intros A cs H D. apply orb_true_iff in D. rewrite !Z.leb_le in D. pose proof (rw_cells_bound _ _ _ _ H) as BD.
    unfold m1. apply rw_cells_frame; [exact H|lia|rewrite length_le1; lia|rewrite length_le1; lia]. }
  assert (W2 : forall A cs, rw_cells (ms_segs B) m1 A cs ->
    (A + Z.of_nat (cells_size cs) <=? 0x318d8) || (0x318e0 <=? A) = true ->
    rw_cells (ms_segs B) (write_to_mem m1 (Z_to_bv 64 0x318d8) (le8 a0)) A cs).
  { intros A cs H D. apply orb_true_iff in D. rewrite !Z.leb_le in D. pose proof (rw_cells_bound _ _ _ _ H) as BD.
    apply rw_cells_frame; [exact H|lia|rewrite length_le8; lia|rewrite length_le8; lia]. }
  assert (G7' : rw_cells (ms_segs B) m1 G_EINTR [C1 (Z_to_bv 8 1)]).
  { exact (rw_cells_write _ _ _ _ 0%nat (C1 (Z_to_bv 8 ei)) (C1 (Z_to_bv 8 1)) G7 eq_refl eq_refl I). }
  assert (G11' : rw_cells (ms_segs B) m1 G_OUTV [C8 mx; C8 no; C8 cap; C8 out]).
  { apply W1; [exact G11|vm_compute; reflexivity]. }
  unfold globals_at.
  split; [apply W2; [apply W1; [exact G1|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G2|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G3|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G4|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G5|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G6|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [exact G7'|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G8|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G9|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G10|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [exact (rw_cells_write _ _ _ _ 0%nat (C8 mx) (C8 a0) G11' eq_refl eq_refl I)|].
  split; [apply W2; [apply W1; [exact G12|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split; [apply W2; [apply W1; [exact G13|vm_compute; reflexivity]|vm_compute; reflexivity]|].
  split.
  { destruct ER as [ev ER]. exists ev. rewrite ERR in ER |- *.
    apply W2; [apply W1; [exact ER|vm_compute; reflexivity]|vm_compute; reflexivity]. }
  split; [exact HCL|]. split; [exact HBR|]. split; [exact HGN|]. split; [exact HDD|]. split; [right; reflexivity|].
  split; [exact HGG|exact HA0].
Qed.

Lemma MI_flag : forall B API LS SH SK ra empty rc fx j E CS RI t K s c off pc0 OP,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract ->
  (off = 8 \/ off = 12) -> pick_op OP = true -> OP <> 1 ->
  ((pc0 =? TAIL_CHECK) || (pc0 =? TAIL_STEP)) = false ->
  (forall (S : Z)
     (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
     (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
   0 < S < 2 ^ 64 -> S mod 8 = 0 ->
   store_ok rsegs m (Z_to_bv 64 (S + off)) 4 = true ->
   evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
       x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
       (write_to_mem m (Z_to_bv 64 (S + off)) (le4 (Z_to_bv 64 1))) ro)
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17
       x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc0) fc None m ro)) ->
  walk_at (ss_pl E) (t + 1) K ->
  MI (rc := rc) B (API rc) E RI t K pc0 (fun _ hj no regs => no = 0 /\ disp_src OP s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c off pc0 OP HF CB HOFF HP HN1 HPC RUN HW HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 27 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  assert (ERR : errno_addr B = 0x31acc).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  assert (GA : forall a, 0x318a0 <= a < 0x31aa0 -> in_globals frame_G a).
  { intros a Ha. apply in_G_bss. lia. }
  assert (IMG : forall a, 0x318a0 <= a < 0x31aa0 -> in_img B a).
  { intros a Ha. exact (proj1 (FG a (GA a Ha))). }
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  rewrite HPC, Z.add_0_r in HREL.
  destruct HR as (_ & DS & (B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & R9).
  destruct DS as [(_ & i & HI & OI & ->)|([HPF|HO1] & _)]; [|congruence|exfalso; exact (HN1 HO1)].
  set (HA := G_S + SRC_SIZE * Z.of_nat i) in *.
  assert (HAR : 0x31920 <= HA /\ HA + 96 <= 0x31aa0) by (unfold HA, G_S, SRC_SIZE; lia).
  assert (HA8 : HA mod 8 = 0).
  { unfold HA, G_S, SRC_SIZE. replace (0x31920 + 96 * Z.of_nat i) with ((25380 + 12 * Z.of_nat i) * 8) by lia.
    apply Z.mod_mul. lia. }
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _ & _ & _).
  assert (SRCI : exists h, src_at B L A mem HA h).
  { pose proof OI as OI'. unfold slot_open in OI'. apply existsb_exists in OI'. destruct OI' as (q & HQ & HE).
    apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
    destruct (pair_find _ _ _ _ _ (h, i) PA HQ) as [e HP0]. exists h.
    destruct HP0 as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC. exact SRC. }
  destruct SRCI as (h & SRCI). pose proof SRCI as (HC & _).
  assert (SOK : store_ok rsegs mem (Z_to_bv 64 (HA + off)) 4 = true).
  { rewrite <- SEG. destruct HOFF as [-> | ->].
    - change (Z_to_bv 64 (HA + 8)) with (wa (HA + Z.of_nat 8)).
      eapply (rw_cells_store_ok _ _ _ _ 8%nat (C4 (Z_to_bv 64 (hs_closed h)))); [exact HC|reflexivity|reflexivity].
    - change (Z_to_bv 64 (HA + 12)) with (wa (HA + Z.of_nat 12)).
      eapply (rw_cells_store_ok _ _ _ _ 12%nat (C4 (Z_to_bv 64 (hs_eintr h)))); [exact HC|reflexivity|reflexivity]. }
  assert (MWR : forall a, HA + off <= a < HA + off + 4 -> writable_at (ms_segs B) mem a).
  { intros a Ha. eapply cells_writable; [exact HC|]. change (HA <= a < HA + 16). lia. }
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 HA) by exact R9.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - K)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    apply RUN; [lia|exact HA8|exact SOK]. }
  intros ms1 (can1 & -> & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  remember (write_to_mem mem (Z_to_bv 64 (HA + off)) (le4 (Z_to_bv 64 1))) as mem' eqn:EM.
  assert (MU : munch [(HA + off, HA + off + 4)] mem mem').
  { rewrite EM. change (Z_to_bv 64 (HA + off)) with (wa (HA + off)).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le4; lia|cbn [inside]; left; rewrite length_le4; lia]. }
  assert (WM : wmono (ms_segs B) mem mem') by (rewrite EM; apply wmono_write, wmono_refl).
  destruct (gs_keep B API LS SH SK ra empty rc fx j E CS L A mem mem' md (target_addrs G (bv_unsigned out) es hj)
    (HA + off) (HA + off + 4) HF MU WM ltac:(lia) ltac:(lia) MWR HMR HRO HIK HST HDK) as (MR' & RO' & IK' & ST' & DK').
  assert (GL' : globals_at B mem' cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out).
  { eapply gs_globals_src; [exact MU|exact WM|unfold G_S; lia|exact ERR|lia|exact HGL]. }
  assert (REL' : relay_at (rc := rc) B L A mem' t nfd G (bv_unsigned out) (map short_entry es) (upd_src off i hj)).
  { eapply (gs_relay_flag B mem mem' (HA + off) (HA + off + 4) MU WM IMG);
      [lia|lia|exact HOFF|exact HI|exact OI|reflexivity|reflexivity|rewrite EM; reflexivity|exact HREL]. }
  pose proof (gs_output B mem mem' (HA + off) (HA + off + 4) MU IMG ltac:(lia) ltac:(lia) L A nout cap out HOUT) as OUT'.
  rewrite <- SEG.
  eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
    [exact HF|exact CB|intros; assumption|exact HW|].
  exists fx', L, A, R1, mem', md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), (upd_src off i hj).
  split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
  split; [exact MR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|].
  split; [rewrite short_target, upd_target; exact DK'|].
  split; [rewrite length_map; exact GL'|]. split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|]. split; [exact OUT'|]. split; [eapply relay_at_t; [exact REL'|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [rewrite length_map; exact Hes|]. split; [rewrite short_cost, upd_cost; exact Hcost|].
  rewrite upd_view, short_view. exact HRI.
Qed.

Lemma pass3_holds : check_bounded_contract -> forall RI, RI_mono RI -> pass_ok RI 3.
Proof.
  intros CB RI RIM B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 3) with 0x143a0 in HM.
  eapply SR_mono; [eapply (MI_flag B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 3 k) s c' 8 0x143a0 3);
    [exact HF|exact CB|left; reflexivity|reflexivity|discriminate|reflexivity|exact op3_run
    |exact (walk_pick E t k 3 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_intror (or_introl eq_refl)))|exact HM]|].
  intros c2 H2. exists (disp_k E 3 k). exact H2.
Qed.

Lemma pass6_holds : check_bounded_contract -> forall RI, RI_mono RI -> pass_ok RI 6.
Proof.
  intros CB RI RIM B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 6) with 0x143f4 in HM.
  eapply SR_mono; [eapply (MI_flag B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 6 k) s c' 12 0x143f4 6);
    [exact HF|exact CB|right; reflexivity|reflexivity|discriminate|reflexivity|exact op6_run
    |exact (walk_pick E t k 6 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_intror (or_intror (or_intror eq_refl))))|exact HM]|].
  intros c2 H2. exists (disp_k E 6 k). exact H2.
Qed.

Lemma MI_op8 : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> RI_mono RI ->
  walk_at (ss_pl E) (t + 1) (if K <? ss_n E then K + 1 else K) ->
  MI (rc := rc) B (API rc) E RI t K 0x14408 (fun _ hj no regs => no = 0 /\ disp_src 8 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB RIM HW HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 27 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  assert (ERR : errno_addr B = 0x31acc).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  assert (GA : forall a, 0x318a0 <= a < 0x31aa0 -> in_globals frame_G a).
  { intros a Ha. apply in_G_bss. lia. }
  assert (IMG : forall a, 0x318a0 <= a < 0x31aa0 -> in_img B a).
  { intros a Ha. exact (proj1 (FG a (GA a Ha))). }
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x14408 =? TAIL_CHECK) || (0x14408 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (_ & _ & (B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (HPK : K < ss_n E -> 0 < ss_p E + K < 2 ^ 64 - 1).
  { intros HK1. pose proof (proj1 (proj1 PRE)) as (MR0 & _).
    destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
    destruct PIN as [(HN & _)|(_ & p & HPp & EP)]; [lia|].
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p (ss_n E) 0 MR0 HPp ltac:(lia)) as (_ & P0 & P1 & _).
    rewrite EP in P0, P1. pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    lia. }
  assert (RB : K < ss_n E -> ov_read_bytes rsegs mem (Z_to_bv 64 (ss_p E + K)) 1 =
    Some [nth (Z.to_nat K) (ss_pl E) (Z_to_bv 8 0)]).
  { intros HK1. rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia]. }
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & _).
  assert (S1 : store_ok rsegs mem (Z_to_bv 64 0x318b0) 1 = true).
  { rewrite <- SEG. change (Z_to_bv 64 0x318b0) with (wa (G_EINTR + Z.of_nat 0)).
    eapply (rw_cells_store_ok _ _ _ _ 0%nat (C1 (Z_to_bv 8 ei))); [exact G7|reflexivity|reflexivity]. }
  assert (G11' : rw_cells (ms_segs B) (write_to_mem mem (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) G_OUTV
    [C8 mx; C8 nout; C8 cap; C8 out]).
  { pose proof (rw_cells_bound _ _ _ _ G11) as BD.
    apply rw_cells_frame; [exact G11|lia|rewrite length_le1; lia|right; apply Z.leb_le; vm_compute; reflexivity]. }
  assert (S2 : store_ok rsegs (write_to_mem mem (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) (Z_to_bv 64 0x318d8) 8 = true).
  { rewrite <- SEG. change (Z_to_bv 64 0x318d8) with (wa (G_OUTV + Z.of_nat 0)).
    eapply (rw_cells_store_ok _ _ _ _ 0%nat (C8 mx)); [exact G11'|reflexivity|reflexivity]. }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - K)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    apply (op8_run (ss_p E) (ss_n E) K); [lia|unfold INPUT_MAX in Hn; lia|exact HPK|exact RB|exact S1|exact S2]. }
  intros ms1 (can1 & (s0 & s10 & a0 & a1 & K' & -> & E0 & E10 & HCASE) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1). subst s0 s10.
  assert (KR : K <= K' <= ss_n E /\ bv_unsigned a0 <= 255).
  { destruct HCASE as [(HK1 & -> & ->)|(-> & -> & ->)].
    - split; [lia|]. unfold zxb.
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat K) (ss_pl E) (Z_to_bv 8 0))) as RB8.
      unfold bv_modulus in RB8. change (2 ^ Z.of_N 8) with 256 in RB8. rewrite unsigned_lit by lia. lia.
    - split; [lia|]. rewrite unsigned_lit by lia. lia. }
  assert (HW' : walk_at (ss_pl E) (t + 1) K').
  { destruct HCASE as [(HK1 & -> & _)|(HK1 & -> & _)].
    - rewrite (proj2 (Z.ltb_lt _ _) HK1) in HW. exact HW.
    - rewrite (proj2 (Z.ltb_ge K (ss_n E)) ltac:(lia)) in HW. exact HW. }
  clear HCASE.
  remember (write_to_mem mem (Z_to_bv 64 0x318b0) (le1 (Z_to_bv 64 1))) as m1 eqn:EM1.
  remember (write_to_mem m1 (Z_to_bv 64 0x318d8) (le8 a0)) as m2 eqn:EM2.
  assert (MU1 : munch [(0x318b0, 0x318b1)] mem m1).
  { rewrite EM1. change (Z_to_bv 64 0x318b0) with (wa 0x318b0).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le1; lia|cbn [inside]; left; rewrite length_le1; lia]. }
  assert (WM1 : wmono (ms_segs B) mem m1) by (rewrite EM1; apply wmono_write, wmono_refl).
  assert (MU2 : munch [(0x318d8, 0x318e0)] m1 m2).
  { rewrite EM2. change (Z_to_bv 64 0x318d8) with (wa 0x318d8).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|cbn [inside]; left; rewrite length_le8; lia]. }
  assert (WM2 : wmono (ms_segs B) m1 m2) by (rewrite EM2; apply wmono_write, wmono_refl).
  destruct (gs_keep B API LS SH SK ra empty rc fx j E CS L A mem m1 md (target_addrs G (bv_unsigned out) es hj)
    0x318b0 0x318b1 HF MU1 WM1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; eapply cells_writable; [exact G7|change (0x318b0 <= a < 0x318b0 + 1); lia])
    HMR HRO HIK HST HDK) as (MR1 & RO1 & IK1 & ST1 & DK1).
  destruct (gs_keep B API LS SH SK ra empty rc fx j E CS L A m1 m2 md (target_addrs G (bv_unsigned out) es hj)
    0x318d8 0x318e0 HF MU2 WM2 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; eapply cells_writable; [exact G11'|change (0x318d8 <= a < 0x318d8 + 32); lia])
    MR1 RO1 IK1 ST1 DK1) as (MR2 & RO2 & IK2 & ST2 & DK2).
  pose proof (gs_relay B mem m1 0x318b0 0x318b1 MU1 WM1 IMG ltac:(lia) ltac:(lia) L A t nfd G (bv_unsigned out) es hj
    ltac:(unfold G_S; lia) HREL) as REL1.
  pose proof (gs_relay B m1 m2 0x318d8 0x318e0 MU2 WM2 IMG ltac:(lia) ltac:(lia) L A t nfd G (bv_unsigned out)
    (map short_entry es) hj ltac:(unfold G_S; lia) REL1) as REL2.
  pose proof (gs_output B mem m1 0x318b0 0x318b1 MU1 IMG ltac:(lia) ltac:(lia) L A nout cap out HOUT) as OUT1.
  pose proof (gs_output B m1 m2 0x318d8 0x318e0 MU2 IMG ltac:(lia) ltac:(lia) L A nout cap out OUT1) as OUT2.
  assert (GL2 : globals_at B m2 cl br gn dd 1 (Z.of_nat (length es)) G nfd a0 nout cap out).
  { rewrite EM2, EM1. exact (globals_op8 B mem cl br gn dd ei _ G nfd mx nout cap out a0 ERR (proj2 KR) HGL). }
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K' (fun _ _ _ r => tail_regs E t K' r));
    [exact HF|exact CB|intros; assumption|exact HW'|]|intros c' HC; exists K'; exact HC].
  exists fx', L, A, R1, m2, md, cl, br, gn, dd, 1, G, nfd, a0, nout, cap, out, (map short_entry (map short_entry es)), hj.
  split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
  split; [exact MR2|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact RO2|]. split; [exact IK2|]. split; [exact ST2|].
  split; [rewrite !short_target; exact DK2|].
  split; [rewrite !length_map; exact GL2|]. split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|]. split; [exact OUT2|]. split; [eapply relay_at_t; [exact REL2|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [rewrite !length_map; exact Hes|]. split; [rewrite !short_cost; lia|].
  rewrite !short_view. eapply RIM; [exact HRI|lia].
Qed.

Lemma pass8_holds : check_bounded_contract -> forall RI, RI_mono RI -> pass_ok RI 8.
Proof.
  intros CB RI RIM B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 8) with 0x14408 in HM.
  assert (HW8 : walk_at (ss_pl E) (t + 1) (if disp_k E 8 k <? ss_n E then disp_k E 8 k + 1 else disp_k E 8 k)).
  { change (disp_k E 8 k) with (k + 1). replace (k + 1 + 1) with (k + 2) by lia.
    exact (walk_one E t k 8 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_intror (or_introl eq_refl))). }
  exact (MI_op8 B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 8 k) s c' HF CB RIM HW8 HM).
Qed.
