(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotPass1 SlotWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c pthread_mutex_lock_ro pthread_mutex_unlock_ro.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op9g_pre : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b : byte),
  0 <= K < N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b] -> Z.odd (bv_unsigned b) = true ->
  evt rsegs (fun ms => exists (s0 s1 a0 s10 : word),
      ms = MS (mkR (Z_to_bv 64 0x1444c) x2 x3 x4 x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19
        (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 s10 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1e7a8) fc None m ro /\
      s0 = Z_to_bv 64 0x318f8 /\ a0 = Z_to_bv 64 0x318f8 /\ s1 = Z_to_bv 64 (P + K + 1) /\
      s10 = Z_to_bv 64 (N - K - 1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F
      (Z_to_bv 64 0x14424) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m ro b HK HN HP0 HPN RB ODD.
  assert (LAND1 : Z.land (bv_unsigned (zxb b)) 1 = 1).
  { unfold zxb. pose proof (bv_unsigned_in_range 8 b) as RB8. unfold bv_modulus in RB8.
    change (2 ^ Z.of_N 8) with 256 in RB8. rewrite unsigned_lit by lia.
    change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    rewrite Zmod_odd, ODD. reflexivity. }
  assert (LAND2 : Z.land (bv_unsigned (zxb b)) (bv_wrap 64 1) = 1).
  { change (bv_wrap 64 1) with 1. exact LAND1. }
  step. if_cases HC.
  - exfalso. unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia.
  - step. step. if_cases HT.
    + exfalso. zify_cond HT. lia.
    + step. step. step. step. if_cases HA.
      * exfalso.
        first [ (unfold bv_eqb in HA; rewrite ?LAND1, ?LAND2 in HA; rewrite !unsigned_lit in HA by lia;
                 apply Z.eqb_eq in HA; lia)
              | let T := type of HA in fail 100 "HA:" T ].
      * step. step. step. apply evt_done. do 4 eexists. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; f_equal; lia.
Qed.

Lemma op9g_mid : forall (SP : Z)
    (x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 SP) 8 = Some (le8 (Z_to_bv 64 0x210e4)) ->
  store_ok rsegs m (Z_to_bv 64 0x21624) 4 = true ->
  evt rsegs (fun ms => exists (a0 a1 : word),
      ms = MS (mkR (Z_to_bv 64 0x14460) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 0x318f8) x9 a0 a1 x12 x13 x14 x15
        x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1ec94) fc None
        (write_to_mem m (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) ro /\ a0 = Z_to_bv 64 0x318f8)
    (MS (mkR (Z_to_bv 64 0x1444c) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 0x318f8) x9 x10 x11 x12 x13 x14 x15
      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1444c) fc None m ro).
Proof.
  intros SP x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro RD SO.
  step. step. step. step. step. apply evt_done. do 2 eexists. split; reflexivity.
Qed.

Lemma op9g_end : forall (P K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  store_ok rsegs m (Z_to_bv 64 0x318a8) 1 = true ->
  evt rsegs (fun ms => exists (s0 a5 : word),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 (Z_to_bv 64 (P + K + 1)) x10 x11 x12 x13 x14 a5 x16 x17
        x18 x19 (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK)
        fc None (write_to_mem m (Z_to_bv 64 0x318a8) (le1 (Z_to_bv 64 1))) ro /\ s0 = Z_to_bv 64 (P + K + 1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (P + K + 1)) x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14460) fc None
      m ro).
Proof.
  intros P K x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31
    F fc m ro SO.
  step. step. step. step. apply evt_done. do 2 eexists. split; [reflexivity|]. f_equal; lia.
Qed.

Definition g9_W (SP : Z) : list (Z * Z) :=
  [(SP - 96, SP); (0x21624, 0x21628); (0x318a8, 0x318a9); (0x318fc, 0x31900)].

Lemma g9_dj_sub : forall (W : list (Z * Z)) a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H HW]. split; [lia|exact (IH a n a' n' HW H1 H2)].
Qed.

Lemma g9_cases : forall SP a, outside (g9_W SP) a \/
  (0x21624 <= a < 0x21628 \/ 0x318a8 <= a < 0x318a9 \/ 0x318fc <= a < 0x31900) \/ (SP - 96 <= a < SP).
Proof. intros SP a. unfold g9_W. cbn [outside]. lia. Qed.

Lemma g9_img : forall B, ms_segs B = rsegs -> forall a, 0x21000 <= a < 0x53000 -> in_img B a.
Proof.
  intros B SEG a Ha.
  assert (C : existsb (fun s => (bv_unsigned (fst s) =? 0x21000) && (bv_unsigned (snd s) =? 0x32000))
    (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  apply existsb_exists in C. destruct C as (s & HS & HB). apply andb_true_iff in HB. destruct HB as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  unfold in_img. rewrite SEG. split.
  - intro HN. rewrite HN in HS. cbn in HS. exact HS.
  - exists s. split; [exact HS|lia].
Qed.

Lemma g9_listen_not_ro : forall a, 0x21620 <= a < 0x21630 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  assert (C : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x21620 + Z.of_nat i)))) (seq 0 16) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat (a - 0x21620))).
  rewrite Z2Nat.id in C by lia. replace (0x21620 + (a - 0x21620)) with a in C by lia.
  apply negb_true_iff. apply C. apply in_seq. lia.
Qed.

Lemma g9_in_listen : forall a, 0x21620 <= a < 0x21630 -> in_globals frame_G a.
Proof. intros a H. exists 0x21620, 16. split; [left; reflexivity|lia]. Qed.

Lemma g9_glob_not_ro : forall a, in_globals frame_G a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a (lo & len & HI & HA). unfold frame_G in HI. destruct HI as [EE|[EE|[]]]; inversion EE; subst.
  - apply g9_listen_not_ro. lia.
  - apply sp_ro_glob. lia.
Qed.

Lemma g9_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma g9_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma g9_ro_munch : forall (W : list (Z * Z)) m m', munch W m m' ->
  (forall a, ro_addr rsegs a = true -> outside W (bv_unsigned a)) ->
  MemNorm.ro_agree rsegs m -> MemNorm.ro_agree rsegs m'.
Proof. intros W m m' MU HO RO a HA. unfold mrd. rewrite (MU a (HO a HA)). exact (RO a HA). Qed.

Lemma op9g_run : pthread_mutex_lock_ro_contract -> pthread_mutex_unlock_ro_contract ->
  forall (P N K SP cl gn : Z)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : byte),
  0 <= K < N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b] -> Z.odd (bv_unsigned b) = true ->
  0x31b00 <= SP - 96 -> SP < 2 ^ 64 ->
  stk rsegs m (SP - 96) SP -> RoAdapt.not_ro rsegs (SP - 96) 96 ->
  rw_cells rsegs m SP [C8 (Z_to_bv 64 0x210e4)] ->
  rw_cells rsegs m 0x21620 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 cl)] ->
  rw_cells rsegs m 0x318a8 [C1 (Z_to_bv 8 gn)] ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  MemNorm.ro_agree rsegs m ->
  evt rsegs (fun ms => exists (y1 y5 y6 y7 s0 y9 y10 y11 y12 y13 y14 y15 y16 y17 s10 y28 y29 y30 y31 : word)
      (m' : word -> option byte),
      ms = MS (mkR y1 (Z_to_bv 64 SP) x3 x4 y5 y6 y7 s0 y9 y10 y11 y12 y13 y14 y15 y16 y17
        x18 x19 (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 s10 x27 y28 y29 y30 y31)
        F (Z_to_bv 64 TAIL_CHECK) fc None m' (seg_rom rsegs) /\
      s0 = Z_to_bv 64 (P + (K + 1)) /\ s10 = Z_to_bv 64 (N - (K + 1)) /\
      munch (g9_W SP) m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' 0x21620 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
      rw_cells rsegs m' 0x318a8 [C1 (Z_to_bv 8 1)] /\
      rw_cells rsegs m' 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x14424) fc None m (seg_rom rsegs)).
Proof.
  intros LCK ULK P N K SP cl gn x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27
    x28 x29 x30 x31 F fc m b HK HN HP0 HPN RB ODD SPL SPH ST NRO CS CL CG CK RO.
  destruct (g9_cut _ _ [_] [_; _] CK) as [K0 K12].
  destruct (g9_cut _ _ [_] [_] K12) as [K1 K2]. clear K12.
  assert (K1' : rw_cells rsegs m 0x318fc [C4 (Z_to_bv 64 0)]) by exact K1.
  assert (K2' : rw_cells rsegs m 0x31900 [C4 (Z_to_bv 64 0)]) by exact K2.
  clear K1 K2.
  assert (TB : bytes_at rsegs m 0x318f8 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 K0)) as B0. cbn [cells_bytes cbytes] in B0. rewrite app_nil_r in B0.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B0. apply bytes_at_app in B0. exact (proj1 B0). }
  eapply evt_cut; [eapply (op9g_pre P N K); [exact HK|exact HN|exact HP0|exact HPN|exact RB|exact ODD]|].
  intros ms0 (s0 & s1 & a0 & s10 & -> & -> & -> & -> & ->).
  eapply evt_cut.
  { eapply (LCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8
      (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))));
      [reflexivity|exact TB|reflexivity|exact K1'|intros i Hi; unfold wa; apply sp_ro_glob; cbn in Hi; lia|exact RO]. }
  intros ms1 PO. unfold pthread_mutex_lock_post_ro in PO.
  destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & -> & MU1 & WM1 & RO1 & L16).
  rewrite (ret_pc_even 0x1444c) by lia.
  assert (D1 : forall A cs, rw_cells rsegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x318fc \/ 0x31900 <= A ->
    rw_cells rsegs m1 A cs).
  { intros A cs H D. eapply rw_cells_transport; [exact H|exact MU1|exact WM1|]. cbn [disjoint_from]. split; [lia|exact I]. }
  pose proof (D1 _ _ CS ltac:(cbn; lia)) as CS1.
  pose proof (D1 _ _ CL ltac:(cbn; lia)) as CL1.
  pose proof (D1 _ _ CG ltac:(cbn; lia)) as CG1.
  pose proof (D1 _ _ K0 ltac:(cbn; lia)) as K01.
  pose proof (D1 _ _ K2' ltac:(cbn; lia)) as K21.
  assert (ST1 : stk rsegs m1 (SP - 96) SP).
  { eapply stk_transport_disjoint; [exact ST|exact MU1|exact WM1|cbn [disjoint_from]; split; [lia|exact I]]. }
  assert (RD : ov_read_bytes rsegs m1 (Z_to_bv 64 SP) 8 = Some (le8 (Z_to_bv 64 0x210e4))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C8 (Z_to_bv 64 0x210e4)) CS1 eq_refl) as R0.
    change (Z.of_nat 0) with 0 in R0. rewrite Z.add_0_r in R0. exact R0. }
  assert (SO : store_ok rsegs m1 (Z_to_bv 64 0x21624) 4 = true).
  { change (Z_to_bv 64 0x21624) with (wa (0x21620 + Z.of_nat 4)).
    eapply (rw_cells_store_ok _ _ _ _ 4%nat (C4 (Z_to_bv 64 cl))); [exact CL1|reflexivity|reflexivity]. }
  eapply evt_cut; [apply op9g_mid; [exact RD|exact SO]|].
  intros ms2 (a0' & a1' & -> & ->).
  assert (F2 : forall A cs, rw_cells rsegs m1 A cs -> A + Z.of_nat (cells_size cs) <= 0x21624 \/ 0x21628 <= A ->
    rw_cells rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) A cs).
  { intros A cs H D. apply rw_cells_frame; [exact H|lia|rewrite length_le4; lia|rewrite length_le4; lia]. }
  assert (KK : rw_cells rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) 0x318f8
    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]).
  { apply F2; [|cbn; lia].
    apply (g9_join _ _ (0x318f8 + 4) [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] K01); [|reflexivity].
    apply (g9_join _ _ 0x31900 [C4 (Z_to_bv 64 16)] [C4 (Z_to_bv 64 0)] L16); [exact K21|reflexivity]. }
  assert (ST2 : stk rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) (SP - 96) SP).
  { apply stk_write; [exact ST1|lia|rewrite length_le4; lia]. }
  assert (RO2 : MemNorm.ro_agree rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1))))).
  { apply (g9_ro_munch [(0x21624, 0x21628)] m1).
    - change (Z_to_bv 64 0x21624) with (wa 0x21624).
      eapply munch_write; [apply munch_refl|lia|rewrite length_le4; lia|cbn [inside]; left; rewrite length_le4; lia].
    - intros a HA. cbn [outside]. split; [|exact I]. intro HX.
      pose proof (g9_listen_not_ro (bv_unsigned a) ltac:(lia)) as HNR. rewrite Z_to_bv_bv_unsigned in HNR. congruence.
    - exact RO1. }
  eapply evt_cut.
  { eapply (ULK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8 (SP - 96));
      [reflexivity|exact KK|intros i Hi; unfold wa; apply sp_ro_glob; cbn in Hi; lia
      |rewrite unsigned_lit by lia; exact ST2
      |rewrite unsigned_lit by lia; replace (SP - (SP - 96)) with 96 by lia; exact NRO
      |rewrite unsigned_lit by lia; lia|rewrite unsigned_lit by lia; lia|exact RO2]. }
  intros ms3 PO. unfold pthread_mutex_unlock_post_ro in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & RO3 & ST3 & K3).
  rewrite (ret_pc_even 0x14460) by lia.
  rewrite unsigned_lit in MU3 by lia.
  assert (D3 : forall A cs, rw_cells rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) A cs ->
    A + Z.of_nat (cells_size cs) <= 0x318fc \/ 0x31900 <= A -> A + Z.of_nat (cells_size cs) <= SP - 96 ->
    rw_cells rsegs m3 A cs).
  { intros A cs H D E. eapply rw_cells_transport; [exact H|exact MU3|exact WM3|].
    cbn [disjoint_from]. split; [lia|]. split; [lia|exact I]. }
  pose proof (D3 _ _ (F2 _ _ CG1 ltac:(cbn; lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as CG3.
  assert (CL2 : rw_cells rsegs (write_to_mem m1 (Z_to_bv 64 0x21624) (le4 (Z_to_bv 64 (-1)))) 0x21620
    [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))]).
  { exact (rw_cells_write _ _ _ _ 4%nat (C4 (Z_to_bv 64 cl)) (C4 (Z_to_bv 64 (-1))) CL1 eq_refl eq_refl I). }
  pose proof (D3 _ _ CL2 ltac:(cbn; lia) ltac:(cbn; lia)) as CL3.
  assert (SO3 : store_ok rsegs m3 (Z_to_bv 64 0x318a8) 1 = true).
  { change (Z_to_bv 64 0x318a8) with (wa (0x318a8 + Z.of_nat 0)).
    eapply (rw_cells_store_ok _ _ _ _ 0%nat (C1 (Z_to_bv 8 gn))); [exact CG3|reflexivity|reflexivity]. }
  eapply evt_cut; [apply (op9g_end P K); exact SO3|].
  intros ms4 (s0' & a5' & -> & ->).
  apply evt_done.
  do 20 eexists. split; [reflexivity|].
  split; [f_equal; lia|]. split; [f_equal; lia|].
  split.
  { change (Z_to_bv 64 0x318a8) with (wa 0x318a8).
    eapply munch_write; [|lia|rewrite length_le1; lia|unfold g9_W; cbn [inside]; right; right; left; rewrite length_le1; lia].
    eapply munch_trans; [|eapply munch_weaken; [|exact MU3]].
    - change (Z_to_bv 64 0x21624) with (wa 0x21624).
      eapply munch_write; [|lia|rewrite length_le4; lia|unfold g9_W; cbn [inside]; right; left; rewrite length_le4; lia].
      eapply munch_weaken; [|exact MU1]. intros x HX. unfold g9_W in HX. cbn [outside] in HX |- *.
      destruct HX as (H1 & H2 & H3 & H4 & _). split; [lia|exact I].
    - intros x HX. unfold g9_W in HX. cbn [outside] in HX |- *.
      destruct HX as (H1 & H2 & H3 & H4 & _). split; [lia|]. split; [lia|exact I]. }
  split.
  { apply wmono_write. eapply wmono_trans; [|exact WM3]. apply wmono_write. exact WM1. }
  split; [apply rw_cells_frame; [exact CL3|lia|rewrite length_le1; lia|rewrite length_le1; cbn; lia]|].
  split; [exact (rw_cells_write _ _ _ _ 0%nat (C1 (Z_to_bv 8 gn)) (C1 (Z_to_bv 8 1)) CG3 eq_refl eq_refl I)|].
  apply rw_cells_frame; [exact K3|lia|rewrite length_le1; lia|rewrite length_le1; cbn; lia].
Qed.

Section G9Fresh.
Context {rc : RunCeil}.

Lemma g9_fresh_apart : forall B a n lo hi c d, fresh_block B a n -> 0 < n ->
  (forall x, c <= x < d -> in_img B x) -> c <= lo - 7 -> lo <= hi -> hi <= d ->
  a + (n + 7) <= lo \/ hi <= a.
Proof.
  intros B a n lo hi c d (_ & _ & NI) HN IMG H1 H2 H3.
  destruct (Z_le_gt_dec (a + (n + 7)) lo) as [H|H]; [left; exact H|right].
  destruct (Z_le_gt_dec hi a) as [HA|HA]; [exact HA|exfalso].
  destruct (Z_le_gt_dec c a) as [A0|A0].
  - apply (NI 0 ltac:(lia)), IMG. lia.
  - apply (NI (c - a) ltac:(lia)), IMG. lia.
Qed.

Lemma g9_fresh : forall B SP a n, ms_segs B = rsegs -> @YM05.alloc_ceiling rc + 7 <= SP - 96 ->
  fresh_block B a n -> 0 < n -> disjoint_from (g9_W SP) a (n + 7).
Proof.
  intros B SP a n SEG HS FR HN. pose proof FR as (F0 & F1 & _).
  pose proof (g9_img B SEG) as IH.
  unfold g9_W. cbn [disjoint_from]. split; [left; lia|].
  split; [exact (g9_fresh_apart B a n 0x21624 0x21628 0x21000 0x53000 FR HN IH ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (g9_fresh_apart B a n 0x318a8 0x318a9 0x21000 0x53000 FR HN IH ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (g9_fresh_apart B a n 0x318fc 0x31900 0x21000 0x53000 FR HN IH ltac:(lia) ltac:(lia) ltac:(lia))|exact I].
Qed.

End G9Fresh.

Section G9Store.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variables (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono (ms_segs B) m m'.
Hypothesis FA : forall a n, fresh_block B a n -> 0 < n -> disjoint_from W a (n + 7).
Hypothesis SA : disjoint_from W G_S 384.

Lemma g9_bytes : forall a bs, bytes_at (ms_segs B) m a bs -> disjoint_from W a (Z.of_nat (length bs)) ->
  bytes_at (ms_segs B) m' a bs.
Proof. intros a bs H D. eapply bytes_at_transport; [exact H|exact MU|exact D]. Qed.
Lemma g9_cells : forall a cs, rw_cells (ms_segs B) m a cs -> disjoint_from W a (Z.of_nat (cells_size cs)) ->
  rw_cells (ms_segs B) m' a cs.
Proof. intros a cs H D. eapply rw_cells_transport; [exact H|exact MU|exact WM|exact D]. Qed.
Lemma g9_fresh_bytes : forall a n bs, fresh_block B a n -> 0 < n ->
  Z.of_nat (length bs) <= n + 7 -> bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a bs.
Proof. intros a n bs FR HN HL HB. apply g9_bytes; [exact HB|]. eapply g9_dj_sub; [exact (FA a n FR HN)|lia|lia]. Qed.
Lemma g9_fresh_cells : forall a n cs, fresh_block B a n -> 0 < n ->
  Z.of_nat (cells_size cs) <= n -> rw_cells (ms_segs B) m a cs -> rw_cells (ms_segs B) m' a cs.
Proof. intros a n cs FR HN HL HB. apply g9_cells; [exact HB|]. eapply g9_dj_sub; [exact (FA a n FR HN)|lia|lia]. Qed.

Lemma g9_entry : forall L A e, CF.RelayRep.entry_ok B L A m e -> CF.RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold CF.RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    eapply g9_fresh_cells; [exact FR|exact C|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|exact BC]. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply g9_fresh_bytes; [exact FR|lia| |exact HB].
      rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { eapply g9_fresh_bytes; [exact FR|lia| |].
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length]. rewrite length_firstn. lia.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt))
        (firstn 8 (Z_to_bv 8 0 :: slack))). apply bytes_at_prefix. exact HT. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma g9_list : forall L A LA l lines,
  disjoint_from W LA 16 -> list_at B L A m LA l lines -> list_at B L A m' LA l lines.
Proof.
  intros L A LA l lines HLA (C & HN & AR & ND1 & ND2 & RS).
  split; [apply g9_cells; [exact C|exact HLA]|]. split; [exact HN|]. split.
  { destruct AR as [AR|(HC & IN & FR & HJ & HA)]; [left; exact AR|right].
    split; [exact HC|]. split; [exact IN|]. split; [exact FR|]. split; [exact HJ|].
    eapply g9_fresh_cells; [exact FR|lia| |exact HA]. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  split; [exact ND1|]. split; [exact ND2|]. eapply Forall_impl; [|exact RS].
  intros r (IN & FR & CR & R1 & R2). split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply g9_fresh_cells; [exact FR|lia|cbn; lia|exact CR].
Qed.

Lemma g9_src : forall L A HA h, disjoint_from W HA 96 -> src_at B L A m HA h -> src_at B L A m' HA h.
Proof.
  intros L A HA h HHA (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND).
  split; [apply g9_cells; [exact C1|eapply g9_dj_sub; [exact HHA|lia|cbn; lia]]|].
  do 4 (split; [assumption|]). split; [apply g9_list; [eapply g9_dj_sub; [exact HHA|lia|lia]|exact LP]|].
  split; [apply g9_cells; [exact C2|eapply g9_dj_sub; [exact HHA|lia|cbn; lia]]|]. do 6 (split; [assumption|]). split.
  { eapply g9_fresh_cells; [exact FR|lia|cbn; lia|exact C3]. }
  split; [exact NZ|]. split; [apply g9_list; [eapply g9_dj_sub; [exact HHA|lia|lia]|exact LE]|].
  split; [apply g9_list; [eapply g9_dj_sub; [exact HHA|lia|lia]|exact LH]|exact ND].
Qed.

Lemma g9_output : forall L A no cap out, output_at (rc := rc) B L A m no cap out ->
  output_at (rc := rc) B L A m' no cap out.
Proof.
  intros L A no cap out ((O & junk & H) & CAP). split; [|exact CAP]. exists O, junk.
  destruct H as [H|(HC & HN & IN & FR & BY & LO & LJ)]; [left; exact H|right].
  split; [exact HC|]. split; [exact HN|]. split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply g9_fresh_bytes; [exact FR|exact HC|rewrite length_app; lia|exact BY].
Qed.

Lemma g9_relay : forall L A t nfd G OUT es hj,
  relay_at (rc := rc) B L A m t nfd G OUT es hj ->
  relay_at (rc := rc) B L A m' t nfd G OUT (map short_entry es) hj.
Proof.
  intros L A t nfd G OUT es hj ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA).
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply short_entry_bytes. }
    rewrite EB. eapply g9_fresh_cells; [exact FR|unfold SRC_TABLE, SRC_ENTRY; lia|cbn; unfold SRC_TABLE, SRC_ENTRY; lia|exact TC]. }
  split; [exact IN|]. split; [exact FR|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact ES]. intros e HE. exact (g9_entry L A e HE). }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { clear HT TC IN FR ES ND FD NDH ZH NDA.
    induction PA as [|e p es hj HE HP IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
    unfold pair_ok in *. cbv zeta in *. cbn [short_entry re_keys re_fd re_skip re_used re_eof re_U].
    rewrite short_keys_texts. destruct HE as (SRC & HI & REST).
    split; [apply g9_src; [eapply g9_dj_sub; [exact SA| |]; unfold SRC_SIZE; lia|exact SRC]|]. split; assumption. }
  split; [exact NDH|]. split.
  { intros i HI HZ. apply g9_cells; [exact (ZH i HI HZ)|]. eapply g9_dj_sub; [exact SA| |]; cbn; unfold SRC_SIZE; lia. }
  rewrite short_target. exact NDA.
Qed.

End G9Store.

Lemma g9_keep : forall B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  munch (g9_W (slot_sp E)) mem mem' -> wmono (ms_segs B) mem mem' ->
  (forall a, 0x21624 <= a < 0x21628 \/ 0x318a8 <= a < 0x318a9 \/ 0x318fc <= a < 0x31900 ->
     writable_at (ms_segs B) mem a) ->
  aa_MR (API rc) L A mem md -> ro_agree (ms_segs B) mem -> image_kept (rc := rc) B E mem ->
  stack_mid B E mem -> driver_kept B E TA L A mem ->
  aa_MR (API rc) L A mem' md /\ ro_agree (ms_segs B) mem' /\ image_kept (rc := rc) B E mem' /\
  stack_mid B E mem' /\ driver_kept B E TA L A mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA HF MU WM MWR HMR HRO HIK HST HDK.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 27 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  pose proof FF as FFA. do 31 (destruct FFA as [_ FFA]). specialize (FFA fx).
  do 12 (destruct FFA as [_ FFA]). destruct FFA as (AX & UNG & _).
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPB : @YM05.alloc_ceiling rc + 65000 <= slot_sp E - 96 /\ slot_sp E < 2 ^ 63).
  { unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (OL : forall a, 0 <= a < @YM05.alloc_ceiling rc -> ~ in_globals frame_G a -> outside (g9_W (slot_sp E)) a).
  { intros a Ha HG. destruct (g9_cases (slot_sp E) a) as [H|[H|H]]; [exact H| |lia].
    exfalso. apply HG. destruct H as [H|[H|H]]; [apply g9_in_listen; lia|apply in_G_bss; lia|apply in_G_bss; lia]. }
  assert (OH : forall a, @YM05.alloc_ceiling rc <= a < 2 ^ 64 -> ~ lib_scratch B SLOT_STACK (ss_regs E) a ->
    outside (g9_W (slot_sp E)) a).
  { intros a Ha HS. destruct (g9_cases (slot_sp E) a) as [H|[H|H]]; [exact H|lia|].
    exfalso. apply HS. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> outside (g9_W (slot_sp E)) a ->
    mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha HO. split; [exact (munch_mbyte _ _ _ _ a MU Ha HO)|exact (munch_writable _ _ _ _ a MU Ha HO)]. }
  assert (BX : forall L0 A0 m0 md0 p n i,
    aa_MR (API rc) L0 A0 m0 md0 -> In (p, n) (user_blocks A0) -> 0 <= i < n ->
    0 <= ptr_addr L0 p + i < 2 ^ 64 /\ outside (g9_W (slot_sp E)) (ptr_addr L0 p + i)).
  { intros L0 A0 m0 md0 p n i HM HP HI.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HM HP HI) as (_ & B0 & B1 & _).
    split; [lia|]. apply OL; [lia|]. intro HX.
    apply (ax_blocks_img AX L0 A0 m0 md0 p n i HM HP HI). exact (proj1 (FG _ HX)). }
  split.
  { apply (mr_frame _ _ (aa_laws (API rc)) L A mem mem' md md HMR).
    - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      apply EQ; [lia|]. apply OL; [exact HA|]. intro HX. exact (UNG L A mem md a HMR HX HO).
    - intros a HO HP. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      eapply munch_present; [exact MU|lia| |exact HP]. apply OL; [exact HA|]. intro HX.
      exact (UNG L A mem md a HMR HX HO).
    - intros p n i HP HI. destruct (BX L A mem md p n i HMR HP HI) as [HR HO].
      eapply munch_present; [exact MU|exact HR|exact HO|].
      exact (proj1 (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HMR HP HI)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split.
  { intros a HA. unfold mrd. rewrite (MU a); [apply HRO; exact HA|].
    pose proof (bv_unsigned_in_range 64 a) as AB. change (bv_modulus 64) with (2 ^ 64) in AB.
    destruct (g9_cases (slot_sp E) (bv_unsigned a)) as [H|[H|H]]; [exact H|exfalso|exfalso].
    - assert (HG : in_globals frame_G (bv_unsigned a)).
      { destruct H as [H|[H|H]]; [apply g9_in_listen; lia|apply in_G_bss; lia|apply in_G_bss; lia]. }
      pose proof (g9_glob_not_ro _ HG) as HN. rewrite Z_to_bv_bv_unsigned, <- SEG in HN. congruence.
    - pose proof (ro_in_img B SEG (bv_unsigned a) AB) as RI0. rewrite Z_to_bv_bv_unsigned, <- SEG in RI0.
      specialize (RI0 HA). pose proof (in_img_low B SEG _ RI0) as AL. lia. }
  split.
  { destruct HIK as (I1 & I2 & I3 & I4). split.
    - intros a HA H1 H2 H3 H4. destruct (I1 a HA H1 H2 H3 H4) as [EA WA].
      pose proof (in_img_low B SEG a HA) as AR.
      assert (HO : outside (g9_W (slot_sp E)) a) by (apply OL; [lia|exact H4]).
      destruct (EQ a ltac:(lia) HO) as [EB WB]. split; [congruence|tauto].
    - split.
      + intros a HA. pose proof (I2 a HA) as WA.
        assert (AR : 0 <= a < 2 ^ 64).
        { unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EE|[EE|[]]] & HR); inversion EE; subst; lia. }
        destruct (g9_cases (slot_sp E) a) as [H|[H|H]].
        * destruct (EQ a AR H) as [EB WB]. tauto.
        * pose proof (MWR a H) as W0. pose proof (WM (Z_to_bv 64 a) W0) as W1. tauto.
        * assert (W0 : writable_at (ms_segs B) mem a).
          { apply I4. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
          pose proof (WM (Z_to_bv 64 a) W0) as W1. tauto.
      + split.
        * intros a HA HNS. destruct (I3 a HA HNS) as [EA WA].
          destruct (EQ a ltac:(lia) (OH a HA HNS)) as [EB WB]. split; [congruence|tauto].
        * intros a HA. apply WM. exact (I4 a HA). }
  split.
  { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [eapply rw_cells_transport; [exact ST1|exact MU|exact WM|unfold g9_W; cbn [disjoint_from]; repeat split; right; lia]|].
    split; [eapply rw_cells_transport; [exact ST2|exact MU|exact WM|unfold g9_W; cbn [disjoint_from]; repeat split; right; lia]|].
    eapply rw_cells_transport; [exact ST3|exact MU|exact WM|unfold g9_W; cbn [disjoint_from]; repeat split; right; lia]. }
  destruct HDK as (D1 & D2 & D3 & D4). split; [exact D1|]. split.
  - intros p n i HP HNT HNP HI. destruct (BX _ _ _ _ p n i MR0 HP HI) as [AR AO].
    rewrite (proj1 (EQ _ AR AO)). exact (D2 p n i HP HNT HNP HI).
  - split; [|exact D4]. intros i HI.
    destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
    destruct PIN as [(HN & _)|(HN & p & HP & EP)]; [lia|].
    destruct (BX _ _ _ _ p (ss_n E) i MR0 HP HI) as [AR AO]. rewrite EP in AR, AO.
    rewrite (proj1 (EQ _ AR AO)). exact (D3 i HI).
Qed.

Lemma globals_op9g : forall B SP m m' cl br gn dd ei N G nfd mx no cap out,
  errno_addr B = 0x31acc -> 0x31ad0 <= SP - 96 ->
  munch (g9_W SP) m m' -> wmono (ms_segs B) m m' ->
  rw_cells (ms_segs B) m' G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] ->
  rw_cells (ms_segs B) m' G_GONE [C1 (Z_to_bv 8 1)] ->
  rw_cells (ms_segs B) m' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out ->
  globals_at B m' (-1) br 1 dd ei N G nfd mx no cap out.
Proof.
  intros B SP m m' cl br gn dd ei N G nfd mx no cap out ERR SPB MU WM CL CG CK
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & HCL & HBR & HGN & HDD & HEI & HGG & HMX).
  assert (T : forall A cs, rw_cells (ms_segs B) m A cs ->
    (A + Z.of_nat (cells_size cs) <=? 0x31ad0) && ((A + Z.of_nat (cells_size cs) <=? 0x21624) || (0x21628 <=? A)) &&
    ((A + Z.of_nat (cells_size cs) <=? 0x318a8) || (0x318a9 <=? A)) &&
    ((A + Z.of_nat (cells_size cs) <=? 0x318fc) || (0x31900 <=? A)) = true -> rw_cells (ms_segs B) m' A cs).
  { intros A cs H D. rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le in D.
    destruct D as (((D0 & D1) & D2) & D3).
    eapply rw_cells_transport; [exact H|exact MU|exact WM|]. unfold g9_W. cbn [disjoint_from].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
  unfold globals_at.
  split; [exact CL|].
  split; [apply T; [exact G2|reflexivity]|].
  split; [apply T; [exact G3|reflexivity]|].
  split; [apply T; [exact G4|reflexivity]|].
  split; [exact CG|].
  split; [apply T; [exact G6|reflexivity]|].
  split; [apply T; [exact G7|reflexivity]|].
  split; [apply T; [exact G8|reflexivity]|].
  split; [apply T; [exact G9|reflexivity]|].
  split; [apply T; [exact G10|reflexivity]|].
  split; [apply T; [exact G11|reflexivity]|].
  split; [exact CK|].
  split; [apply T; [exact G13|reflexivity]|].
  split; [destruct ER as [ev ER]; exists ev; apply T; [exact ER|rewrite ERR; reflexivity]|].
  split; [right; reflexivity|]. split; [exact HBR|]. split; [right; reflexivity|]. split; [exact HDD|].
  split; [exact HEI|]. split; [split; [intros HX; discriminate HX|intros _; left; reflexivity]|]. exact HMX.
Qed.

Lemma MI_op9g : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract ->
  pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> RI_mono RI ->
  K < ss_n E -> Z.odd (in_byte E K) = true -> walk_at (ss_pl E) (t + 1) (K + 1) ->
  MI (rc := rc) B (API rc) E RI t K OP9_AT
    (fun _ hj no regs => no = 0 /\ disp_src 9 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB LCK ULK RIM HKN HODD HW HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (ERR : errno_addr B = 0x31acc).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPB : @YM05.alloc_ceiling rc + 65000 <= slot_sp E - 96 /\ slot_sp E < 2 ^ 63).
  { unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (OP9_AT =? TAIL_CHECK) || (OP9_AT =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold OP9_AT, TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (_ & _ & (B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (RB : ov_read_bytes rsegs mem (Z_to_bv 64 (ss_p E + K)) 1 =
    Some [nth (Z.to_nat K) (ss_pl E) (Z_to_bv 8 0)]).
  { rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia]. }
  assert (ODD : Z.odd (bv_unsigned (nth (Z.to_nat K) (ss_pl E) (Z_to_bv 8 0))) = true) by exact HODD.
  pose proof HGL as (G1 & _ & _ & _ & G5 & _ & _ & _ & _ & _ & _ & G12 & _).
  pose proof HST as (ST1 & ST2 & ST3).
  pose proof HIK as (_ & _ & _ & IK4).
  assert (STK : stk rsegs mem (slot_sp E - 96) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs mem a).
    { rewrite <- SEG. apply IK4. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    split; [exact WA|]. destruct (writable_hi_present mem a ltac:(lia) WA) as [b HB].
    exists b. unfold mrd, wa. rewrite HB. reflexivity. }
  assert (NRO : RoAdapt.not_ro rsegs (slot_sp E - 96) 96).
  { intros i Hi. unfold wa. destruct (ro_addr rsegs (Z_to_bv 64 (slot_sp E - 96 + i))) eqn:HX; [|reflexivity].
    exfalso. pose proof (ro_in_img B SEG (slot_sp E - 96 + i) ltac:(lia) HX) as HI.
    pose proof (in_img_low B SEG _ HI). lia. }
  assert (CSP : rw_cells rsegs mem (slot_sp E) [C8 (Z_to_bv 64 0x210e4)]) by (rewrite <- SEG; exact ST2).
  assert (CL : rw_cells rsegs mem 0x21620 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 cl)]) by (rewrite <- SEG; exact G1).
  assert (CG : rw_cells rsegs mem 0x318a8 [C1 (Z_to_bv 8 gn)]) by (rewrite <- SEG; exact G5).
  assert (CK : rw_cells rsegs mem 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    by (rewrite <- SEG; exact G12).
  assert (RO : MemNorm.ro_agree rsegs mem) by (rewrite <- SEG; exact HRO).
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
  assert (PB : 0 < ss_p E /\ ss_p E + ss_n E < 2 ^ 64).
  { destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
    destruct PIN as [(HN & _)|(_ & p & HPp & EP)]; [lia|].
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p (ss_n E) 0 MR0 HPp ltac:(lia)) as (_ & P0 & P1 & _).
    rewrite EP in P0, P1. lia. }
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (op9g_run (pthread_mutex_lock_ro_of LCK) (pthread_mutex_unlock_ro_of ULK) (ss_p E) (ss_n E) K (slot_sp E) cl gn);
      [lia|unfold INPUT_MAX in Hn; lia|lia|lia|exact RB|exact ODD|lia|lia|exact STK|exact NRO|exact CSP|exact CL|exact CG
      |exact CK|exact RO]. }
  intros ms1 (can1 & (y1 & y5 & y6 & y7 & s0 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & s10 &
    y28 & y29 & y30 & y31 & m' & -> & E0 & E7 & MUW & WMW & CLW & CGW & CKW) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1). subst s0 s10.
  assert (WM' : wmono (ms_segs B) mem m') by (rewrite SEG; exact WMW).
  assert (MWR : forall a, 0x21624 <= a < 0x21628 \/ 0x318a8 <= a < 0x318a9 \/ 0x318fc <= a < 0x31900 ->
    writable_at (ms_segs B) mem a).
  { intros a [Ha|[Ha|Ha]].
    - eapply cells_writable; [exact G1|change (0x21620 <= a < 0x21620 + 8); lia].
    - eapply cells_writable; [exact G5|change (0x318a8 <= a < 0x318a8 + 1); lia].
    - eapply cells_writable; [exact G12|change (0x318f8 <= a < 0x318f8 + 12); lia]. }
  destruct (g9_keep B API LS SH SK ra empty rc fx j E CS L A mem m' md (target_addrs G (bv_unsigned out) es hj)
    HF MUW WM' MWR HMR HRO HIK HST HDK) as (MR' & RO' & IK' & ST' & DK').
  assert (GL' : globals_at B m' (-1) br 1 dd ei (Z.of_nat (length es)) G nfd mx nout cap out).
  { eapply (globals_op9g B (slot_sp E) mem m'); [exact ERR|lia|exact MUW|exact WM'
      |rewrite SEG; exact CLW|rewrite SEG; exact CGW|rewrite SEG; exact CKW|exact HGL]. }
  assert (FA : forall a n, fresh_block B a n -> 0 < n -> disjoint_from (g9_W (slot_sp E)) a (n + 7)).
  { intros a n FR HN. exact (@g9_fresh rc B (slot_sp E) a n SEG ltac:(lia) FR HN). }
  assert (SA : disjoint_from (g9_W (slot_sp E)) G_S 384).
  { unfold g9_W, G_S. cbn [disjoint_from]. repeat split; first [left; lia|right; lia]. }
  assert (REL' : relay_at (rc := rc) B L A m' t nfd G (bv_unsigned out) (map short_entry es) hj)
    by (eapply g9_relay; eassumption).
  assert (OUT' : output_at (rc := rc) B L A m' nout cap out) by (eapply g9_output; eassumption).
  rewrite <- SEG.
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t (K + 1)
    (fun _ _ _ r => tail_regs E t (K + 1) r)); [exact HF|exact CB|intros; assumption|exact HW|]|intros c' HC; exists (K + 1); exact HC].
  exists fx', L, A, R1, m', md, (-1), br, 1, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
  split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
  split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
  split; [exact MR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|].
  split; [rewrite short_target; exact DK'|].
  split; [rewrite length_map; exact GL'|].
  split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|].
  split; [exact OUT'|].
  split; [eapply relay_at_t; [exact REL'|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [rewrite length_map; exact Hes|]. split; [rewrite short_cost; lia|].
  rewrite ?short_view. eapply RIM; [exact HRI|lia].
Qed.

Theorem pass9_gone_holds : check_bounded_contract -> pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  forall RI, RI_mono RI -> pass9_gone_ok RI.
Proof.
  intros CB LCK ULK RI RIM B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk HP.
  cbv beta in HP. destruct HP as (Hop & HK1 & HODD).
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 9) with OP9_AT in HM. change (disp_k E 9 k) with (k + 1) in HM.
  assert (HW9 : walk_at (ss_pl E) (t + 1) (k + 1 + 1)).
  { pose proof (walk_one E t k 9 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_intror (or_intror eq_refl))) as W.
    rewrite (proj2 (Z.ltb_lt _ _) HK1) in W. replace (k + 1 + 1) with (k + 2) by lia. exact W. }
  exact (MI_op9g B API LS SH SK ra empty rc fx j E CS RI t (k + 1) s c' HF CB LCK ULK RIM HK1 HODD HW9 HM).
Qed.
