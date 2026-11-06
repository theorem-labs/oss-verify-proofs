(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its numbers changed; 1524 of its 1624 lines of code are new or changed and 558 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept SlotInv SlotRI3 SlotNcWt
  ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotPass1 list_push_c ListTr HarnessGlue HarnessFrame SlotWalk
  SlotParse SlotMove RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotEntry relay_remove_b_lem.
From Stdlib Require Import Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Ltac zc C :=
  unfold bv_eqb, bv_ltu in C; rewrite ?unsigned_lit in C by lia;
  repeat match type of C with
  | negb _ = true => apply negb_true_iff in C
  | negb _ = false => apply negb_false_iff in C
  end;
  lazymatch type of C with
  | (_ =? _) = true => apply Z.eqb_eq in C
  | (_ =? _) = false => apply Z.eqb_neq in C
  | (_ <? _) = true => apply Z.ltb_lt in C
  | (_ <? _) = false => apply Z.ltb_ge in C
  end.

Ltac weq := first [ reflexivity | (f_equal; lia)
  | (f_equal; unfold zxb; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia)
  | (rewrite ?unsigned_lit by lia; f_equal; lia) ].

Lemma op1_len : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 <= P -> P + N < 2 ^ 64 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (s0 a0 a2 s7 : word) (D B0 B1 : Z),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 x9 a0 x11 a2 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19 x20 x21 x22 s7
        x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m ro /\
      s0 = Z_to_bv 64 (P + K + D) /\ s7 = Z_to_bv 64 (N - K - D) /\
      a0 = Z_to_bv 64 B0 /\ a2 = Z_to_bv 64 (256 * B1) /\
      ((K = N /\ D = 0 /\ B0 = 0 /\ B1 = 0) \/
       (K + 1 = N /\ D = 1 /\ B0 = bv_unsigned b0 /\ B1 = 0) \/
       (K + 2 <= N /\ D = 2 /\ B0 = bv_unsigned b0 /\ B1 = bv_unsigned b1)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19 x20 x21
      x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c98) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN HP HPN RB0 RB1.
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  step. if_cases Q1.
  - zc Q1. assert (KN : K = N) by lia.
    step. step. step.
    apply evt_done. do 4 eexists. exists 0, 0, 0. split; [reflexivity|].
    split; [weq|]. split; [weq|]. split; [weq|]. split; [weq|]. left. lia.
  - zc Q1. specialize (RB0 ltac:(lia)).
    step. step. if_cases Q2.
    + zc Q2. specialize (RB1 ltac:(lia)).
      step. step. step. step.
      apply evt_done. do 4 eexists. exists 2, (bv_unsigned b0), (bv_unsigned b1). split; [reflexivity|].
      split; [weq|]. split; [weq|]. split; [weq|]. split; [weq|]. right. right. lia.
    + zc Q2.
      step. step. step. step.
      apply evt_done. do 4 eexists. exists 1, (bv_unsigned b0), 0. split; [reflexivity|].
      split; [weq|]. split; [weq|]. split; [weq|]. split; [weq|]. right. left. lia.
Qed.

Lemma op1_take : forall (Q R S B0 B1 : Z)
    (x1 x2 x3 x4 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= B0 < 256 -> 0 <= B1 < 256 -> 0 <= R < 2 ^ 26 -> 0 <= Q -> Q + R < 2 ^ 64 -> 0 <= S < 2 ^ 63 ->
  evt rsegs (fun ms => exists (r1 s0 a0 a1 a2 s2 s7 : word) (pc : Z),
      ms = MS (mkR r1 x2 x3 x4 x5 x6 x7 s0 (Z_to_bv 64 S) a0 a1 a2 x13 x14 x15 x16 x17 s2 x19 x20 x21 x22 s7
        x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m ro /\
      s2 = Z_to_bv 64 (Q + Z.min (B0 + 256 * B1) R) /\ s7 = Z_to_bv 64 (R - Z.min (B0 + 256 * B1) R) /\
      (((S = 0 \/ Z.min (B0 + 256 * B1) R = 0) /\ pc = TAIL_CHECK /\ r1 = x1 /\ s0 = s2) \/
       (S <> 0 /\ 0 < Z.min (B0 + 256 * B1) R /\ pc = LIST_PUSH /\ r1 = Z_to_bv 64 0x13d34 /\
        s0 = Z_to_bv 64 Q /\ a0 = Z_to_bv 64 (S + 16) /\ a1 = Z_to_bv 64 Q /\
        a2 = Z_to_bv 64 (Z.min (B0 + 256 * B1) R))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Q) (Z_to_bv 64 S) (Z_to_bv 64 B0) x11 (Z_to_bv 64 (256 * B1)) x13 x14
      x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 R) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m ro).
Proof.
  intros Q R S B0 B1 x1 x2 x3 x4 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro HB0 HB1 HR HQ HQR HS.
  assert (HU : Z.lor (256 * B1) B0 = B0 + 256 * B1).
  { rewrite Z.lor_comm. rewrite <- lor_shiftl8_add by lia. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia. }
  step. rewrite (unsigned_lit (256 * B1)), (unsigned_lit B0), HU by lia.
  step. if_cases Q1.
  - zc Q1. step. step. step. if_cases Q2.
    + zc Q2. step.
      apply evt_done. do 8 eexists. split; [reflexivity|].
      split; [weq|]. split; [weq|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. weq.
    + zc Q2. step. if_cases Q3.
      * zc Q3. step.
        apply evt_done. do 8 eexists. split; [reflexivity|].
        split; [weq|]. split; [weq|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. weq.
      * zc Q3. step. step. step.
        apply evt_done. do 8 eexists. split; [reflexivity|].
        split; [weq|]. split; [weq|]. right. split; [lia|]. split; [lia|]. split; [reflexivity|].
        split; [weq|]. split; [weq|]. split; [weq|]. split; [weq|]. weq.
  - zc Q1. step. step. step. step. if_cases Q2.
    + zc Q2. step.
      apply evt_done. do 8 eexists. split; [reflexivity|].
      split; [weq|]. split; [weq|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. weq.
    + zc Q2. step. if_cases Q3.
      * zc Q3. step.
        apply evt_done. do 8 eexists. split; [reflexivity|].
        split; [weq|]. split; [weq|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. weq.
      * zc Q3. step. step. step.
        apply evt_done. do 8 eexists. split; [reflexivity|].
        split; [weq|]. split; [weq|]. right. split; [lia|]. split; [lia|]. split; [reflexivity|].
        split; [weq|]. split; [weq|]. split; [weq|]. split; [weq|]. weq.
Qed.

Lemma op1_ret : forall (Y : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Y) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Y)
      x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Y)
      x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d34) fc None m ro).
Proof.
  intros. step. apply evt_done. reflexivity.
Qed.

Lemma op1_run : forall (P N K S : Z)
    (x1 x2 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 <= P -> P + N < 2 ^ 64 -> 0 <= S < 2 ^ 63 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (r1 s0 a0 a1 a2 s2 s7 : word) (pc D M : Z),
      ms = MS (mkR r1 x2 x3 x4 x5 x6 x7 s0 (Z_to_bv 64 S) a0 a1 a2 x13 x14 (Z_to_bv 64 1) x16 x17 s2 x19 x20 x21 x22 s7
        x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m ro /\
      (D = 2 \/ K + D = N) /\ 0 <= D /\ K + D <= N /\ 0 <= M <= N - K - D /\ M < 65536 /\
      K + D + M = (if K + 2 <=? N then K + 2 + Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (N - (K + 2)) else N) /\
      s2 = Z_to_bv 64 (P + K + D + M) /\ s7 = Z_to_bv 64 (N - K - D - M) /\
      (((S = 0 \/ M = 0) /\ pc = TAIL_CHECK /\ r1 = x1 /\ s0 = s2) \/
       (S <> 0 /\ 0 < M /\ pc = LIST_PUSH /\ r1 = Z_to_bv 64 0x13d34 /\ s0 = Z_to_bv 64 (P + K + D) /\
        a0 = Z_to_bv 64 (S + 16) /\ a1 = Z_to_bv 64 (P + K + D) /\ a2 = Z_to_bv 64 M)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) (Z_to_bv 64 S) x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18
      x19 x20 x21 x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c98) fc None m ro).
Proof.
  intros P N K S x1 x2 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN HP HPN HS RB0 RB1.
  eapply evt_cut; [exact (op1_len P N K x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x16 x17 x18 x19 x20
    x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro b0 b1 HK HN HP HPN RB0 RB1)|].
  intros ms (s0 & a0 & a2 & s7 & D & B0 & B1 & -> & -> & -> & -> & -> & HC).
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  assert (HB : 0 <= B0 < 256 /\ 0 <= B1 < 256 /\ (D = 2 \/ K + D = N) /\ 0 <= D /\ K + D <= N) by lia.
  destruct HB as (HB0 & HB1 & HD & HD0 & HDN).
  assert (HX : K + D + Z.min (B0 + 256 * B1) (N - K - D) =
    (if K + 2 <=? N then K + 2 + Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (N - (K + 2)) else N)).
  { destruct (Z.leb_spec (K + 2) N); cbv beta iota; lia. }
  clear HC.
  eapply evt_cut; [apply (op1_take (P + K + D) (N - K - D) S B0 B1); lia|].
  intros ms (r1 & s0 & a0 & a1 & a2 & s2 & s7 & pc & -> & E2 & E7 & HC).
  apply evt_done. exists r1, s0, a0, a1, a2, s2, s7, pc, D, (Z.min (B0 + 256 * B1) (N - K - D)).
  split; [reflexivity|]. split; [exact HD|]. split; [exact HD0|]. split; [exact HDN|]. split; [lia|]. split; [lia|].
  split; [exact HX|].
  split; [rewrite E2; f_equal; lia|]. split; [rewrite E7; f_equal; lia|].
  destruct HC as [(H1 & H2 & H3 & H4)|(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)]; [left|right].
  - split; [lia|]. split; [exact H2|]. split; [exact H3|]. exact H4.
  - split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact H6|]. split; [exact H7|]. exact H8.
Qed.

Definition set_pending (h : hsrc) (l : hlist) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) l (hs_off h) (hs_partial h) (hs_pjunk h) (hs_npartial h)
     (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).

Lemma pending_push : forall h l d x,
  hl_recs l = hl_recs (hs_pending h) ++ [(d, x)] ->
  (hl_recs (hs_pending h) = [] -> hs_off h = 0) ->
  pending_stream (set_pending h l) = pending_stream h ++ x.
Proof.
  intros h l d x HR H0. unfold pending_stream at 1. unfold set_pending. cbn [hs_pending hs_off]. rewrite HR.
  unfold pending_stream. destruct (hl_recs (hs_pending h)) as [|r rs] eqn:E.
  - rewrite (H0 eq_refl). cbn. rewrite app_nil_r. reflexivity.
  - cbn [app]. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Lemma pair_cost_push : forall e h i l d x,
  hl_recs l = hl_recs (hs_pending h) ++ [(d, x)] ->
  (hl_recs (hs_pending h) = [] -> hs_off h = 0) ->
  pair_cost e (set_pending h l, i) = pair_cost e (h, i) + Z.of_nat (length x).
Proof.
  intros e h i l d x HR H0. unfold pair_cost. cbn [fst]. rewrite (pending_push h l d x HR H0), length_app. lia.
Qed.

Lemma slot_cost_app : forall es1 es2 hj1 hj2, length es1 = length hj1 ->
  slot_cost (es1 ++ es2) (hj1 ++ hj2) = slot_cost es1 hj1 + slot_cost es2 hj2.
Proof.
  induction es1 as [|e es1 IH]; intros es2 [|p hj1] hj2 HL; cbn in HL; try discriminate; [reflexivity|].
  change (pair_cost e p + slot_cost (es1 ++ es2) (hj1 ++ hj2) = pair_cost e p + slot_cost es1 hj1 + slot_cost es2 hj2).
  rewrite IH by lia. lia.
Qed.

Lemma slot_cost_cons : forall e es p hj, slot_cost (e :: es) (p :: hj) = pair_cost e p + slot_cost es hj.
Proof. reflexivity. Qed.

Definition rdb (B : malloc_syms) (mem : word -> option byte) (a : Z) : byte :=
  match mbyte (ms_segs B) mem a with Some b => b | None => Z_to_bv 8 0 end.

Definition key_pad (k : Z * list byte * list byte) : Z := (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8.

Definition fresh_key (B : malloc_syms) (mem : word -> option byte) (k : Z * list byte * list byte)
    : Z * list byte * list byte :=
  (fst k, map (fun j => rdb B mem (key_addr k + Z.of_nat (length (key_text k)) + 1 + Z.of_nat j))
              (seq 0 (Z.to_nat (key_pad k)))).

Definition fresh_entry (B : malloc_syms) (mem : word -> option byte) (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e)
     (re_hp e) (re_kh e) (re_pad2 e) (map (fresh_key B mem) (re_keys e)) (re_U e) (re_junk e).

Lemma fresh_keys_addr : forall B mem ks, map key_addr (map (fresh_key B mem) ks) = map key_addr ks.
Proof. intros B mem ks. rewrite map_map. reflexivity. Qed.
Lemma fresh_keys_text : forall B mem ks, map key_text (map (fresh_key B mem) ks) = map key_text ks.
Proof. intros B mem ks. rewrite map_map. reflexivity. Qed.
Lemma fresh_keys_texts : forall B mem ks, keys_texts (map (fresh_key B mem) ks) = keys_texts ks.
Proof. intros B mem ks. unfold keys_texts. rewrite map_map. reflexivity. Qed.
Lemma fresh_keys_ptrs : forall B mem ks, key_ptrs (map (fresh_key B mem) ks) = key_ptrs ks.
Proof. intros B mem ks. unfold key_ptrs. rewrite map_map. reflexivity. Qed.
Lemma fresh_keys_total : forall B mem ks, keys_total (map (fresh_key B mem) ks) = keys_total ks.
Proof.
  intros B mem. induction ks as [|q ks IH]; [reflexivity|].
  change (Z.of_nat (length (key_text q)) + 5 + keys_total (map (fresh_key B mem) ks) =
          Z.of_nat (length (key_text q)) + 5 + keys_total ks). rewrite IH. reflexivity.
Qed.
Lemma fresh_entry_bytes : forall B mem e, entry_bytes (fresh_entry B mem e) = entry_bytes e.
Proof. intros B mem e. unfold entry_bytes, re_nheld. cbn. rewrite length_map. reflexivity. Qed.
Lemma fresh_entry_blocks : forall B mem e, entry_blocks (fresh_entry B mem e) = entry_blocks e.
Proof. intros B mem e. unfold entry_blocks. cbn. rewrite fresh_keys_addr. reflexivity. Qed.
Lemma fresh_entries_bytes : forall B mem es, map entry_bytes (map (fresh_entry B mem) es) = map entry_bytes es.
Proof. intros B mem es. rewrite map_map. apply map_ext. apply fresh_entry_bytes. Qed.
Lemma fresh_entries_blocks : forall B mem es, map entry_blocks (map (fresh_entry B mem) es) = map entry_blocks es.
Proof. intros B mem es. rewrite map_map. apply map_ext. apply fresh_entry_blocks. Qed.
Lemma fresh_cost : forall B mem es hj, slot_cost (map (fresh_entry B mem) es) hj = slot_cost es hj.
Proof.
  intros B mem es. induction es as [|e es IH]; intros [|h hj]; try reflexivity.
  change (pair_cost (fresh_entry B mem e) h + slot_cost (map (fresh_entry B mem) es) hj = pair_cost e h + slot_cost es hj).
  rewrite IH. unfold pair_cost. cbn [fresh_entry re_keys re_skip re_used]. rewrite fresh_keys_total. reflexivity.
Qed.

Lemma ta_split : forall G OUT es hj1 h i hj2,
  target_addrs G OUT es (hj1 ++ (h, i) :: hj2) =
  (G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj1)) ++
  list_blocks (hs_pending h) ++
  (([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ++
   concat (map (fun p => hs_blocks (fst p)) hj2)).
Proof.
  intros G OUT es hj1 h i hj2. unfold target_addrs, hs_blocks. rewrite map_app, concat_app. cbn [map concat fst app].
  repeat rewrite <- app_assoc. cbn [app]. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma nodup_swap : forall (X Y l l' : list Z), NoDup (X ++ l ++ Y) -> List.NoDup l' ->
  (forall q, In q l' -> In q (X ++ Y) -> False) -> NoDup (X ++ l' ++ Y).
Proof.
  intros X Y l l' ND N' D. apply hf_nodup in ND. apply hf_nodup.
  pose proof (hf_nodup_l X (l ++ Y) ND) as NX.
  pose proof (NoDup_app_remove_l X (l ++ Y) ND) as NLY.
  pose proof (NoDup_app_remove_l l Y NLY) as NY.
  apply hf_nodup_app; [exact NX| |].
  - apply hf_nodup_app; [exact N'|exact NY|]. intros a H1 H2. apply (D a H1). apply in_or_app. right. exact H2.
  - intros a H1 H2. apply in_app_iff in H2 as [H2|H2].
    + apply (D a H2). apply in_or_app. left. exact H1.
    + apply (hf_nodup_disj X (l ++ Y) a ND H1). apply in_or_app. right. exact H2.
Qed.

Lemma nodup_mid_out : forall (X Y l : list Z) q, NoDup (X ++ l ++ Y) -> In q (X ++ Y) -> ~ In q l.
Proof.
  intros X Y l q ND HQ HL. apply hf_nodup in ND. apply in_app_iff in HQ as [HQ|HQ].
  - apply (hf_nodup_disj X (l ++ Y) q ND HQ). apply in_or_app. left. exact HL.
  - pose proof (NoDup_app_remove_l X (l ++ Y) ND) as NLY. exact (hf_nodup_disj l Y q NLY HL HQ).
Qed.

Lemma push_cap_bound : forall N CAP t, 0 <= N <= t -> N <= CAP -> CAP <= Z.max 8 (2 * t) ->
  grow_cap N CAP <= Z.max 8 (2 * (t + 1)).
Proof.
  intros N CAP t HN HC HT. unfold grow_cap.
  destruct (Z.eqb_spec N CAP) as [->|NE]; [destruct (Z.eqb_spec CAP 0) as [->|NZ]|]; lia.
Qed.

Lemma slack_round8 : forall N, 8 * ((N + 7) / 8) = N + (- N) mod 8.
Proof. intros N. Z.div_mod_to_equations. lia. Qed.

Section PT.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.

Lemma fresh_slack_at : forall L A mem md k, block_slack_present Bm API -> aa_MR API L A mem md ->
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) ->
  0 <= key_addr k -> key_addr k + Z.of_nat (length (key_text k)) + 1 + 8 <= 2 ^ 64 ->
  bytes_at (ms_segs Bm) mem (key_addr k + Z.of_nat (length (key_text k)) + 1) (snd (fresh_key Bm mem k)).
Proof.
  intros L A mem md k SL HM Hin H0 H1.
  set (N0 := key_addr k + Z.of_nat (length (key_text k)) + 1) in *.
  pose proof (Z.mod_pos_bound (- N0) 8 ltac:(lia)) as R8.
  apply bytes_at_of_mbyte.
  - lia.
  - cbn [snd fresh_key]. rewrite length_map, length_seq. unfold key_pad. fold N0. lia.
  - intros i Hi. cbn [snd fresh_key] in Hi |- *. rewrite length_map, length_seq in Hi.
    unfold key_pad in Hi. fold N0 in Hi.
    rewrite nth_error_map, (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi).
    rewrite seq_nth by exact Hi. cbn [option_map Nat.add]. fold N0.
    assert (HA : key_addr k + (Z.of_nat (length (key_text k)) + 1) <= N0 + Z.of_nat i <
                 8 * ((key_addr k + (Z.of_nat (length (key_text k)) + 1) + 7) / 8)).
    { replace (key_addr k + (Z.of_nat (length (key_text k)) + 1)) with N0 by (unfold N0; lia).
      rewrite slack_round8. lia. }
    destruct (SL L A mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) (N0 + Z.of_nat i) HM Hin HA) as [b Hb].
    unfold rdb, mbyte. rewrite Hb. reflexivity.
Qed.

Lemma entry_rmid : forall K sp E F L A mem md L' A' mem' md' e,
  block_slack_present Bm API ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  RelayRep.entry_ok Bm L A mem e ->
  (forall q, In q (entry_blocks e) -> kept_block E F L A q) ->
  RelayRep.entry_ok Bm L' A' mem' (fresh_entry Bm mem' e).
Proof.
  intros K sp E F L A mem md L' A' mem' md' e SL R
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS) KB.
  pose proof R as (M' & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  unfold RelayRep.entry_ok, re_nheld in *.
  cbn [fresh_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, fresh_keys_ptrs, fresh_keys_addr, fresh_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    assert (KQ : kept_block E F L A (re_buf e)).
    { apply KB. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left. reflexivity. }
    destruct KQ as (NF & NE).
    split; [exact C|].
    split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R IN C NF ltac:(lia)
                           (NE _ 0 IN ltac:(lia))))|].
    split; [exact FR|]. split; [exact J|].
    eapply (rmid_rw_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R IN C NF BC);
      [lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia |].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia. apply (NE _ i IN). lia. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right.
      assert (HP0 : re_hp e <> 0) by (destruct FR as (F0 & _); lia).
      assert (KQ : kept_block E F L A (re_hp e)).
      { apply KB. unfold entry_blocks. apply in_or_app. right.
        rewrite (proj2 (Z.eqb_neq (re_hp e) 0) HP0). apply in_or_app. left. left. reflexivity. }
      destruct KQ as (NF & NE).
      split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R IN ltac:(lia) NF
                             ltac:(lia) (NE _ 0 IN ltac:(lia))))|].
      split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply (rmid_bytes_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R IN ltac:(lia) NF HB);
        [lia | rewrite slot_key_ptrs_length; lia |].
      intros i Hi. rewrite slot_key_ptrs_length in Hi. apply (NE _ i IN). lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. rewrite Forall_forall in KS |- *. intros k Hk.
  destruct (KS k Hk) as (IN & FR & HB & NZ & LEN & PAD).
  assert (KQ : kept_block E F L A (key_addr k)).
  { apply KB. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk. }
  destruct KQ as (NF & NE).
  change (key_addr (fresh_key Bm mem' k)) with (key_addr k).
  change (key_text (fresh_key Bm mem' k)) with (key_text k).
  change (key_slack (fresh_key Bm mem' k)) with (snd (fresh_key Bm mem' k)).
  pose proof FR as (FR0 & FR1 & _).
  split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R IN ltac:(lia) NF
                         ltac:(lia) (NE _ 0 IN ltac:(lia))))|].
  split; [exact FR|].
  split.
  { replace (key_text k ++ Z_to_bv 8 0 :: key_slack k) with ((key_text k ++ [Z_to_bv 8 0]) ++ key_slack k) in HB
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in HB as [HB0 _].
    assert (HB1 : bytes_at (ms_segs Bm) mem' (key_addr k) (key_text k ++ [Z_to_bv 8 0])).
    { eapply (rmid_bytes_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R IN ltac:(lia) NF HB0);
        [lia | rewrite length_app; cbn [length]; lia |].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply (NE _ i IN). lia. }
    assert (HS := fresh_slack_at L' A' mem' md' k SL M'
      (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R IN ltac:(lia) NF
                ltac:(lia) (NE _ 0 IN ltac:(lia)))) ltac:(lia) ltac:(lia)).
    replace (key_text k ++ Z_to_bv 8 0 :: snd (fresh_key Bm mem' k))
      with ((key_text k ++ [Z_to_bv 8 0]) ++ snd (fresh_key Bm mem' k)) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact HB1|]. rewrite length_app. cbn [length].
    replace (key_addr k + Z.of_nat (length (key_text k) + 1)) with (key_addr k + Z.of_nat (length (key_text k)) + 1)
      by lia.
    exact HS. }
  split; [exact NZ|]. split; [exact LEN|].
  cbn [snd fresh_key]. rewrite length_map, length_seq. unfold key_pad.
  pose proof (Z.mod_pos_bound (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma output_rmid : forall K sp E F L A mem md L' A' mem' md' nout cap out,
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  output_at (rc := rc) Bm L A mem nout cap out ->
  (0 < bv_unsigned cap -> kept_block E F L A (bv_unsigned out)) ->
  output_at (rc := rc) Bm L' A' mem' nout cap out.
Proof.
  intros K sp E F L A mem md L' A' mem' md' nout cap out R ((O & junk & H) & CAP) KB.
  split; [|exact CAP]. exists O, junk.
  destruct H as [H|(HC & HN & IN & FR & BY & LO & LJ)]; [left; exact H|right].
  destruct (KB HC) as (NF & NE).
  split; [exact HC|]. split; [exact HN|].
  split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R IN HC NF ltac:(lia)
                         (NE _ 0 IN ltac:(lia))))|].
  split; [exact FR|].
  split; [|split; assumption].
  eapply (rmid_bytes_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R IN HC NF BY);
    [lia | rewrite length_app; lia |].
  intros i Hi. rewrite length_app in Hi. apply (NE _ i IN). lia.
Qed.

Lemma src_at_rmid : forall K sp E F L A mem md L' A' mem' md' HA h,
  ms_segs Bm = rsegs -> YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  src_at Bm L A mem HA h ->
  (forall i, 0 <= i < 96 -> img_plain Bm (HA + i) /\ ~ E (HA + i)) ->
  (forall q, In q (hs_blocks h) -> kept_block E F L A q) ->
  src_at Bm L' A' mem' HA h.
Proof.
  intros K sp E F L A mem md L' A' mem' md' HA h SEG HK HM R S HL HB.
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND). apply src_at_iff.
  split.
  { apply (src_base_rmid Bm API AX BW K sp E F L A mem md L' A' mem' md' HA h SEG HK HM R SB).
    - intros i Hi. apply HL. lia.
    - intros q [Hq|Hq]; apply HB; unfold hs_blocks; apply in_app_iff; [left; exact Hq|right].
      subst q. left. reflexivity. }
  split.
  { apply (list_at_rmid Bm API AX BW K sp E F L A mem md L' A' mem' md' (HA + 64) _ true SEG HK HM R LE).
    - intros i Hi. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply HL. lia.
    - intros q Hq. apply HB. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hq. }
  split; [|exact ND].
  apply (list_at_rmid Bm API AX BW K sp E F L A mem md L' A' mem' md' (HA + 80) _ true SEG HK HM R LH).
  - intros i Hi. replace (HA + 80 + i) with (HA + (80 + i)) by lia. apply HL. lia.
  - intros q Hq. apply HB. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
Qed.

End PT.

Lemma forall2_app_split : forall {X Y} (P : X -> Y -> Prop) l1 l2 m1 m2, length l1 = length m1 ->
  Forall2 P (l1 ++ l2) (m1 ++ m2) -> Forall2 P l1 m1 /\ Forall2 P l2 m2.
Proof.
  intros X Y P l1. induction l1 as [|a l1 IH]; intros l2 [|b m1] m2 HL H; cbn in HL; try discriminate.
  - split; [constructor|exact H].
  - cbn in H. inversion H as [|x0 y0 l0 l0' Hab Hrest]; subst.
    destruct (IH l2 m1 m2 ltac:(lia) Hrest) as [H1 H2]. split; [constructor; assumption|exact H2].
Qed.

Lemma forall2_map_l : forall {X X' Y} (P : X -> Y -> Prop) (Q : X' -> Y -> Prop) (f : X -> X') l m,
  Forall2 P l m -> (forall a b, In b m -> P a b -> Q (f a) b) -> Forall2 Q (map f l) m.
Proof.
  intros X X' Y P Q f l m H. induction H as [|a b l m Hab H IH]; intros HQ; cbn [map]; constructor.
  - apply HQ; [left; reflexivity|exact Hab].
  - apply IH. intros a0 b0 Hb. apply HQ. right. exact Hb.
Qed.

Section PD.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Hypothesis SEG : ms_segs Bm = rsegs.

Lemma list_blocks_low : forall L A mem LA l lines q, list_at Bm L A mem LA l lines -> In q (list_blocks l) ->
  4096 <= q.
Proof.
  intros L A mem LA l lines q (_ & _ & AR & _ & _ & FA) Hq. unfold list_blocks in Hq.
  apply in_app_iff in Hq as [Hq|Hq].
  - destruct (hl_cap l =? 0) eqn:EC; [destruct Hq|]. apply Z.eqb_neq in EC. destruct Hq as [<-|[]].
    destruct AR as [(X & _)|(_ & _ & (F0 & _) & _)]; [lia|exact F0].
  - apply in_map_iff in Hq as (r & <- & Hr). rewrite Forall_forall in FA. destruct (FA r Hr) as (_ & (F0 & _) & _).
    exact F0.
Qed.

Lemma push_src : forall K sp Ew Fw L A mem md L' A' mem' md' HA h l' d x,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  src_at Bm L A mem HA h ->
  (forall i, (0 <= i < 16 \/ 32 <= i < 96) -> img_plain Bm (HA + i) /\ ~ Ew (HA + i)) ->
  (forall q, In q ([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ->
     kept_block Ew Fw L A q) ->
  list_at Bm L' A' mem' (HA + 16) l' false ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] -> (1 <= length x)%nat ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks (hs_pending h)) -> ~ In q (list_blocks l')) ->
  src_at Bm L' A' mem' HA (set_pending h l').
Proof.
  intros K sp Ew Fw L A mem md L' A' mem' md' HA h l' d x HK HM R S HL HB LP' HR HX NEW.
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND).
  destruct SB as (C1 & H1 & H2 & H3 & H4 & PL & C2 & H5 & H6 & H7 & PIn & PFr & PJ & PC & PW).
  assert (T : forall a cs, rw_cells (ms_segs Bm) mem a cs ->
      (forall j, 0 <= j < Z.of_nat (cells_size cs) -> 0 <= a - HA + j < 16 \/ 32 <= a - HA + j < 96) ->
      rw_cells (ms_segs Bm) mem' a cs).
  { intros a cs H D. apply (rmid_rw_img Bm API AX K sp Ew Fw L A mem md L' A' mem' md' a cs (hg_img_low Bm SEG)
      HK HM R H). intros j Hj. replace (a + j) with (HA + (a - HA + j)) by lia. apply HL. apply D. exact Hj. }
  destruct (HB (hs_partial h) (or_introl eq_refl)) as (NF & NE).
  unfold src_at. unfold set_pending. cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk
    hs_npartial hs_overlong hs_pad hs_expected hs_held].
  split; [apply T; [exact C1|cbn; intros j Hj; lia]|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact LP'|].
  split; [apply T; [exact C2|cbn; intros j Hj; lia]|].
  split.
  { right. destruct H5 as [(E0 & F0)|(r & rs & E0 & Hr)].
    - exists (d, x), []. rewrite HR, E0, F0. split; [reflexivity|]. cbn [snd]. lia.
    - exists r, (rs ++ [(d, x)]). rewrite HR, E0. split; [reflexivity|exact Hr]. }
  split; [exact H6|]. split; [exact H7|].
  split; [exact (proj1 (rmid_block Bm API BW K sp Ew Fw L A mem md L' A' mem' md' _ _ 0 R PIn ltac:(lia) NF
                         ltac:(lia) (NE _ 0 PIn ltac:(lia))))|].
  split; [exact PFr|]. split; [exact PJ|].
  split.
  { eapply (rmid_rw_block Bm API BW K sp Ew Fw L A mem md L' A' mem' md' _ _ _ _ R PIn ltac:(lia) NF PC);
      [lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia |].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia. apply (NE _ i PIn). lia. }
  split; [exact PW|].
  split.
  { apply (list_at_rmid Bm API AX BW K sp Ew Fw L A mem md L' A' mem' md' (HA + 64) _ true SEG HK HM R LE).
    - intros i Hi. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply HL. lia.
    - intros q Hq. apply HB. apply in_app_iff. right. apply in_app_iff. left. exact Hq. }
  split.
  { apply (list_at_rmid Bm API AX BW K sp Ew Fw L A mem md L' A' mem' md' (HA + 80) _ true SEG HK HM R LH).
    - intros i Hi. replace (HA + 80 + i) with (HA + (80 + i)) by lia. apply HL. lia.
    - intros q Hq. apply HB. apply in_app_iff. right. apply in_app_iff. right. exact Hq. }
  unfold hs_blocks. cbn [hs_pending hs_partial hs_expected hs_held].
  apply hf_nodup. apply hf_nodup in ND. unfold hs_blocks in ND.
  apply hf_nodup_app.
  - exact (list_blocks_nodup Bm L' A' mem' _ _ _ LP').
  - exact (NoDup_app_remove_l _ _ ND).
  - intros q Q1 Q2.
    assert (NP : ~ In q (list_blocks (hs_pending h))) by (intros X; exact (hf_nodup_disj _ _ q ND X Q2)).
    assert (POS : exists k, 0 < k /\ In (q, k) (blocks L A)).
    { apply in_app_iff in Q2 as [Q2|Q2]; [destruct Q2 as [<-|[]]; exists 6000; split; [lia|exact PIn]|].
      apply in_app_iff in Q2 as [Q2|Q2];
        [exact (hf_list_pos Bm L A mem _ _ _ q LE Q2) | exact (hf_list_pos Bm L A mem _ _ _ q LH Q2)]. }
    destruct POS as (k & Hk & Hin). exact (NEW q k Hin Hk NP Q1).
Qed.

Lemma push_pair : forall K sp Ew Fw L A mem md L' A' mem' md' t e h i l' d x,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  pair_ok (rc := rc) Bm L A mem t e (h, i) -> 0 <= t ->
  (forall j, (0 <= j < 16 \/ 32 <= j < 96) ->
     img_plain Bm (G_S + SRC_SIZE * Z.of_nat i + j) /\ ~ Ew (G_S + SRC_SIZE * Z.of_nat i + j)) ->
  (forall q, In q ([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ->
     kept_block Ew Fw L A q) ->
  list_at Bm L' A' mem' (G_S + SRC_SIZE * Z.of_nat i + 16) l' false ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] -> (1 <= length x)%nat -> Z.of_nat (length x) <= WRITE_MAX ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks (hs_pending h)) -> ~ In q (list_blocks l')) ->
  pair_ok (rc := rc) Bm L' A' mem' (t + 1) (fresh_entry Bm mem' e) (set_pending h l', i).
Proof.
  intros K sp Ew Fw L A mem md L' A' mem' md' t e h i l' d x HK HM R P Ht HL HB LP' HR HX HXW HC NEW.
  unfold pair_ok in P |- *. cbv zeta in P |- *. cbn [fst snd] in P |- *.
  destruct P as (S & Hi & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  pose proof S as (_ & _ & _ & _ & _ & LP & _ & H5 & _).
  assert (OFF : hl_recs (hs_pending h) = [] -> hs_off h = 0).
  { intros E0. destruct H5 as [(_ & F0)|(r & rs & E1 & _)]; [exact F0|]. rewrite E0 in E1. discriminate. }
  split; [exact (push_src K sp Ew Fw L A mem md L' A' mem' md' _ h l' d x HK HM R S HL HB LP' HR HX NEW)|].
  split; [exact Hi|].
  rewrite (pending_push h l' d x HR OFF).
  unfold set_pending. cbn [hs_fd hs_overlong hs_held hs_expected hs_pending fresh_entry re_fd re_eof re_skip re_U re_keys].
  rewrite fresh_keys_texts.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
  pose proof LP as (_ & LB & _).
  split; [unfold hl_n in *; rewrite HR, length_app; cbn [length]; lia|].
  split; [rewrite HC; apply push_cap_bound; [unfold hl_n in *; lia|lia|exact P7]|].
  split; [rewrite length_app; unfold WRITE_MAX in *; lia|].
  split; [exact P9|exact P10].
Qed.

Lemma pair_rmid : forall K sp Ew Fw L A mem md L' A' mem' md' t e h j,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  pair_ok (rc := rc) Bm L A mem t e (h, j) ->
  (forall k, 0 <= k < 96 -> img_plain Bm (G_S + SRC_SIZE * Z.of_nat j + k) /\ ~ Ew (G_S + SRC_SIZE * Z.of_nat j + k)) ->
  (forall q, In q (hs_blocks h) -> kept_block Ew Fw L A q) ->
  pair_ok (rc := rc) Bm L' A' mem' t (fresh_entry Bm mem' e) (h, j).
Proof.
  intros K sp Ew Fw L A mem md L' A' mem' md' t e h j HK HM R P HL HB.
  unfold pair_ok in P |- *. cbv zeta in P |- *. cbn [fst snd] in P |- *.
  destruct P as (S & REST).
  split; [exact (src_at_rmid Bm API AX BW K sp Ew Fw L A mem md L' A' mem' md' _ h SEG HK HM R S HL HB)|].
  cbn [fresh_entry re_fd re_eof re_skip re_U re_keys]. rewrite fresh_keys_texts. exact REST.
Qed.

Lemma ta_pos : forall L A mem t nfd G OUT es hj q,
  relay_at (rc := rc) Bm L A mem t nfd G OUT es hj ->
  (OUT = 0 \/ exists k, 0 < k /\ In (OUT, k) (blocks L A)) ->
  In q (target_addrs G OUT es hj) -> q = 0 \/ exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem t nfd G OUT es hj q (_ & GIN & _ & ES & _ & _ & PA & _) HO HQ.
  destruct HQ as [<-|[<-|HQ]]; [right; exists SRC_TABLE; split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact GIN]|exact HO|].
  right. apply in_app_iff in HQ as [HQ|HQ].
  - apply in_concat in HQ as (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as (e & <- & He).
    rewrite Forall_forall in ES. destruct (ES e He) as (_ & _ & _ & _ & _ & H6 & _ & _ & _ & BU & _ & HP & _ & _ & KS).
    unfold entry_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq].
    + destruct (Z.eqb_spec (re_cap e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
      destruct BU as [(X & _)|(HC & IN & _)]; [lia|]. exists (re_cap e). split; [exact HC|exact IN].
    + apply in_app_iff in Hq as [Hq|Hq].
      * destruct (Z.eqb_spec (re_hp e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
        destruct HP as [(X & _)|(IN & _ & _ & HH & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
      * apply in_map_iff in Hq as (k & <- & Hk). rewrite Forall_forall in KS. destruct (KS k Hk) as (IN & _).
        exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact IN].
  - apply in_concat in HQ as (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as ([h j] & <- & Hp). cbn [fst] in Hq.
    destruct (pair_find _ _ _ _ _ (h, j) PA Hp) as [e (S & _)]. cbn [fst snd] in S.
    apply src_at_iff in S. destruct S as (SB & LE & LH & _).
    unfold hs_blocks in Hq.
    replace (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h))
      with ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks (hs_held h))
      in Hq by (rewrite <- !app_assoc; reflexivity).
    apply in_app_iff in Hq as [Hq|Hq]; [eapply src_parts_pos; eassumption|exact (hf_list_pos Bm L A mem _ _ _ q LH Hq)].
Qed.

End PD.

Section PR.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Hypothesis SEG : ms_segs Bm = rsegs.
Hypothesis PL : forall a, in_globals G_reply a -> img_plain Bm a.

Lemma slot_img : forall j k, (j < 4)%nat -> 0 <= k < 96 -> img_plain Bm (G_S + SRC_SIZE * Z.of_nat j + k).
Proof. intros j k Hj Hk. apply PL, in_G_bss. unfold G_S, SRC_SIZE. lia. Qed.

Lemma push_relay : forall K sp Ew Fw L A mem md L' A' mem' md' t nfd G OUT es1 e es2 hj1 h i hj2 l' d x,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md -> block_slack_present Bm API ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  relay_at (rc := rc) Bm L A mem t nfd G OUT (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2) -> 0 <= t ->
  length es1 = length hj1 ->
  (OUT = 0 \/ exists k, 0 < k /\ In (OUT, k) (blocks L A)) ->
  (forall a, in_img Bm a -> ~ (G_S + SRC_SIZE * Z.of_nat i + 16 <= a < G_S + SRC_SIZE * Z.of_nat i + 32) -> ~ Ew a) ->
  (forall q, In q (target_addrs G OUT (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2)) ->
     ~ In q (list_blocks (hs_pending h)) -> kept_block Ew Fw L A q) ->
  list_at Bm L' A' mem' (G_S + SRC_SIZE * Z.of_nat i + 16) l' false ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] -> (1 <= length x)%nat -> Z.of_nat (length x) <= WRITE_MAX ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks (hs_pending h)) -> ~ In q (list_blocks l')) ->
  relay_at (rc := rc) Bm L' A' mem' (t + 1) nfd G OUT (map (fresh_entry Bm mem') (es1 ++ e :: es2))
    (hj1 ++ (set_pending h l', i) :: hj2).
Proof.
  intros K sp Ew Fw L A mem md L' A' mem' md' t nfd G OUT es1 e es2 hj1 h i hj2 l' d x
    HK HM SL R REL Ht HL1 HO HIMG KP LP' HR HX HXW HC NEW.
  pose proof REL as ((tail & TL & TC) & GIN & GFR & ES & NDF & FD & PA & NDH & ZH & NDA).
  assert (ND0 := NDA). rewrite ta_split in NDA.
  assert (KX : forall q, In q ((G :: OUT :: concat (map entry_blocks (es1 ++ e :: es2)) ++
                  concat (map (fun p => hs_blocks (fst p)) hj1)) ++
                 (([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ++
                  concat (map (fun p => hs_blocks (fst p)) hj2))) -> kept_block Ew Fw L A q).
  { intros q Hq. apply KP; [|exact (nodup_mid_out _ _ _ q NDA Hq)].
    rewrite ta_split. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
    apply in_app_iff. right. exact Hq. }
  assert (HI : (i < 4)%nat).
  { apply (Forall2_app_inv_r hj1 ((h, i) :: hj2)) in PA as (es1' & es2' & _ & P2 & _).
    inversion P2 as [|x0 y0 l0 l0' Hab _]; subst. unfold pair_ok in Hab. cbv zeta in Hab. cbn [fst snd] in Hab.
    exact (proj1 (proj2 Hab)). }
  assert (NIH : forall p, In p (hj1 ++ hj2) -> snd p <> i).
  { intros p Hp E. rewrite map_app in NDH. cbn [map] in NDH. apply hf_nodup in NDH.
    apply in_app_iff in Hp as [Hp|Hp].
    - apply (hf_nodup_disj (map snd hj1) (snd (h, i) :: map snd hj2) i NDH); [rewrite <- E; apply in_map; exact Hp|].
      left. reflexivity.
    - pose proof (NoDup_app_remove_l _ _ NDH) as N2. inversion N2 as [|y ys NI _].
      apply NI. cbn [snd]. rewrite <- E. apply in_map. exact Hp. }
  assert (SLOTNE : forall j k, (j < 4)%nat -> j <> i -> 0 <= k < 96 -> ~ Ew (G_S + SRC_SIZE * Z.of_nat j + k)).
  { intros j k Hj NE Hk. apply HIMG; [exact (proj1 (slot_img j k Hj Hk))|].
    unfold G_S, SRC_SIZE. intros (X1 & X2).
    destruct (Nat.lt_ge_cases j i) as [LT|GE].
    - assert (Z.of_nat j + 1 <= Z.of_nat i) by lia. lia.
    - assert (Z.of_nat i + 1 <= Z.of_nat j) by lia. lia. }
  apply (forall2_app_split _ es1 (e :: es2) hj1 ((h, i) :: hj2) HL1) in PA as [PA1 PA2].
  inversion PA2 as [|x0 y0 l0 l0' PE PA3]; subst.
  pose proof PE as PE'. unfold pair_ok in PE'. cbv zeta in PE'. cbn [fst snd] in PE'.
  destruct PE' as (SH & _).
  assert (OTHER : forall hj0 es0, Forall2 (pair_ok (rc := rc) Bm L A mem t) es0 hj0 ->
      (forall p, In p hj0 -> snd p <> i) ->
      (forall p q, In p hj0 -> In q (hs_blocks (fst p)) -> kept_block Ew Fw L A q) ->
      Forall2 (pair_ok (rc := rc) Bm L' A' mem' (t + 1)) (map (fresh_entry Bm mem') es0) hj0).
  { intros hj0 es0 P0 NI0 KB0. apply (forall2_map_l _ _ _ _ _ P0).
    intros e0 [h0 j0] Hp P. apply (pair_ok_t rc Bm L' A' mem' t (t + 1)); [|lia].
    assert (Hj0 : (j0 < 4)%nat).
    { unfold pair_ok in P. cbv zeta in P. cbn [fst snd] in P. exact (proj1 (proj2 P)). }
    apply (pair_rmid Bm API AX BW SEG K sp Ew Fw L A mem md L' A' mem' md' t e0 h0 j0 HK HM R P).
    - intros k Hk. split; [exact (slot_img j0 k Hj0 Hk)|]. apply SLOTNE; [exact Hj0| |exact Hk].
      exact (NI0 (h0, j0) Hp).
    - intros q Hq. exact (KB0 (h0, j0) q Hp Hq). }
  split.
  { exists tail. split; [rewrite length_map; exact TL|].
    rewrite fresh_entries_bytes.
    destruct (KX G ltac:(apply in_or_app; left; left; reflexivity)) as (NF & NE).
    eapply (rmid_rw_block Bm API BW K sp Ew Fw L A mem md L' A' mem' md' _ _ _ _ R GIN
              ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) NF TC);
      [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia |].
    intros k Hk. cbn [cells_size csize] in Hk. apply (NE _ k GIN). unfold SRC_TABLE, SRC_ENTRY. lia. }
  destruct (KX G ltac:(apply in_or_app; left; left; reflexivity)) as (NFG & NEG).
  split; [exact (proj1 (rmid_block Bm API BW K sp Ew Fw L A mem md L' A' mem' md' _ _ 0 R GIN
                         ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) NFG ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)
                         (NEG _ 0 GIN ltac:(unfold SRC_TABLE, SRC_ENTRY; lia))))|].
  split; [exact GFR|].
  split.
  { apply Forall_map. rewrite Forall_forall in ES |- *. intros e0 He0.
    apply (entry_rmid Bm API BW K sp Ew Fw L A mem md L' A' mem' md' e0 SL R (ES e0 He0)).
    intros q Hq. apply KX. apply in_app_iff. left. right. right. apply in_app_iff. left.
    apply in_concat. exists (entry_blocks e0). split; [apply in_map; exact He0|exact Hq]. }
  split; [rewrite map_map; exact NDF|].
  split; [apply Forall_map; exact FD|].
  split.
  { rewrite map_app. cbn [map]. apply Forall2_app; [|constructor].
    - apply OTHER; [exact PA1| |].
      + intros p Hp. apply NIH. apply in_or_app. left. exact Hp.
      + intros p q Hp Hq. apply KX. apply in_app_iff. left. right. right. apply in_app_iff. right.
        apply in_concat. exists (hs_blocks (fst p)). split; [apply (in_map (fun p => hs_blocks (fst p))); exact Hp|exact Hq].
    - apply (push_pair Bm API AX BW SEG K sp Ew Fw L A mem md L' A' mem' md' t _ h i l' d x HK HM R PE Ht);
        [| |exact LP'|exact HR|exact HX|exact HXW|exact HC|exact NEW].
      + intros j Hj. split; [apply slot_img; [exact HI|lia]|]. apply HIMG; [apply (slot_img i j HI); lia|lia].
      + intros q Hq. apply KX. apply in_app_iff. right. apply in_app_iff. left. exact Hq.
    - apply OTHER; [exact PA3| |].
      + intros p Hp. apply NIH. apply in_or_app. right. exact Hp.
      + intros p q Hp Hq. apply KX. apply in_app_iff. right. apply in_app_iff. right.
        apply in_concat. exists (hs_blocks (fst p)). split; [apply (in_map (fun p => hs_blocks (fst p))); exact Hp|exact Hq]. }
  split; [rewrite !map_app in *; exact NDH|].
  split.
  { intros q Hq HZ.
    assert (EO : slot_open (hj1 ++ (set_pending h l', i) :: hj2) q = slot_open (hj1 ++ (h, i) :: hj2) q).
    { unfold slot_open. rewrite !map_app. reflexivity. }
    rewrite EO in HZ.
    assert (QI : q <> i).
    { intros ->. unfold slot_open in HZ. rewrite map_app in HZ. cbn [map snd] in HZ.
      rewrite existsb_app in HZ. cbn [existsb] in HZ. rewrite Nat.eqb_refl in HZ.
      rewrite orb_true_r in HZ. discriminate. }
    apply (rmid_rw_img Bm API AX K sp Ew Fw L A mem md L' A' mem' md' _ _ (hg_img_low Bm SEG) HK HM R (ZH q Hq HZ)).
    intros k Hk. cbn [cells_size csize] in Hk. split; [apply slot_img; [exact Hq|lia]|].
    apply SLOTNE; [exact Hq|exact QI|lia]. }
  rewrite ta_split. rewrite fresh_entries_blocks.
  cbn [fst]. apply (nodup_swap _ _ (list_blocks (hs_pending h))); [exact NDA|exact (list_blocks_nodup Bm L' A' mem' _ _ _ LP')|].
  intros q Q1 Q2.
  assert (QT : In q (target_addrs G OUT (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2))).
  { rewrite ta_split. apply in_app_iff in Q2 as [Q2|Q2]; apply in_app_iff; [left; exact Q2|right].
    apply in_app_iff. right. exact Q2. }
  assert (NP := nodup_mid_out _ _ _ q NDA Q2).
  destruct (ta_pos Bm L A mem t nfd G OUT _ _ q REL HO QT) as [->|(k & Hk & Hin)].
  - pose proof (list_blocks_low Bm L' A' mem' _ _ _ 0 LP' Q1). lia.
  - exact (NEW q k Hin Hk NP Q1).
Qed.

End PR.

Section PK.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Hypothesis SEG : ms_segs Bm = rsegs.

Lemma push_driver : forall E0 TA TA' K sp Ew Fw L A mem md L' A' mem' md' (lb lb' : list Z),
  WF A -> List.NoDup (map fst (blocks L A)) ->
  driver_kept Bm E0 TA L A mem ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  (0 < ss_n E0 -> exists q, In (q, ss_n E0) (user_blocks (ss_A E0)) /\ ptr_addr (ss_L E0) q = ss_p E0) ->
  (0 < ss_n E0 -> ~ In (ss_p E0, ss_n E0) (ss_T E0)) ->
  (forall q, In q lb -> In q TA) ->
  (forall q, In q lb' -> In q TA') ->
  (forall q, In q TA -> ~ In q lb -> In q TA') ->
  (forall q, In q TA' -> In q TA \/ In q lb') ->
  (forall q, In q lb -> exists k, 0 < k /\ In (q, k) (blocks L A)) ->
  (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ In q lb)) \/ In q lb') ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q lb -> ~ In q lb') ->
  (forall q, ~ In q TA -> kept_block Ew Fw L A q) ->
  driver_kept Bm E0 TA' L' A' mem'.
Proof.
  intros E0 TA TA' K sp Ew Fw L A mem md L' A' mem' md' lb lb' HW NDB (D1 & D2 & D3 & D4) R INP INT
    LBT LBT' KEEP BACK LBP NEWB NEWN KPT.
  pose proof R as (_ & _ & _ & _ & _ & PA & SV & Z0 & _ & _ & _ & BK & _).
  assert (BL : forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A)).
  { intros p n Hp. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp). }
  assert (KB : forall X m i, In (X, m) (blocks L A) -> ~ In X TA -> 0 <= i < m ->
      mbyte (ms_segs Bm) mem' (X + i) = mbyte (ms_segs Bm) mem (X + i)).
  { intros X m i Hin NT Hi. destruct (KPT X NT) as (NF & NE).
    exact (proj1 (proj2 (rmid_block Bm API BW K sp Ew Fw L A mem md L' A' mem' md' X m i R Hin ltac:(lia) NF Hi
                           (NE m i Hin Hi)))). }
  split.
  { intros q m Hq HT. destruct (D1 q m Hq HT) as (HN & q' & Hq' & Eq').
    pose proof (SlotEntry.entry_ub_nonneg _ _ _ HW Hq') as M0.
    assert (NTA : 0 < m -> ~ In (ptr_addr (ss_L E0) q) TA) by exact HN.
    split.
    - intros Hm X. destruct (BACK _ X) as [X1|X1]; [exact (HN Hm X1)|].
      apply (NEWN (ptr_addr (ss_L E0) q) m); [rewrite <- Eq'; exact (BL q' m Hq')|exact Hm| |exact X1].
      intros X2. exact (HN Hm (LBT _ X2)).
    - destruct (Z.eq_dec m 0) as [->|NZ].
      + destruct (Z0 q' Hq') as (Hq'' & Ep). exists q'. split; [exact Hq''|]. rewrite Ep. exact Eq'.
      + assert (Hm : 0 < m) by lia.
        destruct (KPT _ (HN Hm)) as (NF & _). rewrite <- Eq' in NF.
        pose proof (SV q' m Hq' Hm NF) as Hq''. exists q'. split; [exact Hq''|].
        rewrite (PA q' m Hq' Hq'' NF). exact Eq'. }
  split.
  { intros q m i Hq HT HP Hi. destruct (D1 q m Hq HT) as (HN & q' & Hq' & Eq').
    rewrite (KB (ptr_addr (ss_L E0) q) m i ltac:(rewrite <- Eq'; exact (BL q' m Hq')) (HN ltac:(lia)) Hi).
    exact (D2 q m i Hq HT HP Hi). }
  split.
  { intros i Hi. destruct (INP ltac:(lia)) as (q & Hq & Eq).
    destruct (D1 q (ss_n E0) Hq ltac:(rewrite Eq; exact (INT ltac:(lia)))) as (HN & q' & Hq' & Eq').
    rewrite Eq in Eq', HN.
    rewrite (KB (ss_p E0) (ss_n E0) i ltac:(rewrite <- Eq'; exact (BL q' _ Hq')) (HN ltac:(lia)) Hi).
    exact (D3 i Hi). }
  intros q m Hq. destruct (NEWB q m Hq) as [(Hold & Hm)|Hn]; [|right; exact (LBT' q Hn)].
  destruct (D4 q m Hold) as [X|X]; [left; exact X|right].
  destruct (in_dec Z.eq_dec q lb) as [IL|IL]; [|exact (KEEP q X IL)].
  exfalso. destruct (LBP q IL) as (k & Hk & Hin).
  pose proof (hg_nodup_fst _ q m k NDB Hold Hin) as ->. exact (Hm Hk IL).
Qed.

Lemma push_image : forall E0 K sp Ew Fw L A mem md L' A' mem' md' X,
  image_kept (rc := rc) Bm E0 mem -> rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' -> aa_MR API L A mem md ->
  YM05.alloc_ceiling <= sp - K ->
  (forall a, in_globals G_reply a -> img_plain Bm a) ->
  (forall a, Ew a -> X <= a < X + 16 \/ (~ in_img Bm a /\ a < YM05.alloc_ceiling)) ->
  (forall a, X <= a < X + 16 ->
     in_globals G_reply a /\ writable_at (ms_segs Bm) mem a /\ writable_at (ms_segs Bm) mem' a) ->
  (forall a, sk Bm K sp a -> lib_scratch Bm SLOT_STACK (ss_regs E0) a) ->
  (forall a, lib_scratch Bm SLOT_STACK (ss_regs E0) a -> sk Bm K sp a \/ YM05.alloc_ceiling <= a < 2 ^ 64) ->
  image_kept (rc := rc) Bm E0 mem'.
Proof.
  intros E0 K sp Ew Fw L A mem md L' A' mem' md' X (I1 & I2 & I3 & I4) R HM HK PL HE HX SKL LSK.
  pose proof R as (M' & _ & _ & _ & _ & _ & _ & _ & _ & _ & BY & _ & SC).
  pose proof (aa_laws API) as LAWS.
  assert (HI : forall x, in_img Bm x -> 0 <= x < YM05.alloc_ceiling) by exact (hg_img_low Bm SEG).
  assert (FR : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ sk Bm K sp a -> ~ Ew a ->
      mbyte (ms_segs Bm) mem' a = mbyte (ms_segs Bm) mem a /\
      (writable_at (ms_segs Bm) mem a <-> writable_at (ms_segs Bm) mem' a)).
  { intros a Ha NS NE. apply BY; [left; exact Ha| | |exact NS|exact NE].
    - intro Y. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Y). lia.
    - intro Y. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M' Y). lia. }
  assert (NEH : forall a, YM05.alloc_ceiling <= a -> ~ Ew a).
  { intros a Ha Y. destruct (HE a Y) as [Y1|(_ & Y2)]; [|lia].
    pose proof (HI a (proj1 (PL a (proj1 (HX a Y1))))). lia. }
  split.
  { intros a Ha H1 H2 H3 H4.
    assert (NE : ~ Ew a).
    { intros Y. destruct (HE a Y) as [Y1|(Y2 & _)]; [exact (H4 (proj1 (HX a Y1)))|exact (Y2 Ha)]. }
    destruct (rmid_img Bm API AX K sp Ew Fw L A mem md L' A' mem' md' a HI HK HM R
                ltac:(split; [exact Ha|split; [exact H1|split; [exact H2|exact H3]]]) NE) as [E1 W1].
    destruct (I1 a Ha H1 H2 H3 H4) as [E2 W2]. split; [congruence|tauto]. }
  split.
  { intros a Ha. pose proof (I2 a Ha) as W2.
    assert (D : X <= a < X + 16 \/ ~ (X <= a < X + 16)) by lia.
    destruct D as [D|D].
    - destruct (HX a D) as (_ & W3 & W4). tauto.
    - assert (NE : ~ Ew a).
      { intros Y. destruct (HE a Y) as [Y1|(Y2 & _)]; [exact (D Y1)|exact (Y2 (proj1 (PL a Ha)))]. }
      destruct (rmid_img Bm API AX K sp Ew Fw L A mem md L' A' mem' md' a HI HK HM R (PL a Ha) NE) as [_ W1].
      tauto. }
  split.
  { intros a Ha HN. destruct (I3 a Ha HN) as [E2 W2].
    destruct (FR a Ha ltac:(intros Y; exact (HN (SKL a Y))) (NEH a ltac:(lia))) as [E1 W1].
    split; [congruence|tauto]. }
  intros a Ha. assert (D : sk Bm K sp a \/ ~ sk Bm K sp a) by (unfold sk; lia).
  destruct D as [D|D]; [exact (SC a D)|].
  destruct (LSK a Ha) as [Y|Y]; [exact (False_ind _ (D Y))|].
  destruct (FR a Y D (NEH a ltac:(lia))) as [_ W1]. apply W1. exact (I4 a Ha).
Qed.

Ltac gcell T GB GW :=
  apply T; [eassumption|
    cbn [cells_size csize Nat.add]; unfold G_LISTEN, G_WAKE0, G_THREAD_UP, G_BROKEN, G_GONE, G_DEAD, G_EINTR, G_NSRC,
      G_NFD, G_SRC, G_OUTV, G_LOCK, G_S, Statement.G_NSRC, check_bounded_c.G_NSRC, relay_add_b_c.G_NSRC,
      StatementKept.G_SRC, check_bounded_c.G_SRC, relay_add_b_c.G_SRC, Statement.G_LOCK, relay_event_c.G_LOCK,
      Statement.G_S, HarnessRep.G_S; lia|
    cbn [cells_size csize Nat.add]; unfold G_LISTEN, G_WAKE0, G_THREAD_UP, G_BROKEN, G_GONE, G_DEAD, G_EINTR, G_NSRC,
      G_NFD, G_SRC, G_OUTV, G_LOCK, Statement.G_NSRC, check_bounded_c.G_NSRC, relay_add_b_c.G_NSRC,
      StatementKept.G_SRC, check_bounded_c.G_SRC, relay_add_b_c.G_SRC, Statement.G_LOCK, relay_event_c.G_LOCK;
      intros i Hi; first [apply GB; lia|apply GW; lia]].

Lemma push_globals : forall K sp Ew Fw L A mem md L' A' mem' md' cl br gn dd ei N G nfd mx no cap out,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp Ew Fw L A mem md L' A' mem' md' ->
  (forall a, in_globals G_reply a -> img_plain Bm a) ->
  (forall a, Ew a -> G_S <= a \/ ~ in_img Bm a) ->
  (forall m, exists ev, rw_cells (ms_segs Bm) m (errno_addr Bm) [C4 ev]) ->
  globals_at Bm mem cl br gn dd ei N G nfd mx no cap out -> globals_at Bm mem' cl br gn dd ei N G nfd mx no cap out.
Proof.
  intros K sp Ew Fw L A mem md L' A' mem' md' cl br gn dd ei N G nfd mx no cap out HK HM R PL HE ERRC
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & REST).
  assert (T : forall a cs, rw_cells (ms_segs Bm) mem a cs -> a + Z.of_nat (cells_size cs) <= G_S ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i)) -> rw_cells (ms_segs Bm) mem' a cs).
  { intros a cs H HB HG. apply (rmid_rw_img Bm API AX K sp Ew Fw L A mem md L' A' mem' md' a cs (hg_img_low Bm SEG)
      HK HM R H).
    intros i Hi. split; [exact (PL _ (HG i Hi))|]. intros X. destruct (HE _ X) as [X1|X1]; [lia|].
    exact (X1 (proj1 (PL _ (HG i Hi)))). }
  assert (GB : forall a, 0x30fc0 <= a < 0x30fc0 + 512 -> in_globals G_reply a) by exact in_G_bss.
  assert (GW : forall a, 0x20d38 <= a < 0x20d38 + 16 -> in_globals G_reply a).
  { intros a Ha. exists 0x20d38, 16. split; [left; reflexivity|exact Ha]. }
  unfold globals_at.
  split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|].
  split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|].
  split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|]. split; [gcell T GB GW|].
  split; [gcell T GB GW|].
  split; [exact (ERRC mem')|exact REST].
Qed.

End PK.

(* list_push's post state L' A' (the pushed list l' linked to the run's addresses qs): RI holds at every view that
   covers its blocks, appends the pushed text txt (the input chunk at k' - n) to one pending list, and moves the
   view's nc blocks by the array growth (grow_dels / grow_adds); the text's own block is not an nc block. *)
Definition push_RV_s (RI : res_inv) (E : sstart) (k' : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (l : hlist) (tx : list byte) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall l',
    sh_real L' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs tx)) l' ->
    sh_live A' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs tx)) ->
    forall G' out' es' hj',
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
    (exists p1 x p2 txt, pend_view hj = p1 ++ x :: p2 /\ pend_view hj' = p1 ++ (x ++ [txt]) :: p2 /\
       Z.of_nat (length x) = hl_n l /\ Z.of_nat (length txt) = Z.of_nat (length tx) /\
       In (CK 1 (k' - Z.of_nat (length tx)) (plz txt)) (pl_chunks (ss_pl E))) ->
    ek_view hj' = ek_view hj ->
    (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
    nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A' (grow_dels (hl_v l) (hl_n l) (hl_cap l))
      (grow_adds (hl_v l') (hl_n l) (hl_cap l)) ->
    List.NoDup (map fst (blocks L' A')) ->
    (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
       In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
       ~ In (ptr_addr L p) (map fst (grow_dels (hl_v l) (hl_n l) (hl_cap l))) ->
       In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
    ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' ->
    nc_wt es' hj' <= nc_wt es hj + NC_PER + DATA_PER * Z.of_nat (length tx) ->
    RI E k' (view_of G' out' es' hj') L' A'.

Definition push_resources_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k k' L A (l : hlist) (tx : list byte) G out es hj, RI E k (view_of G out es hj) L A ->
    List.NoDup (map fst (blocks L A)) ->
    0 <= hl_n l <= hl_cap l -> hl_n l < OPS_MAX -> hl_cap l <= 2 * OPS_MAX ->
    1 <= Z.of_nat (length tx) <= WRITE_MAX -> k' = k + 2 + Z.of_nat (length tx) -> k' <= ss_n E ->
    res_tr F (push_RV_s RI E k' L A G out es hj l tx) A (list_push_tr (sh_of (known_at L A) l) (bzs tx)).

Lemma push_arr_nc : forall lo l', hl_cap l' = grow_cap (hl_n lo) (hl_cap lo) -> (hl_n lo < hl_cap lo -> hl_v l' = hl_v lo) ->
  0 <= hl_n lo <= hl_cap lo ->
  forall a, In a (arr_nc lo) -> ~ In a (map fst (grow_dels (hl_v lo) (hl_n lo) (hl_cap lo))) -> In a (arr_nc l').
Proof.
  intros lo l' HC HV HN a Ha HD. revert Ha. unfold arr_nc.
  destruct (Z.eqb_spec (hl_cap lo) 0) as [C0|C0]; [intros []|]. intros [<-|[]].
  destruct (Z.eqb_spec (hl_n lo) (hl_cap lo)) as [EQ|NE].
  - exfalso. apply HD. unfold grow_dels. rewrite (proj2 (Z.eqb_eq _ _) EQ), (proj2 (Z.eqb_neq _ _) C0).
    cbn. left. reflexivity.
  - rewrite HC. unfold grow_cap. rewrite (proj2 (Z.eqb_neq _ _) NE), (proj2 (Z.eqb_neq _ _) C0).
    rewrite (HV ltac:(lia)). cbn. left. reflexivity.
Qed.

Lemma push_nw_list : forall lo l' (d : Z) (x : list byte), hl_recs l' = hl_recs lo ++ [(d, x)] ->
  hl_cap l' = grow_cap (hl_n lo) (hl_cap lo) -> 0 <= hl_n lo <= hl_cap lo -> nw_list l' <= nw_list lo + NC_PER.
Proof.
  intros lo l' d x HR HC HN. unfold nw_list. rewrite HC. unfold grow_cap. unfold hl_n in *.
  rewrite HR, length_app. cbn [length]. unfold NC_PER.
  destruct (Z.eqb_spec (Z.of_nat (length (hl_recs lo))) (hl_cap lo)); destruct (Z.eqb_spec (hl_cap lo) 0); lia.
Qed.

Lemma push_nw_src : forall h l' d x, hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] ->
  (hl_recs (hs_pending h) = [] -> hs_off h = 0) ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= hl_n (hs_pending h) <= hl_cap (hs_pending h) ->
  nw_src (set_pending h l') <= nw_src h + NC_PER + DATA_PER * Z.of_nat (length x).
Proof.
  intros h l' d x HR H0 HC HN. pose proof (push_nw_list (hs_pending h) l' d x HR HC HN) as NL.
  unfold nw_src. rewrite (pending_push h l' d x HR H0), length_app.
  cbn [set_pending hs_pending hs_expected hs_held]. unfold DATA_PER, NC_PER in *. lia.
Qed.

Lemma fresh_nw : forall B mem es, AllocBound.zsum nw_ent (map (fresh_entry B mem) es) = AllocBound.zsum nw_ent es.
Proof.
  intros B mem es. induction es as [|e es IH]; [reflexivity|]. cbn [map]. rewrite !AllocBound.zsum_cons, IH. f_equal.
  unfold nw_ent, re_nheld, fresh_entry. cbn [re_cap re_used re_hp re_kh re_keys]. rewrite length_map. reflexivity.
Qed.

Definition push_EW (LA : Z) (l : hlist) (a : Z) : Prop :=
  LA <= a < LA + 16 \/ (0 < hl_cap l /\ hl_v l <= a < hl_v l + 16 * hl_cap l).

Definition push_FW (l : hlist) (q : Z) : Prop := q = hl_v l /\ 0 < hl_cap l.

Lemma forall2_mid : forall {X Y} (P : X -> Y -> Prop) xs hj1 y hj2, Forall2 P xs (hj1 ++ y :: hj2) ->
  exists xs1 x xs2, xs = xs1 ++ x :: xs2 /\ length xs1 = length hj1 /\ P x y /\ Forall2 P xs1 hj1 /\
    Forall2 P xs2 hj2.
Proof.
  intros X Y P xs hj1 y hj2 H. apply Forall2_app_inv_r in H as (xs1 & xs2' & H1 & H2 & ->).
  inversion H2 as [|x0 y0 l0 l0' Hxy Hr]; subst.
  exists xs1, x0, l0. split; [reflexivity|]. split; [exact (Forall2_length H1)|]. split; [exact Hxy|].
  split; [exact H1|exact Hr].
Qed.

Lemma input_bytes : forall B mem E TA L A k m,
  driver_kept B E TA L A mem -> blk_data B (ss_mem E) (ss_p E) (ss_pl E) ->
  ss_n E = Z.of_nat (length (ss_pl E)) -> 0 <= k -> 0 <= m -> k + m <= ss_n E -> 0 <= ss_p E ->
  ss_p E + ss_n E <= 2 ^ 64 ->
  bytes_at (ms_segs B) mem (ss_p E + k) (firstn (Z.to_nat m) (skipn (Z.to_nat k) (ss_pl E))).
Proof.
  intros B mem E TA L A k m (_ & _ & D3 & _) BD LEN Hk Hm Hkm H0 H1.
  assert (LX : length (firstn (Z.to_nat m) (skipn (Z.to_nat k) (ss_pl E))) = Z.to_nat m).
  { rewrite length_firstn, length_skipn. lia. }
  apply bytes_at_of_mbyte; [lia|rewrite LX; lia|].
  intros i Hi. rewrite LX in Hi.
  replace (ss_p E + k + Z.of_nat i) with (ss_p E + (k + Z.of_nat i)) by lia.
  rewrite (D3 (k + Z.of_nat i)) by lia. rewrite (BD (k + Z.of_nat i)) by lia.
  rewrite nth_error_firstn, (proj2 (Nat.ltb_lt i (Z.to_nat m)) Hi), nth_error_skipn.
  f_equal. lia.
Qed.

Lemma ta_split_push : forall G OUT es hj1 h l' i hj2,
  target_addrs G OUT es (hj1 ++ (set_pending h l', i) :: hj2) =
  (G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj1)) ++
  list_blocks l' ++
  (([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ++
   concat (map (fun p => hs_blocks (fst p)) hj2)).
Proof. intros. rewrite ta_split. reflexivity. Qed.

(* ---- list_push moves the view's nc blocks by grow_dels / grow_adds (push_RV_s). ---- *)

Lemma p1_blk_nn {rc : YM05.RunCeil} : forall (B : malloc_syms) (API : AllocAPI B) L A m md x k, aa_MR API L A m md ->
  In (x, k) (blocks L A) -> 0 <= k.
Proof.
  intros B API L A m md x k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-.
  exact (relay_remove_b_lem.rk_ub_nonneg A p k' (mr_wf _ _ (aa_laws API) L A m md HM) Hp).
Qed.

Lemma p1_concat_incl : forall {X Y : Type} (f g : X -> list Y) l y,
  (forall a z, In z (f a) -> In z (g a)) -> In y (concat (map f l)) -> In y (concat (map g l)).
Proof.
  intros X Y f g l y Hfg Hy. apply in_concat in Hy as (ys & Hys & Hy). apply in_map_iff in Hys as (a & <- & Ha).
  apply in_concat. exists (g a). split; [apply in_map; exact Ha|exact (Hfg a y Hy)].
Qed.

Lemma p1_arr_lb : forall l x, In x (arr_nc l) -> In x (list_blocks l).
Proof. intros l x H. unfold list_blocks. apply in_or_app. left. exact H. Qed.

Lemma p1_enc_eb : forall e x, In x (entry_nc e) -> In x (entry_blocks e).
Proof. intros e x H. unfold entry_nc in H. unfold entry_blocks. rewrite app_assoc. apply in_or_app. left. exact H. Qed.

Lemma p1_snc_hb : forall h x, In x (src_nc h) -> In x (hs_blocks h).
Proof.
  intros h x H. unfold src_nc in H. unfold hs_blocks. rewrite !in_app_iff in H |- *.
  destruct H as [H|[H|[H|H]]]; [left; exact (p1_arr_lb _ _ H)|right; left; exact H
    |right; right; left; exact (p1_arr_lb _ _ H)|right; right; right; exact (p1_arr_lb _ _ H)].
Qed.

Lemma p1_lb_in : forall l q, 0 <= hl_cap l ->
  In q (list_blocks l) <-> (0 < hl_cap l /\ q = hl_v l) \/ In q (map fst (hl_recs l)).
Proof.
  intros l q HC. unfold list_blocks. rewrite in_app_iff. destruct (Z.eqb_spec (hl_cap l) 0) as [E|E].
  - split; [intros [[]|H]; right; exact H|intros [(X & _)|H]; [lia|right; exact H]].
  - split.
    + intros [[<-|[]]|H]; [left; split; [lia|reflexivity]|right; exact H].
    + intros [(_ & ->)|H]; [left; left; reflexivity|right; exact H].
Qed.

Lemma p1_nc_split : forall G OUT es hj1 h i hj2,
  rv_nc (view_of G OUT es (hj1 ++ (h, i) :: hj2)) =
  (G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj1)) ++ arr_nc (hs_pending h) ++
  (([hs_partial h] ++ arr_nc (hs_expected h) ++ arr_nc (hs_held h)) ++ concat (map (fun p => src_nc (fst p)) hj2)).
Proof.
  intros G OUT es hj1 h i hj2. unfold view_of, src_nc. cbn [rv_nc]. rewrite map_app, concat_app. cbn [map concat fst app].
  repeat rewrite <- app_assoc. cbn [app]. repeat rewrite <- app_assoc. reflexivity.
Qed.

Section PM.
Context {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.

(* lo (N records, CAP slots) is the pending list of h; list_push makes l' with the text txt at d appended. The array
   is freed and remade when N = CAP; the text block d is a new block that is not an nc block. *)
Lemma push_move : forall (L : layout) (A : astate) (mem : word -> option byte) (L' : layout) (A' : astate)
    (mem' : word -> option byte) (LA LA' G OUT : Z) (es es' : list rentry) (hj1 : list (hsrc * nat)) (h : hsrc)
    (i : nat) (hj2 : list (hsrc * nat)) (lo : hlist) (N CAP : Z) (l' : hlist) (d : Z) (txt : list byte),
  hs_pending h = lo -> N = hl_n lo -> CAP = hl_cap lo ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall x m, In (x, m) (blocks L' A') -> 0 <= m) ->
  NoDup (target_addrs G OUT es (hj1 ++ (h, i) :: hj2)) ->
  concat (map entry_nc es') = concat (map entry_nc es) ->
  list_at Bm L A mem LA lo false -> list_at Bm L' A' mem' LA' l' false ->
  hl_recs l' = hl_recs lo ++ [(d, txt)] -> hl_cap l' = grow_cap N CAP -> (N < CAP -> hl_v l' = hl_v lo) ->
  (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks lo) -> In (q, m) (blocks L' A')) ->
  (forall q m, In (q, m) (blocks L' A') ->
     (In (q, m) (blocks L A) /\ (0 < m -> ~ In q (list_blocks lo))) \/ In q (list_blocks l')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks lo) -> ~ In q (list_blocks l')) ->
  nc_move (view_of G OUT es (hj1 ++ (h, i) :: hj2)) L A
    (view_of G OUT es' (hj1 ++ (set_pending h l', i) :: hj2)) L' A'
    (grow_dels (hl_v lo) N CAP) (grow_adds (hl_v l') N CAP).
Proof.
  intros L A mem L' A' mem' LA LA' G OUT es es' hj1 h i hj2 lo N CAP l' d txt Elo EN0 EC0 ND0 ND1 NN1 NDT EN
    LP LP' HREC HCAP HV KB1 KB2 KB3.
  pose proof LP as (_ & (NC0 & _) & AR0 & _ & RV0 & FA0).
  pose proof LP' as (_ & _ & AR1 & RND1 & RV1 & FA1).
  rewrite Forall_forall in FA0, FA1.
  assert (N0 : 0 <= N) by (rewrite EN0; unfold hl_n; lia).
  assert (NC : N <= CAP) by (rewrite EN0, EC0; exact NC0).
  assert (C0 : 0 <= CAP) by lia.
  assert (CP' : N = CAP -> 0 < hl_cap l').
  { intros EQ. rewrite HCAP. unfold grow_cap. rewrite (proj2 (Z.eqb_eq N CAP) EQ).
    destruct (Z.eqb_spec CAP 0); cbn [negb]; lia. }
  assert (CE : N <> CAP -> hl_cap l' = CAP).
  { intros NE. rewrite HCAP. unfold grow_cap. rewrite (proj2 (Z.eqb_neq N CAP) NE). reflexivity. }
  assert (C1 : 0 <= hl_cap l') by (destruct (Z.eq_dec N CAP) as [EQ|NE]; [pose proof (CP' EQ)|rewrite (CE NE)]; lia).
  assert (VBo : 0 < CAP -> In (hl_v lo, 16 * CAP) (blocks L A)).
  { intros HC. rewrite EC0 in HC |- *. destruct AR0 as [(X & _)|(_ & Hin & _)]; [lia|exact Hin]. }
  assert (VBn : 0 < hl_cap l' -> In (hl_v l', 16 * hl_cap l') (blocks L' A')).
  { intros HC. destruct AR1 as [(X & _)|(_ & Hin & _)]; [lia|exact Hin]. }
  assert (RB0 : forall r, In r (hl_recs lo) -> In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A))
    by (intros r Hr; exact (proj1 (FA0 r Hr))).
  assert (RL : forall r, In r (hl_recs lo) \/ r = (d, txt) -> In r (hl_recs l')).
  { intros r Hr. rewrite HREC. apply in_or_app. destruct Hr as [Hr| ->]; [left; exact Hr|right; left; reflexivity]. }
  assert (RB1 : forall r, In r (hl_recs lo) \/ r = (d, txt) ->
      In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L' A'))
    by (intros r Hr; exact (proj1 (FA1 r (RL r Hr)))).
  apply hf_nodup in RND1. rewrite HREC, map_app in RND1. cbn [map fst] in RND1.
  assert (DNO : ~ In d (map fst (hl_recs lo))).
  { intros X. exact (hf_nodup_disj _ _ d RND1 X (or_introl eq_refl)). }
  rewrite HREC, map_app in RV1. cbn [map fst] in RV1.
  assert (VD : hl_v l' <> d) by (intros X; apply RV1; apply in_or_app; right; left; exact (eq_sym X)).
  assert (VR : ~ In (hl_v l') (map fst (hl_recs lo))) by (intros X; apply RV1; apply in_or_app; left; exact X).
  assert (LBo : forall q, In q (list_blocks lo) <-> (0 < CAP /\ q = hl_v lo) \/ In q (map fst (hl_recs lo))).
  { intros q. rewrite EC0. apply p1_lb_in. rewrite <- EC0. exact C0. }
  assert (LBn : forall q, In q (list_blocks l') <->
      (0 < hl_cap l' /\ q = hl_v l') \/ In q (map fst (hl_recs lo)) \/ d = q).
  { intros q. rewrite (p1_lb_in l' q C1), HREC, map_app, in_app_iff. cbn [map fst In]. tauto. }
  assert (KD : forall m, In (d, m) (blocks L A) -> 0 < m -> N = CAP /\ 0 < CAP /\ d = hl_v lo).
  { intros m Hm Pm. destruct (List.in_dec Z.eq_dec d (list_blocks lo)) as [Hl|Hl].
    - apply LBo in Hl as [(Cp & Ed)|Hl]; [|contradiction].
      split; [|split; [exact Cp|exact Ed]].
      destruct (Z.eq_dec N CAP) as [EQ|NE]; [exact EQ|exfalso].
      apply VD. rewrite Ed. apply HV. lia.
    - exfalso. apply (KB3 d m Hm Pm Hl). apply LBn. right. right. reflexivity. }
  assert (KV : N = CAP -> forall m, In (hl_v l', m) (blocks L A) -> 0 < m -> 0 < CAP /\ hl_v l' = hl_v lo).
  { intros EQ m Hm Pm. destruct (List.in_dec Z.eq_dec (hl_v l') (list_blocks lo)) as [Hl|Hl].
    - apply LBo in Hl as [(Cp & E)|Hl]; [split; [exact Cp|exact E]|contradiction].
    - exfalso. apply (KB3 _ m Hm Pm Hl). apply LBn. left. split; [exact (CP' EQ)|reflexivity]. }
  assert (AD : forall t, In t (grow_adds (hl_v l') N CAP) <-> N = CAP /\ t = (hl_v l', 16 * hl_cap l')).
  { intros u. unfold grow_adds. rewrite HCAP. unfold grow_cap. destruct (Z.eqb_spec N CAP) as [EQ|NE].
    - destruct (Z.eqb_spec CAP 0) as [Z0|Z0]; cbn [In]; split.
      + intros [<-|[]]. split; [exact EQ|f_equal; lia].
      + intros (_ & ->). left. f_equal; lia.
      + intros [<-|[]]. split; [exact EQ|f_equal; lia].
      + intros (_ & ->). left. f_equal; lia.
    - cbn [In]. split; [intros []|intros (X & _); contradiction]. }
  assert (DL : forall t, In t (grow_dels (hl_v lo) N CAP) <-> N = CAP /\ 0 < CAP /\ t = (hl_v lo, 16 * CAP)).
  { intros u. unfold grow_dels.
    destruct (Z.eqb_spec N CAP) as [EQ|NE]; destruct (Z.eqb_spec CAP 0) as [Z0|Z0]; cbn [andb negb In].
    - split; [intros []|intros (_ & X & _); lia].
    - split; [intros [<-|[]]; split; [exact EQ|split; [lia|reflexivity]]|intros (_ & _ & ->); left; reflexivity].
    - split; [intros []|intros (X & _); contradiction].
    - split; [intros []|intros (X & _); contradiction]. }
  assert (DEC : forall a b : Z * Z, {a = b} + {a <> b}) by (decide equality; apply Z.eq_dec).
  pose (keep := fun x : Z => negb (((N =? CAP) && negb (CAP =? 0)) && (x =? hl_v lo))).
  assert (KF : forall x, keep x = false -> N = CAP /\ 0 < CAP /\ x = hl_v lo).
  { intros x Hx. unfold keep in Hx. cbv beta in Hx. apply negb_false_iff in Hx. apply andb_prop in Hx as (Hx & Hv).
    apply andb_prop in Hx as (He & Hz). apply Z.eqb_eq in He, Hv. apply negb_true_iff in Hz. apply Z.eqb_neq in Hz.
    split; [exact He|split; [lia|exact Hv]]. }
  assert (KT : forall x, (N = CAP -> 0 < CAP -> x <> hl_v lo) -> keep x = true).
  { intros x Hx. destruct (keep x) eqn:K; [reflexivity|]. destruct (KF x K) as (X1 & X2 & X3).
    exfalso. exact (Hx X1 X2 X3). }
  assert (KFT : forall x, N = CAP -> 0 < CAP -> x = hl_v lo -> keep x = false).
  { intros x EQ Cp ->. unfold keep. cbv beta.
    rewrite (proj2 (Z.eqb_eq N CAP) EQ), (proj2 (Z.eqb_neq CAP 0) ltac:(lia)), Z.eqb_refl. reflexivity. }
  pose (Pf := G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj1)).
  pose (Sf := ([hs_partial h] ++ arr_nc (hs_expected h) ++ arr_nc (hs_held h)) ++
              concat (map (fun p => src_nc (fst p)) hj2)).
  pose (R := Pf ++ (if N =? CAP then [] else arr_nc lo) ++ Sf).
  assert (NV : rv_nc (view_of G OUT es (hj1 ++ (h, i) :: hj2)) = Pf ++ arr_nc lo ++ Sf)
    by (rewrite p1_nc_split, Elo; reflexivity).
  assert (NV' : rv_nc (view_of G OUT es' (hj1 ++ (set_pending h l', i) :: hj2)) = Pf ++ arr_nc l' ++ Sf)
    by (rewrite p1_nc_split, EN; reflexivity).
  assert (ARo : arr_nc lo = if CAP =? 0 then [] else [hl_v lo]) by (rewrite EC0; reflexivity).
  assert (ARn1 : N = CAP -> arr_nc l' = [hl_v l']).
  { intros EQ. pose proof (CP' EQ) as Cp. unfold arr_nc. rewrite (proj2 (Z.eqb_neq (hl_cap l') 0) ltac:(lia)).
    reflexivity. }
  assert (ARn2 : N <> CAP -> arr_nc l' = arr_nc lo).
  { intros NE. unfold arr_nc. rewrite (CE NE), (HV ltac:(lia)), <- EC0. reflexivity. }
  assert (RXY : forall x, In x R -> N = CAP ->
      In x ((G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj1)) ++
            (([hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks (hs_held h)) ++
             concat (map (fun p => hs_blocks (fst p)) hj2)))).
  { intros x Hx EQ. unfold R in Hx.
    replace (if N =? CAP then [] else arr_nc lo) with (@nil Z) in Hx
      by (rewrite (proj2 (Z.eqb_eq N CAP) EQ); reflexivity).
    rewrite app_nil_l in Hx. unfold Pf, Sf in Hx.
    apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right].
    - destruct Hx as [<-|[<-|Hx]]; [left; reflexivity|right; left; reflexivity|right; right].
      apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff.
      + left. exact (p1_concat_incl entry_nc entry_blocks es x p1_enc_eb Hx).
      + right. exact (p1_concat_incl (fun p => src_nc (fst p)) (fun p => hs_blocks (fst p)) hj1 x
          (fun a z H => p1_snc_hb (fst a) z H) Hx).
    - rewrite !in_app_iff in Hx |- *.
      destruct Hx as [[Hx|[Hx|Hx]]|Hx];
        [left; left; exact Hx|left; right; left; exact (p1_arr_lb _ _ Hx)
        |left; right; right; exact (p1_arr_lb _ _ Hx)|right].
      exact (p1_concat_incl (fun p => src_nc (fst p)) (fun p => hs_blocks (fst p)) hj2 x
        (fun a z H => p1_snc_hb (fst a) z H) Hx). }
  assert (KR : forall x m, In (x, m) (blocks L A) -> keep x = false -> ~ In x R).
  { intros x m _ Kx Hx. destruct (KF x Kx) as (EQ & Cp & Ex).
    rewrite ta_split, Elo in NDT.
    apply (nodup_mid_out _ _ _ x NDT (RXY _ Hx EQ)). apply LBo. left. split; [exact Cp|exact Ex]. }
  assert (H1 : forall x m, In (x, m) (blocks L' A') -> (In (x, m) (blocks L A) /\ keep x = true) \/
      In (x, m) (grow_adds (hl_v l') N CAP ++ [(d, Z.of_nat (length txt) + 1)])).
  { intros x m Hn. destruct (KB2 x m Hn) as [(Ho & HN)|HL].
    - left. split; [exact Ho|]. apply KT. intros EQ Cp Ex. rewrite Ex in Ho, HN.
      rewrite (mv_fst_uniq _ _ m (16 * CAP) ND0 Ho (VBo Cp)) in HN.
      apply (HN ltac:(lia)). apply LBo. left. split; [exact Cp|reflexivity].
    - apply LBn in HL as [(Cp' & Ex)|[HL|Ex]].
      + subst x. rewrite (mv_fst_uniq _ _ m (16 * hl_cap l') ND1 Hn (VBn Cp')).
        destruct (Z.eq_dec N CAP) as [EQ|NE].
        * right. apply in_or_app. left. apply AD. split; [exact EQ|reflexivity].
        * left. assert (NL : N < CAP) by lia. rewrite (HV NL), (CE NE).
          split; [apply VBo; lia|]. apply KT. intros X. contradiction.
      + apply in_map_iff in HL as (r & Ex & Hr). subst x.
        rewrite (mv_fst_uniq _ _ m _ ND1 Hn (RB1 r (or_introl Hr))).
        left. split; [exact (RB0 r Hr)|]. apply KT. intros _ _ X. apply RV0. rewrite <- X. apply in_map. exact Hr.
      + subst x. rewrite (mv_fst_uniq _ _ m _ ND1 Hn (RB1 (d, txt) (or_intror eq_refl))). cbn [fst snd].
        right. apply in_or_app. right. left. reflexivity. }
  assert (H2 : forall x m, In (x, m) (blocks L A) -> keep x = true -> In (x, m) (blocks L' A')).
  { intros x m Ho Kx. destruct (List.in_dec Z.eq_dec x (list_blocks lo)) as [HL|HL]; [|exact (KB1 x m Ho HL)].
    apply LBo in HL as [(Cp & Ex)|HL].
    - subst x. assert (NE : N <> CAP).
      { intros EQ. rewrite (KFT _ EQ Cp eq_refl) in Kx. discriminate. }
      rewrite (mv_fst_uniq _ _ m (16 * CAP) ND0 Ho (VBo Cp)). rewrite <- (HV ltac:(lia)), <- (CE NE).
      apply VBn. rewrite (CE NE). exact Cp.
    - apply in_map_iff in HL as (r & Ex & Hr). subst x.
      rewrite (mv_fst_uniq _ _ m _ ND0 Ho (RB0 r Hr)). exact (RB1 r (or_introl Hr)). }
  assert (H3 : incl (grow_adds (hl_v l') N CAP ++ [(d, Z.of_nat (length txt) + 1)]) (blocks L' A')).
  { intros u Hu. apply in_app_iff in Hu as [Hu|[<-|[]]].
    - apply AD in Hu as (EQ & ->). exact (VBn (CP' EQ)).
    - exact (RB1 (d, txt) (or_intror eq_refl)). }
  assert (NDa : List.NoDup (grow_adds (hl_v l') N CAP ++ [(d, Z.of_nat (length txt) + 1)])).
  { apply mv_nodup_app.
    - unfold grow_adds. destruct (N =? CAP); cbn [app]; repeat constructor; intros [].
    - repeat constructor. intros [].
    - intros a Ha [<-|[]]. apply AD in Ha as (_ & E). injection E as E1 E2. exact (VD (eq_sym E1)). }
  assert (Ka : forall t, In t (grow_adds (hl_v l') N CAP ++ [(d, Z.of_nat (length txt) + 1)]) ->
      keep (fst t) = false \/ ~ In t (blocks L A)).
  { intros u Hu. destruct (List.in_dec DEC u (blocks L A)) as [Hin|Hin]; [left|right; exact Hin].
    apply in_app_iff in Hu as [Hu|[<-|[]]].
    - apply AD in Hu as (EQ & ->). cbn [fst]. pose proof (CP' EQ) as Cp'.
      destruct (KV EQ _ Hin ltac:(lia)) as (Cp & E). exact (KFT _ EQ Cp E).
    - cbn [fst]. destruct (KD _ Hin ltac:(lia)) as (EQ & Cp & E). exact (KFT _ EQ Cp E). }
  apply (mv_build _ _ L A L' A' _ _ [(d, Z.of_nat (length txt) + 1)] R [] keep ND0 ND1).
  - rewrite NV. unfold R. rewrite app_nil_r, <- app_assoc. apply Permutation_app_head.
    unfold grow_dels. rewrite ARo.
    destruct (Z.eqb_spec N CAP) as [EQ|NE]; destruct (Z.eqb_spec CAP 0) as [Z0|Z0]; cbn [andb negb map fst app].
    + rewrite app_nil_r. apply Permutation_refl.
    + apply Permutation_cons_append.
    + rewrite app_nil_r. apply Permutation_refl.
    + rewrite app_nil_r. apply Permutation_refl.
  - rewrite NV'. unfold R. rewrite <- app_assoc. apply Permutation_app_head. unfold grow_adds.
    destruct (Z.eqb_spec N CAP) as [EQ|NE].
    + rewrite (ARn1 EQ). cbn [map fst app]. apply Permutation_cons_append.
    + rewrite (ARn2 NE). cbn [map fst app]. rewrite app_nil_r. apply Permutation_refl.
  - intros u Hu. apply DL in Hu as (_ & Cp & ->). exact (VBo Cp).
  - unfold grow_dels. destruct ((N =? CAP) && negb (CAP =? 0)); cbn [map fst]; repeat constructor; intros [].
  - intros u Hu. apply DL in Hu as (EQ & Cp & ->). cbn [fst]. exact (KFT _ EQ Cp eq_refl).
  - exact KR.
  - exact H1.
  - exact H2.
  - exact H3.
  - exact NDa.
  - exact Ka.
  - exact NN1.
  - intros u Hu. apply DL in Hu as (_ & Cp & ->). cbn [snd]. lia.
  - intros g [].
Qed.

End PM.

Section P1.
Variable F : ResFormT.

Lemma MI_op1 : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> RI_mono RI ->
  push_resources_s F RI -> (forall fx', @list_push_contract fx' rc B (API rc) F) -> 0 < ss_n E ->
  walk_at (ss_pl E) (t + 1) (take_end E K) ->
  (K + 2 <= ss_n E -> In (CK 1 (K + 2) (plz (firstn (Z.to_nat (Z.min (in_byte E K + 256 * in_byte E (K + 1))
                                                                       (ss_n E - (K + 2))))
                                                  (skipn (Z.to_nat (K + 2)) (ss_pl E))))) (pl_chunks (ss_pl E))) ->
  MI (rc := rc) B (API rc) E RI t K 0x13c98
    (fun _ hj no regs => no = 0 /\ disp_src 1 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB RIM HRES HLP HN0 HW HCK HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (SL : block_slack_present B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (BLOW : blocks_low B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (ERR : errno_addr B = 0x311ec) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as ((LPRE & LEN & BD & _) & _ & _ & _ & _ & _ & NIT & _).
  pose proof LPRE as (_ & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TP & _ & _ & _ & INPUT & _).
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x13c98 =? TAIL_CHECK) || (0x13c98 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  assert (Hnfd' : 0 <= nfd <= t + 1) by (revert Hnfd; unfold TAIL_CHECK, TAIL_STEP; cbn; lia). clear Hnfd.
  destruct HR as (_ & DS & (B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & R9 & R15).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  destruct INPUT as [(X & _)|(_ & q0 & Hq0 & Eq0)]; [lia|].
  assert (INB : In (ss_p E, ss_n E) (blocks L A) /\ ~ In (ss_p E) (target_addrs G (bv_unsigned out) es hj)).
  { destruct HDK as (D1 & _).
    destruct (D1 q0 (ss_n E) Hq0 ltac:(rewrite Eq0; exact (NIT HN0))) as (HNT & q' & Hq' & Eq').
    rewrite Eq0 in HNT, Eq'. split; [|exact (HNT HN0)].
    rewrite <- Eq'. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q', ss_n E) Hq'). }
  destruct INB as (INB & INT).
  assert (PB : 4096 <= ss_p E /\ ss_p E + ss_n E <= YM05.alloc_ceiling).
  { split; [exact (BLOW L A mem md _ _ HMR INB)|].
    pose proof INB as INB'. unfold blocks in INB'. apply in_map_iff in INB' as ([q n] & EQ & Hq).
    cbn [fst snd] in EQ. injection EQ as EQ1 EQ2. subst n.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ q (ss_n E) (ss_n E - 1) HMR Hq ltac:(lia)) as (_ & IB0 & IB1 & _).
    lia. }
  assert (RB : forall k0, 0 <= k0 < ss_n E -> ov_read_bytes rsegs mem (Z_to_bv 64 (ss_p E + k0)) 1 =
      Some [nth (Z.to_nat k0) (ss_pl E) (Z_to_bv 8 0)]).
  { intros k0 Hk0. rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia]. }
  assert (HS : 0 <= s < 2 ^ 63) by (destruct DS as [(_ & i & HI & _ & ->)|(_ & ->)]; unfold G_S, SRC_SIZE; lia).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 s) by exact R9.
  assert (E15 : reg_get regs 15 = Z_to_bv 64 1) by exact R15.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - K)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E15, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (op1_run (ss_p E) (ss_n E) K s); [lia|unfold INPUT_MAX in Hn; lia|lia|lia|exact HS| |].
    - intros HK1. apply RB. lia.
    - intros HK1. replace (ss_p E + K + 1) with (ss_p E + (K + 1)) by lia. apply RB. lia. }
  intros ms1 (can1 & (r1 & s0 & a0 & a1 & a2 & s2 & s7 & pc & D & M & -> & HD & HD0 & HDN & HM0 & HM1 & HKE & ES2 & ES7 & HC)
    & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1). subst s2 s7.
  destruct HC as [(HS0 & -> & -> & ->)|(HSN & HMP & -> & -> & -> & -> & -> & ->)].
  - replace (ss_p E + K + D + M) with (ss_p E + (K + D + M)) in X1 by lia.
    replace (ss_n E - K - D - M) with (ss_n E - (K + D + M)) in X1 by lia.
    rewrite <- SEG.
    eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t (K + D + M)
      (fun _ _ _ r => tail_regs E t (K + D + M) r)); [exact HF|exact CB|intros; assumption|rewrite HKE; exact HW|]
      |intros c' HC'; exists (K + D + M); exact HC'].
    exists fx', L, A, R1, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj.
    split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
    split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X1|].
    split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [exact HRO|]. split; [exact HIK|]. split; [exact HST|]. split; [exact HDK|]. split; [exact HGL|].
    split; [unfold TAIL_CHECK, TAIL_STEP; cbn; lia|]. split; [exact HOUT|].
    split; [eapply relay_at_t; [exact HREL|unfold TAIL_CHECK, TAIL_STEP; cbn; lia]|].
    split; [exact Hes|]. split; [lia|]. eapply RIM; [exact HRI|lia].
  - assert (D2 : D = 2) by lia. subst D.
    assert (MEQ : M = Z.min (in_byte E K + 256 * in_byte E (K + 1)) (ss_n E - (K + 2))).
    { assert (TE : K + 2 + M = take_end E K) by exact HKE. unfold take_end in TE.
      rewrite (proj2 (Z.leb_le _ _) HDN) in TE. clear - TE. lia. }
    pose proof (HCK HDN) as HCK1. rewrite <- MEQ in HCK1.
    destruct DS as [(_ & i & HI & OI & ->)|(_ & X)]; [|exfalso; exact (HSN X)].
    set (HA := G_S + SRC_SIZE * Z.of_nat i) in *.
    assert (HAR : 0x31040 <= HA /\ HA + 96 <= 0x311c0) by (unfold HA, G_S, SRC_SIZE; lia).
    assert (HIN : exists h, In (h, i) hj).
    { unfold slot_open in OI. apply existsb_exists in OI. destruct OI as (q & HQ & HE).
      apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
      exists h. exact HQ. }
    destruct HIN as (h & HHI).
    destruct (in_split _ _ HHI) as (hj1 & hj2 & EHJ). subst hj.
    pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _).
    destruct (forall2_mid _ _ _ _ _ PA) as (es1 & e & es2 & EES & HL1 & PE & _ & _). subst es. clear PA.
    pose proof PE as PE'. unfold pair_ok in PE'. cbv zeta in PE'. cbn [fst snd] in PE'.
    destruct PE' as (SRC & _ & _ & _ & _ & _ & _ & PN & PCAP & _ & _ & _).
    pose proof SRC as (_ & _ & _ & _ & _ & LP & _ & H5 & _).
    pose proof LP as (_ & LB & LAR & _).
    assert (OFF : hl_recs (hs_pending h) = [] -> hs_off h = 0).
    { intros E0. destruct H5 as [(_ & F0)|(r & rs & E1 & _)]; [exact F0|]. rewrite E0 in E1. discriminate. }
    assert (HMW : M <= WRITE_MAX) by (unfold WRITE_MAX; lia).
    assert (RS1 : 0 <= hl_n (hs_pending h) <= hl_cap (hs_pending h)) by (unfold hl_n in *; lia).
    assert (RS2 : hl_n (hs_pending h) < OPS_MAX) by (unfold OPS_MAX in *; lia).
    assert (RS3 : hl_cap (hs_pending h) <= 2 * OPS_MAX) by (unfold OPS_MAX in *; lia).
    assert (LTX : Z.of_nat (length (firstn (Z.to_nat M) (skipn (Z.to_nat (K + 2)) (ss_pl E)))) = M)
      by (rewrite length_firstn, length_skipn; lia).
    assert (NDL : List.NoDup (map fst (blocks L A))) by (apply hf_nodup; exact (NDB L A mem md HMR)).
    destruct (HRES E K (K + 2 + M) L A (hs_pending h) (firstn (Z.to_nat M) (skipn (Z.to_nat (K + 2)) (ss_pl E)))
      G (bv_unsigned out) (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2) HRI NDL RS1 RS2 RS3
      ltac:(rewrite LTX; lia) ltac:(rewrite LTX; reflexivity) ltac:(lia)) as (bnd & ROK & ROOM & RIK).
    assert (G1 : getr R1 1 = Z_to_bv 64 0x13d34) by geq X1.
    assert (G2 : getr R1 2 = Z_to_bv 64 (slot_sp E)) by geq X1.
    assert (G3 : getr R1 3 = getr (ss_regs E) 3) by geq X1.
    assert (G4 : getr R1 4 = getr (ss_regs E) 4) by geq X1.
    assert (G8 : getr R1 8 = Z_to_bv 64 (ss_p E + K + 2)) by geq X1.
    assert (G9 : getr R1 9 = Z_to_bv 64 (HA)) by geq X1.
    assert (G10 : getr R1 10 = Z_to_bv 64 (HA + 16)) by geq X1.
    assert (G11 : getr R1 11 = Z_to_bv 64 (ss_p E + K + 2)) by geq X1.
    assert (G12 : getr R1 12 = Z_to_bv 64 M) by geq X1.
    assert (G18 : getr R1 18 = Z_to_bv 64 (ss_p E + K + 2 + M)) by geq X1.
    assert (G19 : getr R1 19 = Z_to_bv 64 (slot_sp E + 32)) by geq X1.
    assert (G20 : getr R1 20 = Z_to_bv 64 G_RELAY_LO) by geq X1.
    assert (G21 : getr R1 21 = Z_to_bv 64 DIV10) by geq X1.
    assert (G22 : getr R1 22 = Z_to_bv 64 t) by geq X1.
    assert (G23 : getr R1 23 = Z_to_bv 64 (ss_n E - K - 2 - M)) by geq X1.
    assert (G24 : getr R1 24 = Z_to_bv 64 (slot_sp E + 16)) by geq X1.
    assert (G25 : getr R1 25 = Z_to_bv 64 4) by geq X1.
    assert (G26 : getr R1 26 = Z_to_bv 64 (G_S + 4)) by geq X1.
    assert (G27 : getr R1 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by geq X1.
    assert (U10 : bv_unsigned (getr R1 10) = HA + 16) by (rewrite G10; apply unsigned_lit; lia).
    assert (U11 : bv_unsigned (getr R1 11) = ss_p E + K + 2) by (rewrite G11; apply unsigned_lit; lia).
    assert (U12 : bv_unsigned (getr R1 12) = M) by (rewrite G12; apply unsigned_lit; lia).
    assert (G2' : YK11.getr R1 2 = Z_to_bv 64 (slot_sp E)) by exact G2.
    assert (G1y : YK11.getr R1 1 = Z_to_bv 64 0x13d34) by exact G1.
    assert (G4y : YK11.getr R1 4 = getr (ss_regs E) 4) by exact G4.
    assert (SPR : spZ R1 = slot_sp E) by (unfold spZ; rewrite G2'; apply unsigned_lit; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
    assert (U10y : bv_unsigned (YK11.getr R1 10) = HA + 16) by exact U10.
    assert (U11y : bv_unsigned (YK11.getr R1 11) = ss_p E + K + 2) by exact U11.
    assert (U12y : bv_unsigned (YK11.getr R1 12) = M) by exact U12.
    assert (VB : 0 < hl_cap (hs_pending h) -> In (hl_v (hs_pending h), 16 * hl_cap (hs_pending h)) (blocks L A))
      by (intros HC0; exact (proj1 (hf_list_v B L A mem _ _ _ LP HC0))).
    assert (VT : 0 < hl_cap (hs_pending h) ->
        In (hl_v (hs_pending h)) (target_addrs G (bv_unsigned out) (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2))).
    { intros HC0. rewrite ta_split. apply in_app_iff. right. apply in_app_iff. left.
      exact (proj2 (hf_list_v B L A mem _ _ _ LP HC0)). }
    assert (PV : ss_p E <> hl_v (hs_pending h)).
    { intros EV. destruct (Z.lt_ge_cases 0 (hl_cap (hs_pending h))) as [HC0|HC0].
      - apply INT. rewrite EV. exact (VT HC0).
      - destruct LAR as [(_ & V0)|(X & _)]; [lia|lia]. }
    assert (INX := input_bytes B mem E _ L A (K + 2) M HDK BD LEN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    replace (ss_p E + (K + 2)) with (ss_p E + K + 2) in INX by lia.
    rewrite <- SEG. eapply SR_bind.
    { apply (HLP fx' L A R1 mem md bnd (hs_pending h) false (firstn (Z.to_nat M) (skipn (Z.to_nat (K + 2)) (ss_pl E)))).
      - exact SEG.
      - unfold call_pre_k. rewrite SPR.
        split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite ?G1, ?G1y; unfold YK0s.ret_ok; vm_compute; reflexivity|].
        split; [unfold slot_sp, SLOT_FRAME; lia|].
        split; [unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
        split; [unfold slot_sp, SLOT_FRAME in *; lia|].
        split.
        { intros a Ha. apply (proj2 (proj2 (proj2 HIK))). left.
          unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
        split; [rewrite ?G4, ?G4y; exact TP|].
        split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); right; exact Ha|].
        intros X. rewrite HINIT in X. discriminate.
      - exact HINIT.
      - exact HRO.
      - intros a Ha. rewrite ?U10, ?U10y in Ha. split; [apply PL, in_G_bss; lia|]. rewrite SEG. apply sp_ro_glob. lia.
      - rewrite ?U10, ?U10y. exact LP.
      - intros _. unfold OPS_MAX in *. lia.
      - rewrite ?U12, ?U12y. lia.
      - rewrite ?U11, ?U11y. exact INX.
      - rewrite ?U12, ?U12y, length_firstn, length_skipn. lia.
      - rewrite ?U11, ?U12, ?U11y, ?U12y. right. left. exists (ss_p E), (ss_n E). split; [exact INB|]. split; [exact PV|]. lia.
      - rewrite ?U10, ?U11, ?U12, ?U10y, ?U11y, ?U12y.
        destruct (Z_le_gt_dec (ss_p E + K + 2 + M) (HA + 16)) as [D1|D1]; [left; exact D1|].
        destruct (Z_le_gt_dec (HA + 16 + 16) (ss_p E + K + 2)) as [D3|D3]; [right; exact D3|].
        exfalso. set (a := Z.max (ss_p E + K + 2) (HA + 16)).
        apply (hf_blk_img B (API rc) AX L A mem md (ss_p E) (ss_n E) (a - ss_p E) HMR INB); [unfold a; lia|].
        replace (ss_p E + (a - ss_p E)) with a by lia.
        exact (proj1 (PL a ltac:(apply in_G_bss; unfold a; lia))).
      - intros X. discriminate.
      - intros _. rewrite ?U12, ?U12y. lia.
      - exact ROK.
      - rewrite ?U12, ?U12y. exact ROOM. }
    intros c' (L' & A' & regs' & mem' & md' & l' & d & -> & RP & INIT' & RF' & RO' & LP' & HREC & HCAP & HV &
      KB1 & KB2 & KB3).
    rewrite ?U10, ?U10y in LP'. rewrite ?U12, ?U12y in RF'.
    destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RM RPR]. rewrite SPR in RM.
    assert (RW : rmid B (API rc) LIST_PUSH_K (slot_sp E) (push_EW (HA + 16) (hs_pending h))
        (push_FW (hs_pending h)) L A mem md L' A' mem' md').
    { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ RM).
      - intros a Ha. rewrite ?U10, ?U10y in Ha. unfold push_EW. unfold hl_n in *. lia.
      - intros q (Q1 & Q2 & Q3). split; [exact Q3|exact Q2]. }
    clear RM RP.
    pose proof RW as (M' & W' & BD' & _ & _ & _ & _ & _ & _ & VM' & _).
    destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ M') as (Hh' & Hl' & _).
    assert (HK : YM05.alloc_ceiling <= slot_sp E - LIST_PUSH_K)
      by (unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
    assert (KEPT : forall q, (0 < hl_cap (hs_pending h) -> q <> hl_v (hs_pending h)) ->
        kept_block (push_EW (HA + 16) (hs_pending h)) (push_FW (hs_pending h)) L A q).
    { intros q HQ. apply (hf_kept B (API rc) AX L A mem md _ _ (HA + 16)
        (HA + 16 + 16) (hl_cap (hs_pending h)) (hl_v (hs_pending h)) q HMR).
      - intros a Ha. exact (proj1 (PL a ltac:(apply in_G_bss; lia))).
      - intros a Ha. exact Ha.
      - exact VB.
      - intros (Q1 & Q2). exact (HQ Q2 Q1).
      - exact HQ. }
    assert (IMGNE : forall a, in_img B a ->
        ~ (HA + 16 <= a < HA + 32) ->
        ~ push_EW (HA + 16) (hs_pending h) a).
    { intros a Ha HN. apply (hf_img_notE B (API rc) AX (push_EW (HA + 16) (hs_pending h)) (HA + 16)
        (HA + 16 + 16) (hl_cap (hs_pending h)) (hl_v (hs_pending h)) a L A mem md HMR
        (fun a0 X => X) VB Ha). lia. }
    assert (KTA : forall q, In q (target_addrs G (bv_unsigned out) (es1 ++ e :: es2) (hj1 ++ (h, i) :: hj2)) ->
        ~ In q (list_blocks (hs_pending h)) ->
        kept_block (push_EW (HA + 16) (hs_pending h)) (push_FW (hs_pending h)) L A q).
    { intros q HQ HNL. apply KEPT. intros HC0 ->. exact (HNL (proj2 (hf_list_v B L A mem _ _ _ LP HC0))). }
    rewrite ?G1, ?G1y.
    assert (P2 : reg_get regs' 2 = Z_to_bv 64 (slot_sp E)) by exact (eq_trans (RPR 2 ltac:(unfold callee_saved; lia)) G2).
    assert (P3 : reg_get regs' 3 = getr (ss_regs E) 3) by exact (eq_trans (RPR 3 ltac:(unfold callee_saved; lia)) G3).
    assert (P4 : reg_get regs' 4 = getr (ss_regs E) 4) by exact (eq_trans (RPR 4 ltac:(unfold callee_saved; lia)) G4).
    assert (P8 : reg_get regs' 8 = Z_to_bv 64 (ss_p E + K + 2)) by exact (eq_trans (RPR 8 ltac:(unfold callee_saved; lia)) G8).
    assert (P9 : reg_get regs' 9 = Z_to_bv 64 (HA))
      by exact (eq_trans (RPR 9 ltac:(unfold callee_saved; lia)) G9).
    assert (P18 : reg_get regs' 18 = Z_to_bv 64 (ss_p E + K + 2 + M))
      by exact (eq_trans (RPR 18 ltac:(unfold callee_saved; lia)) G18).
    assert (P19 : reg_get regs' 19 = Z_to_bv 64 (slot_sp E + 32))
      by exact (eq_trans (RPR 19 ltac:(unfold callee_saved; lia)) G19).
    assert (P20 : reg_get regs' 20 = Z_to_bv 64 G_RELAY_LO) by exact (eq_trans (RPR 20 ltac:(unfold callee_saved; lia)) G20).
    assert (P21 : reg_get regs' 21 = Z_to_bv 64 DIV10) by exact (eq_trans (RPR 21 ltac:(unfold callee_saved; lia)) G21).
    assert (P22 : reg_get regs' 22 = Z_to_bv 64 t) by exact (eq_trans (RPR 22 ltac:(unfold callee_saved; lia)) G22).
    assert (P23 : reg_get regs' 23 = Z_to_bv 64 (ss_n E - K - 2 - M))
      by exact (eq_trans (RPR 23 ltac:(unfold callee_saved; lia)) G23).
    assert (P24 : reg_get regs' 24 = Z_to_bv 64 (slot_sp E + 16))
      by exact (eq_trans (RPR 24 ltac:(unfold callee_saved; lia)) G24).
    assert (P25 : reg_get regs' 25 = Z_to_bv 64 4) by exact (eq_trans (RPR 25 ltac:(unfold callee_saved; lia)) G25).
    assert (P26 : reg_get regs' 26 = Z_to_bv 64 (G_S + 4)) by exact (eq_trans (RPR 26 ltac:(unfold callee_saved; lia)) G26).
    assert (P27 : reg_get regs' 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4))
      by exact (eq_trans (RPR 27 ltac:(unfold callee_saved; lia)) G27).
    rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh'|exact Hl'|].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      rewrite P2, P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27.
      apply (op1_ret (ss_p E + K + 2 + M)). }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R3 & -> & X3).
    replace (ss_p E + K + 2 + M) with (ss_p E + (K + 2 + M)) in X3 by lia.
    replace (ss_n E - K - 2 - M) with (ss_n E - (K + 2 + M)) in X3 by lia.
    rewrite <- SEG.
    eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t (K + 2 + M)
      (fun _ _ _ r => tail_regs E t (K + 2 + M) r)); [exact HF|exact CB|intros; assumption|rewrite HKE; exact HW|]
      |intros c2 HC2; exists (K + 2 + M); exact HC2].
    exists fx', L', A', R3, mem', md', cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out,
      (map (fresh_entry B mem') (es1 ++ e :: es2)), (hj1 ++ (set_pending h l', i) :: hj2).
    split; [rewrite ?SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
    split; [unfold tail_regs, base_regs, fix_regs; repeat split; geq X3|].
    split; [exact M'|]. split; [exact W'|]. split; [exact BD'|]. split; [exact INIT'|].
    split; [destruct HVM as (vm & ->); destruct VM' as (vm' & ->); exists vm'; apply YI04.with_vmmaps_twice|].
    split; [exact RO'|].
    assert (EWV : forall a, 0 < hl_cap (hs_pending h) /\ hl_v (hs_pending h) <= a < hl_v (hs_pending h) + 16 * hl_cap (hs_pending h) ->
        ~ in_img B a /\ a < YM05.alloc_ceiling).
    { intros a (HC0 & Ha). pose proof (hf_list_head B L A mem _ _ _ LP) as (_ & _ & _ & HV0). destruct (HV0 HC0) as (_ & HV1).
      split; [|lia]. replace a with (hl_v (hs_pending h) + (a - hl_v (hs_pending h))) by lia.
      exact (hf_blk_img B (API rc) AX L A mem md _ _ (a - hl_v (hs_pending h)) HMR (VB HC0) ltac:(lia)). }
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDA). rewrite ta_split in NDA.
    assert (OUTP : bv_unsigned out = 0 \/ exists k0, 0 < k0 /\ In (bv_unsigned out, k0) (blocks L A)).
    { unfold output_at in HOUT. cbv zeta in HOUT.
      destruct HOUT as ((O & junk & [(H1 & H2 & _)|(H1 & _ & H3 & _)]) & _); [left; exact H2|right].
      exists (bv_unsigned cap). split; assumption. }
    split.
    { apply (push_image B (API rc) AX SEG E LIST_PUSH_K (slot_sp E) _ _ L A mem md L' A' mem' md'
        (HA + 16) HIK RW HMR HK PL).
      - intros a [Ha|Ha]; [left; exact Ha|right; exact (EWV a Ha)].
      - intros a Ha. split; [apply in_G_bss; lia|]. split.
        + exact (cells_writable _ _ _ _ a (proj1 LP) ltac:(cbn [cells_size csize Nat.add]; lia)).
        + exact (cells_writable _ _ _ _ a (proj1 LP') ltac:(cbn [cells_size csize Nat.add]; lia)).
      - intros a Ha. unfold sk in Ha. unfold lib_scratch. destruct Ha as [Ha|Ha]; [left|right; exact Ha].
        unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      - intros a Ha. unfold lib_scratch in Ha. unfold sk. destruct Ha as [Ha|Ha]; [right|left; right; exact Ha].
        unfold SLOT_STACK in *. lia. }
    split.
    { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
      assert (SK0 : forall a cs, rw_cells (ms_segs B) mem a cs -> slot_sp E <= a ->
          a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> rw_cells (ms_segs B) mem' a cs).
      { intros a cs H1 H2 H3. apply (rmid_rw_hi B (API rc) LIST_PUSH_K (slot_sp E) (push_EW (HA + 16) (hs_pending h)) (push_FW (hs_pending h))
          L A mem md L' A' mem' md' a cs);
          [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|rewrite ERR; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia
          |exact HMR|exact RW|exact H1|exact H2|exact H3|].
        intros k0 Hk0 X. destruct X as [X|X]; [unfold G_S, SRC_SIZE, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
        destruct (EWV _ X) as (_ & X2). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      split; [apply SK0; [exact ST1|lia|unfold saved_cells; cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]|].
      split; [apply SK0; [exact ST2|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]|].
      apply SK0; [exact ST3|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]. }
    split.
    { assert (ND1 : List.NoDup (map fst (blocks L A))) by (apply hf_nodup; exact (NDB L A mem md HMR)).
      apply (push_driver B (API rc) BW E _ _ LIST_PUSH_K (slot_sp E) _ _ L A mem md L' A' mem' md'
        (list_blocks (hs_pending h)) (list_blocks l') HWF ND1 HDK RW).
      - intros _. exists q0. split; [exact Hq0|exact Eq0].
      - exact NIT.
      - intros q Hq. rewrite ta_split. apply in_app_iff. right. apply in_app_iff. left. exact Hq.
      - intros q Hq. rewrite ta_split_push, fresh_entries_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hq.
      - intros q Hq HNL. rewrite ta_split in Hq. rewrite ta_split_push, fresh_entries_blocks.
        apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
        apply in_app_iff in Hq as [Hq|Hq]; [exfalso; exact (HNL Hq)|]. apply in_app_iff. right. exact Hq.
      - intros q Hq. rewrite ta_split_push, fresh_entries_blocks in Hq. rewrite ta_split.
        apply in_app_iff in Hq as [Hq|Hq]; [left; apply in_app_iff; left; exact Hq|].
        apply in_app_iff in Hq as [Hq|Hq]; [right; exact Hq|].
        left. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
      - intros q Hq. exact (hf_list_pos B L A mem _ _ _ q LP Hq).
      - exact KB2.
      - exact KB3.
      - intros q HQ. apply KEPT. intros HC0 ->. exact (HQ (VT HC0)). }
    split.
    { rewrite length_map. apply (push_globals B (API rc) AX SEG LIST_PUSH_K (slot_sp E) _ _ L A mem md L' A' mem' md'
        cl br gn dd ei _ G nfd mx nout cap out HK HMR RW PL).
      - intros a [X|X]; [left; unfold G_S, SRC_SIZE in *; lia|right; exact (proj1 (EWV a X))].
      - intros m0. rewrite SEG. exact (SlotEntry.entry_errno_cells B SEG ETP EOFF m0).
      - exact HGL. }
    split; [unfold TAIL_CHECK, TAIL_STEP; cbn; lia|].
    assert (OUT1 : output_at (rc := rc) B L' A' mem' nout cap out).
    { apply (output_rmid B (API rc) BW LIST_PUSH_K (slot_sp E) _ _ L A mem md L' A' mem' md' nout cap out RW HOUT).
      intros HC0. apply KTA; [rewrite ta_split; apply in_app_iff; left; right; left; reflexivity|].
      exact (nodup_mid_out _ _ _ _ NDA ltac:(apply in_app_iff; left; right; left; reflexivity)). }
    assert (REL1 : relay_at (rc := rc) B L' A' mem' (t + 1) nfd G (bv_unsigned out)
        (map (fresh_entry B mem') (es1 ++ e :: es2)) (hj1 ++ (set_pending h l', i) :: hj2)).
    { apply (push_relay B (API rc) AX BW SEG PL LIST_PUSH_K (slot_sp E) _ _ L A mem md L' A' mem' md' t nfd G
        (bv_unsigned out) es1 e es2 hj1 h i hj2 l' d _ HK HMR SL RW HREL ltac:(lia) HL1 OUTP IMGNE KTA LP' HREC);
        [rewrite length_firstn, length_skipn; lia|rewrite length_firstn, length_skipn; unfold WRITE_MAX; lia
        |exact HCAP|exact KB3]. }
    split; [exact OUT1|].
    split; [apply (relay_at_t rc B L' A' mem' (t + 1)); [exact REL1|unfold TAIL_CHECK, TAIL_STEP; cbn; lia]|].
    split; [rewrite length_map; exact Hes|].
    split.
    { rewrite fresh_cost, (slot_cost_app es1 (e :: es2) hj1 ((set_pending h l', i) :: hj2) HL1), slot_cost_cons.
      rewrite (pair_cost_push e h i l' d _ HREC OFF), length_firstn, length_skipn.
      rewrite (slot_cost_app es1 (e :: es2) hj1 ((h, i) :: hj2) HL1), slot_cost_cons in Hcost. lia. }
    destruct RF' as (qs & QLEN & ROK' & SHR & SHL).
    assert (NDL' : List.NoDup (map fst (blocks L' A'))) by (apply hf_nodup; exact (NDB L' A' mem' md' M')).
    assert (ENC : concat (map entry_nc (map (fresh_entry B mem') (es1 ++ e :: es2))) =
        concat (map entry_nc (es1 ++ e :: es2))).
    { rewrite map_map. f_equal; apply map_ext; intros a0; reflexivity. }
    apply (RIK L' A' qs QLEN ROK' l' SHR SHL).
    + intros q m HQ. destruct (KB2 q m HQ) as [(X & _)|X]; [left; exact X|right].
      rewrite ta_split_push, fresh_entries_blocks. apply in_app_iff. right. apply in_app_iff. left. exact X.
    + exists (pend_view hj1), (map snd (hl_recs (hs_pending h))), (pend_view hj2).
      eexists. split; [unfold pend_view; rewrite map_app; reflexivity|].
      split; [unfold pend_view; rewrite map_app; cbn [map fst hs_pending set_pending]; rewrite HREC, map_app;
              reflexivity|].
      split; [rewrite length_map; reflexivity|]. cbn [snd fst].
      split; [rewrite length_firstn, length_skipn; lia|].
      rewrite LTX. replace (K + 2 + M - M) with (K + 2) by lia. exact HCK1.
    + unfold ek_view. rewrite !map_app. cbn [map fst set_pending hs_expected]. reflexivity.
    + rewrite length_map. exact Hes.
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & PA2 & _). apply Forall2_length in PA2.
      clear - PA2 Hes. rewrite !length_app in *. cbn [length] in *. lia.
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDT).
      exact (push_move B L A mem L' A' mem' _ _ G (bv_unsigned out) (es1 ++ e :: es2)
        (map (fresh_entry B mem') (es1 ++ e :: es2)) hj1 h i hj2 (hs_pending h) (hl_n (hs_pending h))
        (hl_cap (hs_pending h)) l' d _ eq_refl eq_refl eq_refl NDL NDL'
        (fun x0 m0 H0 => p1_blk_nn B (API rc) L' A' mem' md' x0 m0 M' H0) NDT ENC LP LP' HREC HCAP HV
        KB1 KB2 KB3).
    + exact NDL'.
    + intros p n n' Hp _ Hin HND. pose proof RW as (_ & _ & _ & LYW & _).
      rewrite (lf_addr A L L' p n HWF LYW Hp).
      pose proof (push_arr_nc (hs_pending h) l' HCAP HV RS1 (ptr_addr L p)) as PA.
      unfold view_of in Hin |- *. cbn [rv_nc] in Hin |- *. rewrite ENC.
      rewrite !map_app, !concat_app in Hin |- *. cbn [map concat fst] in Hin |- *.
      unfold src_nc in Hin |- *. cbn [set_pending hs_pending hs_partial hs_expected hs_held] in Hin |- *.
      cbn [In] in Hin |- *. rewrite ?in_app_iff in Hin |- *. cbn [In] in Hin |- *. rewrite ?in_app_iff in Hin |- *.
      tauto.
    + exact (ncs_le_wt B (API rc) L' A' mem' md' (t + 1) nfd G nout cap out _ _ M' OUT1 REL1
        ltac:(rewrite length_map; exact Hes) NDL').
    + unfold nc_wt. rewrite fresh_nw, !length_map, !AllocBound.zsum_app, !AllocBound.zsum_cons, !length_app.
      cbn [length fst].
      pose proof (push_nw_src h l' d _ HREC OFF HCAP RS1) as NS.
      unfold NW_ENT0, NW_SRC0, NC_PER, DATA_PER, PARTIAL_BYTES in NS |- *. lia.
Qed.

Lemma pass1_holds : check_bounded_contract ->
  (forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
     forall rc fx, @list_push_contract fx rc B (API rc) F) ->
  forall RI, RI_mono RI -> push_resources_s F RI -> pass_ok RI 1.
Proof.
  intros CB LPC RI RIM HRES B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  assert (HN0 : 0 < ss_n E).
  { pose proof HL as (fx0 & L0 & A0 & regs0 & mem0 & md0 & cl0 & br0 & gn0 & dd0 & ei0 & G0 & nfd0 & mx0 & no0 & cap0 &
      out0 & es0 & hj0 & _ & _ & _ & HK0 & _). lia. }
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 1) with 0x13c98 in HM.
  exact (MI_op1 B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 1 k) s c' HF CB RIM HRES
    (fun fx' => LPC B API LS SH SK ra empty (proj1 HF) rc fx') HN0
    (walk_op1 E t k (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop)
    (fun HLe => proj2 (walk_take E t k 1 (disp_k E 1 k) (LI_walk _ _ _ _ _ _ _ _ HL)
       (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop (or_introl (conj eq_refl eq_refl)) HLe)
       ltac:(unfold OPS_MAX in Ht; lia)) HM).
Qed.

End P1.
