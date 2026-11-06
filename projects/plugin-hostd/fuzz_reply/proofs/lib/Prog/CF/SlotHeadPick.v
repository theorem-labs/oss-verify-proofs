From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHeadRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition dk (OP K N : Z) : Z := if pick_op OP && (K + 1 <? N) then K + 2 else K + 1.

Definition dsrc (OP f0 f1 f2 f3 : Z) (s : word) : Prop :=
  (pick_op OP = true /\ exists j, (j < 4)%nat /\ nth j [f0; f1; f2; f3] 0 = 1 /\ s = Z_to_bv 64 (0x31040 + 96 * Z.of_nat j)) \/
  ((pick_op OP = false \/ OP = 1) /\ s = Z_to_bv 64 0).

Definition dpost (OP K N P f0 f1 f2 f3 : Z)
    (x1 x2 x3 x4 x5 x6 x7 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  exists (s0 s1 s2 s7 a0 a1 a2 a3 a4 : word) (pc : Z),
    ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 1) x16 x17 s2 x19 x20 x21 x22 s7 x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m ro /\
    s0 = Z_to_bv 64 (P + dk OP K N) /\ s7 = Z_to_bv 64 (N - dk OP K N) /\
    ((pc = jt_target OP /\ s2 = Z_to_bv 64 (P + K) /\ dsrc OP f0 f1 f2 f3 s1) \/
     (pc = TAIL_STEP /\ pick_op OP = true /\ OP <> 1 /\ s1 = Z_to_bv 64 (N - dk OP K N) /\
      s2 = Z_to_bv 64 (P + dk OP K N) /\ f0 = 0 /\ f1 = 0 /\ f2 = 0 /\ f3 = 0)).

Lemma dpick : forall (OP N K P SP f0 f1 f2 f3 : Z)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 ro : word -> option byte) (b1 : byte),
  (K + 1 < N -> ov_read_bytes rsegs m1 (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31044) 4 = Some (le4 (Z_to_bv 64 f0)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x310a4) 4 = Some (le4 (Z_to_bv 64 f1)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31104) 4 = Some (le4 (Z_to_bv 64 f2)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31164) 4 = Some (le4 (Z_to_bv 64 f3)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (SP + 8)) 8 = Some (le8 (Z_to_bv 64 0x31040)) ->
  bytes_at rsegs m1 JT_BASE JTB ->
  (f0 = 0 \/ f0 = 1) -> (f1 = 0 \/ f1 = 1) -> (f2 = 0 \/ f2 = 1) -> (f3 = 0 \/ f3 = 1) ->
  0 <= K < N -> N < 2 ^ 26 -> 0 <= OP < 10 -> pick_op OP = true ->
  evt rsegs (dpost OP K N P f0 f1 f2 f3 x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x16 x17 x19 x20 x21 x22 x24 x25
               (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4) x28 x29 x30 x31 F fc m1 ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K + 1)) (Z_to_bv 64 (N - K)) (Z_to_bv 64 OP) x11 x12
             x13 x14 (Z_to_bv 64 1) x16 x17 (Z_to_bv 64 (P + K)) x19 x20 x21 x22 (Z_to_bv 64 (N - K + -1)) x24 x25
             (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4) x28 x29 x30 x31) F (Z_to_bv 64 0x13c30) fc None m1 ro).
Proof.
  intros OP N K P SP f0 f1 f2 f3 x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31
    F fc m1 ro b1 R1 F0 F1 F2 F3 RSP JT H0 H1 H2 H3 HK HN HOP HP.
  assert (DK : dk OP K N = if K + 1 <? N then K + 2 else K + 1) by (unfold dk; rewrite HP; reflexivity).
  eapply evt_cut; [eapply (dsel OP N K P SP f0 f1 f2 f3); eassumption|].
  intros ms (s0 & s1 & s2 & s7 & a1 & a2 & a3 & a4 & pc & -> & E0 & E7 & HO).
  destruct HO as [(-> & E2 & j & Hj & Hf & E1) | [(-> & -> & E1 & E2 & Z0 & Z1 & Z2 & Z3) |
                  (-> & HN1 & E1 & E2 & Z0 & Z1 & Z2 & Z3)]].
  - eapply evt_cut; [eapply djt; [exact JT | exact HOP]|].
    intros ms (a0' & a1' & ->). apply evt_done. unfold dpost.
    do 10 eexists. split; [reflexivity|]. rewrite DK.
    split; [exact E0|]. split; [exact E7|]. left. split; [reflexivity|]. split; [exact E2|].
    left. split; [exact HP|]. exists j. split; [exact Hj|]. split; [exact Hf | exact E1].
  - apply evt_done. unfold dpost. do 10 eexists. split; [reflexivity|]. rewrite DK.
    split; [exact E0|]. split; [exact E7|]. left. split; [reflexivity|]. split; [exact E2|].
    right. split; [right; reflexivity | exact E1].
  - apply evt_done. unfold dpost. do 10 eexists. split; [reflexivity|]. rewrite DK.
    split; [exact E0|]. split; [exact E7|]. right. split; [reflexivity|]. split; [exact HP|].
    split; [exact HN1|]. split; [exact E1|]. split; [exact E2|]. repeat split; assumption.
Qed.

Lemma dsp_run : forall (T N K P SP f0 f1 f2 f3 : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x16 x17 x23 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 ro : word -> option byte) (b0 b1 : byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0] ->
  store_ok rsegs m (Z_to_bv 64 0x31000) 8 = true ->
  m1 = write_to_mem m (Z_to_bv 64 0x31000) (le8 (Z_to_bv 64 0)) ->
  (K + 1 < N -> ov_read_bytes rsegs m1 (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31044) 4 = Some (le4 (Z_to_bv 64 f0)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x310a4) 4 = Some (le4 (Z_to_bv 64 f1)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31104) 4 = Some (le4 (Z_to_bv 64 f2)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31164) 4 = Some (le4 (Z_to_bv 64 f3)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (SP + 8)) 8 = Some (le8 (Z_to_bv 64 0x31040)) ->
  bytes_at rsegs m1 JT_BASE JTB ->
  (f0 = 0 \/ f0 = 1) -> (f1 = 0 \/ f1 = 1) -> (f2 = 0 \/ f2 = 1) -> (f3 = 0 \/ f3 = 1) ->
  0 <= K < N -> N < 2 ^ 26 ->
  evt rsegs (dpost (bv_unsigned b0 mod 10) K N P f0 f1 f2 f3 x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x16 x17
               (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) (Z_to_bv 64 0x199999999999999a) (Z_to_bv 64 T)
               (Z_to_bv 64 (SP + 16)) (Z_to_bv 64 4) (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4) x28 x29 x30 x31
               F fc m1 ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (N - K)) x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17
             (Z_to_bv 64 (P + K)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) (Z_to_bv 64 0x199999999999999a)
             (Z_to_bv 64 T) x23 (Z_to_bv 64 (SP + 16)) (Z_to_bv 64 4) (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4)
             x28 x29 x30 x31) F (Z_to_bv 64 0x13c00) fc None m ro).
Proof.
  intros T N K P SP f0 f1 f2 f3 x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x16 x17 x23 x28 x29 x30 x31 F fc m m1 ro b0 b1
    R0 S0 EM R1 F0 F1 F2 F3 RSP JT H0 H1 H2 H3 HK HN.
  step. step. step. step. step. step. step. step. step. rewrite <- EM.
  change (zxb b0) with (Z_to_bv 64 (bv_unsigned b0)).
  pose proof (bv_unsigned_in_range 8 b0) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
  rewrite (unsigned_lit (bv_unsigned b0)) by lia.
  rewrite (mulhu10 (bv_unsigned b0)) by lia.
  replace (bv_unsigned b0 - (bv_unsigned b0 - bv_unsigned b0 mod 10) + -1) with (bv_unsigned b0 mod 10 + -1) by lia.
  replace (bv_unsigned b0 - (bv_unsigned b0 - bv_unsigned b0 mod 10)) with (bv_unsigned b0 mod 10) by lia.
  assert (HOP : 0 <= bv_unsigned b0 mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  remember (bv_unsigned b0 mod 10) as OP eqn:EOP. clear EOP.
  step. rewrite (ltu_op OP HOP).
  destruct ((1 <=? OP) && (OP <=? 4)) eqn:C1; cbv iota.
  - assert (HP : pick_op OP = true).
    { apply andb_true_iff in C1. destruct C1 as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
      unfold pick_op. assert (OP = 1 \/ OP = 2 \/ OP = 3 \/ OP = 4) as [-> |[-> |[-> | ->]]] by lia; reflexivity. }
    eapply dpick; eassumption.
  - step. step. rewrite (beq_lit OP 6) by lia.
    destruct (OP =? 6) eqn:C2; cbn [negb]; cbv iota.
    + apply Z.eqb_eq in C2. subst OP. eapply dpick; try eassumption; try lia; reflexivity.
    + apply Z.eqb_neq in C2.
      assert (HP : pick_op OP = false).
      { apply andb_false_iff in C1. unfold pick_op.
        assert (OP = 0 \/ OP = 5 \/ OP = 7 \/ OP = 8 \/ OP = 9) as [-> |[-> |[-> |[-> | ->]]]]
          by (destruct C1 as [C1|C1]; [apply Z.leb_gt in C1 | apply Z.leb_gt in C1]; lia); reflexivity. }
      step. eapply evt_cut; [eapply djt; [exact JT | exact HOP]|].
      intros ms (a0' & a1' & ->). apply evt_done. unfold dpost.
      assert (DK : dk OP K N = K + 1) by (unfold dk; rewrite HP; reflexivity).
      do 10 eexists. split; [reflexivity|]. rewrite DK.
      split; [f_equal; lia|]. split; [f_equal; lia|]. left. split; [reflexivity|]. split; [reflexivity|].
      right. split; [left; exact HP | reflexivity].
Qed.
