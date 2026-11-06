(* The premises of the six check contracts (check_forward, check_ret, check_downstream, check_meter,
   check_counter, check_width; fuzz_wire ubsan 6e91fe0b5555) hold at their real call states: LLVMFuzzerTestOneInput's calls,
   fuzz_wire.c:265-270. One closed lemma per contract, with the caller's register values there and a memory of the shape
   the caller has there. The state is wire_lib_sat.v's: the fuzz_dup heap block at SAT_F holding the frame,
   the stack window [SAT_LO, SAT_HI) mapped, the loaded image everywhere else; the frame is the 124-byte 2-channel REAC
   audio frame an input of 125 bytes gives (n = 124 <= W_RECV_MAX = 1600, fuzz_wire.c:260-262). sp = SAT_CHK_SP
   (wire_lib_sat.v) = 0x7fffffffe6c0, the entry sp of every check_*: SAT_SP = 0x7fffffffe700 is LLVMFuzzerTestOneInput's
   ENTRY sp, and its prologue `addi sp, sp, -0x40` (plain 0x12d78 / ubsan 0x12dc0) leaves SAT_SP - 0x40, the sp each of
   these calls passes on. This is the one sp convention of every fuzz_wire sat lemma: a callee's entry sp = its caller's
   entry sp minus the caller's frame at that call (so check_meter's rp_meter_counter is entered at 0x7fffffffe690,
   &ctr = 0x7fffffffe69e; check_width's rp_frame_channels at 0x7fffffffe6b0); lo = SAT_LO, the low end of the stack
   window. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import wire_lib_sat check_forward_c check_ret_c
  check_downstream_c check_meter_c check_counter_c check_width_c.
Import ListNotations.
Open Scope Z_scope.

(* The premises the five checks that read the frame share, for a frame of fr bytes: f = SAT_F, n = 124, entry sp
   SAT_CHK_SP. *)
Lemma chk_sat_common : forall fr, 0 <= fr <= 0x1000 ->
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + fr <= bv_unsigned sp) /\
  (bv_unsigned sp mod 2 = 0) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - fr \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  intros fr Hfr. cbv zeta.
  rewrite (unsigned_lit SAT_CHK_SP) by (sat_num; lia).
  rewrite (unsigned_lit SAT_F) by (unfold SAT_F; lia). rewrite (unsigned_lit 124) by lia.
  split; [rewrite sat_frame_length; reflexivity|].
  split; [apply sat_frame_at; rewrite sat_frame_length; lia|].
  split; [unfold SAT_F; lia|].
  split; [apply sat_stk; [rewrite sat_frame_length; lia | lia | sat_num; lia]|].
  split; [sat_num; lia|].
  split; [sat_num; reflexivity|].
  left. sat_num. lia.
Qed.

(* check_forward at LLVMFuzzerTestOneInput's call (ubsan 0x12e60 `jal check_forward`: a0 = s0 = f, a1 = s1 = n, a2 = s5 = bcast,
   ra = 0x12e64, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_forward_premises_sat :
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  let a2 := Z_to_bv 64 1 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + CHECK_FORWARD_FRAME <= bv_unsigned sp) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_FORWARD_FRAME \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. destruct (chk_sat_common CHECK_FORWARD_FRAME ltac:(unfold CHECK_FORWARD_FRAME; lia)) as (L & B & NZ & S & LO & E & D).
  split; [exact L|]. split; [exact B|]. split; [exact NZ|]. split; [exact S|]. split; [exact LO|]. exact D.
Qed.

(* check_ret at LLVMFuzzerTestOneInput's call (ubsan 0x12e6c `jal check_ret`: a0 = s0 = f, a1 = s1 = n,
   ra = 0x12e70, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_ret_premises_sat :
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + CHECK_RET_FRAME <= bv_unsigned sp) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_RET_FRAME \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. destruct (chk_sat_common CHECK_RET_FRAME ltac:(unfold CHECK_RET_FRAME; lia)) as (L & B & NZ & S & LO & E & D).
  split; [exact L|]. split; [exact B|]. split; [exact NZ|]. split; [exact S|]. split; [exact LO|]. exact D.
Qed.

(* check_downstream at LLVMFuzzerTestOneInput's call (ubsan 0x12e78 `jal check_downstream`: a0 = s0 = f, a1 = s1 = n,
   ra = 0x12e7c, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_downstream_premises_sat :
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + CHECK_DOWNSTREAM_FRAME <= bv_unsigned sp) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_DOWNSTREAM_FRAME \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. destruct (chk_sat_common CHECK_DOWNSTREAM_FRAME ltac:(unfold CHECK_DOWNSTREAM_FRAME; lia)) as (L & B & NZ & S & LO & E & D).
  split; [exact L|]. split; [exact B|]. split; [exact NZ|]. split; [exact S|]. split; [exact LO|]. exact D.
Qed.

(* check_meter at LLVMFuzzerTestOneInput's call (ubsan 0x12e84 `jal check_meter`: a0 = s0 = f, a1 = s1 = n,
   ra = 0x12e88, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_meter_premises_sat :
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + CHECK_METER_FRAME <= bv_unsigned sp) /\
  (bv_unsigned sp mod 2 = 0) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_METER_FRAME \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. destruct (chk_sat_common CHECK_METER_FRAME ltac:(unfold CHECK_METER_FRAME; lia)) as (L & B & NZ & S & LO & E & D).
  split; [exact L|]. split; [exact B|]. split; [exact NZ|]. split; [exact S|]. split; [exact LO|]. split; [exact E|]. exact D.
Qed.

(* check_counter at LLVMFuzzerTestOneInput's call (ubsan 0x12e90 `jal check_counter`: a0 = s0 = f, a1 = s1 = n,
   ra = 0x12e94, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_counter_premises_sat :
  let m := sat_mem sat_frame in
  let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 SAT_F in let a1 := Z_to_bv 64 124 in
  (Z.of_nat (length sat_frame) = bv_unsigned a1) /\
  bytes_at rsegs m (bv_unsigned a0) sat_frame /\
  (bv_unsigned a0 <> 0) /\
  stk rsegs m SAT_LO (bv_unsigned sp) /\
  (SAT_LO + CHECK_COUNTER_FRAME <= bv_unsigned sp) /\
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_COUNTER_FRAME \/ bv_unsigned sp <= bv_unsigned a0).
Proof.
  cbv zeta. destruct (chk_sat_common CHECK_COUNTER_FRAME ltac:(unfold CHECK_COUNTER_FRAME; lia)) as (L & B & NZ & S & LO & E & D).
  split; [exact L|]. split; [exact B|]. split; [exact NZ|]. split; [exact S|]. split; [exact LO|]. exact D.
Qed.

(* check_width at LLVMFuzzerTestOneInput's call (ubsan 0x12e98 `jal check_width`: a0 = s1 = n,
   ra = 0x12e9c, sp = SAT_CHK_SP = 0x7fffffffe6c0, its entry sp). *)
Lemma check_width_premises_sat :
  let m := sat_mem sat_frame in let sp := Z_to_bv 64 SAT_CHK_SP in let a0 := Z_to_bv 64 124 in
  (bv_unsigned a0 <= 1600) /\ mem_inv rsegs m /\ stk rsegs m SAT_LO (bv_unsigned sp) /\
  SAT_LO + CHECK_WIDTH_STACK <= bv_unsigned sp.
Proof.
  cbv zeta. rewrite (unsigned_lit SAT_CHK_SP) by (sat_num; lia). rewrite (unsigned_lit 124) by lia.
  split; [lia|]. split; [apply sat_mem_inv; rewrite sat_frame_length; lia|].
  split; [apply sat_stk; [rewrite sat_frame_length; lia | lia | sat_num; lia]|].
  unfold CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME. sat_num. lia.
Qed.
