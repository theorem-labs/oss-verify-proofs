(* The body-sum loop of fuzz_frame's LLVMFuzzerTestOneInput, 0x12e20-0x12e2c (the inlined spec_sum of
   fuzz/spec.h:174 with its mask left to the store): lbu a3, 0(a1); addi a1, a1, 1; add a2, a2, a3;
   bne a1, a0. At byte i of the body bd at A, a1 = A + i and a2 is the sum of the first i bytes.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c FrameBytes lt_seg_b2_lib.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 xa0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).

Local Abbreviation ST pc a1 a2 a3 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma b2_loop : forall (Q : machine_state -> Prop) (A : Z) (bd : list byte),
  0 <= A -> A + Z.of_nat (length bd) < 2 ^ 63 -> xa0 = Z_to_bv 64 (A + Z.of_nat (length bd)) ->
  bytes_at rsegs m A bd ->
  forall r (i : nat) (a3 : word) (v1 v2 : Z),
  (i + S r = length bd)%nat -> v1 = A + Z.of_nat i -> v2 = sum_bytes (firstn i bd) ->
  (forall (a3' : word) (w1 w2 : Z), w1 = A + Z.of_nat (length bd) -> w2 = sum_bytes bd ->
     evt rsegs Q (ST 0x12e30 (Z_to_bv 64 w1) (Z_to_bv 64 w2) a3')) ->
  evt rsegs Q (ST 0x12e20 (Z_to_bv 64 v1) (Z_to_bv 64 v2) a3).
Proof.
  intros Q A bd HA HAL HA0 BD r. rewrite HA0. induction r as [|r IH]; intros i a3 v1 v2 Hi -> -> K.
  all: pose proof (rd1 m A bd i BD ltac:(lia)) as HR.
  all: step; clear HR; step; step; step.
  - (* the last byte: fall through to 0x12e30 *)
    b2_br false. eapply K; [lia |].
    rewrite sum_step by lia. rewrite firstn_all2 by lia. reflexivity.
  - (* more bytes: back to 0x12e20 *)
    b2_br true. eapply (IH (S i)); [lia | lia | apply sum_step; lia | exact K].
Qed.

End Loop.
