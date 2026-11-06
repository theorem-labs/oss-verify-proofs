(* check_ack_frame (fuzz/fuzz_transport.c:422-430), entry 0x15020:
     0x15020 lw    a1, 36(a0)        a1 = f->ack (sign-extended)
     0x15024 auipc a2, 0x2d          a2 = 0x42024
     0x15028 lw    a2, 1352(a2)      a2 = g_rx_send (0x4256c = W_BASE_PLAIN + OFF_g_rx_send)
     0x1502c bne   a1, a2, 0x15044   to the abort path; not taken: the model premise gives f->ack = g_rx_send
     0x15030 ld    a1, 56(a0)        a1 = f->body_len
     0x15034 bnez  a1, 0x15044       not taken: f->body_len = 0
     0x15038 lhu   a0, 30(a0)        a0 = f->retry
     0x1503c bnez  a0, 0x15044       not taken: f->retry = 0
     0x15040 ret
   The abort path (0x15044 addi sp, sp, -16; sd ra, 8(sp); jal abort) is unreachable. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TContract check_ack_frame_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_ack_frame_holds : check_ack_frame_contract.
Proof.
  unfold check_ack_frame_contract, check_ack_frame_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' fp fa frame -> SF OWN WM MOD SPA ST LO WOS MI.
  (* the model premise: the ACK echoes g_rx_send with no body and retry 0 (fuzz_transport.c:428-429), and the world
     is unchanged *)
  assert (HM : sf_ack (rf frame) = g_rx_send B /\ sf_body_len (rf frame) = 0 /\ sf_retry (rf frame) = 0 /\ B' = B).
  { revert MOD. unfold check_ack_frame_m. cbv zeta.
    destruct (Z.eqb_spec (sf_ack (rf frame)) (g_rx_send B)) as [E1|E1];
      destruct (Z.eqb_spec (sf_body_len (rf frame)) 0) as [E2|E2];
      destruct (Z.eqb_spec (sf_retry (rf frame)) 0) as [E3|E3];
      cbn [negb orb]; intros MOD; try discriminate MOD.
    injection MOD as E4. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. symmetry; exact E4. }
  destruct HM as (EA & EL & ER & ->). clear MOD.
  destruct SF as (P0 & P8 & SB & SBAT & SBL & Fcode & Fdst & Fsrc & Feth & Fnum & Fsum & Fretry & Fsend & Fack
    & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  (* the reads of f->ack (4 bytes at f + 36), f->body_len (8 at f + 56) and f->retry (2 at f + 30) *)
  assert (R36 : ov_read_bytes rsegs m (Z_to_bv 64 (fp + 36)) 4 = Some (sub SB 36 4)).
  { exact (bytes_at_read rsegs m fp SB 36 4 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  assert (R56 : ov_read_bytes rsegs m (Z_to_bv 64 (fp + 56)) 8 = Some (sub SB 56 8)).
  { exact (bytes_at_read rsegs m fp SB 56 8 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  assert (R30 : ov_read_bytes rsegs m (Z_to_bv 64 (fp + 30)) 2 = Some (sub SB 30 2)).
  { exact (bytes_at_read rsegs m fp SB 30 2 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  (* the machine compares the sign extensions of the two 32-bit words; the model's unsigned equality gives them *)
  assert (XEQ : s32_at SB 36 = s32_at B 64988).
  { unfold s32_at. rewrite Fack, EA. reflexivity. }
  assert (XL : u_at SB 56 8 = 0) by (rewrite Fblen; exact EL).
  assert (XR : u_at SB 30 2 = 0) by (rewrite Fretry; exact ER).
  step.                                   (* lw a1, 36(a0): f->ack *)
  step.                                   (* auipc a2, 0x2d *)
  step.                                   (* lw a2, 1352(a2): g_rx_send *)
  rewrite ?wm_lw.
  rewrite XEQ.
  step.                                   (* bne a1, a2: not taken *)
  if_false.
  step.                                   (* ld a1, 56(a0): f->body_len *)
  rewrite ?wm_ld.
  rewrite XL.
  step.                                   (* bnez a1: not taken *)
  if_false.
  step.                                   (* lhu a0, 30(a0): f->retry *)
  rewrite ?wm_lhu.
  rewrite XR.
  step.                                   (* bnez a0: not taken *)
  if_false.
  step.                                   (* ret *)
  apply evt_done. hnf.
  do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity | exact WM].
Qed.
