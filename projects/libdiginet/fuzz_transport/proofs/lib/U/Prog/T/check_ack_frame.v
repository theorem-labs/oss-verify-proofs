(* check_ack_frame (fuzz/fuzz_transport.c:422-430), entry 0x1543c:
     0x1543c andi  a1, a0, 7         the alignment check of f
     0x15440 bnez  a1, 0x15474       to the trap (unimp); not taken: f is 8-aligned (sframe_at)
     0x15444 lw    a1, 36(a0)        a1 = f->ack (sign-extended)
     0x15448 auipc a2, 0x2e          a2 = 0x43448
     0x1544c lw    a2, -876(a2)      a2 = g_rx_send (0x430dc = W_BASE_UBSAN + OFF_g_rx_send)
     0x15450 bne   a1, a2, 0x15468   to the abort path; not taken: the model premise gives f->ack = g_rx_send
     0x15454 ld    a1, 56(a0)        a1 = f->body_len
     0x15458 bnez  a1, 0x15468       not taken: f->body_len = 0
     0x1545c lhu   a0, 30(a0)        a0 = f->retry
     0x15460 bnez  a0, 0x15468       not taken: f->retry = 0
     0x15464 ret
   The trap (0x15474 unimp) and the abort path (0x15468 addi sp, sp, -16; sd ra, 8(sp); jal abort) are
   unreachable. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract check_ack_frame_c.
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
  pose proof SBAT as (FP0 & FP1 & _).
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
  step.                                   (* andi a1, a0, 7 *)
  (* f mod 8 = 0, so the low three bits of f are zero *)
  lazymatch goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 fp)) ?X] =>
    replace (Z.land (bv_unsigned (Z_to_bv 64 fp)) X) with 0
      by (rewrite unsigned_lit by lia; change X with (Z.ones 3); rewrite Z.land_ones by lia; symmetry; exact P8)
  end.
  step.                                   (* bnez a1: not taken *)
  if_false.
  step.                                   (* lw a1, 36(a0): f->ack *)
  step.                                   (* auipc a2, 0x2e *)
  step.                                   (* lw a2, -876(a2): g_rx_send *)
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
