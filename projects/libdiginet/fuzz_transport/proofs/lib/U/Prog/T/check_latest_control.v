(* check_latest_control (fuzz/fuzz_transport.c:599-607), entry 0x15478:
     0x15478 andi  a1, a0, 7         the alignment check of f
     0x1547c bnez  a1, 0x15494       to the trap (unimp); not taken: f is 8-aligned (sframe_at)
     0x15480 lw    a0, 32(a0)        a0 = f->send (sign-extended)
     0x15484 auipc a1, 0x1e          a1 = 0x33484
     0x15488 lw    a1, -304(a1)      a1 = M.host_counter (0x33354 = W_BASE_UBSAN + A_M_host_counter)
     0x1548c bne   a0, a1, 0x15498   to the abort path; not taken: the model premise gives f->send = M.host_counter
     0x15490 ret
   The trap (0x15494 unimp) and the abort path (0x15498 addi sp, sp, -16; sd ra, 8(sp); jal abort) are unreachable. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract check_latest_control_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_latest_control_holds : check_latest_control_contract.
Proof.
  unfold check_latest_control_contract, check_latest_control_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' fp fa frame -> SF OWN WM MOD SPA ST LO WOS MI.
  (* the model premise: f->send = M.host_counter (fuzz_transport.c:605-606), and the world is unchanged *)
  assert (HM : sf_send (rf frame) = M_host_counter B /\ B' = B).
  { revert MOD. unfold check_latest_control_m.
    destruct (Z.eqb_spec (sf_send (rf frame)) (M_host_counter B)) as [E|E]; cbn [negb]; intros MOD;
      [|discriminate MOD].
    injection MOD as E'. split; [exact E | symmetry; exact E']. }
  destruct HM as [EQ ->]. clear MOD.
  destruct SF as (P0 & P8 & SB & SBAT & SBL & Fcode & Fdst & Fsrc & Feth & Fnum & Fsum & Fretry & Fsend & Fack
    & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  pose proof SBAT as (FP0 & FP1 & _).
  (* the read of f->send, the 4 bytes at f + 32 of the struct *)
  assert (R32 : ov_read_bytes rsegs m (Z_to_bv 64 (fp + 32)) 4 = Some (sub SB 32 4)).
  { exact (bytes_at_read rsegs m fp SB 32 4 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  (* the machine compares the sign extensions of the two 32-bit words; the model's unsigned equality gives them *)
  assert (XEQ : s32_at SB 32 = s32_at B 84).
  { unfold s32_at. rewrite Fsend, EQ. reflexivity. }
  step.                                   (* andi a1, a0, 7 *)
  (* f mod 8 = 0, so the low three bits of f are zero *)
  lazymatch goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 fp)) ?X] =>
    replace (Z.land (bv_unsigned (Z_to_bv 64 fp)) X) with 0
      by (rewrite unsigned_lit by lia; change X with (Z.ones 3); rewrite Z.land_ones by lia; symmetry; exact P8)
  end.
  step.                                   (* bnez a1: not taken *)
  if_false.
  step.                                   (* lw a0, 32(a0): f->send *)
  step.                                   (* auipc a1, 0x1e *)
  step.                                   (* lw a1, -304(a1): M.host_counter *)
  rewrite ?wm_lw.
  rewrite XEQ.
  step.                                   (* bne a0, a1: not taken *)
  if_false.
  step.                                   (* ret *)
  apply evt_done. hnf.
  do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity | exact WM].
Qed.
