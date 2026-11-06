(* check_latest_control (fuzz/fuzz_transport.c:599-607), entry 0x15050:
     0x15050 lw    a0, 32(a0)        a0 = f->send (sign-extended)
     0x15054 auipc a1, 0x1d          a1 = 0x32054
     0x15058 lw    a1, 1936(a1)      a1 = M.host_counter (0x327e4 = W_BASE_PLAIN + A_M_host_counter)
     0x1505c bne   a0, a1, 0x15064   to the abort path; not taken: the model premise gives f->send = M.host_counter
     0x15060 ret
   The abort path (0x15064 addi sp, sp, -16; sd ra, 8(sp); jal abort) is unreachable. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TContract check_latest_control_c.
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
  (* the read of f->send, the 4 bytes at f + 32 of the struct *)
  assert (R32 : ov_read_bytes rsegs m (Z_to_bv 64 (fp + 32)) 4 = Some (sub SB 32 4)).
  { exact (bytes_at_read rsegs m fp SB 32 4 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  (* the machine compares the sign extensions of the two 32-bit words; the model's unsigned equality gives them *)
  assert (XEQ : s32_at SB 32 = s32_at B 84).
  { unfold s32_at. rewrite Fsend, EQ. reflexivity. }
  step.                                   (* lw a0, 32(a0): f->send *)
  step.                                   (* auipc a1, 0x1d *)
  step.                                   (* lw a1, 1936(a1): M.host_counter *)
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
