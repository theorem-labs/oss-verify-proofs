(* io_now, entry 0x14bbc: auipc a0,0x2e; ld a0,1324(a0) (g_now = W_BASE_UBSAN + OFF_g_now = 0x430e8); ret.
   The ld is a world load: the WMem hook rewrites it to u_at B OFF_g_now 8 = g_now B = io_now_m B.
   No store, no call, no UBSan check: the memory is unchanged, so munch, wmono, mem_inv, stk and wmem hold of m. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem io_now_c.
Import ListNotations.
Open Scope Z_scope.

Theorem io_now_holds : io_now_contract.
Proof.
  unfold io_now_contract, io_now_ENTRY, io_now_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B
    WM Hsp ST LO WS MI.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  step.                                   (* 0x14bbc auipc a0, 0x2e *)
  step.                                   (* 0x14bc0 ld a0, 1324(a0): a0 = u_at B 65000 8 *)
  change (u_at B 65000 8) with (io_now_m B).
  step.                                   (* 0x14bc4 ret *)
  apply evt_done. hnf. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM].
Qed.
