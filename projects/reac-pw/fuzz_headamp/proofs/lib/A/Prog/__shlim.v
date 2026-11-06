(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Prog/__shlim.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 0 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Prog Require Import __shlim_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __shlim_holds : __shlim_contract.
Proof.
  unfold __shlim_contract, SHLIM.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp
    rpos rend buf junk R1 R2 R3 MI.
  pose proof (rw_cells_bound _ _ _ _ R1) as B1. pose proof (rw_cells_bound _ _ _ _ R2) as B2.
  pose proof (rw_cells_bound _ _ _ _ R3) as B3. cbn [cells_size csize Nat.add] in B1, B2, B3.
  pose proof (munch_refl [(Fp + 184, Fp + 208)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. if_true. zstep. zstep.
  finish.
Qed.
