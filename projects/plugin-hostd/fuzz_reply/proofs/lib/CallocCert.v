From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
(* At either allocation mode: the program has no calloc, so the proof is the pc's [discriminate]. *)
Theorem src0_calloc_realizes {fx : YK11.FPState} {rc : YM05.RunCeil} {AM : Cfg.AllocMode} :
  calloc_realizes src0_msyms (MRx src0_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
