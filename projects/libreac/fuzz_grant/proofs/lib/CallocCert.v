From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
Theorem src0_calloc_realizes {fx : YK11.FPState} {rc : YM05.RunCeil} : calloc_realizes src0_msyms (MRx src0_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
