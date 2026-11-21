From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
Theorem src0_calloc_realizes {fx : YK11.FPState} {rc : YM05.RunCeil} : calloc_realizes src0_msyms (MRx src0_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
(* 08b1429: the same vacuous certificate (this image has no calloc) over the record's invariant at any
   allocation mode; ZAllocatorMF's record is at MayFail (YO0d.AllocAPI carries its mode). *)
Theorem src0_calloc_realizes_m {fx : YK11.FPState} {rc : YM05.RunCeil} {AM : Cfg.AllocMode} :
  calloc_realizes src0_msyms (MRx (AM:=AM) src0_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
