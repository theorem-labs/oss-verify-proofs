From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YT01 YX08 YY03 YV02.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_realloc_realizes : realloc_realizes src0_msyms (MRx src0_msyms).
Proof using. exact (realloc_by_class (realloc_small realloc_fb_gen) realloc_k3b). Qed.
End a.
