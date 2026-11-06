From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YO0d YH02 YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YT01_cf YX08_cf YY03_cf YV02_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_realloc_realizes : realloc_realizes_cf src0_msyms (MRx src0_msyms).
Proof using. exact (realloc_by_class (realloc_small realloc_fb_gen) realloc_k3b). Qed.
End a.
