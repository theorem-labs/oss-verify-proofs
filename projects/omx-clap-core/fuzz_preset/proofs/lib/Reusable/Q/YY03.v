From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YN0i YN10 YN23 YN0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW06 YW0a YY00 YY02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem realloc_fb_gen : OBL_fb_gen.
Proof using.
exact (fb_gen_of_api (src0_malloc_impl (src0_malloc_realizes_of_hyps src0_alloc_meta src0_alloc_slot))
(src0_free_impl src0_free_realizes_closed) src0_memcpy_spec).
Qed.
End a.
