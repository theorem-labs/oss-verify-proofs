From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YN0i_cf YN10_cf YN23_cf YN0x_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW06_cf YW0a_cf YY00_cf YY02_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM06_cf YO0d_cf.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem realloc_fb_gen : OBL_fb_gen.
Proof using.
exact (fb_gen_of_api (src0_malloc_impl (src0_malloc_realizes_of_hyps src0_alloc_meta src0_alloc_slot))
(src0_free_impl src0_free_realizes_closed) src0_memcpy_spec).
Qed.
End a.
