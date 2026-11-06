From OSSVerify.tinyobjloader.fuzz_tobj_c Require Statements.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require Theorems.

Theorem ubsan_agrees_holds : OSSVerify.tinyobjloader.fuzz_tobj_c.Statements.ubsan_agrees.
Proof. exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Theorems.strong_universal_error_free_fuzz_tobj_c_ubsan. Qed.
