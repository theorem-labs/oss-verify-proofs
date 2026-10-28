From OssFuzzTheorems.tinyobjloader.fuzz_tobj_c Require Statements.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require Theorems.

Theorem ubsan_agrees_holds : OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.Statements.ubsan_agrees.
Proof. exact OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Theorems.strong_universal_error_free_fuzz_tobj_c_ubsan. Qed.
