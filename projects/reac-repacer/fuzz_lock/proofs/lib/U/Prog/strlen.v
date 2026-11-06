(* Modified by Theorem Labs: ported from libreac/fuzz_disco proofs/libreac/fuzz_disco/lib/U/Prog/strlen.v at 25e3d17bdb5059606131377a3722d585415ab5d6, donor pin sha256 56121de6ba4cff85e0fa262e9783f384e35fb8642d057f7a3a4290bcc245b22e, for reac-repacer/fuzz_lock: module paths and image addresses only, entry strlen 0x1f12c (donor) -> 0x1b5b0 (this image). *)
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import strlen_c.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
