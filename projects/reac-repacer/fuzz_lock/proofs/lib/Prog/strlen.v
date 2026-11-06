(* Modified by Theorem Labs: ported from libreac/fuzz_disco proofs/libreac/fuzz_disco/lib/Prog/strlen.v at 25e3d17bdb5059606131377a3722d585415ab5d6, donor pin sha256 04988e3ab31341965e44f0ca1bb0e5ed18fe6892e2c753df7a87bec197576f7c, for reac-repacer/fuzz_lock: module paths and image addresses only, entry strlen 0x1e970 (donor) -> 0x1b414 (this image). *)
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import strlen_c.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
