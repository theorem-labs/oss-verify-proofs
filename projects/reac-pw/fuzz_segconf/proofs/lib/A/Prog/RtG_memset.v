(* Taken from lib/A/Prog/memset.v of an earlier relocation for fuzz_command; module paths re-pointed (lib/A/Prog names prefixed RtG_, lib.A.Ox -> lib.Ox, lib.A.Strw kept). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import RtG_memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
