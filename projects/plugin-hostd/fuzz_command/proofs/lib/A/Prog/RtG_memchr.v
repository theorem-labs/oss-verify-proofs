(* Taken from lib/A/Prog/memchr.v of an earlier relocation for fuzz_command; module paths re-pointed (lib/A/Prog names prefixed RtG_, lib.A.Ox -> lib.Ox, lib.A.Strw kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RtG_memchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
