(* Taken from lib/A/Prog/memchr.v of an earlier relocation for fuzz_command; module paths re-pointed (lib/A/Prog names prefixed RtG_, lib.A.Ox -> lib.Ox, lib.B.Strw kept). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RtG_memchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
