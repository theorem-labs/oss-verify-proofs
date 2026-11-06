(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/memchr.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; its relocation table has no rows). *)
(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/memchr.v, unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import memchr_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
