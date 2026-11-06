(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_twoway_strstr.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* lib/A/Prog/twoway_strstr.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8), over the
   local-shadow statements (FMss_twoway_strstr_c.v, FMss_TwFront.v, FMss_TwBack.v); the proof line is the original's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memchr_wrap_c memcmp_wrap_c twoway_strstr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import
  FMss_memchr_wrap_c FMss_memcmp_wrap_c FMss_twoway_strstr_c FMss_TwSetup_c FMss_TwFront FMss_TwBack.

Theorem twoway_strstr_holds : memchr_wrap_contract_L -> memcmp_wrap_contract_L -> twoway_strstr_contract.
Proof. intros MCW MPW. exact (tw_front (tw_back MCW MPW)). Qed.
