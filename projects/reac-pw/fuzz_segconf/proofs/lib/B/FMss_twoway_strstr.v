(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_twoway_strstr.v at cold/port-fm-int 5d8d8a15571, relocated A->B by asan-kit elfmap.py + remap.py over the unstripped twins; every image numeral re-derived by symbol / section (fmb-b4 reloc report). *)
(* lib/A/Prog/twoway_strstr.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8), over the
   local-shadow statements (FMss_twoway_strstr_c.v, FMss_TwFront.v, FMss_TwBack.v); the proof line is the original's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import memchr_wrap_c memcmp_wrap_c twoway_strstr_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import
  FMss_memchr_wrap_c FMss_memcmp_wrap_c FMss_twoway_strstr_c FMss_TwSetup_c FMss_TwFront FMss_TwBack.

Theorem twoway_strstr_holds : memchr_wrap_contract_L -> memcmp_wrap_contract_L -> twoway_strstr_contract.
Proof. intros MCW MPW. exact (tw_front (tw_back MCW MPW)). Qed.
