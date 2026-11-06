(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.bilateral_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_closed () := "I69OSSVerify5KrLib2K53A028RT_iface<rt_contracts00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A02=RT_gaps_iface7rt_gaps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:D_libiface<fuzz_one_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028TopA_s3s?s3s_A02_of_coneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:D_libiface5LIB_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_gaps_proof6rta_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_gaps_proof8rta_gapsC1?~~~~~~~~~~~~~~~".

Theorem s3s_of_conetop : (rt_contracts RTA -> rt_gaps RTA -> fuzz_one_cps RTA LIB_A) ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_closed ()) [] "h04CONEp;1p;2g0000j13Tg0013j12Tg0026j20Tg0039j11Tg004=R0#3%20g0053,00[[f0g005og006oO2#1W0o"). Qed.
