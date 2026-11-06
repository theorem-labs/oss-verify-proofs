(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.bilateral_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed RT_fk_iface RT_fk_proof Bi_top Bi_fuzz Bi_fuzz_adapt.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_final () := "I69OSSVerify5KrLib2K53A028RT_iface<rt_contracts00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A02=RT_gaps_iface7rt_gaps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027Bi_fuzz:bi_fuzz_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=Bi_fuzz_adapt=bi_fuzz_adaptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Bi_top?bi_cone_of_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;TopA_closed>s3s_of_conetopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;RT_fk_proof@rta_fk_contractsC1?~~~~~~~~~~~~~~~".

Theorem s3s_closed : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_final ()) [] "h02GPh12RCp;1p;6g0000j15Tg0013j14Tg0026j10Tg0034j11Tg004;j63Tg005=j12Tg006CR0#5%40P0f1f0g0079%00%10E3W0W1#2o"). Qed.
