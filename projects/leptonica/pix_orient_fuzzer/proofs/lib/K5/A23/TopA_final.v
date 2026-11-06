(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Asan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s RT_fk_iface RT_fk_proof RT23_iface RT23b_iface RT_stackmalloc347 RT_stackfree7 RT_strchr23 RT_sscanf23 Po_top Po_fuzz Po_fuzz_adapt.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_final () := "C69OSSVerify5KrLib2K53A237Po_fuzz:po_fuzz_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_fuzz_adapt=po_fuzz_adaptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238TopA_s3s?s3s_A02_of_coneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236Po_top?po_cone_of_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=RT_gaps_proof6rta_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=RT_gaps_proof8rta_gapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_fk_proof@rta_fk_contractsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23ART_stackmalloc347Crta_stack_malloc_3FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23ART_stackmalloc347Crta_stack_malloc_4FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_strchr23;rta_strchrFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_sscanf23>rta_sscanf_ddFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23ART_stackmalloc347Crta_stack_malloc_7FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=RT_stackfree7Arta_stack_free_7FC1?~~~~~~~~~~~~~~~".

Theorem s3s_closed : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_final ()) [] "p;1p;<g0000j14Tg000nj13Tg0025j11Tg0039l<2Tg004;R0g0051g0061g0073g008;g009Lg00:]g00;`g00<fg00>7f1f0M<2p=0%40%30'0#1o"). Qed.
