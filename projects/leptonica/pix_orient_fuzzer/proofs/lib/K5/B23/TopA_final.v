(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.leptonica.pix_orient_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_s3s RT_fk_iface RT_fk_proof RT23_iface RT23b_iface RT_stackmalloc347 RT_stackfree7 RT_strchr23 RT_sscanf23 RT_facts_lo Po_rot90_defs Po_top Po_fuzz Po_fuzz_adapt.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_final () := "C69OSSVerify5KrLib2K53B23;RT_facts_lo;rta_live_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237Po_fuzz:po_fuzz_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=Po_fuzz_adapt=po_fuzz_adaptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238TopA_s3s?s3s_B02_of_coneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Po_top?po_cone_of_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_gaps_proof6rta_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_gaps_proof8rta_gapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_fk_proof@rta_fk_contractsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_3FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_4FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_strchr23;rta_strchrFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;RT_sscanf23>rta_sscanf_ddFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23ART_stackmalloc347Crta_stack_malloc_7FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23=RT_stackfree7Arta_stack_free_7FC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23:TopA_final?rta_art_live_loC1?~~~~~~~~~~~~~~~".

Lemma rta_art_live_lo : art_live_lo RTA.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_final ()) [] "g0000o"). Qed.

Theorem s3s_closed : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_final ()) [] "p;1p;=g0013j14Tg0021j13Tg0038j11Tg004<l=2Tg005>R0g0064g0074g0086g009>g00:Og00;`g00<cg00=ig00?:g00@Ef1f0M=2p=0%40%30'0#1o"). Qed.
