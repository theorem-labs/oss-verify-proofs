(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 69a6a2e91fb7, checker port_addr_check.py 39e67a7eb166. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02 YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs B_PTHREAD_GETSPECIFIC_PC 7%nat (build_table tfibsegs B_TLS_GET_ADDR_PC 9%nat (build_table tfibsegs B_ERRNO_LOCATION_PC 3%nat (build_table tfibsegs B_DISABLEDINTHISTHREAD_PC 6%nat (build_table tfibsegs B_UNWIND_PC 70%nat (build_table tfibsegs B_GETCURRENTPC_PC 90%nat (build_table tfibsegs B_SETERRNOTOENOMEM_PC 8%nat (build_table tfibsegs B_RUNMALLOCHOOKS_PC 93%nat (build_table tfibsegs B_SETALLOCATOROUTOFMEMORY_PC 18%nat (build_table tfibsegs B_STACK_TOP_PC 44%nat (build_table tfibsegs B_GETCURRENTTHREAD_PC 8%nat (build_table tfibsegs B_GETCURRENTTHREADSTATS_PC 14%nat (build_table tfibsegs B_GETMALLOCCONTEXTSIZE_PC 88%nat (build_table tfibsegs B_TRYASANINITFROMRTL_PC 40%nat (build_table tfibsegs B_ASANINITED_PC 6%nat (build_table tfibsegs B_ASANTSDGET_PC 16%nat (build_table tfibsegs B_CANPOISONMEMORY_PC 324%nat (build_table tfibsegs B_WRAP_FREE_PC 206%nat (build_table tfibsegs B_INTERCEPTOR_TLS_GET_ADDR_PC 31%nat (build_table tfibsegs B_SIZECLASSALLOCATOR64LOCALCACHE_PC 1016%nat (build_table tfibsegs B_10RE_PC 96%nat (build_table tfibsegs B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build, B_10RE_PC, B_ASANINITED_PC, B_ASANTSDGET_PC, B_ASAN_MALLOC_BUFFEREDSTACKTRACE_PC, B_CANPOISONMEMORY_PC, B_DISABLEDINTHISTHREAD_PC, B_ERRNO_LOCATION_PC, B_GETCURRENTPC_PC, B_GETCURRENTTHREADSTATS_PC, B_GETCURRENTTHREAD_PC, B_GETMALLOCCONTEXTSIZE_PC, B_INTERCEPTOR_TLS_GET_ADDR_PC, B_PTHREAD_GETSPECIFIC_PC, B_RUNMALLOCHOOKS_PC, B_SETALLOCATOROUTOFMEMORY_PC, B_SETERRNOTOENOMEM_PC, B_SIZECLASSALLOCATOR64LOCALCACHE_PC, B_STACK_TOP_PC, B_TLS_GET_ADDR_PC, B_TRYASANINITFROMRTL_PC, B_UNWIND_PC, B_WRAP_FREE_PC. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs B_EE4FINDEJNS_10STACKT_PC 145%nat (build_table tfibsegs B_STACKDEPOTPUT_STACKTRACE_PC 169%nat (build_table tfibsegs B_STACKDEPOTNODE_STORE_STACKTRACE_PC 23%nat (build_table tfibsegs B_CREATE_PC 45%nat (build_table tfibsegs B_STACKSTORE_STORE_STACKTRACE_PC 150%nat (build_table tfibsegs B_SANITIZER_INTERNAL_MEMCPY_PC 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build, B_CREATE_PC, B_EE4FINDEJNS_10STACKT_PC, B_SANITIZER_INTERNAL_MEMCPY_PC, B_STACKDEPOTNODE_STORE_STACKTRACE_PC, B_STACKDEPOTPUT_STACKTRACE_PC, B_STACKSTORE_STORE_STACKTRACE_PC. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs B_MAP_PC 87%nat (build_table tfibsegs B_MMAPFIXEDNORESERVE_PC 100%nat (build_table tfibsegs B_RESERVESHADOWMEMORYRANGE_PC 75%nat (build_table tfibsegs B_GETNAMEDMAPPINGFD_PC 131%nat (build_table tfibsegs B_MMAPFIXEDORDIE_PC 111%nat (build_table tfibsegs B_MMAPNAMED_PC 128%nat (build_table tfibsegs B_GETMMAPGRANULARITY_PC 4%nat (build_table tfibsegs B_GETPAGESIZE_PC 2%nat (build_table tfibsegs B_INTERNAL_ISERROR_PC 27%nat (build_table tfibsegs B_INCREASETOTALMMAP_PC 26%nat (build_table tfibsegs B_REPORTMMAPFAILUREANDDIE_PC 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build, B_GETMMAPGRANULARITY_PC, B_GETNAMEDMAPPINGFD_PC, B_GETPAGESIZE_PC, B_INCREASETOTALMMAP_PC, B_INTERNAL_ISERROR_PC, B_MAP_PC, B_MMAPFIXEDNORESERVE_PC, B_MMAPFIXEDORDIE_PC, B_MMAPNAMED_PC, B_REPORTMMAPFAILUREANDDIE_PC, B_RESERVESHADOWMEMORYRANGE_PC. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs B_DONTDUMPSHADOWMEMORY_PC 8%nat (build_table tfibsegs B_SYSCONF_PC 139%nat (build_table tfibsegs B_VSNPRINTF_PC 756%nat (build_table tfibsegs B_SANITIZER_INTERNAL_MEMSET_PC 24%nat (build_table tfibsegs B_MAP_PC 87%nat (build_table tfibsegs B_MMAPFIXEDNORESERVE_PC 100%nat (build_table tfibsegs B_RESERVESHADOWMEMORYRANGE_PC 75%nat (build_table tfibsegs B_GETNAMEDMAPPINGFD_PC 131%nat (build_table tfibsegs B_MMAPFIXEDORDIE_PC 111%nat (build_table tfibsegs B_MMAPNAMED_PC 128%nat (build_table tfibsegs B_GETMMAPGRANULARITY_PC 4%nat (build_table tfibsegs B_GETPAGESIZE_PC 2%nat (build_table tfibsegs B_INTERNAL_ISERROR_PC 27%nat (build_table tfibsegs B_INCREASETOTALMMAP_PC 26%nat (build_table tfibsegs B_REPORTMMAPFAILUREANDDIE_PC 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build, B_DONTDUMPSHADOWMEMORY_PC, B_GETMMAPGRANULARITY_PC, B_GETNAMEDMAPPINGFD_PC, B_GETPAGESIZE_PC, B_INCREASETOTALMMAP_PC, B_INTERNAL_ISERROR_PC, B_MAP_PC, B_MMAPFIXEDNORESERVE_PC, B_MMAPFIXEDORDIE_PC, B_MMAPNAMED_PC, B_REPORTMMAPFAILUREANDDIE_PC, B_RESERVESHADOWMEMORYRANGE_PC, B_SANITIZER_INTERNAL_MEMSET_PC, B_SYSCONF_PC, B_VSNPRINTF_PC. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
