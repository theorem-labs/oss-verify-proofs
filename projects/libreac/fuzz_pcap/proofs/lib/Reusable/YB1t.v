From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1t.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02 YB1v YB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtF_build : ctable := build_table tfibsegs (symaddr Symbols.AsanUbsan.s___sanitizer_internal_memset) 24%nat (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer18internal_allocatorEv) 84%nat (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN6__asan9Allocator15QuarantineChunkEPNS_9AsanChunkEPvPN11__sanitizer18BufferedStackTraceE) (symwords Symbols.AsanUbsan.s__ZN6__asan9Allocator15QuarantineChunkEPNS_9AsanChunkEPvPN11__sanitizer18BufferedStackTraceE (Symbols.AsanUbsan.s__ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x1e4)%Z) (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN6__asan9asan_freeEPvPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE) (symwords Symbols.AsanUbsan.s__ZN6__asan9asan_freeEPvPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE (Symbols.AsanUbsan.s__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE + 0x2b8)%Z) (tfibtbl_rtA)))).
Definition tfibtbl_rtF : ctable := Eval vm_compute in tfibtbl_rtF_build.
Lemma tfibtbl_rtF_eq : tfibtbl_rtF = tfibtbl_rtF_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtF). Qed.
Lemma tfibtbl_rtF_ok : table_ok tfibsegs tfibtbl_rtF.
Proof. rewrite tfibtbl_rtF_eq. unfold tfibtbl_rtF_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
Definition tfibtbl_rtG_build : ctable := build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb) 123%nat (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE5DrainEPNS_15QuarantineCacheIS2_EES2_) (symwords Symbols.AsanUbsan.s__ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE5DrainEPNS_15QuarantineCacheIS2_EES2_ (Symbols.AsanUbsan.s__ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x328)%Z) (tfibtbl_rtF)).
Definition tfibtbl_rtG : ctable := Eval vm_compute in tfibtbl_rtG_build.
Lemma tfibtbl_rtG_eq : tfibtbl_rtG = tfibtbl_rtG_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtG). Qed.
Lemma tfibtbl_rtG_ok : table_ok tfibsegs tfibtbl_rtG.
Proof. rewrite tfibtbl_rtG_eq. unfold tfibtbl_rtG_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtF_ok. Qed.
Definition tfibtbl_rtK_build : ctable := build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer10UnmapOrDieEPvmb) 26%nat (tfibtbl_rtG).
Definition tfibtbl_rtK : ctable := Eval vm_compute in tfibtbl_rtK_build.
Lemma tfibtbl_rtK_eq : tfibtbl_rtK = tfibtbl_rtK_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtK). Qed.
Lemma tfibtbl_rtK_ok : table_ok tfibsegs tfibtbl_rtK.
Proof. rewrite tfibtbl_rtK_eq. unfold tfibtbl_rtK_build. do 1 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtG_ok. Qed.
Definition tfibtbl_rtM_build : ctable := build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer17DecreaseTotalMmapEm) 9%nat (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer16internal_iserrorEmPi) (symwords Symbols.AsanUbsan.s__ZN11__sanitizer16internal_iserrorEmPi (Symbols.AsanUbsan.s__ZN11__sanitizer14internal_closeEi + 0x4)%Z) (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer22ReleaseMemoryPagesToOSEmm) 41%nat (build_table tfibsegs (symaddr Symbols.AsanUbsan.s__ZN6__asan29FlushUnneededASanShadowMemoryEmm) 50%nat (tfibtbl_rtK)))).
Definition tfibtbl_rtM : ctable := Eval vm_compute in tfibtbl_rtM_build.
Lemma tfibtbl_rtM_eq : tfibtbl_rtM = tfibtbl_rtM_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtM). Qed.
Lemma tfibtbl_rtM_ok : table_ok tfibsegs tfibtbl_rtM.
Proof. rewrite tfibtbl_rtM_eq. unfold tfibtbl_rtM_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtK_ok. Qed.
