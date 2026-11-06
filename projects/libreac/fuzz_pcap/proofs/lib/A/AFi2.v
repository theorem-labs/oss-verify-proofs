From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFi2.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AB1q AF0m AF0x AFl0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AFhy AFi1 AFhz AFi0.
Import ListNotations. Open Scope Z_scope.
Definition KS_U : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s__ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj) SS0K.
Definition rs_Uk : smem := match ss_mem KS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition KS_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call KS_U rs_Uk hU1 (symaddr (Symbols.Asan.s___interceptor_malloc + 0x124)%Z))).
Definition KS_A : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1ac)%Z) KS_1.
Definition KS_Ab : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1d8)%Z) (arm BC_LTU true (SLit 8) (SOff 10 0) KS_A).
Definition KS_As : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1d8)%Z) (arm BC_LTU false (SLit 8) (SOff 10 0) KS_A).
Definition KS_B : sstate := Eval vm_compute in noconds (pin (pin KS_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0)).
Lemma KS_B_s : noconds (pin (pin KS_As 10%bv (SOff aR8 0)) 11%bv (SLit 0)) = KS_B. Proof. vm_compute. reflexivity. Qed.
Definition KS_B1 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1f4)%Z) KS_B.
Definition KS_B2 : sstate := Eval vm_compute in pin KS_B1 9%bv (SOff aNP 0).
Definition KS_C0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x28)%Z) KS_B2.
Definition KS_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) KS_C0.
Definition KS_E0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x194)%Z) KS_C.
Definition KS_E : sstate := Eval vm_compute in noconds (pin KS_E0 8%bv (SOff aCL 0)).
Definition KS_F0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1ac)%Z) KS_E.
Definition KS_F : sstate := Eval vm_compute in pin KS_F0 9%bv (SOff aP 0).
Definition KS_JN : sstate := Eval vm_compute in noconds (forget (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1b4)%Z) KS_F) hJN CLOBJ).
Definition KS_G0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1d4)%Z) KS_JN.
Definition KS_G : sstate := Eval vm_compute in pin KS_G0 14%bv (SOff aPV (-16)).
Definition KS_H0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2a0)%Z) KS_G.
Definition KS_H : sstate := Eval vm_compute in pin KS_H0 10%bv (SOff aK 0).
Definition KS_J0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2c4)%Z) KS_H.
Definition KS_J : sstate := Eval vm_compute in
arm BC_LTU false (SAlu ALU_ADD (SOff aR8 16) (SOff aK 0)) (SAlu ALU_ADD (SOff aK 16) (SOff aNP 0)) KS_J0.
Definition KS_K0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2ec)%Z) KS_J.
Definition KS_K : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) KS_K0.
Definition KS_PD : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s__ZN11__sanitizer13StackDepotPutENS_10StackTraceE) KS_K.
Lemma seg1k_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 KS_1) = RS_stopped (SR_branch BC_LTU (SLit 8) (SOff 10 0)) /\
ss_pc KS_A = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1ac)%Z) /\ ss_pc KS_Ab = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1d8)%Z) /\ ss_pc KS_As = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1d8)%Z) /\ ss_pc KS_B1 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x1f4)%Z) /\ ss_pc KS_C0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x28)%Z) /\
ss_pc KS_E0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x194)%Z) /\ ss_pc KS_F0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1ac)%Z) /\ ss_pc KS_JN = (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1b4)%Z) /\ ss_pc KS_G0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm + 0x1d4)%Z) /\ ss_pc KS_H0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2a0)%Z) /\
ss_pc KS_J0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2c4)%Z) /\ ss_pc KS_K0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2ec)%Z) /\ ss_pc KS_PD = (symaddr Symbols.Asan.s__ZN11__sanitizer13StackDepotPutENS_10StackTraceE) /\
sr_get (ss_regs KS_Ab) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs KS_Ab) 11%bv = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0)) (SLit 7) /\
sr_get (ss_regs KS_As) 10%bv = SLit 8 /\ sr_get (ss_regs KS_As) 11%bv = SLit 0 /\
sr_get (ss_regs KS_B1) 9%bv = SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 1)) /\
sr_get (ss_regs KS_E0) 8%bv = SAlu ALU_SRL (SOff aR8 47) (SLit 5) /\
sr_get (ss_regs KS_F0) 9%bv = SAlu ALU_ADD (SOff aT 208) (SMd M_MUL (SOff aCL 0) (SLit 80)) /\
sr_get (ss_regs KS_G0) 14%bv = SAlu ALU_ADD (SOff aP 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff aCNT 0) (SLit 32)) (SLit (-4294967296))) (SLit 30)) /\
sr_get (ss_regs KS_H0) 10%bv = SAlu ALU_ADD (SAlu ALU_ADD (SOff aSB 0) (SAlu ALU_SLL (SOff aCL 0) (SLit 32))) (SAlu ALU_SLL (SOff aV 0) (SLit 4)) /\
sr_get (ss_regs KS_H) 20%bv = SLit 16 /\
sr_get (ss_regs KS_PD) 1%bv = SLit (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3ac)%Z) /\ sr_get (ss_regs KS_PD) 10%bv = SOff 2 (-2112) /\ sr_get (ss_regs KS_PD) 11%bv = SOff aLEN 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition hJ : nat := 139.
Definition hMS2k : nat := 152.
Definition rs_Dk : smem := match ss_mem KS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition KS_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call KS_PD rs_Dk hD1 (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3ac)%Z)).
Definition KS_M0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3d4)%Z) KS_2.
Definition KS_M : sstate := Eval vm_compute in pin KS_M0 10%bv (SOff aSK 0).
Definition KS_N0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4a4)%Z) KS_M.
Definition KS_N : sstate := Eval vm_compute in pin KS_N0 22%bv (SOff aN8D 0).
Definition KS_Nz : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8)%Z) (arm BC_EQ true (SOff aN8D 0) (SLit 0) KS_N).
Definition KS_Nn : sstate := Eval vm_compute in arm BC_EQ false (SOff aN8D 0) (SLit 0) KS_N.
Definition KS_O0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x2b8)%Z) KS_Nn.
Definition KS_O : sstate := Eval vm_compute in pin (pin KS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSK 2).
Definition KS_MS1 : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s_memset) KS_O.
Definition KS_Q1 : sstate := Eval vm_compute in ss_after_stretch KS_MS1 (ss_mem KS_MS1) hMS1 CLOB_MS (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8)%Z).
Definition CLOB_J : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition clr0 (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (R_scr2 :: tl (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition KS_Q : sstate := Eval vm_compute in noconds (forget (clr0 KS_Nz) hJ CLOB_J).
Lemma KS_Q_n : noconds (forget (clr0 KS_Q1) hJ CLOB_J) = KS_Q. Proof. vm_compute. reflexivity. Qed.
Definition KS_Qe : sstate := Eval vm_compute in arm BC_EQ true (SOff aNP 0) (SOff aN8D 0) KS_Q.
Definition KS_Qo : sstate := Eval vm_compute in arm BC_EQ false (SOff aNP 0) (SOff aN8D 0) KS_Q.
Definition KS_P0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x548)%Z) KS_Qo.
Definition KS_Po : sstate := Eval vm_compute in addreg R_pb (pin KS_P0 10%bv (SOff aPB 0)).
Definition kst_T (ss : sstate) : sstate := pin (runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) ss) 10%bv (SOff aSSLOT 0).
Definition kst_X (ss : sstate) : sstate := let m := runto (symaddr Symbols.Asan.s_memset) ss in ss_after_stretch m (ss_mem m) hMS2k CLOB_MS (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6e0)%Z).
Definition KS_Te : sstate := Eval vm_compute in kst_T KS_Qe.
Definition KS_Xe : sstate := Eval vm_compute in kst_X KS_Te.
Definition KS_RETe : sstate := Eval vm_compute in st_RET KS_Xe.
Definition KS_To : sstate := Eval vm_compute in kst_T KS_Po.
Definition KS_Xo : sstate := Eval vm_compute in kst_X KS_To.
Definition KS_RETo : sstate := Eval vm_compute in st_RET KS_Xo.
Definition SSLOT_term : sv := SAlu ALU_ADD (SOff aT 2912) (SAlu ALU_SLL (SAlu ALU_SRL (SOff aR8 47) (SLit 5)) (SLit 3)).
Lemma seg2k_stops :
ss_pc KS_M0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x3d4)%Z) /\ ss_pc KS_N0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4a4)%Z) /\ ss_pc KS_Nz = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8)%Z) /\ ss_pc KS_O0 = (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x2b8)%Z) /\ ss_pc KS_MS1 = (symaddr Symbols.Asan.s_memset) /\
ss_pc KS_Q = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8)%Z) /\ ss_pc KS_P0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x548)%Z) /\
ss_pc (runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) KS_Qe) = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) /\ ss_pc (runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) KS_Po) = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) /\
ss_pc (runto (symaddr Symbols.Asan.s_memset) KS_Te) = (symaddr Symbols.Asan.s_memset) /\ ss_pc (runto (symaddr Symbols.Asan.s_memset) KS_To) = (symaddr Symbols.Asan.s_memset) /\
ss_pc KS_RETe = (symaddr (Symbols.Asan.s___interceptor_malloc + 0x158)%Z) /\ ss_pc KS_RETo = (symaddr (Symbols.Asan.s___interceptor_malloc + 0x158)%Z) /\
sr_get (ss_regs KS_M0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aK 0) (SLit 3)) /\
sr_get (ss_regs KS_N0) 22%bv = SAlu ALU_AND (SOff aNP 0) (SLit 281474976710648) /\
sr_get (ss_regs KS_O0) 8%bv = SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aK 8) (SOff aN8D 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aK 16) (SLit 3)) /\
sr_get (ss_regs KS_O0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aK 16) (SLit 3)) /\
sr_get (ss_regs KS_P0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SAlu ALU_ADD (SOff aK 16) (SOff aN8D 0)) (SLit 3)) /\
sr_get (ss_regs (runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) KS_Qe)) 10%bv = SSLOT_term /\ sr_get (ss_regs (runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x698)%Z) KS_Po)) 10%bv = SSLOT_term /\
sr_get (ss_regs KS_MS1) 1%bv = SLit (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x4b8)%Z) /\ sr_get (ss_regs (runto (symaddr Symbols.Asan.s_memset) KS_Te)) 1%bv = SLit (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6e0)%Z) /\ sr_get (ss_regs (runto (symaddr Symbols.Asan.s_memset) KS_To)) 1%bv = SLit (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x6e0)%Z).
Proof. vm_compute. repeat split; reflexivity. Qed.
