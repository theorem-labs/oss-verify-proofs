From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFie.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFhy AFhz AFi0 AFi4 AFi9 AFid.
Import ListNotations. Open Scope Z_scope.
Definition ENOMEM_RETv : Z := 18446744073709551604.
Definition S_R0 : sstate := Eval vm_compute in mkSS (symaddr (Symbols.Asan.s__ZN11__sanitizer13internal_mmapEPvmiiiy + 0x8)%Z) (sr_set (ss_regs S_N) 10%bv (SLit ENOMEM_RETv)) (ss_mem S_N ++ NREGS) None FS.
Lemma S_R0_eq : S_R0 = mkSS (symaddr (Symbols.Asan.s__ZN11__sanitizer13internal_mmapEPvmiiiy + 0x8)%Z) (sr_set (ss_regs S_N) 10%bv (SLit ENOMEM_RETv)) (ss_mem S_N ++ NREGS) None FS. Proof. vm_compute. reflexivity. Qed.
Definition S_R1 : sstate := Eval vm_compute in runtoC (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc)%Z) S_R0.
Definition S_RET : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s___interceptor_malloc + 0x158)%Z) S_R1.
Definition R_map : YP09.region := YP09.mkRegion (Some aMAP) 0 6144 0 6144 [YP09.mkChunk 6129 (CVal 1 (SLit 0))].
Definition S_P0 : sstate := Eval vm_compute in mkSS (symaddr (Symbols.Asan.s__ZN11__sanitizer13internal_mmapEPvmiiiy + 0x8)%Z) (sr_set (ss_regs S_N) 10%bv (SOff aMAP 0)) (R_map :: ss_mem S_N) None FS2.
Lemma S_P0_eq : S_P0 = mkSS (symaddr (Symbols.Asan.s__ZN11__sanitizer13internal_mmapEPvmiiiy + 0x8)%Z) (sr_set (ss_regs S_N) 10%bv (SOff aMAP 0)) (R_map :: ss_mem S_N) None FS2. Proof. vm_compute. reflexivity. Qed.
Definition S_P1 : sstate := Eval vm_compute in runtoC (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc)%Z) S_P0.
Definition S_L1 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x58)%Z) S_P1.
Definition S_L1l : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x240)%Z) (armR BC_GEU true 14 10 S_L1).
Definition S_L1lo : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s_memset) (armR BC_GEU true 14 11 S_L1l).
Definition S_L1h : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x98)%Z) (armR BC_GEU false 14 10 S_L1).
Definition S_L1h2 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x240)%Z) (armR BC_LTU true 7 10 S_L1h).
Definition S_L1h3 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x280)%Z) (armR BC_GEU false 14 11 S_L1h2).
Definition S_L1hi : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s_memset) (armR BC_GEU false 5 11 S_L1h3).
Definition S_M1 : sstate := Eval vm_compute in psJ sL1 S_L1lo.
Lemma S_M1_h : psJ sL1 S_L1hi = S_M1. Proof. vm_compute. reflexivity. Qed.
Definition S_P2 : sstate := Eval vm_compute in ss_after_stretch S_M1 (ss_mem S_M1) sM1 CLOB_MS (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x114)%Z).
Definition S_P3 : sstate := Eval vm_compute in pin S_P2 23%bv (SOff aEND 0).
Definition S_P4 : sstate := Eval vm_compute in pin (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x120)%Z) S_P3) 11%bv (SOff aTL 0).
Definition S_L2 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x58)%Z) S_P4.
Definition S_L2l : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x240)%Z) (armR BC_GEU true 14 10 S_L2).
Definition S_L2lo : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s_memset) (armR BC_GEU true 14 11 S_L2l).
Definition S_L2h : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x98)%Z) (armR BC_GEU false 14 10 S_L2).
Definition S_L2h2 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x240)%Z) (armR BC_LTU true 7 10 S_L2h).
Definition S_L2h3 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x280)%Z) (armR BC_GEU false 14 11 S_L2h2).
Definition S_L2hi : sstate := Eval vm_compute in runto (symaddr Symbols.Asan.s_memset) (armR BC_GEU false 5 11 S_L2h3).
Definition S_M2 : sstate := Eval vm_compute in psJ sL2 S_L2lo.
Lemma S_M2_h : psJ sL2 S_L2hi = S_M2. Proof. vm_compute. reflexivity. Qed.
Definition S_P5 : sstate := Eval vm_compute in ss_after_stretch S_M2 (ss_mem S_M2) sM2 CLOB_MS (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x124)%Z).
Definition S_P6 : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SOff aMAP 0) (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x15c)%Z) S_P5).
Definition S_P7 : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x160)%Z) S_P6).
Definition S_P8 : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff aNCH 0) (SLit 20)) (SLit 0) (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x1b4)%Z) S_P7).
Definition S_X : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x260)%Z) S_P8.
Definition R_qs : YP09.region := YP09.mkRegion (Some aQS) 0 8 0 8 [].
Definition S_Y0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x278)%Z) (arm BC_EQ false (SOff aNCH 0) (SOff aRES 0) S_X).
Definition S_Y : sstate := Eval vm_compute in addreg R_qs (noconds (pin S_Y0 12%bv (SOff aQS 0))).
Definition S_Z0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2a4)%Z) S_Y.
Definition S_Zt : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2ac)%Z) (arm BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_Z0).
Definition S_Zf : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2ac)%Z) (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_Z0).
Definition S_Z : sstate := Eval vm_compute in noconds (forget S_Zt sMX [12]%bv).
Lemma S_Z_f : noconds (forget S_Zf sMX [12]%bv) = S_Z. Proof. vm_compute. reflexivity. Qed.
Definition S_Z1 : sstate := Eval vm_compute in pin (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2b4)%Z) S_Z) 11%bv (SOff aBSL (-104)).
Definition S_T0 : sstate := Eval vm_compute in runto (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2c4)%Z) S_Z1.
Lemma segS2_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 S_R0) = RS_stopped SR_fetch /\ ss_pc S_R1 = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc)%Z) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_R1) = RS_stopped (SR_jalr (SOff 1 0)) /\ ss_pc S_RET = (symaddr (Symbols.Asan.s___interceptor_malloc + 0x158)%Z) /\
map (sr_get (ss_regs S_RET)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SLit 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 S_P0) = RS_stopped SR_fetch /\ ss_pc S_P1 = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0xbc)%Z) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_P1) = RS_stopped (SR_branch BC_GEU (SOff aSHB (-1)) (SOff aMAP 0))   /\ ss_pc S_L1 = (symaddr (Symbols.Asan.s__ZN6__asan12PoisonShadowEmmh + 0x58)%Z) /\ ss_pc S_M1 = (symaddr Symbols.Asan.s_memset) /\
map (sr_get (ss_regs S_M1)) [1; 10; 11; 12]%bv =
[SLit (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x114)%Z); SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aMAP 0) (SLit 3)); SLit 250;
SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SOff aMAP 4088) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 0) (SLit 3))) (SLit 0)] /\
sr_get (ss_regs S_P2) 23%bv = SAlu ALU_AND (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SLit (-8)) /\
sr_get (ss_regs (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x120)%Z) S_P3)) 11%bv = SAlu ALU_ADD (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SMd M_MUL (SOff aEND 0) (SLit (-1))) /\
ss_pc S_M2 = (symaddr Symbols.Asan.s_memset) /\
map (sr_get (ss_regs S_M2)) [1; 10; 11; 12]%bv =
[SLit (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x124)%Z); SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aEND 0) (SLit 3)); SLit 250;
SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aEND (-8)) (SOff aTL 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aEND 0) (SLit 3))) (SLit 0)] /\
ss_pc S_X = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x260)%Z) /\ ss_pc S_Y0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x278)%Z) /\ sr_get (ss_regs S_Y0) 12%bv = SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3)) /\
ss_pc S_Z0 = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2a4)%Z) /\ ss_pc S_Z = (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2ac)%Z) /\
sr_get (ss_regs (runto (symaddr (Symbols.Asan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x2b4)%Z) S_Z)) 11%bv = SAlu ALU_ADD (SLit (TFIB_INST + 64)) (SAlu ALU_SLL (SAlu ALU_XOR (sr_get (ss_regs S_Z) 19%bv) (SLit 63)) (SLit 3)) /\
ss_pc S_T0 = (symaddr (Symbols.Asan.s__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb + 0x2c4)%Z) /\
map (sr_get (ss_regs S_T0)) [2; 18; 19; 20; 21]%bv = [SOff 2 (-2272); SOff aMAP 4096; SOff aND 0; SOff aMAP 6144; SOff 10 0].
Proof. vm_compute. repeat split; reflexivity. Qed.
