From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap v1.9.0, asan-ubsan build.
   lib/B/Stdio/PStdioImgB.v: the asan-ubsan image's stdio pcs, ONE file per image (a Theorem Labs lane 02:27Z
   ruling (b); the asan twin is a Theorem Labs lane's lib/A/Stdio/PStdioImgA.v). It holds ONLY numerals: no
   statement, no lemma. The contracts (lib/A/Stdio/PFmemopenM.v etc.) take these as parameters.
   IMAGE: the pin fuzz_pcap.asan-ubsan, sha256
   9e66f771f22af67aadc8b8ddcd7ee91f46c4c63442c694faaf2375f9c5b79321. Symbols read from the pin's
   unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59...), whose
   allocated sections are byte-equal to the pin's (only .note.gnu.build-id differs).
   Each pc keyed by SYMBOL + OFFSET on that image (capstone):
     PFMEMOPEN_U    = fmemopen+0    = 0x8e73c (`addi sp,sp,-48`);
     FM_MALLOC_RA_U = fmemopen+0x9c = 0x8e7d8, the return of its first `jal __wrap_malloc`
                      (0x8e7d4 -> 0x52c28).
     PFREAD_U       = fread+0     = 0x8ed28;
     PTOREAD_U      = __toread+0  = 0x8e504;
     PMREAD_U       = mread+0     = 0x8e90c;
     TRAMP_MEMCPY_U = __interceptor_trampoline_memcpy+0 = __wrap_memcpy+0 = 0x51560, the target of
                     both of mread's `jal` (mread+0x64 = 0x8e970, mread+0xa4 = 0x8e9b0).
   For a Theorem Labs lane's asan-ubsan twin lanes (mseek, mclose, fclose, fflush; a Theorem Labs lane 03:40Z: each lane's B pcs
   live here, never in a statement file), all function ENTRIES:
     PMSEEK_U       = mseek+0  = 0x8eaf4 (local);
     PMCLOSE_U      = mclose+0 = 0x8eb90 (local);
     PFCLOSE_MUSL_U = fclose+0 = 0x8e0e0 (WEAK symbol);
     PFFLUSH_MUSL_U = fflush+0 = 0x8e308 (WEAK symbol);
     PFFLUSH_ICPT_U = __interceptor_trampoline_fflush+0 = 0x41618 (the 4-byte jump to the wrapper);
     IC_ENTRY_U     = __interceptor_trampoline_fclose+0 = 0x4161c (the 4-byte jump to the wrapper). It CITES the
                      core's own constant lib/Reusable/YE2e.v:31 IC_ENTRY (the entry of the core's fclose-interceptor
                      walk iclose_front, whose statement names it), so the core stays its single home (a Theorem Labs lane 06:06Z).
   Each function has the same size and the same instruction sequence (mnemonics) in both images.
   CONTROL: the same rule on the asan pin gives 0x8e870 / 0x8e90c / 0x8ee5c / 0x8e638 / 0x8ea40 / 0x51510, the
   values lib/A/Stdio/PStdioImgA.v states; and 0x8ec28 / 0x8ecc4 / 0x8e214 / 0x8e43c / 0x415c8 / 0x415cc for
   the six entries above.
   NAMES keep the _U suffix on purpose: until a Theorem Labs lane's step 2 (a working branch beb05bac2a3)
   lib/A/Stdio/PFmemopenM.v defined the asan PFMEMOPEN, and a short name that two Required files define
   resolves by Require order; that is how this lane's walk once called the asan fmemopen. The suffix keeps
   every B pc distinct from its lib/A/Stdio/PStdioImgA.v name. This is the single home of pcap's
   asan-ubsan stdio pcs: Require it, never re-declare one locally. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE2e.
Open Scope Z_scope.

Definition PFMEMOPEN_U    : Z := (symaddr Symbols.AsanUbsan.s_fmemopen).
Definition FM_MALLOC_RA_U : Z := (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z).
Definition PFREAD_U       : Z := (symaddr Symbols.AsanUbsan.s_fread_unlocked).
Definition PTOREAD_U      : Z := (symaddr Symbols.AsanUbsan.s___toread).
Definition PMREAD_U       : Z := (symaddr Symbols.AsanUbsan.s_mread).
Definition TRAMP_MEMCPY_U : Z := (symaddr Symbols.AsanUbsan.s___wrap_memcpy).
Definition PMSEEK_U       : Z := (symaddr Symbols.AsanUbsan.s_mseek).
Definition PMCLOSE_U      : Z := (symaddr Symbols.AsanUbsan.s_mclose).
Definition PFCLOSE_MUSL_U : Z := (symaddr Symbols.AsanUbsan.s_fclose).
Definition PFFLUSH_MUSL_U : Z := (symaddr Symbols.AsanUbsan.s_fflush_unlocked).
Definition PFFLUSH_ICPT_U : Z := (symaddr Symbols.AsanUbsan.s___wrap_fflush).
Definition IC_ENTRY_U     : Z := YE2e.IC_ENTRY.
