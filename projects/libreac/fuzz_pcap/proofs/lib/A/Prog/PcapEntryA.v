(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: split out of lib/A/Prog/PcapEntry.v (a Theorem Labs lane's lib/B closure rule), so that the generic entry contract there names no image: this file holds lib/A's image data, measured on the original v1.9.0 asan pin (the pinned fuzz_pcap.asan image, sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin; capstone disassembly), and the lib/A instance of the contract. Relocated constants: A_LLVMF = 0x807c8 (the symbol LLVMFuzzerTestOneInput); RA_LLVMF = 0x80634 (target_run's `jal 0x807c8` at 0x80630); A_EMPTY = 0x5d3f20 (the object oft_aligned_copy.empty: target_run 0x8059c `auipc a1,0x554` and 0x805a0 `addi s4,a1,-0x68c` give 0x5d3f10, 0x80614 `addi s1,s4,0x10` gives 0x5d3f20, which 0x80628 `mv a0,s1` passes when the payload is empty); LLVMF_STK = 32768 (a COMPOSITION bound over the frozen callee constants, not a whole-reach figure: the composed need is 19200 bytes = the function's own frame 224 (`addi sp,sp,-0xe0` 0x807c8) + 16 of realignment (`andi sp,sp,-0x20` 0x80808) + 128 if the side stack gives no frame (0x80850-0x80868), then pcap_source_open's 96 + 16 (0x8145c, 0x81494) + 96 (0x814dc-0x814f4) and the fmemopen wrapper's AFMEMOPEN_STK 18624 (lib/A/Stdio/PFmemopenISpec.v), which libreac_fuzz_fopen reaches by a tail jump after it pops its 32 bytes (0x807a8, 0x807ac); every other window composes smaller: the allocator rules' ASTACK 16384 below the call (YC5d.v:60, 16752 from sp0), fclose's PFCLOSE_STK 16528 under pcap_source_open (0x81674, 0x816b8) or pcap_source_close (0x81ec8), fread's AFREAD_STK 8192, the bcmp wrapper's 2 * ESTACK. So LLVMF_STK MOVES if those callee constants move (AFMEMOPEN_STK, PFCLOSE_STK, AFREAD_STK, ESTACK, ASTACK, or the open / close / next windows their own statements fix): it must stay >= 600 + the largest callee window + that callee's own frames. The slack (13568 bytes over 19200) is there because the bound composes constants, each a bound over its callee's reach, and the open / next / close statements that fix their own windows are not final; 32768 = 2^15 is also the value the relocated driver discharges. The caller's astk_ok LLVMF_STK, with ly_bot = ly_top - kStackSpan, kStackSpan = 2^23 (YG0f.v:36, :63) and ASTACK = 16384 (YG0d.v:18), asks ly_top - sp0 < 2^23 - 16384); G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)] (the comment at its Definition). The donor text is cgif's lib/A/ACfn.v (origin/ossv/recipes c8557374ad2e), as PcapEntry.v's header says. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YG0f YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapRelro PcapEntry.
Import ListNotations.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := Eval compute in Symbols.Asan.s_LLVMFuzzerTestOneInput.
Definition RA_LLVMF : Z := Eval compute in (Symbols.Asan.s_target_run + 0xcc)%Z.
Definition A_EMPTY : Z := Eval compute in Symbols.Asan.s_oft_aligned_copy_empty.
Definition LLVMF_STK : Z := 32768.
(* The harness's two globals, the bytes the call writes outside its window and its blocks (half-open object ranges,
   not the redzone hulls): g_file_len at 0x5d3f40 (auipc a1,0x553 0x80928; sd s6,0x618(a1) 0x80938) and g_file at
   0x5d3f60 (auipc a0,0x553 0x80924; addi s2,a0,0x63c 0x8092c; sd s5,0(s2) 0x80930 and sd s3,0(s2) 0x80970), 8 bytes
   each: the stores are 8-byte sd, and the symbols g_file_len / g_file (size 32 in the unstripped twin) are the 8-byte
   object followed by ASan's 24-byte redzone, which is not in G. *)
Definition G_HARNESS : list (Z * Z) := Eval compute in [(Symbols.Asan.s_g_file_len, 8); (Symbols.Asan.s_g_file, 8)].
(* lib/A's instance (obligation row 11): the ASan image's segments, its read-only window (PcapRelro.v), the
   addresses and stack bound above, and the harness's globals G_HARNESS (gx_ok for them: a Theorem Labs lane, on AF0m). *)
Definition tfib_lib_contract_x_all_A {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (KS : asource_syms) : Prop :=
@tfib_lib_contract_x_all rc SK OSSVerify.libreac.fuzz_pcap.images.Asan.M.loaded_segments PCAP_RLO PCAP_RHI
A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS B MT XM_LIB XN_LIB KS.
(* GUARD (a Theorem Labs lane): SK is passed by position; if it went back to implicit, instance search would fill
   it and the positional SK would land on the next argument, so this file would stop compiling. *)
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_contract_x_all_A (rc:=rc) SK).
