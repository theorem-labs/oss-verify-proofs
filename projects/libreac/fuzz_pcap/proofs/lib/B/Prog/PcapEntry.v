(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapEntry.v for fuzz_pcap.asan-ubsan (libreac v1.9.0; image root: the original v1.9.0 set, the pinned fuzz_pcap.asan-ubsan image, sha256 9e66f771f22af67a...; symbols from its unstripped twin fuzz_pcap.asan-ubsan, sha256 c969d83cdd5943a8...; capstone 5.0.7 disassembly). The contract text is lib/A's image-generic one (lib/A/Prog/PcapEntry.v tfib_lib_contract_x_all, a Theorem Labs lane ruling); this file is its named asan-ubsan instance tfib_lib_contract_x_all_B, in the shape of lib/A's tfib_lib_contract_x_all_A, at this image's data, each MEASURED on this pin (never an asan value shifted):
   segs := AsanUbsan.M.loaded_segments; rlo / rhi := lib/B/Prog/PcapRelro.v PCAP_RLO / PCAP_RHI = 0x99198 / 0x9a3f0 (the start of .data.rel.ro, the end of .got);
   A_LLVMF = 0x80818 (the symbol LLVMFuzzerTestOneInput, 2120 bytes);
   RA_LLVMF = 0x80684 (target_run's `jal 0x80818` at 0x80680);
   A_EMPTY = 0x5d3e20 (the object oft_aligned_copy.empty, 32 bytes: target_run 0x805ec `auipc a1,0x554` and 0x805f0 `addi s4,a1,-0x7dc` give 0x5d3e10, 0x80664 `addi s1,s4,0x10` gives 0x5d3e20, which 0x80678 `mv a0,s1` passes when the payload is empty);
   G := G_HARNESS_U = [(0x5d3e40, 8); (0x5d3e60, 8)] (g_file_len, g_file; the contract's ajournal_gx ranges, below);
   LLVMF_STK = 32768, the same composition rule as lib/A's, redone over this image's frames: the composed need is 19232 bytes = the function's own frame 256 (`addi sp,sp,-0x100` 0x80818) + 16 of realignment (`andi sp,sp,-0x20` 0x80858) + 128 if the side stack gives no frame (0x808a0-0x808b8), then pcap_source_open's 96 + 16 (`addi sp,sp,-0x60` 0x811e0, `andi sp,sp,-0x20` 0x81218) + 96 (0x81260-0x81278) and the fmemopen wrapper's AFMEMOPEN_STK 18624 (lib/A/Stdio/PFmemopenISpec.v), which libreac_fuzz_fopen reaches by a tail jump after it pops its 32 bytes (0x807f8, 0x807fc). Every other window composes smaller: the allocator rules' ASTACK 16384 below the call (YC5d.v:60, 16784 from sp0); fclose's PFCLOSE_STK 16528 under pcap_source_open (17136 from sp0) or under pcap_source_close (frame 32, `addi sp,sp,-0x20` 0x81d4c: 16960); fread's AFREAD_STK 8192 under pcap_source_next (frame 256, `addi sp,sp,-0x100` 0x815b8, + 16 + its class-0 frame 64: 8928); rd32 and rd_u32, a 16-byte frame each (`addi sp,sp,-0x10` 0x81060, 0x81c38) and no call that returns; the bcmp wrapper's 2 * ESTACK. The slack is 13536 bytes over 19232. LLVMF_STK MOVES if those callee constants move; it must stay >= 400 + the largest callee window + that callee's own frames.
   EV_LIB and LIVE_LIB are lib/A's shared constants (the allocator calls and their sizes are the same in both builds; the two abbreviations below name lib/A's constants, so this file states no second value for them). SK stays an explicit binder, as in lib/A (a Theorem Labs lane): never inferred, so the plain build's global sink_head instance (lib/Reusable/YI5b.v) is not reachable by inference. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
(* The image-generic contract, required WITHOUT Import: lib/A's file also defines lib/A's image constants under the
   names this file defines, so every use of it is qualified (PEG). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry.
(* (Required first, as lib/A's file requires its own non-Reusable dependencies first: they load lib/U's twins of
   YI16 / YK11 / YM05, and the Reusable imports below must come after them, so that the partial names YI16.x, YK11.x,
   YM05.x name lib/Reusable's modules.) *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapRelro.
Import ListNotations.
Local Open Scope Z_scope.
Module PEG := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapEntry.

Definition A_LLVMF : Z := Eval compute in Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput.
Definition RA_LLVMF : Z := Eval compute in (Symbols.AsanUbsan.s_target_run + 0xcc)%Z.
Definition A_EMPTY : Z := Eval compute in Symbols.AsanUbsan.s_oft_aligned_copy_empty.
Notation EV_LIB := PEG.EV_LIB (only parsing).
Notation LIVE_LIB := PEG.LIVE_LIB (only parsing).
Definition LLVMF_STK : Z := 32768.
(* The harness's two globals, the bytes the call writes outside its window and its blocks (W_journal.v ajournal_gx's
   program-global ranges G; half-open OBJECT ranges, not the redzone hulls): g_file_len at 0x5d3e40 (auipc s8,0x553
   0x809a8; sd s6,0x498(s8) 0x809ac) and g_file at 0x5d3e60 (auipc a0,0x553 0x80984; addi s3,a0,0x4dc 0x80988;
   sd s5,0(s3) 0x80990 and sd s2,0(s3) 0x809dc), 8 bytes each: the stores are 8-byte sd, and this pin's asan_globals
   section (0x9dfd0) registers both with size 8 and size_with_redzone 32 (the .symtab sizes 32 include ASan's 24-byte
   redzone, which is not in G). Neighbours: oft_aligned_copy.empty (0x5d3e20, 32 bytes, the driver's, not registered)
   ENDS at 0x5d3e40, so g_file_len's range abuts it with zero slack and does not overlap it; g_file_len's redzone
   0x5d3e48..0x5d3e60 and g_file's 0x5d3e68..0x5d3e80 separate them from each other and from the next object
   (libunwind's DwarfFDECache _lock, 0x5d3e80). The function reads g_file_len only (ten `ld rd,0x498(s8)`, seven of them
   PLdHi slots of the listing, 0x80a14 .. 0x80e1c, three plain words in the end-of-walk loop, 0x81000, 0x8100c,
   0x8101c); libreac_fuzz_fopen, under the opens, reads both (0x807d8, 0x807e4). *)
Definition G_HARNESS_U : list (Z * Z) :=
  Eval compute in [(Symbols.AsanUbsan.s_g_file_len, 8); (Symbols.AsanUbsan.s_g_file, 8)].

(* lib/B's instance: the asan-ubsan image's segments, its read-only window (PcapRelro.v), the addresses and stack
   bound above, and the harness's globals G_HARNESS_U. *)
Definition tfib_lib_contract_x_all_B {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (KS : asource_syms) : Prop :=
@PEG.tfib_lib_contract_x_all rc SK OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.loaded_segments PCAP_RLO PCAP_RHI
A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS_U B MT XM_LIB XN_LIB KS.
(* GUARD (a Theorem Labs lane): SK is passed by position; if it went back to implicit, instance search would fill
   it and the positional SK would land on the next argument, so this file would stop compiling. *)
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_contract_x_all_B (rc:=rc) SK).
