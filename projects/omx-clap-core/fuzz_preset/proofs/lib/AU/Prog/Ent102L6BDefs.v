(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, PIN sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): the SYMBOLIC
   STATE of segment L6x of LLVMFuzzerTestOneInput (B' entry 0x816cc), the exit lane (listing +0x1c4 .. the `ret` at
   +0x2c4, no call), for the lane proof in lib/AU/Prog/Ent102L6B.v. Definitions only: the regions the lane touches,
   the atom numbering, the facts and the entry environment. The cut statements are lib/AU/Ent102CutsB.v's (blob
   4802d1fcf13d at the time of writing; earlier, blob
   a74a7497b9d0); nothing is restated here.
   PORTED from lib/A/Prog/Ent102L6ADefs.v (blob f2445bce68a1, a working branch a2d6bb26a279) by
   port/a2b.py (sha256 f5113cbc90e503da, no --map; a2b's rename L6_A_FLAG / L6_A_RA -> L6_B_FLAG / L6_B_RA). Hand
   fixes: the Require routing (lib.B Listing_prog Ent102PLB) and A_prog_listing -> B_prog_listing. The literals a2b
   leaves untranslated (0x7fffff800000, 0x7fff8000, 0x10007fff8000) are ASan constants, the same on both images.
   LISTING: lib/B/Listing_prog.v (a Theorem Labs lane's whole-program listing of B', blob c97cc46b3e13; slot k = byte offset 4k
   from the entry), run through the PAListing PL_102_B of lib/B/Ent102PLB.v (blob e0348e1212c9). Slots 113 .. 177
   (+0x1c4 .. +0x2c4) of the B' listing are word for word the A' slots (65 plain PW words: no call, no pc-relative
   image literal; the two branches `beqz s2,+0x54` / `j +0x44` are function-relative). The image half stays generic
   ({PA : PAImg B_prog_listing}); no PAImg instance is loaded.
   THE KIT TEXTS: none read here.
   rule 24: proves function LLVMFuzzerTestOneInput, segment L6x on B' (reuse search
   a Theorem Labs lane record, the internal file idx-llvm-newpin.txt exit=0; NEW walk; proof-index seg_L6x_B: 0 hits).
   This file: definitions of that segment only.

   WHAT THE LANE'S CODE DOES (listing slots 113 .. 177, the same words as A''s
   a Theorem Labs lane record, the internal file llvmf-A.s):
     +0x1c4 li a0,-8; +0x1c8 .. +0x1e0 sb a0,4..10(s10)          the 7 inner shadow bytes := 0xf8
     +0x1e4 .. +0x1ec lui/addiw a0,0x45e0360e; sd a0,0(s11)       the free magic at [fk]
     +0x1f0 beqz s2,+0x244                                        fk = 0 is NOT taken (ec_own: fk <> 0)
     +0x1f4 .. +0x234 li a0,-11; sb a0,0..15(s10)                 all 16 shadow bytes := 0xf5 (the inline release)
     +0x238 ld a0,0x78(s2); +0x23c sb zero,0(a0)                  the fake frame's flag byte := 0
     +0x240 j +0x284; +0x284 li a0,0                              the return value
     +0x288 addi sp,s0,-0x80; +0x28c .. +0x2bc ld ra,s0..s11      the saved block; +0x2c0 addi sp,sp,0x80; +0x2c4 ret

   ATOMS (the engine's numbering; registers are 0..31, extra atoms from 32, image atoms from A_TEXT = 240):
     8  = sp0 (s0), 18 = fk (s2), 26 = shadow_addr fk (s10), 27 = fk (s11)
     32 = the fake frame's flag address, read at [fk + 120]
     33 = the saved ra, 34 .. 45 = the saved s0, s1, s2 .. s11 (the entry values of x8, x9, x18 .. x27)
   REGIONS: the saved block (read only), the 16 frame shadow bytes (written), the frame header word (written), the
   flag-pointer word at [fk + 120] (read), and the flag byte (written). The flag byte is the inline release of the
   fake frame: the whole lane is ONE run of the flag-store rule (lib/A/Prog/Ent102L6AFlag.v, image-free), whose
   write premise admits the flag byte beside the journal's own bytes, so the flag region is in the entry state.
   NUMERALS: 128 / 120 / 104 / 16 / 8 are LENGTHs of this frame (EC_SAVE, EC_FRAME_BYTES of Ent102CutsB.v and the
   saved-block slots); 452 = 0x1c4 is the lane's slot offset (DERIVED: EC_EXIT - EC_BASE); the atom indices are
   DERIVED from the register map; 2 ^ 46, 2 ^ 47, 4096, 0x7fffff800000, 0x7fff8000 and 0x10007fff8000 are the
   engine's range facts (ASan constants, never an image address). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the lane's first pc, as the listing's slot offset from the entry (EC_EXIT = EC_BASE + 0x1c4) *)
Definition L6_K : Z := 452.

(* the atom numbers of this lane *)
Definition L6_B_FLAG : nat := 32.
Definition L6_B_RA : nat := 33.

(* the saved block, read by the epilogue at sp0 - 8, -16, ..., -104 (base atom 8 = s0 = sp0) *)
Definition l6_saved_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition l6_r_saved : YP09.region := YP09.mkRegion (Some 8%nat) (-128) 0 0 0 l6_saved_chunks.
(* the sixteen shadow bytes of the frame (base atom 26 = s10 = shadow_addr fk), all written *)
Definition l6_r_shadow : YP09.region := YP09.mkRegion (Some 26%nat) 0 16 0 16 [].
(* the frame's header word (base atom 27 = s11 = fk), written with the free magic *)
Definition l6_r_hdr : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [].
(* the flag-pointer word the inline release reads at [fk + 120] (base atom 18 = s2 = fk) *)
Definition l6_r_flagptr : YP09.region :=
  YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
(* the flag byte itself (base atom 32), written with 0 by the inline release *)
Definition l6_r_flag : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition l6_regions : smem := [l6_r_saved; l6_r_shadow; l6_r_hdr; l6_r_flagptr; l6_r_flag].

(* the range facts of the base atoms: the stack window, the frame (32-aligned, in the app band, both registers
   that hold it), its shadow (in the shadow band) and the flag byte (in the app band) *)
Definition l6_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (18%nat, mkAF 4096 0x7fffff800000 5);
           (27%nat, mkAF 4096 0x7fffff800000 5);
           (26%nat, mkAF 0x7fff8000 0x10007fff8000 0);
           (32%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition ss_l6 : sstate := mkSS L6_K sr_atoms l6_regions None l6_facts.
(* no instrumented load is in this lane, so the shadow-entry list is empty; the span the token machinery reserves is
   the one-byte window at 0, off every region of the lane (the lane writes its frame's own shadow bytes, inside the
   ASan shadow band) *)
Definition L6_SH : list shent := [].
Definition L6_Bx : sv := SLit SHADOW_OFF.
Definition L6_Bspan : Z * Z := (0, 0).

(* the extra atoms of this lane at a given entry register file: the flag address, then the thirteen saved values *)
Definition l6_extra (regs0 : bvmap 5 word) (flag : Z) : list word :=
  map (Z_to_bv 64)
    [flag; bv_unsigned (getr regs0 1);
     bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9);
     bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19);
     bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21);
     bv_unsigned (getr regs0 22); bv_unsigned (getr regs0 23);
     bv_unsigned (getr regs0 24); bv_unsigned (getr regs0 25);
     bv_unsigned (getr regs0 26); bv_unsigned (getr regs0 27)].

Section D. Context {rc : YM05.RunCeil} {PA : @PAImg rc B_prog_listing}.
Definition L6_EI (regs0 : bvmap 5 word) (flag : Z) (regs : bvmap 5 word) : env :=
  Eimg (L := B_prog_listing) (PI := PA) (Ereg regs (l6_extra regs0 flag)).
End D.
