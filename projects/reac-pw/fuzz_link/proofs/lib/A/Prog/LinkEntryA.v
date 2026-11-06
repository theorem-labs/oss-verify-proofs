(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: split out of lib/A/Prog/PcapEntry.v (a Theorem Labs lane lib/B closure rule), so that the generic entry contract there names no image: this file holds lib/A's image data, measured on the original v1.9.0 asan pin (internal path, sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin; capstone disassembly), and the lib/A instance of the contract. Relocated constants: A_LLVMF = 0x807c8 (the symbol LLVMFuzzerTestOneInput); RA_LLVMF = 0x80634 (target_run's `jal 0x807c8` at 0x80630); A_EMPTY = 0x5d3f20 (the object oft_aligned_copy.empty: target_run 0x8059c `auipc a1,0x554` and 0x805a0 `addi s4,a1,-0x68c` give 0x5d3f10, 0x80614 `addi s1,s4,0x10` gives 0x5d3f20, which 0x80628 `mv a0,s1` passes when the payload is empty); LLVMF_STK = 32768 (a COMPOSITION bound over the frozen callee constants, not a whole-reach figure: the composed need is 19200 bytes = the function's own frame 224 (`addi sp,sp,-0xe0` 0x807c8) + 16 of realignment (`andi sp,sp,-0x20` 0x80808) + 128 if the side stack gives no frame (0x80850-0x80868), then pcap_source_open's 96 + 16 (0x8145c, 0x81494) + 96 (0x814dc-0x814f4) and the fmemopen wrapper's AFMEMOPEN_STK 18624 (lib/A/Stdio/PFmemopenISpec.v), which libreac_fuzz_fopen reaches by a tail jump after it pops its 32 bytes (0x807a8, 0x807ac); every other window composes smaller: the allocator rules' ASTACK 16384 below the call (YC5d.v:60, 16752 from sp0), fclose's PFCLOSE_STK 16528 under pcap_source_open (0x81674, 0x816b8) or pcap_source_close (0x81ec8), fread's AFREAD_STK 8192, the bcmp wrapper's 2 * ESTACK. So LLVMF_STK MOVES if those callee constants move (AFMEMOPEN_STK, PFCLOSE_STK, AFREAD_STK, ESTACK, ASTACK, or the open / close / next windows their own statements fix): it must stay >= 600 + the largest callee window + that callee's own frames. The slack (13568 bytes over 19200) is there because the bound composes constants, each a bound over its callee's reach, and the open / next / close statements that fix their own windows are not final; 32768 = 2^15 is also the value the relocated driver discharges. The caller's astk_ok LLVMF_STK, with ly_bot = ly_top - kStackSpan, kStackSpan = 2^23 (YG0f.v:36, :63) and ASTACK = 16384 (YG0d.v:18), asks ly_top - sp0 < 2^23 - 16384); G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)] (the comment at its Definition). The donor text is cgif's lib/A/ACfn.v (origin/ossv/recipes c8557374ad2e), as PcapEntry.v's header says. *)
(* lib/A's image data for LLVMFuzzerTestOneInput's entry contract (LinkEntry.v) and its instance, measured on
   fuzz_link.asan (the PUBLISHED pin, sha256 059dae63e07c...; symbols from its unstripped twin sha256 66cd0f159895...,
   whose .text / .rodata / .data are byte-identical at the same addresses; target_run listing
   (internal path) (internal record, sha256 fd94c6a37bf3), LLVMFuzzerTestOneInput
   listing (internal path) (internal record, sha256 e84d6f0c6974)):
   - A_LLVMF = 0x827d4: the symbol LLVMFuzzerTestOneInput (size 5468; link_aaddr.v LA_LLVMFuzzerTestOneInput).
   - RA_LLVMF = 0x820c8: target_run 0x820c4 `jal 0x827d4`, inside its call loop 0x820b4 .. 0x820e8.
   - A_EMPTY = 0x5dcaa0: the object oft_aligned_copy.empty (32 bytes): target_run 0x82030 `auipc a1,0x55b`,
     0x82034 `addi s4,a1,-0x5a0` give 0x5dca90 (target_run.initialized); on an empty input (0x82054 `beqz s0`)
     0x820a8 `addi s1,s4,0x10` gives 0x5dcaa0, which 0x820bc `mv a0,s1` passes with 0x820c0 `mv a1,s0` (= 0).
   - LLVMF_STK = 32768: the stack bound of the call (a bound, not a measured count): LLVMFuzzerTestOneInput's frame
     is 0x1a0 = 416 bytes (0x827d4 `addi sp,sp,-0x1a0`) plus up to 16 bytes of realignment (0x82814
     `andi sp,sp,-0x20`), below which the deepest callee window is mark_quietly's 24608 (mark_quietly_c.v
     MARK_QUIETLY_AK; the entry comparer's recomputation); 416 + 16 + 24608 = 25040 <= 32768. The class-4 frame (0x82840
     `addi a0,zero,0x380`, frame_alloc_4 at 0x82844) is on the side stack, not in this window; the real-stack
     fallback arm (0x8285c .. 0x82874) is refuted under the side-stack room.
   - G_HARNESS: the objects one call may change outside its window and its blocks, without their ASan redzones
     (the ruling of link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 item 2): g_nl (271992),
     g_names (512), msg_build.long_alias (301), g_sink (8), g_said (4096), g_say (8) and ofl_head (8), at link_aaddr.v's
     addresses. It is link_aaddr.v's LA_G without its first object, __stderr_FILE + 136 (4 bytes, the orientation word),
     so image A's G differs from the plain frame_G (lib/FrameAPI.v, lib/Prog/LLVMFuzzerTestOneInput_c.v llvm_G) by that
     one word (ruling of 2026-10-30 16:43Z, option (a)): link's harness never takes say()'s stderr arm: reac_served_mark
     loads the stderr pointer only where g_say holds 0 (0x89858, 0x89a94, 0x89adc, 0x89b48), and under amf_gi g_say is 0
     only with g_sink 0, when mark_quietly calls reac_served_say_to (0x8841c, the image's only caller of the only store
     to g_say, 0x89508) with fmemopen's non-zero result before the mark; the runtime and libc code below the call's
     callees stores into __stderr_FILE only on paths gated by runtime state (pthread_create's lock init 0x9bfe4,
     libunwind's error print, __assert_fail), and the walk applies those callees by contracts whose posts keep every
     image byte outside as_owned_static and errno, which __stderr_FILE [0xa5fa0, 0xa6088) meets in no range of
     Tfib_owned_static; the post's journal states the word unchanged, so the walk proves it (measured on link.asan,
     with controls: link-a/slot/stderr-scan/RESULT.md (internal record, sha256 7bc6c60cd0d5) sections 1, 5, 6, 8). And
     the ASan driver keeps stderr's FILE across the call (lib/A/AD1y.v DRV_IVS (0xa5f58, 0xa62a0) holds __stderr_FILE =
     0xa5fa0 .. 0xa6088), which a G holding that word would forbid.
   - LA_NUL = msg_build.long_alias + 300 (link_aaddr.v LA_LONG_ALIAS = 0x62fd40; char[301]).
   The read-only window is PcapRelro.v's PCAP_RLO / PCAP_RHI (link's measured relro); the memory FILE's record is
   the lib/A frame's link_amf (AMemFile.v, read from link's asan code by link_amf_code_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YG0f YG0n YI16 YC5d YM05 YImgTop PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m AD1y AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr LinkEntry.
Import ListNotations.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := 0x827d4.
Definition RA_LLVMF : Z := 0x820c8.
Definition A_EMPTY : Z := 0x5dcaa0.
Definition LLVMF_STK : Z := 32768.
Definition G_HARNESS : list (Z * Z) :=
  [(LA_G_NL, 271992); (LA_G_NAMES, 512); (LA_LONG_ALIAS, 301);
   (LA_G_SINK, 8); (LA_G_SAID, 4096); (LA_G_SAY, 8); (LA_OFL_HEAD, 8)].
Lemma G_HARNESS_of_LA_G : LA_G = (LA_STDERR_FILE + 136, 4) :: G_HARNESS. Proof. reflexivity. Qed.
Lemma G_HARNESS_sorted : la_sorted G_HARNESS = true. Proof. vm_compute. reflexivity. Qed.
Definition LA_NUL : Z := LA_LONG_ALIAS + 300.
Lemma A_LLVMF_is_entry : A_LLVMF = LA_LLVMFuzzerTestOneInput. Proof. reflexivity. Qed.
(* The harness globals are image bytes outside the runtime's statics (W_journalG.v gx_ok, the premise of the
   journal's run rules), for every B with link's statics (AF0m.v Tfib_owned_static; link's PcapB has them,
   lib/A/AD2l.v): each object lies in the image hull [0x10000, IMG_TOP) (AD1y.v in_img_hull), and no range of
   Tfib_owned_static meets an object (checked by computation over the eight objects). *)
Definition g_avoids (lo n : Z) (r : Z * Z) : bool := (lo + n <=? fst r) || (fst r + snd r <=? lo).
Lemma G_HARNESS_avoids_owned :
  forallb (fun g => forallb (g_avoids (fst g) (snd g)) Tfib_owned_static) G_HARNESS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma G_HARNESS_in_hull : forallb (fun g => (0x10000 <=? fst g) && (fst g + snd g <=? IMG_TOP)) G_HARNESS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma G_HARNESS_gx_ok : forall B : asyms, as_owned_static B = Tfib_owned_static -> gx_ok tfibsegs B G_HARNESS.
Proof.
intros B HO a Ha. unfold inG in Ha. apply Exists_exists in Ha as (g & Hg & Hz). unfold in_zr in Hz.
split.
- apply in_img_hull. pose proof (proj1 (forallb_forall _ _) G_HARNESS_in_hull g Hg) as X.
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. unfold pcap_img_end. lia.
- rewrite HO. intros Ho. apply Exists_exists in Ho as (r & Hr & Hzr). unfold in_zr in Hzr.
  pose proof (proj1 (forallb_forall _ _) G_HARNESS_avoids_owned g Hg) as X.
  pose proof (proj1 (forallb_forall _ _) X r Hr) as Y. unfold g_avoids in Y.
  apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia.
Qed.
(* lib/A's instance: link's ASan segments, read-only window, the addresses and stack bound above, the harness
   globals, the memory FILE record link_amf and long_alias's NUL. *)
Definition tfib_lib_contract_xf_all_A {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) : Prop :=
@tfib_lib_contract_xf_all rc SK tfibsegs PCAP_RLO PCAP_RHI
A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS B MT XM_LIB XN_LIB link_amf LA_NUL.
(* GUARD (pcap PcapEntryA.v:30-32): SK is passed by position. *)
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_contract_xf_all_A (rc:=rc) SK).
