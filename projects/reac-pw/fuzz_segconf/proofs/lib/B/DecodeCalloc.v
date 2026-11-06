(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeCalloc.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* libreac/fuzz_decode's ASan calloc runtime contract: the unit-generic kit of lib/Reusable/YGCalloc.v at the
   addresses measured in this unit's two ASan images.  fuzz_decode is the only unit of the 14 whose ASYMS has
   as_calloc = Some 0x51f68: check_round_trip calls calloc, so its TFIB_T walk needs this contract where
   cgif_file_fuzzer's needs only malloc and free.

   Addresses (ORIGINAL binaries, FACTS f0e6eb38667, read with capstone from
   fuzz_decode.{asan,asan-ubsan};
   the twins' loaded PROGBITS equal the published, stripped pins of harness.yaml):

   |                                   | image A (.asan) | image B (.asan-ubsan) |
   |---|---|---|
   | __wrap_calloc / __interceptor_trampoline_calloc (4 bytes, `j`) | 0x51f68 | 0x51fb4 |
   | ___interceptor_calloc (368 bytes, 92 insns)                    | 0x52364 | 0x523b0 |
   | __asan::asan_calloc (224 bytes, 56 insns)                      | 0x31bd4 | 0x31c20 |
   | __asan::Allocator::Allocate (the callee calloc shares with malloc) | 0x3124c | 0x31298 |
   | pc the allocation's stack trace records (ra of GetCurrentPc, interceptor + 0xd4) | 0x52438 | 0x52484 |
   | __sanitizer::allocator_may_return_null (1 byte, .bss)          | 0x123021 | 0x1235a1 |
   | __sanitizer::allocator_out_of_memory (1 byte, .bss; the Allocate statement's oomb) | 0x123020 | 0x1235a0 |
   | __asan::instance (3632 bytes, a0 of Allocate)                  | 0x9d758 | 0x9dcd8 |
   | loaded image (PT_LOAD) lo .. end                               | 0x10000 .. 0x5f5638 | 0x10000 .. 0x5f5bb8 |

   Image B's calloc chain is image A's, moved by +0x4c: the trampoline, the interceptor and the entry have the
   same sizes and the same bytes word for word except three lo12 immediates that name data, which the two images
   place differently (A 0x5243c the flags pointer load, A 0x31c08 the `addi` that forms &instance, A 0x31c44 the
   `real_memset` GOT load; B's are at +0x4c).  The two tables above were read out of each binary separately.

   The contract is stated here over an [asyms] record [B] of the image, as the unit's TFIB_T walk will take it:
   the kit's predicates are the allocator model's (lib/Reusable/YG0d.v), the image's segments are
   lib/A/DecodeTFIB.v's [decodesegs0] / [decodesegsB0], and the Allocate contract the walk consumes is c-asan's
   M1 (lib/Reusable/YGAlloc.v, the by-path copy of AllocG.v) at this image's Allocate pc, allocator instance and
   out-of-memory byte, with the call site's a2 = 8, a4 = 1 and a5 = 0.  The call
   rule is instantiated at this unit's own walk layer: YCbq.v:349 ajournal and YCbq.v:823 acall_kept, with the
   meter YC5d.v:17-20 ameter_ops left as the parameter [MT] that cgif's own rule carries (cgif instantiates it at
   ameter_triv, YCbp.v:17).

   THE CALL SITE.  The whole image calls the trampoline 0x51f68 once: check_round_trip (0x80bc8) at 0x80c4c
   `jal 0x51f68`, with
     a1 (sz) = 1       : 0x80c48 `addi a1, zero, 1`, a constant;
     a0 (nm) = s4      : 0x80c3c `mv a0, s4`, where 0x80c18 `mul s7, a3, a2`, 0x80c1c `slli s4, s7, 1`,
                         0x80c20 `add s4, s4, s7`, so nm = 3 * (a3 * a2); or nm = 1 when s7 = 0
                         (0x80c40 `bnez s7, 0x80c48`, 0x80c44 `addi a0, zero, 1`).
   (The two calls just before it, 0x80c28 and 0x80c34, go to the malloc trampoline 0x51f64.)  In image B the one
   call site is 0x80de4, inside check_round_trip 0x80d54.

   The seven runtime addresses of the table above were checked pair by pair with c-asan's port_addr_check.py
   (A against B): 8 SAME-SYMBOL, and one DIFFERENT-SYMBOL on the call site
   alone (check_round_trip + 0x84 against + 0x90), which is the harness-code difference just named, not a port
   error.

   NO OVERFLOW ARM FOR THIS UNIT.  The kit's [acalloc_overflow_realizesP] returns NULL with errno = ENOMEM only
   under the premise that the runtime's allocator_may_return_null byte is not zero at the call
   (A 0x5df50 `auipc` + 0x5df54 `lb a0, 0xd1(a0)` + 0x5df58 `snez a0, a0`, the byte 0x123021).  That byte is
   .bss: it is 0 in the image and start-up writes it from the harness's __asan_default_options (A 0x7fbb8
   returns the string at 0x1dcdf, "allocator_may_return_null=1"), so its value at the call is a START-UP fact,
   which this unit's start-up certificate does not yet carry.  It is therefore NOT provably 1 here, and this file
   instantiates no overflow arm: it does not need one, because the single call site above passes the constant
   sz = 1, so nm * sz = nm < 2 ^ 64 refutes the arm's premise outright.  The same holds for Allocate's
   allocation-size-too-big path (inside Allocate, A 0x31458 `slli a0, a1, 0x28` = 2 ^ 40, A 0x31460 / 0x31464,
   A 0x31470): nm = 3 * a3 * a2 is bounded by the program's constants, far below both 2 ^ 28 (the in-range arm's
   room premise) and 2 ^ 40.

   HOW THE WALK DISCHARGES REFUSAL.  As cgif discharges malloc's (A/AD1n.v:24-34 tfib_malloc_site): the room
   premises 0 <= n < MALLOC_MAX and blocks_bytes S + n <= LIVE_MAX at n = nm * sz = 3 * a3 * a2 feed
   YG0d.v:526-527 ml_malloc_ns (fst r = PNull -> ns = false), whose ns is forced true by the granted flag of
   YG0d.v:184 amreal_SRr04 (YG0d.v:173 last_flag_true, :175 atok_apath_flag); a kernel answer of 0 ends the path
   as a refusal, not as a NULL return.  [decode_acalloc04_A] is that in call-rule form, with 4096 <= res. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtLCallocR.
Import ListNotations.
Open Scope Z_scope.

(* The ASan images' own sink heads: musl's open-file list head `ofl_head` (8 bytes, .bss), by symbol in the
   ORIGINAL unstripped twins - fuzz_decode.asan 0x5f4450, fuzz_decode.asan-ubsan 0x5f49d0 (the plain build's is
   0x4eb00).  The type is written by its full path: this unit carries two modules named YI16 (lib/Reusable,
   which YCbq.v uses, and lib/U/Reusable), and the short name resolves to the ubsan one in lib/A. *)
Definition DEC_A_ofl_head : Z := 0x5ffef0.
Definition dec_A_sink_head : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI16.sink_head :=
{| OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI16.sk_ofl_head := DEC_A_ofl_head |}.

(* Image A (fuzz_decode.asan). *)
Definition DEC_A_wrap_calloc : Z := 0x56cc4.
Definition DEC_A_icpt_calloc : Z := 0x570c0.
Definition DEC_A_asan_calloc : Z := 0x33b2c.
Definition DEC_A_allocate : Z := 0x331a4.
Definition DEC_A_calloc_ra0 : Z := 0x57194.
Definition DEC_A_amrn : Z := 0x12ea21.
Definition DEC_A_oom : Z := 0x12ea20.
Definition DEC_A_instance : Z := 0xa9158.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section a.
Variable B : asyms.

(* The ASan image: the Allocate contract this walk consumes, the in-range calloc contract, the thin caller walk
   from the one to the other, and the call rule a program walk uses at the calloc site. *)
Definition decode_aalloc_A : Prop :=
RtLCallocR.aseg_aalloc_calloc tfibsegs B DEC_A_instance DEC_A_oom DEC_A_allocate.
Definition decode_acalloc_A : Prop :=
RtLCallocR.aseg_acalloc_realizes tfibsegs B DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH.
Definition decode_acalloc_of_allocate_A : Prop :=
RtLCallocR.aseg_acalloc_of_allocate tfibsegs B DEC_A_instance DEC_A_oom
DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_A_allocate DEC_CALLOC_MAX DEC_CALLOC_DEPTH.
End a.
End d.
