(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the trace premise is the one the trace-store change of this port gives, In tr U or room charged to the event count. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the two allocating string entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (strdup, strndup), in the form cgif_file_fuzzer's lib/YG0d.v:243-260 states amalloc_realizes and its leaf, with the copied bytes added to the leaf. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtAlloc.v for fuzz_command.asan-ubsan: module paths and that image's addresses (the runtime entries and their bodies, the UnwindFast stop sites, and the program's call sites of strdup and strndup). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/B/Rt/RtAlloc.v (donor image sha256 bbe55d24d096), with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require StrFun.
Import ListNotations.
Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.StrFun.

(* The entries, on the pinned image: strdup 0x45228 -> 0x4ccfc, strndup 0x45184 -> 0x4575c. Both take a stack
   trace of their own call site and allocate with asan_malloc, so their contract is cgif_file_fuzzer's malloc
   contract (lib/YG0d.v:253-260) with the copied bytes added, not an interceptor contract: the model step is the
   same [malloc n tr S], and the state of the allocator changes.

   [pc_ra0] is the program counter the entry gives the unwinder for the allocation (GetCurrentPc inside the entry),
   as [pc_malloc_ra0] is for a direct call of malloc. The instance pins it from the image.

   strdup has no real_strdup slot: it calls internal_strlen, asan_malloc and real_memcpy (GOT 0xa5f78 -> 0xa7e08).
   strndup reads at most n bytes of its argument (internal_strnlen 0x69dc0, a byte loop bounded by n) and copies
   them with __sanitizer_internal_memcpy 0x6998c, also a byte loop; strdup reads with internal_strlen 0x69b5c, a
   byte loop, and copies with musl's memcpy, which reads nothing outside the bytes it copies. So neither entry
   reads past the terminator, and neither contract carries the tail-word premise the string entries carry. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.

(* cgif_file_fuzzer lib/YG0d.v:243-252, with the bytes of the copy added. *)
Definition adup_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (out : list byte)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post segs B ASTACK ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r <> PNull -> abytes_at segs W' mem' (sptr_addr B ly' (fst r)) out).
(* Where the source string may live. Both entries read their source AFTER the allocation (strdup copies at 0x4ce84,
   after asan_malloc at 0x4ce0c; strndup checks and copies at 0x457cc-0x459b0, after the malloc body at 0x457b8),
   and the malloc post keeps a byte only where the allocator does not own it before and after. So the source must
   be in a place the allocator never takes: the image's bytes outside the runtime's owned statics, the real stack,
   or a live block. These are the three cases the journal of a program walk carries across a call
   (lib/Reusable/YCbq.v al_owned_image, al_stack, al_blocks), so a caller discharges the premise as the 04 malloc
   rule does. fuzz_command's two strdup calls pass a live block (verbs_receive 0x8d078, the trimmed line) and an
   image static (check_round_trip 0x88528, g_rec.reply). *)
Definition adup_src_kept (ly : alayout) (S : astate) (a : Z) : Prop :=
~ aerrno_cell B a /\
((in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B)) \/ ly_stk_lo ly <= a < ly_stk_hi ly \/
 (exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m)).

Definition astrdup_realizes (pc pc_ra0 : Z) : Prop :=
forall ly S W regs mem md x s ch,
acall_pre segs B ly S W regs mem md ch ->
getr regs 10 = w64 x -> 0 < x ->
astr_at segs W mem x s ->
aread_ok segs ASTACK W regs mem x (astr_len s + 1) ->
(forall a, x <= a < x + (astr_len s + 1) -> adup_src_kept ly S a) ->
rt_rom_view segs B W mem ->
astr_len s + 1 < MALLOC_MAX -> blocks_bytes S + (astr_len s + 1) <= LIVE_MAX ->
(In (call_trace ly pc_ra0 regs ch) (as_universe B) \/ st_nev S < EV_MAX) ->
amreal segs (malloc (astr_len s + 1) (call_trace ly pc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(adup_leaf ly S W regs mem md (astr_len s + 1) (s ++ [Z_to_bv 8 0])).

(* strndup(x, n): the argument is a buffer of n bytes, which need not hold a terminator. fuzz_command calls it on
   the fuzz input itself (verbs_receive, L/src/verbs.c:219, call at 0x8cfbc), on a block of exactly n bytes. The
   length the entry copies is therefore the one the plain proof of the same binary names, strnlen_res n buf
   (lib/Spec/StrFun.v:103), and the readable range is the prefix up to the terminator or n, whichever comes first.
   memchr_ok (:95) is the plain proof's premise that the search of the terminator stays inside the buffer. *)
(* The trace strndup records: the entry allocates by calling the malloc interceptor's body (0x457b8 calls 0x58ba4),
   whose frame pointer, the first bp of UnwindFast, is the entry's sp less strndup's frame of 2,160 bytes. The unwinder
   records only [pc_ra0] when that bp is at or below the stack bottom (0x78f80) or at or above the stack top less 16
   (0x78f88) or when the first return address is below a page (0x78fa4); otherwise the malloc entry's return address
   [mid], then the caller's chain under the same stop rules as call_trace. pc_ra0 = 0x58c6c, mid = 0x457bc. bp is
   always 8-aligned (sp mod 16 = 0, 2,160 mod 16 = 0), so the alignment stop (0x78f90) never fires. *)
Definition STRNDUP_FRAME : Z := 2160.
Definition adup_trace (ly : alayout) (pc0 mid : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
if (spZ regs - STRNDUP_FRAME <=? ly_bot ly) || (ly_top ly - 16 <=? spZ regs - STRNDUP_FRAME) || (mid <? 4096)
then [pc0]
else if frame0_ok ly regs
then unwind_of_chain pc0 ((0, mid, 0) :: (spZ regs, raZ regs, s0Z regs) :: ch)
else unwind_of_chain pc0 [(0, mid, 0)].

Definition astrndup_realizes (pc pc_ra0 mid : Z) : Prop :=
forall ly S W regs mem md x n buf ch,
let k := PStrFun.strnlen_res n buf in
acall_pre segs B ly S W regs mem md ch ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x ->
abytes_at segs W mem x buf ->
PStrFun.memchr_ok x 0 n buf ->
aread_ok segs ASTACK W regs mem x (Z.min (k + 1) (Z.of_nat (length buf))) ->
(* strndup also reads the SHADOW of its source after the allocation, which the malloc post keeps for a live
   block; its only caller passes the fuzz-input block (verbs_receive 0x8cfbc), so the source is a live block. *)
(exists p m, In (p, m) (ablocks B ly S) /\ p <= x /\ x + Z.min (k + 1) (Z.of_nat (length buf)) <= p + req_size m) ->
~ (exists a, x <= a < x + Z.min (k + 1) (Z.of_nat (length buf)) /\ aerrno_cell B a) ->
rt_rom_view segs B W mem ->
k + 1 < MALLOC_MAX -> blocks_bytes S + (k + 1) <= LIVE_MAX ->
(In (adup_trace ly pc_ra0 mid regs ch) (as_universe B) \/ st_nev S < EV_MAX) ->
amreal segs (malloc (k + 1) (adup_trace ly pc_ra0 mid regs ch) S) W
(cfg_at segs pc regs mem md)
(adup_leaf ly S W regs mem md (k + 1) (firstn (Z.to_nat k) buf ++ [Z_to_bv 8 0])).

End c.
End b.
