(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* The contract of joined on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block and the meter as cgif's trawnew_specX states them
   (lib/YC7x.v:88, :92-101). Functional content: fuzz_command's own released plain contract lib/Prog/joined_c.v:20-79
   (join_need; words_view / words_place; a fresh block of join_need ws + 1 bytes that holds join_sp ws and its
   terminator, and *len = |join_sp ws|) and the model lib/Prog/RecFacts.v (join_sp).
   joined(w, len) (H/fuzz_command.c:152-177) sums strlen(w->w[k]) + 1 over the w->n words with the strlen wrapper
   (`___interceptor_strlen`, reached through the 4-byte jump `__interceptor_trampoline_strlen`), allocates that sum
   plus 1 through the malloc wrapper (0x88c48, the only allocation of the program whose size the input decides),
   writes the words with `__asan_memcpy`, one space between two, and a terminator, stores the length to *len and
   returns the block. The malloc rule returns a block at or above 4096, so the abort edge (`__asan_handle_no_return`,
   then abort, 0x88e3c) on a null result is not taken.
   `struct words` is {text @0, copy @8, w @16, n @24}; it lives in LLVMFuzzerTestOneInput's real stack frame. len
   is in the caller's real stack frame too (check_words passes s1 + 208 at 0x87c24, check_round_trip s1 + 144 at
   0x88550, s1 being each caller's realigned real stack pointer: ASan's stack-safety analysis kept it out of their
   side-stack frames), above joined's own stack pointer, so the footprint names [len, len + 8); as a written
   caller-stack slot it lies below ly_top (awr_byte's caller-stack clause, YCbq.v:502).
   s0 holds the running sum n at the strlen calls and at the malloc wrapper (0x88bd0, 0x88c30, call 0x88c48) and the
   space character 32 in the copy loop (0x88c98); the malloc rule asks chain_pre of s0, and n < MALLOC_MAX lies below
   alloc_ceiling, so achain_low and achain_chain_pre (YCbq.v:269, :327) give it with the empty chain. A's joined
   keeps len in s0 at its malloc call and so has a premise on the stack above len; B's walk reads no word above len,
   so B has neither that premise nor the frame chain from len (pass 5b, this port's decision). The words
   are harness words, pointers into words_of's `copy` block (fuzz_command.c:120) for both callers, so they are
   stated as live blocks; the strlen wrapper's reads come from AR's block facts and each tail word from
   `cmd_heap_tail_vis`.

   Addresses: entry BASE + AF_joined = 0x88b50 (B, the pinned image). 215 instructions, frame 128 bytes, 2 loops
   (0x88bf0, 0x88c9c), no side-stack frame, 13 inline checks: load4 on w->n (0x88bac, 0x88c68, 0x88d60), load8 on
   w->w (0x88bc8, 0x88c9c, 0x88d10) and on w->w[k] (0x88c14, 0x88cd4, 0x88d48), store1 on the block (0x88c5c,
   0x88cfc, 0x88db4) and store8 on *len (0x88dd8), each a read of the shadow byte at (a >> 3) + SHADOW_OFF through
   the shadow base word (0xa5f50, a RELRO word arodata_okP keeps). The error path (a call of `__asan_report_*`) is
   not reached: the struct and len lie in the stack window, whose shadow AR's zshadow_ok keeps usable at every
   state (YG0n.v:188), the word array is in a live block, and every store to the block lands below
   join_need ws + 1.

   UBSan (B only, 17 trap sites, all branches to the `unimp` at 0x88e24; the second `unimp`, 0x88e44, follows
   `jal abort` and no branch reaches it). The 17 are four checks of `w->w`, repeated at fuzz_command.c:159, 167
   and 171, the alignment of `w`, three wraps of s + n and the alignment of `len`: 0x88b90 is `w` not 8-aligned (:158); 0x88bf0, 0x88cb8, 0x88d2c are the unsigned wrap of
   w->w + 8k; 0x88bfc, 0x88cb4, 0x88d28 the pointer-overflow pair (the result null while w->w is not); 0x88c00,
   0x88cbc, 0x88d30 are `w->w` null; 0x88c08, 0x88cc8, 0x88d3c are `w->w + 8k` not 8-aligned; 0x88cec, 0x88d0c,
   0x88d98 are the wrap of s + n at :170, :171 and :174; 0x88dc8 is `len` not 8-aligned (:175).
   Two premises are added over the A statement for them, both held by the two callers (each passes
   LLVMFuzzerTestOneInput's `struct words` and its malloc'd word array): `W0 mod 8 = 0` (0x88b90) and
   `arr mod 8 = 0` (0x88c08, 0x88cc8, 0x88d3c). The null and wrap checks of w->w need none: `in_blockA` with AR's
   block law (in_app: 4096 <= p, p + req_size n <= ASAN_CEIL, lib/Reusable/YG0d.v:431-437) gives 0 < arr and
   arr + 8k < 2 ^ 64, and the same law for the fresh block gives s + n < 2 ^ 64 for n <= join_need ws. The
   alignment of `len` is A's `outp mod 8 = 0` (0x88dc8). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PJoin := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 128-byte frame, and the window the malloc wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; amalloc04_rule asks ASTACK - o <= STK, lib/YC5d.v:62). The strlen wrapper's window and
   __asan_memcpy's (ESTACK each, the runtime contracts' final windows) are smaller. *)
Definition JOINED_STK : Z := 128 + ASTACK.
(* one allocator event: the malloc *)
Definition EV_JOINED : Z := 1.
(* the live bytes the call adds: at most one malloc's worth (MALLOC_MAX, cgif lib/YG00.v:38) *)
Definition LIVE_JOINED : Z := MALLOC_MAX.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one malloc of join_need ws + 1 bytes *)
Definition XM_JOINED (ws : list (list byte)) : Z := mo_malloc MT (PJoin.join_need ws + 1).
(* the runtime entries the call reaches *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Definition tjoined_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (W0 arr outp : Z) (wp : list Z) (ws : list (list byte)),
afn_pre SEGS B JOINED_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 W0 -> getr regs 11 = w64 outp ->
(* the struct words, on the caller's real stack above this call's window, read only: n at +24, w at +16 (plain
   words_view, joined_c.v:41-44, and :58). It is 8-aligned: UBSan checks that at 0x88b90 *)
spZ regs <= W0 + 16 -> W0 + 32 <= ly_stk_hi ly -> W0 mod 8 = 0 ->
length wp = length ws -> Z.of_nat (length ws) < 2 ^ 31 ->
aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)) ->
aval_mem (rdW W mem) (W0 + 16) 8 arr -> 0 <= arr < 2 ^ 64 ->
(* the word array in a live block, each word a string in a live block (plain words_view / words_place,
   joined_c.v:36-46); the array is 8-aligned (words_of's malloc of cap pointers of 8 bytes, fuzz_command.c:118),
   which UBSan checks at 0x88c08, 0x88cc8 and 0x88d3c *)
arr mod 8 = 0 ->
in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws)) ->
(forall k, (k < length ws)%nat ->
 aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
 astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) ->
(* the size fits one malloc (plain :59; amalloc04_rule asks n < MALLOC_MAX, lib/YC5d.v:61) *)
PJoin.join_need ws + 1 < MALLOC_MAX ->
(* len: 8 aligned bytes of the caller's real stack that the call writes, inside the stack window below ly_top,
   apart from the struct's fields (plain :60-62). The alignment is UBSan's check at 0x88dc8 *)
spZ regs <= outp -> outp + 8 <= ly_top ly -> outp mod 8 = 0 ->
(outp + 8 <= W0 + 16 \/ W0 + 32 <= outp) ->
(* len's 8 bytes are present (the store at 0x88de0 asks writable_at). No premise on the stack above len: s0 at the
   malloc call 0x88c48 is the running length (0x88c30 addi s0,a0,1), not len, so the malloc rule's chain_pre of s0
   is achain's empty case and the walk reads no word above len. A keeps a premise there (the presence of
   [len - 16, ly_top), pass 5b) because A's joined has s0 = len at its malloc call; B
   drops the frame chain from len that both sides had before (pass 5b, this port's decision) *)
(forall i, 0 <= i < 8 -> apresent (w_H W) mem (outp + i)) ->
st_nev S + EV_JOINED <= EV_MAX -> blocks_bytes S + LIVE_JOINED <= LIVE_MAX ->
mo_ok MT S (XM_JOINED ws) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_joined) regs mem md)
(apost_base SEGS B JOINED_STK [(outp, outp + 8)] regs ly S W mem md EV_JOINED
(fun ly' S' W' regs' mem' md' => exists res : Z,
 getr regs' 10 = w64 res /\ 4096 <= res < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (plain joined_c.v:70-71) *)
 Permutation (ablocks B ly' S') ((res, PJoin.join_need ws + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart res (PJoin.join_need ws + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* it holds the words joined by one space and a terminator, in a live block (the form send_message asks of its
    message); *len holds that length (plain :72-73) *)
 in_blockA (ablocks B ly' S') res (PJoin.join_need ws + 1) /\
 abytes_atR (rdW W' mem') res (join_sp ws ++ [Z_to_bv 8 0]) /\
 aval_mem (rdW W' mem') outp 8 (Z.of_nat (length (join_sp ws))) /\
 (* the blocks that were live are kept (plain :74) *)
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_JOINED /\
 mo_le MT S S' (XM_JOINED ws))).
End e.
End f.
End d.
