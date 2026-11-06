(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 36 of its 64 lines of code are new or changed and 124 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/check_words_pin_set_c.v; 24 of its 48 lines of code are new or changed and 40 lines of the source are left out. *)
(* The contract of xmalloc on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the meter
   as there (:88, :92). It is the allocation part of the A side's xstrdup contract (lib/A/Prog/xstrdup_c.v: the
   fresh block, apart from every live block, in block form, the meter and the live bytes), for the size the caller
   asks. A has no xmalloc of its own (it is inlined into xstrdup there); B keeps it as a function, called by
   rec_canonical, rec_calls_copy (the inlined xstrdup), sup_resp, arg_s, hand_back, sup_host_setting, sup_chain and
   socket_send.
   The function (H/recorder.c:87-95) asks the malloc wrapper (reached through the 4-byte jump
   `__interceptor_trampoline_malloc`) for n bytes, or 1 byte for n = 0 (`seqz a1,a0; add a0,a0,a1`, unsigned, no
   UBSan check). The malloc rule (amalloc04_rule, lib/Reusable/YC5d.v:58-75) returns a block at or above 4096, so
   the abort edge on a null result (`__asan_handle_no_return`, then abort) is not taken. It reads and writes no
   memory outside its own frame (ra at sp + 8) and has no inline check. It does not touch s0, so s0 at the malloc
   call is the caller's: the malloc wrapper's chain_pre comes from afn_pre's frame chain for s0 by achain_chain_pre
   (YCbq.v:327; the call's stack pointer is 16 below the entry's); no presence of the stack up to ly_top is
   assumed.

   Addresses: entry BASE + AF_xmalloc = 0x899b4 (B, the pinned image). 12 instructions, frame 16 bytes, no side-stack
   frame, 0 inline checks, no loop; callees: the malloc wrapper (0x589d0), and on the null path, not taken,
   `__asan_handle_no_return` (0x5f790) and abort (0x94ba8). UBSan: 0 trap sites; the one `unimp` (0x899e0) follows
   `jal abort` and is not reached. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 16-byte frame, and the window the malloc wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; amalloc04_rule asks ASTACK - o <= STK with o = -16, lib/YC5d.v:62) *)
Definition XMALLOC_STK : Z := 16 + ASTACK.
(* one allocator event: the malloc *)
Definition EV_XMALLOC : Z := 1.
(* the bytes of the block: malloc(n ? n : 1) (recorder.c:89) *)
Definition LIVE_XMALLOC (n : Z) : Z := Z.max n 1.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the meter the call spends: one malloc of n ? n : 1 bytes *)
Definition XM_XMALLOC (n : Z) : Z := mo_malloc MT (LIVE_XMALLOC n).
(* the runtime entry the call reaches, with cgif's name *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Definition txmalloc_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (n : Z),
afn_pre SEGS B XMALLOC_STK ly S W regs mem md ch ->
getr regs 10 = w64 n ->
(* the size the malloc rule admits (0 <= (n ? n : 1) < MALLOC_MAX, YC5d.v:61) *)
0 <= n < MALLOC_MAX ->
st_nev S + EV_XMALLOC <= EV_MAX -> blocks_bytes S + LIVE_XMALLOC n <= LIVE_MAX ->
mo_ok MT S (XM_XMALLOC n) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_xmalloc) regs mem md)
(apost_base SEGS B XMALLOC_STK [] regs ly S W mem md EV_XMALLOC
(fun ly' S' W' regs' mem' md' => exists p : Z,
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (cgif trawnew_specX, lib/YC7x.v:93-101) *)
 Permutation (ablocks B ly' S') ((p, LIVE_XMALLOC n) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart p (LIVE_XMALLOC n) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* in the block form its callers' callees ask *)
 in_blockA (ablocks B ly' S') p (LIVE_XMALLOC n) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_XMALLOC n /\
 mo_le MT S S' (XM_XMALLOC n))).
End e.
End f.
End d.
