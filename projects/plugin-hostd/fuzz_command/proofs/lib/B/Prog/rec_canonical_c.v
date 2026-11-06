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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/check_words_pin_set_c.v, with its module paths and module names changed; 25 of its 54 lines of code are new or changed and 35 lines of the source are left out. *)
(* The contract of rec_canonical on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the meter
   as there (:88, :92). Functional content: fuzz_command's own released plain contract lib/Prog/rec_canonical_c.v:24-52
   and its model lib/Prog/RecFacts.v (canon = join_sp (words T): the words of the line, joined by one space).
   rec_canonical(text, len) (H/recorder.c:104-122) allocates len + 1 bytes with xmalloc (a program call here, 0x89814;
   A has xmalloc inlined), then copies the words of text[0..len) into the block, one space between two words, and a
   terminator. xmalloc's contract (lib/B/Prog/xmalloc_c.v) is a Section hypothesis, not restated; it returns a block
   at or above 4096, so no null result reaches this code.

   Addresses: entry BASE + AF_rec_canonical = 0x897e8 (B, the pinned image). 115 instructions, frame 32 bytes,
   3 loops (0x8983c, 0x8984c, 0x898d0), no side-stack frame, 5 inline checks: load1 on text[i] (0x8986c, 0x898e0)
   and store1 on out[o] (0x898b4, 0x89904, 0x89964), each a read of the shadow byte at (a >> 3) + SHADOW_OFF through
   the shadow base word (0xa5f50, a RELRO word arodata_okP keeps). The error path (a call of `__asan_report_load1` /
   `__asan_report_store1`, 0x8994c, 0x89998, 0x8999c, 0x899a4, 0x899ac) is not reached: text lies in a live block
   (its one caller, arg_line, passes verbs_receive's strndup line), and out[o] lies in the fresh block of len + 1
   bytes, because o <= |canon T| <= len. s0 holds len at the xmalloc call (0x897fc mv s0,a1), at most LMAX and so
   below alloc_ceiling: achain_low (YCbq.v:269) gives the empty chain xmalloc's afn_pre asks for.

   UBSan (B only, 7 trap sites, all to the one `unimp` at 0x89988): 0x89850, 0x8985c and 0x89860 are the three
   checks of `text[i]` at recorder.c:111 (unsigned wrap of text + i; the result null while text is not; text null);
   0x898d0 is the wrap of text + i at recorder.c:117; 0x898a4, 0x898f4 and 0x89954 are the wrap of out + o at
   recorder.c:116, 118 and 120. No premise is added for them: `in_blockA (ablocks B ly S) text (len + 1)` with AR's
   block law (in_app: 4096 <= p, p + req_size n <= ASAN_CEIL, lib/Reusable/YG0d.v:431-437) gives 0 < text and
   text + i < 2 ^ 64 for i <= len, and the same law applied to the block xmalloc returns gives 0 < out and
   out + o < 2 ^ 64 for o <= len. The accesses are byte-wide, so UBSan adds no alignment check here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c.
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
(* the stack this call needs: its own 32-byte frame and xmalloc's (which carries the malloc wrapper's ASTACK) *)
Definition REC_CANONICAL_STK : Z := 32 + XMALLOC_STK.
(* one allocator event: the malloc xmalloc makes *)
Definition EV_REC_CANONICAL : Z := EV_XMALLOC.
(* the live bytes the call adds: the block of len + 1 bytes *)
Definition LIVE_REC_CANONICAL (T : list byte) : Z := Z.of_nat (length T) + 1.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xmalloc of len + 1 bytes *)
Definition XM_REC_CANONICAL (T : list byte) : Z := XM_XMALLOC MT (Z.of_nat (length T) + 1).
(* the program callee's contract *)
Hypothesis HXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Definition trec_canonical_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (text : Z) (T : list byte),
afn_pre SEGS B REC_CANONICAL_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 text -> 0 <= text < 2 ^ 64 -> getr regs 11 = w64 (Z.of_nat (length T)) ->
(* the line: its len bytes hold no NUL and len <= LMAX (plain rec_canonical_c.v:44-46); arg_line, the one caller,
   hands over a NUL-terminated string inside a live block (its own block-form premise), so the block form, not
   astr_argA. The text is read byte by byte inline, so no tail word is read. The block form also
   excludes the UBSan checks of text + i (0x89850, 0x8985c, 0x89860, 0x898d0) through AR's block law *)
in_blockA (ablocks B ly S) text (Z.of_nat (length T) + 1) -> astr_atR (rdW W mem) text T ->
Z.of_nat (length T) + 1 <= LMAX + 1 ->
st_nev S + EV_REC_CANONICAL <= EV_MAX -> blocks_bytes S + LIVE_REC_CANONICAL T <= LIVE_MAX ->
mo_ok MT S (XM_REC_CANONICAL T) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_canonical) regs mem md)
(apost_base SEGS B REC_CANONICAL_STK [] regs ly S W mem md EV_REC_CANONICAL
(fun ly' S' W' regs' mem' md' => exists p : Z,
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (plain rec_canonical_c.v:30-31) *)
 Permutation (ablocks B ly' S') ((p, LIVE_REC_CANONICAL T) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart p (LIVE_REC_CANONICAL T) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* it holds the canonical line and its terminator, and the line is kept (plain rec_canonical_c.v:34-35) *)
 abytes_atR (rdW W' mem') p (canon T ++ [Z_to_bv 8 0]) /\ abytes_atR (rdW W' mem') text T /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CANONICAL T /\
 mo_le MT S S' (XM_REC_CANONICAL T))).
End e.
End f.
End d.
