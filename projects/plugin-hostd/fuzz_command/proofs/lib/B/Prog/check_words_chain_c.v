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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 49 of its 78 lines of code are new or changed and 123 lines of the source are left out. *)
(* The contract of check_words_chain on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the side-stack frame as cgif's users take it (aj_stack_malloc_atS,
   lib/YC85.v:292-310). Functional content: fuzz_command's own released plain contract
   lib/Prog/check_words_chain_c.v:22-41, with the member list taken at the ASan atoi value: `chain_list_at atoi_a`
   is the plain chain_items / chain_list (lib/Prog/check_words_chain_c.v:14-20) with the atoi function as a
   parameter (lib/B/Prog/HarnessPropsA.v:54), and `atoi_a` (lib/B/Prog/sup_reply_code_c.v) is the value the atoi
   wrapper returns, bv_swrap 32 of musl's strtol value (aatoi_realizes, lib/B/Rt/RtNumber.v). pf_dec and
   pf_bytes are lib/Prog/printf_facts_c.v:54, :91. The B twin of lib/A/Prog/check_words_chain_c.v, re-derived on
   B's code.
   The function (fuzz_command.c:356-371) builds in its local list[769] the words 2 .. read-1 read as numbers and
   joined by one space (one call of the atoi wrapper `___interceptor_atoi` and one of the snprintf wrapper
   `___interceptor_snprintf` per word, reached through the 4-byte jumps `__interceptor_trampoline_atoi` and
   `__interceptor_trampoline_snprintf`), writes read - 2 into its local count[16] (a second snprintf call), then
   checks that the recorded chain call has 3 arguments and that arguments 1 and 2 are count and list (two calls of
   the strcmp wrapper), and calls abort() if not. The premises `nargs = 3`, `x1 = pf_bytes (pf_dec (r - 2))` and
   `x2 = pf_bytes (chain_list_at atoi_a r ws)` are what the caller (check_words) has established from
   `call_words_ok_at atoi_a` (lib/B/Prog/HarnessPropsA.v:58), so the abort edge (`__asan_handle_no_return` 0x5f790,
   then abort 0x94ba8) is not taken.
   The two locals live in a side-stack frame of class 4 (992 bytes in a 1024-byte slot, __asan_stack_malloc_4 at
   0x89158): list at frame + 32, count at frame + 944 (the frame description "2 32 769 8 list:358 944 16 9
   count:358", RO_lit_20814). The function marks the frame's shadow itself: 0xf1 at bytes 0-3 inline, then
   `__asan_set_shadow_f8` (97 bytes from shadow + 4), the redzone bytes 0xf2 (101-117), 0xf8 (118-119) and 0xf3
   (120-123) inline, `__asan_set_shadow_00` (96 bytes from shadow + 4, the usable list), 0x01 at 100 and 0x00 at
   118-119 inline (list's last byte, count); at the end 0xf8 0xf8 inline (118-119), `__asan_set_shadow_f8` again,
   the magic 0x45e0360e at frame + 0, `__asan_set_shadow_f5` (128 bytes from shadow + 0, the whole frame), and the
   frame's flag byte (its address at frame + 1016) set to 0. Only the side-stack branch is stated: the
   use-after-return flag (read through the GOT word 0xa5fa8 from 0xb0c40) is a const cell of the allocator record
   (cgif lib/YG0f.v aso_const_law, a law of LAWS) and the stack-malloc rule returns a frame (lib/YC85.v:292-310)
   under the room premise below, so the real-stack fallback (0x89160, 0x8916c-0x89184 with its stack probe loop
   0x89178-0x89180, and 0x89454-0x8945c) is not reached.
   4 inline ASan checks (shadow byte at (a >> 3) + the shadow base, read through the GOT word 0xa5f50 from the cell
   0xb0c38): w[k] in the heap array w->w (8-byte load, in the loop), call->nargs, call->args[1], call->args[2] in
   g_rec; each byte is marked usable (the heap slots by AR's block facts, g_rec by `cmd_addressable_chk`), so no
   error path (a call of `__asan_report_load4/8`) is reached. Every string it hands to a wrapper is a live block
   (the harness words in words_of's `copy` block, fuzz_command.c:120, to atoi; the recorded arguments, blocks by
   acall_at, to strcmp) or its own frame's list / count, so the wrappers' reads come from AR's block and frame facts
   and each tail word from `cmd_heap_tail_vis`; the two format literals' reads from `cmd_aread_ok_chk`. The flag
   byte, the errno cell and the stack guard that the atoi and snprintf entries read come from `cmd_rec_cells`.
   UBSan (trap mode; the UBSan trap-site tables): 10 trap sites, all branching to `unimp` 0x894a8:
   0x892b8 (array bound of `list + o`, o <= 769), 0x892cc (w null), 0x892d0 (w + k null), 0x892d4 (w + k wraps),
   0x892d8 (w + k misaligned), 0x8933c (signed overflow of read - 2), 0x89360 (call null), 0x8936c (call
   misaligned), 0x893a4 (call->args + 1 wraps), 0x893d8 (call->args + 2 wraps). The two alignment sites are
   excluded by the premises `cp mod 8 = 0` and `wp mod 8 = 0` below; 0x892b8 by `0 <= r <= 64` (o <= 12 * (k - 2)
   <= 732 at the loop head of word k <= r - 1: each snprintf of an int writes at most 11 characters, 12 with its space);
   0x8933c by `0 <= r`; the others by the address ranges (g_rec's range, the word slots' blocks with
   AR_blocks_law: 4096 <= block start, block end <= alloc_ceiling).
   s0 is the frame pointer (0x8911c addi s0,sp,224): no caller value, no achain premise. It reaches no heap
   allocator; its only state change is the class-4 side-stack frame taken (stack_malloc, a set_fs,
   lib/Reusable/YG00.v) and released inline, so the post keeps ly and changes S by set_fs only.

   Addresses (B, its disassembly): entry BASE + AF_check_words_chain = 0x890e0. 251 instructions,
   one loop (k = 2 .. read - 1, 0x892b4-0x89330), frame 224 bytes (`addi sp,sp,-224`) realigned to 32
   (`andi sp,sp,-32` at 0x89120). Calls: __asan_stack_malloc_4 (0x3fe04, at 0x89158), __asan_set_shadow_f8
   (0x5a65c, at 0x891e8, 0x89420), __asan_set_shadow_00 (0x5a53c, at 0x89260), the atoi wrapper (0x45230, at
   0x89304), the snprintf wrapper (0x451d0, at 0x89318, 0x89358), the strcmp wrapper (0x45188, at 0x893cc, 0x89400),
   __asan_set_shadow_f5 (0x5a644, at 0x89444). The literals it reads (B's lib/B/Prog/CmdRo.v): "%d" 0x218e0
   (RO_lit_218e0), " %d" 0x21b80 (RO_lit_21b80), and the frame description 0x20814 (RO_lit_20814). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 224-byte frame and up to 16 bytes the realignment to 32 adds, and the
   largest window a callee asks for there: the atoi and snprintf wrappers' 3 * ESTACK (their final windows,
   lib/B/Rt/RtNumber.v:65, RtFormat.v:76). The strcmp wrapper asks 2 * ESTACK (RtString.v:111),
   __asan_stack_malloc_4 and the three shadow-fill entries ESTACK (cgif lib/YG0d.v, RtShadow.v). *)
Definition CHECK_WORDS_CHAIN_STK : Z := 224 + 16 + 3 * ESTACK.
(* no allocator event: the side-stack frame is not an allocator block, and no wrapper allocates *)
Definition EV_CHECK_WORDS_CHAIN : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with cgif's and this tree's names. The atoi and snprintf entries take the
   stack-protector GOT word 0xa6bf8 and guard 0x604158 (A_SSP_GOT, A_SSP_GUARD, lib/B/Rt/RtAPI.v:59-60),
   the atoi entry also the runtime's replace_str flag byte 0xae455 (A_FLAG_REPLACE_STR, RtAPI.v:56). *)
Hypothesis ASMALLOC4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASETF5 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Hypothesis ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_words_chain_spec B MT *)
#[using="MT"]
Definition tcheck_words_chain_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cp wp r nargs p1 p2 : Z) (pw : list Z) (ws : list (list byte))
  (x1 x2 : list byte),
afn_pre SEGS B CHECK_WORDS_CHAIN_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
(* UBSan 0x8933c (signed overflow of read - 2) by 0 <= r; 0x892b8 (array bound of `list + o`, o <= 769) by
   r <= 64: o <= 12 * (k - 2) <= 732 at the loop head of word k <= r - 1 *)
0 <= r <= 64 -> 0 <= wp < 2 ^ 64 ->
(* the read-only bytes of the image, among them the two format literals (their shadow: `cmd_aread_ok_chk`, so no
   shadow premise) *)
cmd_ro_ok (rdW W mem) ->
(* the bridge from the listing's object atoms to the literals' absolute addresses (lib/B/Prog/CmdObj.v) *)
cmd_val_objs ->
(* the recorded call sits inside the recorder's object g_rec (its shadow usable by `cmd_addressable_chk`), so the
   inline checks at cp + 4, cp + 16 and cp + 24 need only the address range. UBSan 0x89360 (call null) by the
   lower bound; 0x893a4 and 0x893d8 (call->args + 1, + 2 wrap) by the upper bound *)
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(* UBSan 0x8936c (alignment of `call`, a struct rec_call, for call->nargs): the caller passes &g_rec.calls[c] =
   A_G_REC + OFF_CALLS + CALL_SIZE * c, a multiple of 8 *)
cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(* its arguments 1 and 2, strings the recorder holds, each in a live block (plain :36-37; acall_at) *)
(nargs = 3 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 8) 8 p1 /\ 0 <= p1 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p1 (Z.of_nat (length x1) + 1) /\ astr_atR (rdW W mem) p1 x1) ->
(nargs = 3 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 16) 8 p2 /\ 0 <= p2 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p2 (Z.of_nat (length x2) + 1) /\ astr_atR (rdW W mem) p2 x2) ->
(* the harness's word list (plain :31-32): slots 2 .. r-1 of the heap array w->w, and the words they point at
   (pointers into the one `copy` block, fuzz_command.c:132-141). UBSan 0x892cc, 0x892d0, 0x892d4 (w null,
   w + k null, w + k wraps) by these slots' blocks (AR_blocks_law: 4096 <= block start, block end <=
   alloc_ceiling) *)
(forall k, 2 <= k < r ->
 in_blockA (ablocks B ly S) (wp + 8 * k) 8 /\
 aval_mem (rdW W mem) (wp + 8 * k) 8 (nth (Z.to_nat k) pw 0) /\ 0 <= nth (Z.to_nat k) pw 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth (Z.to_nat k) pw 0) (Z.of_nat (length (nth (Z.to_nat k) ws [])) + 1) /\
 astr_atR (rdW W mem) (nth (Z.to_nat k) pw 0) (nth (Z.to_nat k) ws [])) ->
(* UBSan 0x892d8 (alignment of the 8-byte load w[k]): w->w is a malloc block start (AR_blocks_law: mod 16 = 0),
   the caller check_words passes it as it read it *)
wp mod 8 = 0 ->
(* what the caller has checked (plain :38): the recorded count and member list are the ones the message asks for *)
nargs = 3 -> x1 = pf_bytes (pf_dec (r - 2)) -> x2 = pf_bytes (chain_list_at atoi_a r ws) ->
(* room for one more frame of class 4 on the side stack (cgif lib/YG0d.v, lib/YC85.v:298) *)
count_cid 4 (frames S) < fs_frames 4 ->
st_nev S + EV_CHECK_WORDS_CHAIN <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words_chain) regs mem md)
(apost_baseF SEGS B CHECK_WORDS_CHAIN_STK [] regs ly S W mem md EV_CHECK_WORDS_CHAIN
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* the side-stack frame is the only state change: the layout is kept, the allocator state up to st_fs *)
 ly' = ly /\ exists f, S' = set_fs f S)).
End e.
End f.
End d.
