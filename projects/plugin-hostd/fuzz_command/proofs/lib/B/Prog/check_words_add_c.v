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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 40 of its 67 lines of code are new or changed and 125 lines of the source are left out. *)
(* The contract of check_words_add on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): the entry condition at the
   entry, SRr of apost_base at the return. The function reaches no allocator and no side-stack entry, so the entry
   condition is afn_pre_na (lib/B/Prog/PaNoChain.v: afn_pre without the frame chain) and the post is the frame form.
   Functional content: fuzz_command's own released plain contract lib/Prog/check_words_add_c.v:24-41, with its model
   in the same file (:12-22: is_placement_b, add_placement, add_next, add_client) and lib/Prog/CommandModel.v:42-45
   (S_DASH, S_OWN, S_DEFAULT, S_POOL). The B twin of lib/A/Prog/check_words_add_c.v, re-derived on B's code.
   The function (fuzz_command.c:341-352, is_placement inlined) takes the placement from word 3 when that word is
   "own", "default" or starts with "pool:" (two calls of the strcmp wrapper `___interceptor_strcmp` and one of the
   strncmp wrapper `___interceptor_strncmp`, reached through the 4-byte jumps `__interceptor_trampoline_strcmp` and
   `__interceptor_trampoline_strncmp`), else "-"; `strcmp(placement, "-")` is inlined (placement[0] == '-' and
   placement[1]); the client is the word after the placement, or "-"; then it checks that the recorded add call has
   4 arguments and that arguments 2 and 3 are the placement and the client (two more strcmp calls), and calls
   abort() if not. The premises `nargs = 4`, `x2 = add_placement r w3` and `x3 = add_client r w3 w4` are what the
   caller (check_words) has established from `call_words_ok_at` (lib/B/Prog/HarnessPropsA.v), so the abort edge
   (`__asan_handle_no_return` 0x5f790, then abort 0x94ba8) is not taken.
   7 inline ASan checks (shadow byte at (a >> 3) + the shadow base, read through the GOT word 0xa5f50 from the cell
   0xb0c38): w[3] and w[next] in the heap array w->w (8-byte loads), placement[0] and placement[1] (1-byte loads, a
   word or the literal "-"), call->nargs, call->args[2], call->args[3] in g_rec; each byte is marked usable (the heap
   slots and words by AR's block facts, g_rec and the literal by `cmd_addressable_chk`), so no error path (a call of
   `__asan_report_load1/4/8`) is reached. Every string it compares is a live block (the recorded call's arguments,
   blocks by acall_at, and harness words in words_of's `copy` block, fuzz_command.c:120), so the wrappers' reads come
   from AR's block facts and each tail word from `cmd_heap_tail_vis`; the literals' reads from `cmd_aread_ok_chk`,
   their tails from `cmd_tail_vis`.
   UBSan (trap mode; the UBSan trap-site tables): 11 trap sites, all branching to `unimp` 0x89094 (the
   `unimp` 0x890a0 after `jal abort` is never reached): 0x88ef4 (w null, offset 24), 0x88efc (w + 24 wraps),
   0x88f08 (w + 24 misaligned), 0x88fc0 (w + next wraps), 0x88fc4 (w null), 0x88fc8 (w + next null), 0x88fd0
   (w + next misaligned), 0x88fe8 (call null), 0x88ff0 (call misaligned), 0x8901c (call->args + 2 wraps), 0x89048
   (call->args + 3 wraps). The three alignment sites are excluded by the premises `cp mod 8 = 0` and `wp mod 8 = 0`
   below; the others by the address ranges (g_rec's range; the word slots' blocks with AR_blocks_law: 4096 <= block
   start, block end <= alloc_ceiling).
   s0 holds cp (0x88ed4 mv s0,a0) at the strcmp / strncmp calls only; no program call, no allocator call. It reaches
   no heap allocator and no side-stack frame: the post keeps ly and S.

   Addresses (B, its disassembly): entry BASE + AF_check_words_add = 0x88eac. 141 instructions, no loop,
   frame 64 bytes (`addi sp,sp,-64`), no side-stack frame. Calls: the strcmp wrapper (0x45188, at 0x88f2c, 0x88f40,
   0x8903c, 0x89068), the strncmp wrapper (0x4518c, at 0x88f58). The literals it reads (B's lib/B/Prog/CmdRo.v):
   "-" 0x21b00 (RO_lit_21b00), "own" 0x21b20 (RO_lit_21b20), "default" 0x21b40 (RO_lit_21b40), "pool:" 0x21b60
   (RO_lit_21b60). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
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
(* the stack this call needs: its own 64-byte frame, and the window the strcmp and strncmp wrappers ask for
   (ecall_pre_stk SEGS B (2 * ESTACK), lib/B/Rt/RtString.v:111, :124). M: the function table gives 16448. *)
Definition CHECK_WORDS_ADD_STK : Z := 64 + 2 * ESTACK.
(* no allocator event: no malloc, no free, and neither wrapper allocates *)
Definition EV_CHECK_WORDS_ADD : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's names *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_words_add_spec B MT *)
#[using="MT"]
Definition tcheck_words_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p3 p4 q2 q3 : Z) (w3 w4 x2 x3 : list byte),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
0 <= r <= 64 -> 0 <= wp < 2 ^ 64 ->
(* the read-only bytes of the image, among them the four literals it reads (their shadow: `cmd_aread_ok_chk`,
   so no shadow premise) *)
cmd_ro_ok (rdW W mem) ->
(* the bridge from the listing's object atoms to the literals' absolute addresses (lib/B/Prog/CmdObj.v) *)
cmd_val_objs ->
(* the recorded call sits inside the recorder's object g_rec (its shadow usable by `cmd_addressable_chk`), so the
   inline checks at cp + 4, cp + 24 and cp + 32 need only the address range. UBSan 0x88fe8 (call null) by the
   lower bound; 0x8901c and 0x89048 (call->args + 2, + 3 wrap) by the upper bound *)
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(* UBSan 0x88ff0 (alignment of `call`, a struct rec_call, for call->nargs): the caller passes &g_rec.calls[c] =
   A_G_REC + OFF_CALLS + CALL_SIZE * c, a multiple of 8 *)
cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(* its arguments 2 and 3, strings the recorder holds, each in a live block (plain :36-37; acall_at) *)
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 16) 8 q2 /\ 0 <= q2 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) q2 (Z.of_nat (length x2) + 1) /\ astr_atR (rdW W mem) q2 x2) ->
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) q3 (Z.of_nat (length x3) + 1) /\ astr_atR (rdW W mem) q3 x3) ->
(* the harness's word list (plain :31-32): slots 3 and 4 of the heap array w->w, and the words they point at,
   pointers into the one `copy` block (fuzz_command.c:132-141). UBSan 0x88ef4, 0x88efc (w null, w + 24 wraps;
   reached when read > 3) and 0x88fc0, 0x88fc4, 0x88fc8 (w + next wraps, w null, w + next null; reached when
   read > next, next = 3 or 4) by these slots' blocks (AR_blocks_law: 4096 <= block start, block end <=
   alloc_ceiling) *)
(3 < r ->
 in_blockA (ablocks B ly S) (wp + 24) 8 /\ aval_mem (rdW W mem) (wp + 24) 8 p3 /\ 0 <= p3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p3 (Z.of_nat (length w3) + 1) /\ astr_atR (rdW W mem) p3 w3) ->
(4 < r ->
 in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p4 (Z.of_nat (length w4) + 1) /\ astr_atR (rdW W mem) p4 w4) ->
(* UBSan 0x88f08, 0x88fd0 (alignment of the 8-byte loads w[3], w[next]): w->w is a malloc block start
   (AR_blocks_law: mod 16 = 0), the caller check_words passes it as it read it *)
wp mod 8 = 0 ->
(* what the caller has checked (plain :38): the recorded placement and client are the ones the message asks for *)
nargs = 4 -> x2 = add_placement r w3 -> x3 = add_client r w3 w4 ->
st_nev S + EV_CHECK_WORDS_ADD <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words_add) regs mem md)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md EV_CHECK_WORDS_ADD
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
End e.
End f.
End d.
