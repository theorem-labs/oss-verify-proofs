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
(* The contract of check_words_pin_set on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): the entry condition at the
   entry, SRr of apost_base at the return. The function reaches no allocator and no side-stack entry, so the entry
   condition is afn_pre_na (lib/B/Prog/PaNoChain.v: afn_pre without the frame chain) and the post is the frame form
   (`ly' = ly /\ S' = S`). Functional content: fuzz_command's own released plain contract
   lib/Prog/check_words_pin_set_c.v:16-31 and its model lib/Prog/CommandModel.v (pin_verdict, S_DASH, S_VERDICT).
   The B twin of lib/A/Prog/check_words_pin_set_c.v, re-derived on B's code.
   The function (fuzz_command.c:375-387) takes the verdict from word 4 when the message has one (word 4 without
   its "verdict=" key when it starts with the key: one call of the strncmp wrapper `___interceptor_strncmp`,
   reached through the 4-byte jump `__interceptor_trampoline_strncmp`), else "-"; then it checks that the pin_set
   call the recorder kept has 4 arguments and that argument 3 is that verdict (one call of the strcmp wrapper), and
   calls abort() if not. The premise `x3 = pin_verdict r w4` is what the caller (check_words) has established, so
   the abort edge (`__asan_handle_no_return` 0x5f790, then abort 0x94ba8) is not taken.
   3 inline ASan checks (shadow byte at (a >> 3) + the shadow base, read through the GOT word 0xa5f50 from the cell
   0xb0c38): w[4] in the heap array w->w (8-byte load), call->nargs (4-byte) and call->args[3] (8-byte) in g_rec;
   each byte is marked usable (the heap slot by the premise below and AR's block facts, g_rec by
   `cmd_addressable_chk`), so no error path (a call of `__asan_report_load4/8`) is reached. The strings it compares
   are the recorded argument 3 (a block by acall_at), the harness word 4 (inside words_of's `copy` block,
   fuzz_command.c:120) and the two literals, so the wrappers' reads come from AR's block facts and each tail word
   from `cmd_heap_tail_vis`, the literals' from `cmd_aread_ok_chk` and `cmd_tail_vis`.
   UBSan (trap mode; the UBSan trap-site tables): 7 trap sites, all branching to `unimp` 0x895c8 (the
   `unimp` 0x895d4 after `jal abort` is never reached): 0x894f8 (w null, offset 32), 0x89500 (w + 32 wraps), 0x8950c
   (w + 32 misaligned), 0x89548 (`j`: w[4] + 8 is null or wraps), 0x89554 (call null), 0x8955c (call misaligned),
   0x89588 (call->args + 3 wraps). The two alignment sites are excluded by the premises `cp mod 8 = 0` and
   `wp mod 8 = 0` below; the others by the address ranges (g_rec's range, the heap slot's and the word's blocks
   with AR_blocks_law: 4096 <= block start, block end <= alloc_ceiling).
   s0 holds cp (0x894f0 mv s0,a0) at the strncmp and strcmp calls; no program call, no allocator call.

   Addresses (B, its disassembly): entry BASE + AF_check_words_pin_set = 0x894cc. 73 instructions,
   frame 32 bytes (`addi sp,sp,-32`), no side-stack frame, no loop. Calls: the strncmp wrapper (0x4518c, at 0x89534),
   the strcmp wrapper (0x45188, at 0x895a8). The literals it reads (B's lib/B/Prog/CmdRo.v): "verdict=" 0x21ba0
   (RO_lit_21ba0), "-" 0x21b00 (RO_lit_21b00). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
(* the released plain contract defines pin_verdict (lib/Prog/check_words_pin_set_c.v:12-14); its module shares
   this file's base name, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
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
(* the stack this call needs: its own 32-byte frame, and the window the strcmp and strncmp wrappers ask for
   (ecall_pre_stk SEGS B (2 * ESTACK), lib/B/Rt/RtString.v:111, :124). M: the function table gives 16416. *)
Definition CWPS_STK : Z := 32 + 2 * ESTACK.
(* no allocator event: no malloc, no free, and neither wrapper allocates *)
Definition EV_CWPS : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's names *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcwps_spec B MT *)
#[using="MT"]
Definition tcwps_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p4 p3 : Z) (w4 x3 : list byte),
afn_pre_na SEGS B CWPS_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the two literals it compares against, "-" 0x21b00 and "verdict=" 0x21ba0 (their shadow: `cmd_aread_ok_chk`,
   so no shadow premise), and the bridge from the listing's object atoms to those addresses (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
0 <= r <= 64 ->
(* the recorded call sits inside the recorder's object g_rec (its shadow usable by `cmd_addressable_chk`), so the
   two inline checks at cp + 4 and cp + 32 need no premise beyond the address range. UBSan 0x89554 (call null)
   by the lower bound, 0x89588 (call->args + 3 wraps) by the upper bound. *)
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(* UBSan 0x8955c (alignment of `call`, a struct rec_call, for call->nargs): the caller passes &g_rec.calls[c] =
   A_G_REC + OFF_CALLS + CALL_SIZE * c, a multiple of 8 *)
cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(* its fourth argument: a string the recorder copied into a live block (acall_at puts every argument in a block,
   lib/B/Prog/CmdRep.v; the plain contract's call_at, lib/Prog/RecInv.v:42-50) *)
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 p3 /\ 0 <= p3 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p3 (Z.of_nat (length x3) + 1) /\ astr_atR (rdW W mem) p3 x3) ->
(* the harness's word list, in the heap array w->w (fuzz_command.c:121): the fifth word's pointer slot lies in
   that live block, which also keeps it apart from this call's own frame and from g_rec (the plain contract's
   word_slot, lib/Prog/check_words_pin_set_c.v:23), and the word itself inside the `copy` block. UBSan 0x894f8
   (w null) and 0x89500 (w + 32 wraps) by the slot's block (AR_blocks_law: 4096 <= its start, its end <=
   alloc_ceiling); 0x89548 (w[4] + 8 null or wraps) by the word's block in the same way *)
(4 < r ->
 in_blockA (ablocks B ly S) (wp + 32) 8 /\
 range_addressable (rdW W mem) SHADOW_OFF (wp + 32) 8 /\
 aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) p4 (Z.of_nat (length w4) + 1) /\ astr_atR (rdW W mem) p4 w4) ->
(* UBSan 0x8950c (alignment of the 8-byte load w[4]): w->w is a malloc block start (AR_blocks_law: mod 16 = 0),
   the caller check_words passes it as it read it *)
wp mod 8 = 0 ->
(* what the caller has checked: the recorded verdict is the one the message asks for *)
nargs = 4 -> x3 = OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_pin_set_c.pin_verdict r w4 ->
st_nev S + EV_CWPS <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words_pin_set) regs mem md)
(apost_base SEGS B CWPS_STK [] regs ly S W mem md EV_CWPS
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S)).
End e.
End f.
End d.
