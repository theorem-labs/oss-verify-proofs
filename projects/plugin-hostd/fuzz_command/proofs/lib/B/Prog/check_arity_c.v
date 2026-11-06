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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 35 of its 64 lines of code are new or changed and 123 lines of the source are left out. *)
(* The contract of check_arity on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre_na
   (lib/B/Prog/PaNoChain.v, cgif's afn_pre without the frame-chain conjunct: the function reaches no allocator and no
   side-stack entry, and the wrapper entries' ecall_pre asks no frame chain) at the entry, SRr of apost_base at the
   return. Functional content: fuzz_command's own released plain contract lib/Prog/check_arity_c.v:108-130 and its
   model in the same file, :15-106 (parsed_rows, row_arity, row_find, passed_on_m, arity_ok), used as they are. This
   is the arity property of fuzz_command.c:272-297: when the message has words, the daemon acted (g_quitting, or a
   recorded call), and the first call is not a broadcast of a verb the daemon passes on (passed_on, :265-269), the
   row of g_parsed whose name is the first word gives the argument counts its syntax allows (syntax_arity /
   syntax_format_arity, H/syntax.h:71-121, inlined), and the function calls abort() when read - 1 (read = min(n, 64))
   is outside them. The pre-condition `arity_ok t v q nc fn0` is what the caller (LLVMFuzzerTestOneInput) has
   established from harness_props_holds (lib/Prog/HarnessProps.v:27), so the abort edge (0x87a94:
   __asan_handle_no_return, then abort) is not taken.

   What the function reads:
   - the harness's `struct words` on the caller's real stack: w->n at a0 + 24 and w->w at a0 + 16;
   - the first word's pointer w->w[0] in the heap array, and the word it points to inside the `copy` block;
   - g_quitting, g_rec.ncalls and g_rec.calls[0].fn, through the GOT words 0xa6be0 and 0xa6bc8;
   - the image's constants: the 22 rows of g_parsed (0xa5680, 528 bytes, in the read-only range), the name and the
     syntax string of each row, and the literals " \t" (0x210e0) and "..." (0x218c0). The literals "pin_layout"
     (0x21180), "pin_expect" (0x211a0), "connect %s %s" (0x211c0) and "disconnect %s %s" (0x211e0) that passed_on
     compares with are the strings of g_parsed's rows 12 and 13 (names) and 19 and 20 (syntaxes): the linker merged
     them (M, read from the B ELF's g_parsed words). All of these bytes
     are in cmd_ro_ok (lib/B/Prog/CmdRo.v); the walk ties them to the plain model's img_str strings of parsed_rows by
     computation (the strings are the same, row for row: M, both pinned ELFs).
   - it does NOT read g_call_words (0xa5920): no instruction of the function forms that address (check_words reads it).
   Each inline check reads the shadow byte at (a >> 3) + 0x7fff8000 of a byte of the caller's frame (inside the stack
   window [spZ regs, ly_stk_hi ly), whose shadow AR's zshadow_ok keeps usable at every state, YG0n.v:188; the function
   only reads it), of a live heap block (in_blockA), of g_rec or g_quitting, or of an image constant; the last two
   CmdRecFacts' cmd_addressable_chk says usable, so the error path (a call of __asan_report_load1/4/8) is not reached.
   The GOT words 0xa6bc8 and 0xa6be0 are cmd_ro_ok's RO_ptr_a6bc8 / RO_ptr_a6be0. What the wrappers ask of the
   literals (aread_ok, the bytes after a terminator) comes from cmd_aread_ok_chk and cmd_tail_vis, of the first word
   (a heap string) from its block (cmd_heap_tail_vis), and the stack-protector cells musl's strcspn reads (aguard_ok,
   0xa6bf8 / 0x604158) from cmd_rec_cells; none is a premise. It keeps the argument in s0 (0x872a0 mv s0,a0) but
   makes no program call, so (afn_pre_na) it needs no achain premise.
   It writes nothing outside its own frame.

   UBSan (trap mode: a failed check branches to the `unimp` at 0x87a2c, a machine fault in cgif's model,
   lib/Reusable/YP00.v). check_arity has 24 trap sites (the trap-site table), all reaching 0x87a2c. The B binary is
   bigger than A's here (477 -> 544 insns) because every pointer walk gets a UBSan guard. Each site, and what rules it
   out:
   - 0x872a8 (fuzz_command.c:277, `andi w,7; bnez`): the misaligned-pointer check on the struct pointer `w` for the
     `w->n` / `w->w` accesses (struct words has 8-byte alignment). NEW premise `wp mod 8 = 0`: the only caller passes
     &w = sp + 120 (LLVMFuzzerTestOneInput 0x86a14), which is 8-aligned.
   - 0x87358, 0x8740c (277, 282, `beqz w->w`): the array-subscript nonnull check on w->w before `w->w[0]`. Reached
     only with w->n > 0 (0x872d0 returns when w->n == 0), so the `0 < t` arm's `in_blockA (ablocks B ly S) ww 8` gives
     ww in a live block, which AR puts in [4096, alloc_ceiling) (YG0d.v:433-434), so ww <> 0.
   - 0x87360, 0x87414 (277, 282, `andi w->w,7; bnez`): the misaligned-pointer check on w->w before loading w->w[0].
     NEW premise `ww mod 8 = 0` in the `0 < t` arm: w->w is words_of's malloc'd array start (fuzz_command.c:121),
     which AR makes 16-aligned (YG0d.v:434), so 8-aligned.
   - 0x874ac, 0x87560, 0x87654, 0x876bc, 0x87788, 0x879f8, 0x87720, 0x877f0, 0x875c4, 0x875b0, 0x8770c, 0x877dc,
     0x879e4, 0x87630, 0x87918, 0x87840, 0x87880 (syntax.h:43-114): the inlined syntax_arity / syntax_format_arity /
     syntax_item / syntax_has walking g_parsed[n].syntax. The pointer-overflow checks (p + 1 wrapping before p++,
     item + len - 1 and item + i), the signed-overflow checks of the counters depth, min and max, and the nonnull check of
     the syntax pointer are all over the matched row's syntax string, a NUL-terminated read-only image literal of at
     most 80 bytes fixed by cmd_ro_ok / cmd_val_objs (parsed_rows): the walk evaluates it, so every pointer stays in
     [0x21140, 0x2186a) < 2^64 - 1 (every row's syntax string and its NUL lies there, M, the B ELF) and every counter stays in
     [0, 80] < 2^31. EXISTING premises cmd_ro_ok / cmd_val_objs.
   - 0x87954 (fuzz_command.c:293, `addiw read-1; bge`): the signed-subtraction overflow of `read - 1`, with
     read = min(w->n, 64). Reached only with w->n > 0, and `0 <= t <= 4096` bounds w->n, so read in [1, 64] and
     read - 1 in [0, 63] does not overflow. EXISTING premise `0 <= t <= 4096`.
   The 10 unreachable `unimp` of the image include 0x87a9c (right after `jal abort`); nothing branches into it.

   Addresses: entry BASE + AF_check_arity = 0x87268 (B, the pinned image). 544 instructions, 20 inline checks
   (load1 9, load4 5, load8 6), 24 UBSan trap sites, 12 loops: the scan of g_parsed (header 0x87448, at most 22
   passes) and 11 loops of the inlined syntax_arity / syntax_format_arity / syntax_item / syntax_has over one constant
   syntax string of at most 80 characters, entered once for the matched row. real frame 144 bytes (A's was 112), no
   side-stack frame. Wrapper calls: strcmp (3 sites), strcspn (1), strncmp (1), bcmp (2). Objects of the listing it
   loads: A_OBJ 0, 2, 5, 6, 14-19 (the image's function table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
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
(* the stack this call needs: its own 144-byte frame (addi sp,sp,-144 at 0x87268), and the window the strcmp,
   strcspn and strncmp wrappers (RtDefs.v ecall_pre_stk segs B (2 * ESTACK)) and the bcmp wrapper (cgif's
   abcmp_realizes, lib/YG0d.v:352-355) ask for *)
Definition CHECK_ARITY_STK : Z := 144 + 2 * ESTACK.
(* no allocator event *)
Definition EV_CHECK_ARITY : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's and cgif's names, at the listing's call targets *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_arity_spec B MT *)
#[using="MT"]
Definition tcheck_arity_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (wp t ww p0 q nc fn0 : Z) (v : list byte),
afn_pre_na SEGS B CHECK_ARITY_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the image's constants it reads (g_parsed, its row strings, " \t" and "...") and the GOT words of g_rec and
   g_quitting, and the bridge from the listing's object atoms to those addresses (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 wp -> 0 <= wp < 2 ^ 64 ->
(* UBSan 0x872a8: the struct pointer w is read at its 8-byte alignment (w->w is a pointer); the caller passes
   &w = sp + 120, 8-aligned *)
wp mod 8 = 0 ->
(* the harness's struct words, in the caller's real stack frame above this call's window and inside the stack
   window (read only): w->w (8 bytes at wp + 16) and w->n (4 bytes at wp + 24) *)
spZ regs <= wp -> wp + WORDS_W + 12 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (wp + WORDS_N) 4 t -> 0 <= t <= 4096 ->
aval_mem (rdW W mem) (wp + WORDS_W) 8 ww -> 0 <= ww < 2 ^ 64 ->
(* when the message has words: the first word's pointer in the heap array w->w, and the word itself, a string in
   the `copy` block (a harness word: every caller passes a token of words_of's copy block, fuzz_command.c:121); and
   (UBSan 0x87360, 0x87414) w->w is 8-aligned, being that block's malloc'd start *)
(0 < t ->
 in_blockA (ablocks B ly S) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\
 0 <= p0 < 2 ^ 64 /\ in_blockA (ablocks B ly S) p0 (Z.of_nat (length v) + 1) /\ astr_atR (rdW W mem) p0 v) ->
(* g_quitting, g_rec.ncalls and, when there is a recorded call, the first call's function *)
aval_mem (rdW W mem) A_G_QUITTING 4 q -> 0 <= q < 2 ^ 32 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 nc -> 0 <= nc <= 16 ->
(0 < nc -> aval_mem (rdW W mem) (A_G_REC + OFF_CALLS + CALL_OFF_FN) 4 fn0 /\ 0 <= fn0 < REC_FN_COUNT) ->
(* what the caller has established: the argument count is one the verb's declared syntax allows *)
arity_ok t v q nc fn0 ->
st_nev S + EV_CHECK_ARITY <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_arity) regs mem md)
(apost_base SEGS B CHECK_ARITY_STK [] regs ly S W mem md EV_CHECK_ARITY
(fun ly' S' W' regs' mem' md' =>
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
