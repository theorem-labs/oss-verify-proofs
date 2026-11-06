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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 69 of its 95 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of sup_host_setting on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92); the side-stack frame as cgif's
   class-0 users take it (aj_stack_malloc_atS, lib/YC85.v:292-310). Functional content: fuzz_command's own released
   plain contract lib/Prog/sup_host_setting_c.v:17-66 and the model lib/Prog/RecModel.v:131-133
   (`sup_host_setting_m`, which records the canonical line, the token count and the tokens joined by single spaces,
   and folds the call into the host_settings digest with `rec_mix_host`, RecModel.v:43). The B twin of
   lib/A/Prog/sup_host_setting_c.v, re-derived on B's code, which differs from A's: B calls record(), arg_s() and
   xmalloc() (lib/B/Prog/record_c.v, arg_s_c.v, xmalloc_c.v) where A inlined record() and xmalloc and called
   xstrdup, and inlines arg_i (B has no arg_i), so this function owns arg_i's class-0 side-stack frame and its
   snprintf.
   sup_host_setting (recorder.c:355-377) records the call with record(6) (a new slot of g_rec.calls, or
   record.spill with its arguments freed when the table already holds 16 calls), adds the canonical line with
   arg_line, prints the token count with snprintf(b, 16, "%d", ntok) (format at 0x21f40) into b[16] of its class-0
   side-stack frame (arg_i inlined, recorder.c:235-241) and adds b with arg_s, adds up the tokens' lengths with the
   strlen wrapper, allocates that many bytes plus one with xmalloc, joins the tokens into it (a separator written
   inline as the two bytes " " and NUL, then the strcat wrapper per token), adds the joined text with arg_s, frees
   it, and folds the call into g_rec.host_settings (g_rec + 952 = 0x5e3678, read and written directly) with
   mix_call. It returns no value and calls no answer.
   The frame: `__asan_stack_malloc_0` (request 64 bytes, 0x8b5b0; this port's decision: the side-stack branch only, the
   use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const cell, so the
   real-stack fallback 0x8b5c8-0x8b5e0 and its page probe are not taken), shadow f1 f1 f1 f1 | f8 f8 | f3 f3 with b
   (frame + 32, 16 bytes) unpoisoned (00) for the snprintf and the first arg_s call (0x8b658, recorder.c:237) and
   poisoned again (f8) after them (0x8b684), released inline before the return (magic 0x45e0360e at frame + 0,
   shadow f5, flag byte through frame + 56: 0x8b820-0x8b85c, cgif's astack_free_law, lib/YG0d.v:309-317). The
   stack-protector cells the musl body under the snprintf wrapper compares (aguard_ok, lib/B/Rt/RtDefs.v; B's GOT word
   0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts).
   UBSan (the trap-site tables' rows of this function): 4 check sites, all branching to the `unimp` at
   0x8b8c0, all of the pointer &tok[n] (tok + 8n, computed by repeated `addi 8`): 0x8b6bc `bltu s6,s8` (tok + 8n
   wrapped below tok, recorder.c:365), 0x8b6c8 `beqz a0` (tok and tok + 8n are not both non-null or both null),
   0x8b6cc `beqz s7` (tok is null or not 8-aligned for the 8-byte load of tok[n]), 0x8b774 `bltu s5,s7` (~tok < 8n:
   tok + 8n wraps, recorder.c:372). None is taken: `ptok <> 0` and `ptok mod 8 = 0` below exclude 0x8b6cc, and
   the token array premise (a live side-stack frame object or a live block of 8 * ntok bytes, so
   ptok + 8 * ntok < 2 ^ 64 by AR's frame and block facts) with ptok <> 0 excludes 0x8b6bc, 0x8b6c8 and 0x8b774 for
   every n < ntok.

   Addresses (B, the disassembly of sup_host_setting): entry BASE + AF_sup_host_setting = 0x8b53c. 239 instructions, 6
   (load8:2 store1:2 store_n:2) inline checks -- the two `__asan_report_store_n` sites of the program (0x8b7c4,
   0x8b8f4), the two-byte separator store of the join loop; the two store1 checks are words[0] = 0 in the taken arm
   (0x8b714) and in the ntok <= 0 arm (0x8b7ec, not taken: 1 <= ntok) --, two loops (one pass per token each, at
   most 64: 0x8b6bc-0x8b6fc and 0x8b738-0x8b7a0), a 160-byte real frame realigned by `andi sp,sp,-32` (0x8b57c) and
   a class-0 side-stack frame (0:64). The error path of each check (a call of `__asan_report_*`) is not reached:
   the token array is in a live block or in a side-stack frame, and words[0] and the separator's two bytes lie
   inside the block xmalloc just returned, which holds hs_words_len toks + 1 bytes. Calls:
   __asan_stack_malloc_0 (0x3f954, at 0x8b5b0), record (0x8a728, at 0x8b648), arg_line (0x8b128, at 0x8b654), the
   snprintf wrapper (0x451d0, at 0x8b674), arg_s (0x8a820, at 0x8b680 with b and at 0x8b800 with words), the strlen
   wrapper (0x4517c, at 0x8b6e4 per token and at 0x8b740 before each separator), xmalloc (0x899b4, at 0x8b704), the
   strcat wrapper (0x45220, at 0x8b794), the free wrapper (0x589cc, at 0x8b808), mix_call (0x8ad54, at 0x8b818). s0
   is this call's frame pointer (0x8b578 `addi s0,sp,160`, the entry sp) at every call: the prologue saved ra at
   s0 - 8 and the caller's s0 at s0 - 16, so each callee's frame chain for s0 is that record on top of afn_pre's
   chain, and achain_chain_pre (YCbq.v:327) gives the runtime entries' chain_pre; no presence of the stack up to
   ly_top is assumed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_line_c arg_s_c xmalloc_c mix_call_c.
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
(* the bytes the joined word list needs, the plain proof's sup_host_setting_len
   (lib/Prog/sup_host_setting_c.v:17-18): one for each token's NUL, which the loop adds up with the strlen
   wrapper *)
Definition hs_words_len (toks : list (list byte)) : Z :=
  fold_right (fun w s => Z.of_nat (length w) + 1 + s) 0 toks.
(* the stack this call needs: its own 160-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0
   at the entry, afn_pre's astk_ok), and the deepest callee, all reached with the frame up: the side-stack entry's
   and the strlen wrapper's window (ESTACK), the snprintf wrapper's (3 * ESTACK, measured), the strcat
   wrapper's (2 * ESTACK), the free wrapper's (ASTACK, cgif lib/YG0d.v:17), record's, arg_line's, arg_s's,
   xmalloc's and mix_call's own needs. It calls no answer.
   M: the image's function table gives 16720 = 160 + record's 16560 (without the realignment's 16) *)
Definition SUP_HOST_SETTING_STK : Z :=
  160 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max (2 * ESTACK) (Z.max ASTACK
    (Z.max RECORD_STK (Z.max ARG_LINE_STK (Z.max ARG_S_STK (Z.max XMALLOC_STK MIX_CALL_STK))))))).
(* the allocator events: the frees of record()'s spill arm, the canonical line, arg_s's copy of the printed token
   count, xmalloc's word list, arg_s's copy of it, and its free; the side-stack frame spends none *)
Definition EV_SUP_HOST_SETTING (R : rstate) : Z :=
  EV_RECORD R + EV_ARG_LINE + EV_ARG_S + EV_XMALLOC + EV_ARG_S + 1.
(* the live bytes the call adds at its peak: the canonical line, the token count, the joined word list and its
   copy *)
Definition LIVE_SUP_HOST_SETTING (R : rstate) (line : list byte) (toks : list (list byte)) : Z :=
  LIVE_ARG_LINE line + LIVE_ARG_S (Some (dec (Z.of_nat (length toks)))) + LIVE_XMALLOC (hs_words_len toks + 1) +
  LIVE_ARG_S (Some (join_sp toks)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, the two recorded arguments before the join, the word list,
   its copy, and the word list's free *)
Definition XM_SUP_HOST_SETTING (R : rstate) (line : list byte) (toks : list (list byte)) : Z :=
  XM_RECORD MT R + XM_ARG_LINE MT line + XM_ARG_S MT (Some (dec (Z.of_nat (length toks)))) +
  XM_XMALLOC MT (hs_words_len toks + 1) + XM_ARG_S MT (Some (join_sp toks)) + mo_free MT.
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge from the image's
   object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASTRCAT : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_host_setting_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pl ptok : Z) (ps : list Z) (line : list byte)
  (toks : list (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_HOST_SETTING_STK ly S W regs mem md ch -> (* astack_rd when it lands *)
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the format "%d" (0x21f40) of the inlined arg_i, and what
   record, arg_line, arg_s and mix_call read; the GOT words of the use-after-return flag (0xa5fa8) and the shadow
   base (0xa5f50). The separator " " is written inline (`li s4,32`, 0x8b734), not read from the image *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 -> getr regs 11 = w64 ptok -> 0 <= ptok < 2 ^ 64 ->
getr regs 12 = w64 (Z.of_nat (length toks)) -> (1 <= length toks <= 64)%nat ->
(* the line: a string of at most LMAX bytes inside a live block that is none of the recorder's (the plain proof's
   str_arg, lib/Prog/RecKindB.v:164-175). The one caller, verbs_receive, passes its strndup line (0x8d93c
   `ld s2,56(s1)`, verbs.c:219), so the block form, not astr_argA; arg_line's strlen reads its tail by
   cmd_heap_tail_vis *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1 ->
(* UBSan: tok is non-null and 8-aligned, so the check 0x8b6cc of each load of tok[n] (recorder.c:365) is not
   taken; with the array premise next, also 0x8b6c8 *)
ptok <> 0 -> ptok mod 8 = 0 ->
(* the array of token pointers: in the caller's side-stack frame (verbs_receive's tok[64], class 4, 0x8d950
   `ld s3,40(s1)`), or in a live block that is none of the recorder's. UBSan: either way
   ptok + 8 * ntok < 2 ^ 64 (AR's frame and block facts), so tok + 8n does not wrap for n < ntok and the checks
   0x8b6bc, 0x8b6c8 (with ptok <> 0) and 0x8b774 are not taken *)
(afobj SEGS B ly S W mem ptok (8 * Z.of_nat (length toks)) \/
 (in_blockA (ablocks B ly S) ptok (8 * Z.of_nat (length toks)) /\
  Forall (fun qk => iv_apart ptok (8 * Z.of_nat (length toks)) (fst qk) (snd qk)) O)) ->
length ps = length toks ->
(* each pointer, an 8-byte word read as a 64-bit value *)
(forall i p, nth_error ps i = Some p -> 0 <= p < 2 ^ 64 /\ aval_mem (rdW W mem) (ptok + 8 * Z.of_nat i) 8 p) ->
(* every token is a string of its own inside a live block that is none of the recorder's (verbs_receive's tokens
   are words of its strdup copy, so the block form; the strlen and strcat wrappers read each tail by
   cmd_heap_tail_vis), and the joined list fits one message (plain sup_host_setting_c.v:59-60) *)
Forall2 (fun p w => in_blockA (ablocks B ly S) p (Z.of_nat (length w) + 1) /\
  Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) O /\
  astr_atR (rdW W mem) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1) ps toks ->
hs_words_len toks <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: this call's class-0 frame (count_cid 0 < fs_frames 0); no callee takes
   one *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_HOST_SETTING R <= EV_MAX -> blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks <= LIVE_MAX ->
mo_ok MT S (XM_SUP_HOST_SETTING R line toks) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_host_setting) regs mem md)
(apost_baseF SEGS B SUP_HOST_SETTING_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_HOST_SETTING R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded with the canonical line, the token count and
    the joined words, and folded into g_rec.host_settings (plain lib/Prog/sup_host_setting_c.v:31-45) *)
 rec_repA B ly' S' (rdW W' mem') (sup_host_setting_m R line toks) O' /\
 (* the recorder owns what it owned plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks /\
 mo_le MT S S' (XM_SUP_HOST_SETTING R line toks))).
End e.
End f.
End d.
