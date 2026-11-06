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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 38 of its 64 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of sup_resp on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/sup_resp_c.v:24-46 (a fresh block that holds `resp code` and its terminator, :36-41; the recorder kept,
   `fst (sup_resp_m R code)`, :42) and the model lib/Prog/RecModel.v:87 (`sup_resp_m R code = (R, resp code)`),
   lib/Prog/RecFacts.v:122 (`resp`). The B twin of lib/A/Prog/sup_resp_c.v, re-derived on B's code: B inlines
   xstrdup (A calls it) and calls the program function xmalloc (B only, lib/B/Prog/xmalloc_c.v) inside it.
   sup_resp(code) (recorder.c:279-285) prints "resp <code>" with snprintf(buf, 32, "resp %d", code) into buf[32] of
   its own side-stack frame and returns xstrdup(buf), here the inlined strlen (recorder.c:99), xmalloc(|buf| + 1)
   and memcpy of |buf| + 1 bytes (:101). It writes nothing the caller owns (FP = []).

   Addresses (B's disassembly): entry BASE + AF_sup_resp = 0x8a188. 132 instructions, no inline ASan check,
   no loop on the walked path (the one CFG loop is the real-stack probe of the fallback branch), a 96-byte real
   frame realigned by `andi sp,sp,-32` (0x8a1b8) and a class-1 side-stack frame (`__asan_stack_malloc_1` 0x3fac8 at
   0x8a1e4, request 96 bytes, buf at frame + 32; shadow f1 f1 f1 f1 | 00 00 00 00 | f3 f3 f3 f3; released inline:
   magic 0x45e0360e at frame + 0 (0x8a2dc), shadow f5, the flag byte through frame + 120, 0x8a328-0x8a32c, cgif's
   astack_free_law, lib/YG0d.v:309-317); the real-stack fallback 0x8a1fc-0x8a214 and its page probe are not taken
   (a per-binary fact: the use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const
   cell, cgif lib/YG0f.v:193 aso_const_law). Calls: the snprintf wrapper (0x451d0, at 0x8a298; the format
   "resp %d" at 0x21d40), the strlen wrapper (`__interceptor_trampoline_strlen` 0x4517c, at 0x8a2a0), xmalloc
   (0x899b4, at 0x8a2ac), `__asan_memcpy` (0x5767c, at 0x8a2bc). s0 is this call's frame pointer (0x8a1b4
   `addi s0,sp,96`, the entry sp, under which this call saved ra and the caller's s0) at the xmalloc call, so
   xmalloc's frame chain comes from afn_pre (achain_chain_pre, lib/Reusable/YCbq.v:327); no presence of the stack up
   to ly_top is assumed. The stack-protector cells the musl body under the snprintf wrapper compares (RtDefs.v's
   aguard_ok; B's GOT word 0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts); buf's tail word,
   which the strlen wrapper reads, lies inside buf (|resp code| <= 16 < 32, RecFacts.v:124), an object of the live
   side-stack frame.
   M: B's function table gives 16496 = 96 + xmalloc's 16400 (without the realignment's 16).
   UBSan: 0 trap sites (B's trap-site summary; the trap exclusion table has no row for this function), no `unimp`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 96-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0 at
   the entry, afn_pre's astk_ok), and the deepest callee: the side-stack entry's, the strlen wrapper's and
   __asan_memcpy's windows (ESTACK), the snprintf wrapper's (3 * ESTACK, the measured 6,672 bytes below the
   trampoline's entry sp), xmalloc's own need *)
Definition SUP_RESP_STK : Z := 96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) XMALLOC_STK).
(* one allocator event: xmalloc's malloc; the side-stack frame spends none *)
Definition EV_SUP_RESP : Z := EV_XMALLOC.
(* the live bytes the call adds: the copy of resp code and its terminator, at most 17 bytes (RecFacts.v:124
   resp_length) *)
Definition LIVE_SUP_RESP (code : Z) : Z := LIVE_XMALLOC (Z.of_nat (length (resp code)) + 1).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xmalloc's block for the copy of resp code *)
Definition XM_SUP_RESP (code : Z) : Z := XM_XMALLOC MT (Z.of_nat (length (resp code)) + 1).
(* the callee's contract, the runtime entries with this tree's and cgif's names, and the bridge for the "resp %d"
   format's address *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_resp_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (code : Z),
afn_pre SEGS B SUP_RESP_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for one more side-stack frame of class 1 (count_cid 1 < fs_frames 1) *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image; the format "resp %d" is RO_lit_21d40 *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
st_nev S + EV_SUP_RESP <= EV_MAX -> blocks_bytes S + LIVE_SUP_RESP code <= LIVE_MAX ->
mo_ok MT S (XM_SUP_RESP code) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_resp) regs mem md)
(apost_baseF SEGS B SUP_RESP_STK [] regs ly S W mem md EV_SUP_RESP
(fun ly' S' W' regs' mem' md' => exists q,
 let n := Z.of_nat (length (resp code)) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, n) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q n (fst qk) (snd qk)) (ablocks B ly S) /\
 (* the text resp code (= snd (sup_resp_m R code) for every R, RecModel.v:87) in the block form reply asks, and
    the recorder untouched (plain sup_resp_c.v:41-42) *)
 In (q, n) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP code))).
End e.
End f.
End d.
