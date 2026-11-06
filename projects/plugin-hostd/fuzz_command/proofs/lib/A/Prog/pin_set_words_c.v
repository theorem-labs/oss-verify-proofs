(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_c.v, with its module paths and module names changed; 51 of its 84 lines of code are new or changed and 40 lines of the source are left out. *)
(* The contract of pin_set_words on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/pin_set_words_c.v:30-62 (the recorder and the return value at :53-54, the block accounting at :56-58)
   and its models lib/Spec/VerbsRun.v:31-38 (pin_set_run, pins_follow) and lib/Spec/Verbs.v:226-235
   (pin_set_words_m).
   The function (L/src/verbs.c:72-91) checks `pin_set <uri> <files> <layout> [verdict=<word>]`: it refuses
   (-902) unless ntok is 4 or 5, strlen(line) <= 4096 and tok[3] is not "-" (the strcmp is inlined into two byte
   compares), and, with five words, unless tok[4] starts with "verdict=" (strncmp, 8 bytes); then
   rc = pins_set(tok[1], tok[2], tok[3], verdict), and when rc = 0 lv2_refusals_forget(NULL). It returns rc.

   Where its arguments live: line is verbs_receive's strndup block (A2), the words are pointers into verbs_receive's
   strdup block `copy` (A3), and tok is verbs_receive's array tok[64] in verbs_receive's class-4 side-stack frame
   (description `2 32 512 7 tok:219 608 8 8 save:219`), hence `afobj` for tok.

   Addresses: entry BASE + AF_pin_set_words = 0x8e66c (M, the pinned image). 94 instructions, frame 48 bytes
   (`addi sp,sp,-48`, no realignment), no loop, no side-stack frame. Six inline checks, each reading the shadow
   byte at (a >> 3) + 0x7fff8000: load8 of tok[3], tok[4], tok[1], tok[2] (in the frame object tok) and load1 of
   tok[3][0], tok[3][1] (in `copy`); the error paths (calls of `__asan_report_load1` / `__asan_report_load8`,
   0x8e7c0-0x8e7e0) are not reached. Calls: the strlen wrapper (0x8e6ac) and the strncmp wrapper (0x8e738)
   (`___interceptor_<f>` through the 4-byte jump `__interceptor_trampoline_<f>`), pins_set (0x8e780) and
   lv2_refusals_forget (0x8e78c). The literal "verdict=" (.str.28, 0x228c0) is RO_lit_228c0 of cmd_ro_ok.
   tok stays in s0 across both program calls (0x8e68c mv s0,a1; 0x8e780 jal pins_set; 0x8e78c jal
   lv2_refusals_forget); tok is in verbs_receive's side-stack frame, below alloc_ceiling, so the frame chain from s0
   is achain's empty case (the survey of s0 at allocating calls). The line and the words are
   heap strings (verbs_receive's strndup
   and strdup blocks): the word tails the strlen wrapper and xstrdup read are readable by cmd_heap_tail_vis
   (lib/A/Prog/CmdRecFacts.v). The stack-protector cells the musl body under answer_code's snprintf wrapper
   compares are cmd_rec_cells; the GOT words the recorder callees load are in cmd_ro_ok (CmdRo.v:433-439).

   Resources: the plain proof's malloc budget, PSW_MALLOCS = 7 allocations of at most PSW_REQ = 8194 bytes
   (lib/Prog/pin_set_words_c.v:18-19), and the events of the two recorder calls. The walk plan
   of pin_set_words proposed this contract; it is followed, with this tree's names
   (atoks_atA, rec_repA) for its proposals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pins_set_c lv2_refusals_forget_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 48-byte frame, and below it the deepest of the two wrappers' windows (strncmp
   asks 2 * ESTACK and strlen ESTACK, RtDefs.v's ecall_pre_stk) and the two recorder callees' own needs *)
Definition PIN_SET_WORDS_STK : Z := 48 + Z.max (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK).
(* pins_set, and lv2_refusals_forget when pins_set accepted (L/src/verbs.c:88-89). Each callee's events depend on
   the recorder state at ITS entry (the spill arm of record(), `rec_spill_frees R`), so lv2_refusals_forget takes
   the state pins_set left: the same two steps the model takes, lib/Spec/VerbsRun.v:31-38 *)
Definition EV_PIN_SET_WORDS (R : rstate) (ln : list byte) (args : list (list byte)) : Z :=
match Verbs.pin_set_words_m ln args with
| Verbs.SPinSet u f l v =>
  let '(R1, r) := pins_set_m R (Some u) (Some f) (Some l) v in
  EV_PINS_SET R + (if r =? 0 then EV_LV2_REFUSALS_FORGET R1 else 0)
| _ => 0
end.
(* the plain proof's budget (lib/Prog/pin_set_words_c.v:18-19): 7 allocations of at most 8194 bytes *)
Definition PIN_SET_WORDS_MALLOCS : Z := 7.
Definition PIN_SET_WORDS_REQ : Z := 8194.
Definition LIVE_PIN_SET_WORDS : Z := PIN_SET_WORDS_MALLOCS * PIN_SET_WORDS_REQ.
(* the recorder statics the two callees write: g_rec and record.spill *)
Definition PIN_SET_WORDS_PG : list (Z * Z) := [(A_G_REC, A_G_REC + REC_SIZE); (A_REC_SPILL, A_REC_SPILL + SC_SIZE)].
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter: each of its allocator events (EV_PIN_SET_WORDS, mallocs and frees) charged the largest allocation and
   a free, verbs_receive's per-event form, so verbs_receive's bound dominates it on every path; the refusal paths
   make no allocator event (EV = 0; checked against Verbs.v:226-235: each refusal is decided before
   pins_set at 0x8e780 and lv2_refusals_forget at 0x8e78c, the only allocating calls) *)
Definition XM_PIN_SET_WORDS (R : rstate) (ln : list byte) (args : list (list byte)) : Z :=
EV_PIN_SET_WORDS R ln args * (mo_malloc MT PIN_SET_WORDS_REQ + mo_free MT).
(* the callees' contracts, never restated *)
Hypothesis PINS_SET : forall fx0 : YK11.FPState, @tpins_set_spec fx0 rc SK PI B MT.
Hypothesis LV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
(* the wrappers it calls, at the listing's call targets *)
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Definition tpin_set_words_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (line nl tok ntok cb ncb : Z) (T : list byte)
  (ptrs : list Z) (tks : list (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B PIN_SET_WORDS_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 line -> 0 <= line < 2 ^ 64 -> getr regs 11 = w64 tok -> 0 <= tok < 2 ^ 64 ->
getr regs 12 = w64 ntok ->
(* the trimmed line: verbs_receive's strndup block, none of the recorder's (plain :36-38) *)
In (line, nl) (ablocks B ly S) -> ~ In (line, nl) O ->
astr_atR (rdW W mem) line T -> Z.of_nat (length T) + 1 <= nl ->
(* the words: tok[0..ntok) in verbs_receive's side-stack frame, each word in the block `copy`, none of the
   recorder's (plain :39-43) *)
afobj SEGS B ly S W mem tok (8 * ntok) ->
atoks_atA (rdW W mem) tok ptrs tks cb ncb -> In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
ntok = Z.of_nat (length tks) -> 1 <= ntok <= 64 -> nth_error tks 0 = Some Verbs.Lit.verb_pin_set ->
(* the recorder (plain :44); the message's two recorder calls fit in its 16-call table (no spill) *)
rec_repA B ly S (rdW W mem) R O -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
(length (r_calls R) + 2 <= 16)%nat ->
(* the constants the recorder callees load, the literal "verdict=", that they are in the read-only range (pins_set
   and lv2_refusals_forget ask it), and the bridge from the listing's object atoms to their addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* room for the callees' side-stack frames *)
Z.of_nat (length (frames S)) <= 5 ->
st_nev S + EV_PIN_SET_WORDS R T (tl tks) <= EV_MAX -> blocks_bytes S + LIVE_PIN_SET_WORDS <= LIVE_MAX ->
mo_ok MT S (XM_PIN_SET_WORDS R T (tl tks)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_pin_set_words) regs mem md)
(apost_baseF SEGS B PIN_SET_WORDS_STK (PIN_SET_WORDS_PG ++ ablocks_fp O) regs ly S W mem md
(EV_PIN_SET_WORDS R T (tl tks))
(fun ly' S' W' regs' mem' md' =>
 let '(R', r) := VerbsRun.pin_set_run R T (tl tks) in
 exists O' : list (Z * Z),
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder's new blocks are fresh; every block not the recorder's is kept (plain :56-58) *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_PIN_SET_WORDS /\
 mo_le MT S S' (XM_PIN_SET_WORDS R T (tl tks)))).
End e.
End f.
End d.
