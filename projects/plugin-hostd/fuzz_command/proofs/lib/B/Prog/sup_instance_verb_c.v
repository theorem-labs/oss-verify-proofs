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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 61 of its 86 lines of code are new or changed and 127 lines of the source are left out. *)
(* The contract of sup_instance_verb on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92); the side-stack frame as cgif's class-0 users take it
   (aj_stack_malloc_atS, lib/YC85.v:292-310). Functional content: fuzz_command's own released plain contract
   lib/Prog/sup_instance_verb_c.v:18-65 and the model lib/Prog/RecModel.v:135-136 (`sup_instance_verb_m`,
   `rec_stub` of the REC id 7 with the canonical line and the ledger number, and the shape rec_shape_of gives the
   line's first word, RecModel.v:68, :73-75). The B twin of lib/A/Prog/sup_instance_verb_c.v, re-derived on B's
   code, which differs from A's: B calls record() and arg_s() (lib/B/Prog/record_c.v, arg_s_c.v) where A inlined
   record(), and inlines arg_i (B has no arg_i), so this function owns arg_i's class-0 side-stack frame and its
   snprintf; it calls answer and releases its frame after answer returns (no tail jump, as A's had).
   sup_instance_verb (recorder.c:379-388) records the call with record(7) (a new slot of g_rec.calls, or
   record.spill with its arguments freed when the table already holds 16 calls), adds the canonical line with
   arg_line, prints the ledger with snprintf(b, 16, "%d", ledger) (format at 0x21f40) into b[16] of its class-0
   side-stack frame (arg_i inlined, recorder.c:235-241) and adds b with arg_s, steps past the leading spaces and
   tabs with the strspn wrapper, measures the verb with the strcspn wrapper (both against " \t" at 0x21da0), asks
   rec_shape_of for the verb's reply shape, and calls answer with changes = 1.
   The frame: `__asan_stack_malloc_0` (request 64 bytes, 0x8b960; this port's decision: the side-stack branch only, the
   use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const cell, so the
   real-stack fallback 0x8b978-0x8b990 and its page probe are not taken), shadow f1 f1 f1 f1 | f8 f8 | f3 f3 with b
   (frame + 32, 16 bytes) unpoisoned (00) for the snprintf and arg_s calls (0x8ba08, recorder.c:237) and poisoned
   again (f8) after them (0x8ba34), released inline after answer (magic 0x45e0360e at frame + 0, shadow f5, flag
   byte through frame + 56: 0x8ba90-0x8bacc, cgif's astack_free_law, lib/YG0d.v:309-317). The stack-protector
   cells the musl bodies under the snprintf, strspn and strcspn wrappers compare (aguard_ok, lib/B/Rt/RtDefs.v; B's GOT
   word 0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts); the separators' aread_ok and tail are
   cmd_aread_ok_chk and cmd_tail_vis; the line's tail (read by the strspn, strcspn and arg_line's strlen wrappers)
   comes from its heap block by cmd_heap_tail_vis.
   UBSan (the trap-site tables' rows of this function): 2 check sites, both of the pointer `line +=
   strspn(line, " \t")` (recorder.c:386), both branching to the `unimp` at 0x8bb28: 0x8ba50 `bltu s4,s3` (the sum
   wrapped below line) and 0x8ba60 `beqz a0` (line and the sum are not both non-null or both null). Neither is
   taken: the strspn wrapper returns at most |line| (astrspn_realizes, lib/B/Rt/RtString.v), and the line premise below
   puts [pl, pl + |line| + 1) inside a live block, so 0 < pl and pl + |line| < 2 ^ 64 (AR's block facts).

   Addresses (B, the disassembly of sup_instance_verb): entry BASE + AF_sup_instance_verb = 0x8b8f8. 141 instructions,
   no inline ASan check (the image's function table: 0 reports; the slot's checks are record's, arg_line's and arg_s's),
   no loop on the walked path (the one CFG loop is the real-stack probe of the fallback branch), a 96-byte real frame
   realigned by `andi sp,sp,-32` (0x8b930) and a class-0 side-stack frame (0:64). Calls: __asan_stack_malloc_0
   (0x3f954, at 0x8b960), record (0x8a728, at 0x8b9f8), arg_line (0x8b128, at 0x8ba04), the snprintf wrapper
   (0x451d0, at 0x8ba24), arg_s (0x8a820, at 0x8ba30), the strspn wrapper (0x45194, at 0x8ba48), the strcspn wrapper
   (0x45198, at 0x8ba70), rec_shape_of (0x896d4, at 0x8ba7c), answer (0x8aa10, at 0x8ba8c). s0 is this call's frame
   pointer (0x8b92c `addi s0,sp,96`, the entry sp) at every call: the prologue saved ra at s0 - 8 and the caller's
   s0 at s0 - 16, so each callee's frame chain for s0 is that record on top of afn_pre's chain, and achain_chain_pre
   (YCbq.v:327) gives the runtime entries' chain_pre; no presence of the stack up to ly_top is assumed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_line_c arg_s_c rec_shape_of_c answer_c.
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
(* the stack this call needs: its own 96-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0
   at the entry, afn_pre's astk_ok), and the deepest callee, all reached with the frame up: the side-stack entry's
   window (ESTACK), the snprintf wrapper's (3 * ESTACK, measured), the strspn and strcspn wrappers'
   (2 * ESTACK, astrspn_realizes of lib/B/Rt/RtString.v), record's, arg_line's, arg_s's, rec_shape_of's and answer's own
   needs. M: the image's function table gives 16704 = 96 + answer's 16608 (without the realignment's 16) *)
Definition SUP_INSTANCE_VERB_STK : Z :=
  96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max (2 * ESTACK)
    (Z.max RECORD_STK (Z.max ARG_LINE_STK (Z.max ARG_S_STK (Z.max REC_SHAPE_OF_STK ANSWER_STK)))))).
(* the allocator events: the frees of record()'s spill arm, the canonical line, arg_s's copy of the printed
   ledger, and answer's free of the old answer with the two copies of the reply text; the side-stack frame spends
   none *)
Definition EV_SUP_INSTANCE_VERB (R : rstate) : Z := EV_RECORD R + EV_ARG_LINE + EV_ARG_S + EV_ANSWER.
(* the live bytes the call adds at its peak: the two recorded arguments and answer's two copies *)
Definition LIVE_SUP_INSTANCE_VERB (R : rstate) (line : list byte) (ledger : Z) : Z :=
  LIVE_ARG_LINE line + LIVE_ARG_S (Some (dec ledger)) + LIVE_ANSWER (snd (sup_instance_verb_m R line ledger)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, the two recorded arguments, and answer's *)
Definition XM_SUP_INSTANCE_VERB (R : rstate) (line : list byte) (ledger : Z) : Z :=
  XM_RECORD MT R + XM_ARG_LINE MT line + XM_ARG_S MT (Some (dec ledger)) +
  XM_ANSWER MT (snd (sup_instance_verb_m R line ledger)).
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge from the image's
   object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_instance_verb_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pl ledger : Z) (line : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_INSTANCE_VERB_STK ly S W regs mem md ch -> (* astack_rd when it lands *)
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the format "%d" (0x21f40) of the inlined arg_i, the
   separators " \t" the strspn and strcspn wrappers read (0x21da0), the verb names and reply shapes rec_shape_of
   walks, and what record, arg_line, arg_s and answer read; the GOT words of the use-after-return flag (0xa5fa8)
   and the shadow base (0xa5f50) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 ->
getr regs 11 = w64 ledger -> -2 ^ 31 <= ledger < 2 ^ 31 ->
(* the line: its one caller, verbs_receive, passes its strndup'd line (0x8d8a0 `ld s2,56(s1)`, the block of
   verbs.c:219), so it is a string in a live heap block that is none of the recorder's (record() and answer free
   the recorder's own blocks during the call); arg_line takes it in this form. The verb rec_shape_of looks up is
   the first word of the line, past the spaces and tabs strspn counts, and strcspn long (recorder.c:386-387), so
   its bytes are bytes of the line, in the same block. UBSan: this block membership (0 < pl, and
   pl + |line| + 1 within a live block, so below 2 ^ 64) with strspn's result <= |line| excludes the trap sites
   0x8ba50 and 0x8ba60 of `line += strspn(line, " \t")` *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) -> astr_atR (rdW W mem) pl line ->
Z.of_nat (length line) + 1 <= LMAX + 1 ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
rec_repA B ly S (rdW W mem) R O ->
(* room for two more side-stack frames: this call's class-0 frame is live while answer takes its class-7 frame
   (answer's pre asks length (frames S) <= 8 of the state with this frame added) *)
Z.of_nat (length (frames S)) <= 7 ->
st_nev S + EV_SUP_INSTANCE_VERB R <= EV_MAX -> blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger <= LIVE_MAX ->
mo_ok MT S (XM_SUP_INSTANCE_VERB R line ledger) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_instance_verb) regs mem md)
(apost_baseF SEGS B SUP_INSTANCE_VERB_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_INSTANCE_VERB R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_instance_verb_c.v:28-50) *)
 sup_instance_verb_m R line ledger = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the caller's copy of the reply text: a block of its own, which the recorder does not own and which is none of
    the blocks that were live and none of the recorder's (record()'s spill arm and answer free recorder blocks,
    whose address and size malloc may hand out again) *)
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (* every block that was live and none of the recorder's is still live, and apart from the copy *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger /\
 mo_le MT S S' (XM_SUP_INSTANCE_VERB R line ledger))).
End e.
End f.
End d.
