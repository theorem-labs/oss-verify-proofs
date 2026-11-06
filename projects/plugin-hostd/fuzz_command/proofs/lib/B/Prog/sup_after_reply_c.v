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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 49 of its 74 lines of code are new or changed and 127 lines of the source are left out. *)
(* The contract of sup_after_reply on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92); the side-stack frame as cgif's
   class-0 users take it (aj_stack_malloc_atS, lib/YC85.v:292-310). Functional content: fuzz_command's own released
   plain contract lib/Prog/sup_after_reply_c.v:17-55 and the model lib/Prog/RecModel.v:165-166
   (`sup_after_reply_m`, which is `rec_record` of the REC id 19 alone: a checkpoint of what a preset or patch
   changed, so it writes the call down and changes no digest). The B twin of lib/A/Prog/sup_after_reply_c.v,
   re-derived on B's code, which differs from A's: B calls record() and arg_s() (lib/B/Prog/record_c.v,
   arg_s_c.v) where A inlined them, and inlines arg_i (B has no arg_i), so this function owns arg_i's class-0
   side-stack frame and its snprintf.
   sup_after_reply (recorder.c:490-496) records the call with record(19) (a new slot of g_rec.calls, or
   record.spill with its arguments freed when the table already holds 16 calls), prints the instance number with
   snprintf(b, 16, "%d", id) (format at 0x21f40) into b[16] of its class-0 side-stack frame (arg_i inlined,
   recorder.c:235-241), adds b and then the verb to the slot with arg_s (each a copy; arg_s itself replaces a
   NULL string by "(null)"), releases its frame and returns. It calls neither answer nor mix_call.
   The frame: `__asan_stack_malloc_0` (request 64 bytes, 0x8c7c0; this port's decision: the side-stack branch only,
   the use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const cell, so the
   real-stack fallback 0x8c7d8-0x8c7f0 and its page probe are not taken), shadow f1 f1 f1 f1 | f8 f8 | f3 f3 with b
   (frame + 32, 16 bytes) unpoisoned (00) for the snprintf and first arg_s calls (0x8c860, recorder.c:237) and
   poisoned again (f8) after them (0x8c88c), released inline after the second arg_s (magic 0x45e0360e at frame + 0,
   shadow f5, flag byte through frame + 56: 0x8c8a0-0x8c8d8, cgif's astack_free_law, lib/YG0d.v:309-317). The
   stack-protector cells the musl body under the snprintf wrapper compares (RtDefs.v's aguard_ok; B's GOT word
   0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts).

   Addresses (B, from its disassembly): entry BASE + AF_sup_after_reply = 0x8c758. 120 instructions, no inline ASan
   check (the image's function table: 0 reports), no loop on the walked path (the one CFG loop is the real-stack probe
   of the fallback branch), a 96-byte real frame realigned by `andi sp,sp,-32` (0x8c790) and a class-0 side-stack frame
   (0:64), 0 UBSan trap sites (the UBSan trap-site table). Calls: __asan_stack_malloc_0 (0x3f954), record (0x8a728, at
   0x8c858), the snprintf wrapper (0x451d0, at 0x8c87c), arg_s (0x8a820, at 0x8c888 with b and at 0x8c89c with the
   verb). s0 is this call's frame pointer (0x8c78c `addi s0,sp,96`, the entry sp) at every call, so its calls'
   frame chains come from afn_pre's chain (achain_push at the frame pointer; achain_chain_pre, YCbq.v:327, gives the
   wrappers' chain_pre); no presence of the stack up to ly_top is assumed. The verb is in s3 (0x8c798 `mv s3,a1`). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c.
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
   window (ESTACK), the snprintf wrapper's (3 * ESTACK, measured), record's and arg_s's own needs.
   M: the image's function table gives 16656 = 96 + record's 16560 (without the realignment's 16) *)
Definition SUP_AFTER_REPLY_STK : Z :=
  96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max RECORD_STK ARG_S_STK)).
(* the allocator events: the frees of record()'s spill arm and arg_s's two copies; the side-stack frame spends
   none *)
Definition EV_SUP_AFTER_REPLY (R : rstate) : Z := EV_RECORD R + EV_ARG_S + EV_ARG_S.
(* the live bytes the call adds: the copies of the two arguments *)
Definition LIVE_SUP_AFTER_REPLY (id : Z) (verb : option (list byte)) : Z :=
  LIVE_ARG_S (Some (dec id)) + LIVE_ARG_S verb.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm and the two copies *)
Definition XM_SUP_AFTER_REPLY (R : rstate) (id : Z) (verb : option (list byte)) : Z :=
  XM_RECORD MT R + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT verb.
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge from the image's
   object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_after_reply_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id pv : Z) (verb : option (list byte)) (R : rstate)
 (O : list (Z * Z)),
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the format "%d" (0x21f40) of the inlined arg_i and what
   record and arg_s read (arg_s's default "(null)" at 0x224c0 on the NULL path, which no caller takes); the GOT
   words of the use-after-return flag (0xa5fa8) and the shadow base (0xa5f50) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 11 = w64 pv -> 0 <= pv < 2 ^ 64 ->
(* verb: its one caller, verbs_receive, passes a token of its strdup'd copy (tok[0]): a string in a live heap
   block that is none of the recorder's (record() frees the spill slot's blocks when the call table is full);
   the tail of its last 8-byte word, which arg_s's strlen wrapper reads, is readable by cmd_heap_tail_vis *)
(exists x, verb = Some x /\
 in_blockA (ablocks B ly S) pv (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pv x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pv (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: this call's class-0 frame (count_cid 0 < fs_frames 0) *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX -> blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY R id verb) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_after_reply) regs mem md)
(apost_baseF SEGS B SUP_AFTER_REPLY_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_AFTER_REPLY R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded, nothing else changed (plain
    lib/Prog/sup_after_reply_c.v:27-41) *)
 rec_repA B ly' S' (rdW W' mem') (sup_after_reply_m R id verb) O' /\
 (* the recorder owns what it owned, less what record() freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb /\
 mo_le MT S S' (XM_SUP_AFTER_REPLY R id verb))).
End e.
End f.
End d.
