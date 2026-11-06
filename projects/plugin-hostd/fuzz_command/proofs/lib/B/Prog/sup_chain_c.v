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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 69 of its 94 lines of code are new or changed and 127 lines of the source are left out. *)
(* The contract of sup_chain on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92); the side-stack frame as cgif's class-1 users take it
   (aj_stack_malloc_atS, lib/YC85.v:292-310). Functional content: fuzz_command's own released plain contract
   lib/Prog/sup_chain_c.v:18-70 and the model lib/Prog/RecModel.v:101-102 (`sup_chain_m`, `rec_stub` of the REC id
   17 with the instance number, the member count and the member list `dec_list ids`, RecModel.v:70-71, :73-75).
   The B twin of lib/A/Prog/sup_chain_c.v, re-derived on B's code, which differs from A's: B calls record(),
   xmalloc() and arg_s() (lib/B/Prog/record_c.v, xmalloc_c.v, arg_s_c.v) where A inlined record() and xmalloc and
   called xstrdup, and inlines arg_i twice (B has no arg_i), so this function owns a class-1 side-stack frame with
   both of arg_i's buffers and their snprintf calls; it calls answer and releases its frame after answer returns
   (no tail jump, as A's had).
   sup_chain (recorder.c:464-479) records the call with record(17) (a new slot of g_rec.calls, or record.spill with
   its arguments freed when the table already holds 16 calls), allocates a text of 12n + 1 bytes for the member list
   with xmalloc, prints the instance number with snprintf(b, 16, "%d", id) into the buffer at frame + 64 and adds it
   with arg_s, prints the member count the same way into the buffer at frame + 32 and adds it with arg_s (format
   "%d" at 0x21f40; arg_i inlined, recorder.c:235-241), prints the members into the text one at a time with the
   sprintf wrapper ("%d" for the first, " %d" at 0x21f20 for the others), adds the text with arg_s and frees it,
   asks rec_shape_of for the shape the verb "chain" declares (the image string at 0x21f60, 5 bytes) and calls
   answer with changes = 1.
   The frame: `__asan_stack_malloc_1` (request 96 bytes, 0x8c23c; this port's decision: the side-stack branch
   only, the use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const cell, so the
   real-stack fallback 0x8c250-0x8c268 and its page probe are not taken), shadow f1 f1 f1 f1 | f8 f8 | f2 f2 | f8 f8
   | f3 f3 with each buffer unpoisoned (00) around its snprintf and arg_s calls (0x8c314 and 0x8c344,
   recorder.c:237) and poisoned again (f8) after them (0x8c34c and 0x8c378), released inline after answer (magic
   0x45e0360e at frame + 0, shadow f5, flag byte through frame + 120: 0x8c47c-0x8c4e4, cgif's astack_free_law,
   lib/YG0d.v:309-317). The stack-protector cells the musl bodies under the snprintf and sprintf wrappers compare
   (RtDefs.v's aguard_ok; B's GOT word 0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts).
   UBSan (the UBSan trap-site tables' rows of this function): 4 check sites, all of the loop line
   `o += sprintf(list + o, k ? " %d" : "%d", ids[k])` (recorder.c:475), all branching to the `unimp` at 0x8c55c:
   0x8c3d0 `bltu s2,s5` (~list < o: list + o wraps), 0x8c3e4 `bltu s8,a0` (ids + 4k wrapped below ids), 0x8c3f0
   `beqz a0` (ids and ids + 4k are not both non-null or both null), 0x8c3f4 `beqz s9` (ids is null or not 4-aligned
   for the 4-byte load of ids[k]). None is taken: 0x8c3f4 by `pids <> 0` and `pids mod 4 = 0` below; 0x8c3e4 and
   0x8c3f0 by the member array premise (a live side-stack frame object or a live block of 4n bytes, so
   pids + 4n < 2 ^ 64 by AR's frame and block facts) with pids <> 0; 0x8c3d0 because o is the length of the text
   printed so far, at most 12k < 12n + 1 (each member a 32-bit int, the Forall premise below, prints in at most 11
   bytes, 12 with its space), and the text is xmalloc's fresh block of 12n + 1 bytes, which lies below 2 ^ 64.

   Addresses (B, from its disassembly): entry BASE + AF_sup_chain = 0x8c1c4. 235 instructions, 2 (store1:1 load4:1)
   inline checks (list[0] = 0 at 0x8c38c and ids[k] at 0x8c404; the slot's checks are record's and arg_s's), one
   loop (one pass per member, at most 62: 0x8c3d0-0x8c428), a 192-byte real frame realigned by `andi sp,sp,-32`
   (0x8c204) and a class-1 side-stack frame (1:96). The error path of each check (a call of `__asan_report_*`) is
   not reached: list[0] is in the block xmalloc just returned and the member array is in a live block or in a
   side-stack frame. Calls: __asan_stack_malloc_1 (0x3fac8, at 0x8c23c), record (0x8a728, at 0x8c2f4), xmalloc
   (0x899b4, at 0x8c30c), the snprintf wrapper (0x451d0, at 0x8c334 and 0x8c364), arg_s (0x8a820, at 0x8c340,
   0x8c374 and 0x8c450), the sprintf wrapper (0x451cc, at 0x8c414), the free wrapper (0x589cc, at 0x8c458),
   rec_shape_of (0x896d4, at 0x8c468), answer (0x8aa10, at 0x8c478). s0 is this call's frame pointer (0x8c200
   `addi s0,sp,192`, the entry sp) at every call: the prologue saved ra at s0 - 8 and the caller's s0 at s0 - 16, so
   each callee's frame chain for s0 is that record on top of afn_pre's chain, and achain_chain_pre (YCbq.v:327)
   gives the runtime entries' chain_pre; no presence of the stack up to ly_top is assumed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c xmalloc_c arg_s_c rec_shape_of_c answer_c.
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
(* the stack this call needs: its own 192-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0
   at the entry, afn_pre's astk_ok), and the deepest callee, all reached with the frame up: the side-stack entry's
   window (ESTACK), the snprintf and sprintf wrappers' (3 * ESTACK, measured), the free wrapper's
   (ASTACK, cgif lib/YG0d.v:17), record's, xmalloc's, arg_s's, rec_shape_of's and answer's own needs.
   M: the image's function table gives 16800 = 192 + answer's 16608 (without the realignment's 16) *)
Definition SUP_CHAIN_STK : Z :=
  192 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max ASTACK
    (Z.max RECORD_STK (Z.max XMALLOC_STK (Z.max ARG_S_STK (Z.max REC_SHAPE_OF_STK ANSWER_STK)))))).
(* the allocator events: the frees of record()'s spill arm, xmalloc's list text, arg_s's copies of the two
   printed numbers and of the list text, the text's free, and answer's three; the side-stack frame spends none *)
Definition EV_SUP_CHAIN (R : rstate) : Z :=
  EV_RECORD R + EV_XMALLOC + EV_ARG_S + EV_ARG_S + EV_ARG_S + 1 + EV_ANSWER.
(* the live bytes the call adds at its peak: the list text of 12n + 1 bytes, the two numbers, the copy of the list
   text, and answer's two copies of the reply *)
Definition LIVE_SUP_CHAIN (R : rstate) (id : Z) (ids : list Z) : Z :=
  LIVE_XMALLOC (12 * Z.of_nat (length ids) + 1) + LIVE_ARG_S (Some (dec id)) +
  LIVE_ARG_S (Some (dec (Z.of_nat (length ids)))) + LIVE_ARG_S (Some (dec_list ids)) +
  LIVE_ANSWER (snd (sup_chain_m R id ids)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, the list text and its free, the three recorded arguments, and
   answer's *)
Definition XM_SUP_CHAIN (R : rstate) (id : Z) (ids : list Z) : Z :=
  XM_RECORD MT R + XM_XMALLOC MT (12 * Z.of_nat (length ids) + 1) + XM_ARG_S MT (Some (dec id)) +
  XM_ARG_S MT (Some (dec (Z.of_nat (length ids)))) + XM_ARG_S MT (Some (dec_list ids)) + mo_free MT +
  XM_ANSWER MT (snd (sup_chain_m R id ids)).
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge from the image's
   object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASPRINTF : forall fx0 : YK11.FPState, @asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa6bf8 0x604158.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_chain_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch -> (* astack_rd when it lands *)
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the two formats the inlined arg_i and sprintf print with,
   "%d" (0x21f40) and " %d" (0x21f20), the verb name "chain" (0x21f60, 5 bytes), and what record, arg_s,
   rec_shape_of and answer read; the GOT words of the use-after-return flag (0xa5fa8) and the shadow base
   (0xa5f50) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 11 = w64 pids -> 0 <= pids < 2 ^ 64 -> getr regs 12 = w64 (Z.of_nat (length ids)) ->
(* the caller (chain_words, 0x8dd54) passes 1 to 62 members, each a 32-bit int (plain sup_chain_c.v:34), so the
   list text is at most 12 * 62 + 1 = 745 bytes, xmalloc's size premise holds, and (UBSan) the printed length o
   stays below 12n + 1, so list + o does not wrap: the check 0x8c3d0 is not taken *)
(1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
(* UBSan: ids is non-null and 4-aligned, so the check 0x8c3f4 of each load of ids[k] (recorder.c:475) is not
   taken; with the array premise next, also 0x8c3f0 *)
pids <> 0 -> pids mod 4 = 0 ->
(* the array of members: in the caller's side-stack frame (chain_words' ids[64], class 3, passed in s6 at
   0x8dd50), or in a live block that is none of the recorder's (record() and answer free the recorder's own
   blocks). UBSan: either way pids + 4n < 2 ^ 64 (AR's frame and block facts), so ids + 4k does not wrap for
   k < n and the checks 0x8c3e4 and 0x8c3f0 (with pids <> 0) are not taken *)
(afobj SEGS B ly S W mem pids (4 * Z.of_nat (length ids)) \/
 (in_blockA (ablocks B ly S) pids (4 * Z.of_nat (length ids)) /\
  Forall (fun qk => iv_apart pids (4 * Z.of_nat (length ids)) (fst qk) (snd qk)) O)) ->
abytes_atR (rdW W mem) pids (concat (map le32 ids)) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for two more side-stack frames: this call's class-1 frame is live while answer takes its class-7 frame
   (answer's pre asks length (frames S) <= 8 of the state with this frame added) *)
Z.of_nat (length (frames S)) <= 7 ->
st_nev S + EV_SUP_CHAIN R <= EV_MAX -> blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CHAIN R id ids) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md)
(apost_baseF SEGS B SUP_CHAIN_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_CHAIN R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_chain_c.v:50-70) *)
 sup_chain_m R id ids = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the caller's copy of the reply text: a block of its own, which the recorder does not own, and none of the
    blocks the call kept (record()'s spill arm and answer free recorder blocks, whose addresses malloc may reuse) *)
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (* every block that was live and none of the recorder's is still live, and apart from the copy *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN R id ids /\
 mo_le MT S S' (XM_SUP_CHAIN R id ids))).
End e.
End f.
End d.
