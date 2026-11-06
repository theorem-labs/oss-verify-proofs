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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 49 of its 75 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of sup_remove on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92); the side-stack frame as cgif's
   class-0 users take it (aj_stack_malloc_atS, lib/YC85.v:292-310). Functional content: fuzz_command's own released
   plain contract lib/Prog/sup_remove_c.v:24-52 and the model lib/Prog/RecModel.v:118-119
   (`sup_remove_m R id = rec_stub R REC_REMOVE [dec id] REC_MOD_HOST_SHAPE true`, with rec_stub :73-75, rec_record
   :38-39, rec_answer :47-50). The B twin of lib/A/Prog/sup_remove_c.v, re-derived on B's code, which differs from
   A's: B calls record() and arg_s() (lib/B/Prog/record_c.v, arg_s_c.v) where A inlined record(), and inlines arg_i
   (B has no arg_i), so this function owns arg_i's class-0 side-stack frame and its snprintf; it calls answer and
   releases its frame after answer returns (no tail jump, as A's had).
   sup_remove(id) (recorder.c:323-329) records the call REC_REMOVE with record(2) (a new slot of g_rec's table, or,
   when the table holds 16 calls, record.spill after rec_calls_free(&spill, 1) freed the spill's old arguments),
   prints id with snprintf(b, 16, "%d", id) (format at 0x21f40, RO_lit_21f40) into b[16] of its class-0 side-stack
   frame (arg_i inlined, recorder.c:235-241) and adds b with arg_s, then calls answer(c, REC_MOD_HOST_SHAPE, 1)
   (the shape is the literal "resp 0" at 0x21d20, RO_lit_21d20) and returns answer's result.
   The frame: `__asan_stack_malloc_0` (request 64 bytes, 0x8b2b8; by design: the side-stack branch only,
   the use-after-return flag read through the GOT word 0xa5fa8 at 0xb0c40 is the record's const cell, so the
   real-stack fallback 0x8b2d0-0x8b2e8 and its page probe are not taken), frame + 8 the descriptor "1 32 16 7
   b.i:237" (RO_lit_15923), shadow through the base read from the GOT word 0xa5f50 (TL's PALib): f1 f1 f1 f1 |
   f8 f8 | f3 f3 with b (frame + 32, 16 bytes) unpoisoned (00) for the snprintf and arg_s calls (0x8b358,
   recorder.c:237) and poisoned again (f8) after them (0x8b384), released inline after answer (magic 0x45e0360e at
   frame + 0, shadow f5, flag byte through frame + 56: 0x8b3a0-0x8b3d8, cgif's astack_free_law,
   lib/YG0d.v:309-317). The stack-protector cells the musl body under the snprintf wrapper compares (RtDefs.v's
   aguard_ok; B's GOT word 0xa6bf8 holds the guard cell 0x604158) are cmd_rec_cells (CmdRecFacts); the format's
   aread_ok and tail are cmd_aread_ok_chk and cmd_tail_vis.
   UBSan: 0 trap sites (the trap-site table; the slot's checks are record's and arg_s's).

   Addresses (B, its disassembly): entry BASE + AF_sup_remove = 0x8b258. 119 instructions, no inline ASan
   check (the function table: 0 reports), no loop on the walked path (the one CFG loop is the real-stack probe of the
   fallback branch), a 96-byte real frame realigned by `andi sp,sp,-32` (0x8b28c) and a class-0 side-stack frame
   (0:64). Calls: __asan_stack_malloc_0 (0x3f954, at 0x8b2b8), record (0x8a728, at 0x8b350), the snprintf wrapper
   (0x451d0, at 0x8b374), arg_s (0x8a820, at 0x8b380), answer (0x8aa10, `jal` at 0x8b39c); `ret` at 0x8b430. s0 is
   this call's frame pointer (0x8b288 `addi s0,sp,96`, the entry sp, with the caller's s0 at s0 - 16 and ra at
   s0 - 8) at every program call: its calls' frame chains come from afn_pre's chain (achain_push at the frame
   pointer, then achain_chain_pre, YCbq.v:327). No presence of the stack up to ly_top is
   assumed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c.
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
   at the entry, afn_pre's astk_ok), and the deepest callee, all reached with the frame up (answer is called, not
   tail-jumped): the side-stack entry's window (ESTACK), the snprintf wrapper's (3 * ESTACK,
   measured), record's, arg_s's and answer's own needs. M: the function table gives 16704 = 96 + answer's 16608
   (without the realignment's 16) *)
Definition SUP_REMOVE_STK : Z :=
96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max RECORD_STK (Z.max ARG_S_STK ANSWER_STK))).
(* the events: record()'s spill arm frees the spill's arguments (EV_RECORD R, CmdRep's rec_spill_frees R: 0 while
   the table holds fewer than 16 calls, recorder.c:210-215), then arg_s's copy of the printed id and answer's; the
   side-stack frame spends none. A function of the recorder state, as ev_calls is (the statements' rule for events). *)
Definition EV_SUP_REMOVE (R : rstate) : Z := EV_RECORD R + EV_ARG_S + EV_ANSWER.
(* the live bytes the call adds: arg_s's copy of dec id and answer's two copies of the text t *)
Definition LIVE_SUP_REMOVE (id : Z) (t : list byte) : Z := LIVE_ARG_S (Some (dec id)) + LIVE_ANSWER t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, then arg_s's and answer's *)
Definition XM_SUP_REMOVE (R : rstate) (id : Z) (t : list byte) : Z :=
XM_RECORD MT R + XM_ARG_S MT (Some (dec id)) + XM_ANSWER MT t.
(* the callees' contracts, the runtime entries with this tree's and cgif's names, and the bridge for the addresses of
   g_rec, record.spill, the format "%d" and the shape "resp 0" *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_remove_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_remove_m R id) in
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry (this function's snprintf call at
   0x8b374 and the one under answer); apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for two more side-stack frames: this call's class-0 frame is live while answer takes its class-7 frame
   (answer's pre asks length (frames S) <= 8 of the state with this frame added); A's tail jump had <= 8 *)
Z.of_nat (length (frames S)) <= 7 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the format "%d" RO_lit_21f40 of the inlined arg_i, the frame descriptor
   RO_lit_15923, the shape "resp 0" RO_lit_21d20, and what record, arg_s and answer read (the format "resp %d"
   RO_lit_21d40, the FNV basis RO_lit_10330). Their read-only position, which answer's astr_argA asks of the shape,
   is cmd_addr_b / cmd_hull_b / cmd_ro_ends by computation; the other conjuncts of its read-only branch are
   cif_ro_unowned. *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE id t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE R id t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O), sup_remove_c.v:37) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_REMOVE R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_m R id = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_remove_c.v:34, :39) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call: a block of O'
    that was live at the entry is a block of O *)
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain sup_remove_c.v:40-47) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (* the caller's copy of the reply text: live after the call; if it was live at the entry it was one of the
    recorder's blocks that record()'s spill arm or answer freed first (the contrapositive freshness form) *)
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE id t /\
 mo_le MT S S' (XM_SUP_REMOVE R id t))).
End e.
End f.
End d.
