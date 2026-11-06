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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 54 of its 80 lines of code are new or changed and 126 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/answer_c.v; 37 of its 74 lines of code are new or changed and 43 lines of the source are left out. *)
(* The contract of sup_broadcast on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92). Functional content: fuzz_command's own
   released plain contract lib/Prog/sup_broadcast_c.v:17-60 (sup_broadcast_sizes :17-18, sup_broadcast_ret :27-48,
   the contract :50-60) and the model lib/Prog/RecModel.v:128-129 (`sup_broadcast_m R line = rec_stub R
   REC_BROADCAST [canon line] REC_MOD_HOST_SHAPE true`, with rec_stub :73-75, rec_record :38-39, rec_answer :47-50).
   The B twin of lib/A/Prog/sup_broadcast_c.v, re-derived on B's code, which differs from A's: B calls record()
   (lib/B/Prog/record_c.v) where A inlined it.
   sup_broadcast(line) (recorder.c:347-353) records the call REC_BROADCAST with record(5) (a new slot of g_rec's
   table, or, when the table holds 16 calls, record.spill after rec_calls_free(&spill, 1) freed the spill's old
   arguments), appends arg_line(c, line), restores its frame and tail-calls answer(c, REC_MOD_HOST_SHAPE, 1)
   (`j answer`, 0x8b538; the shape is the literal "resp 0" at 0x21d20, RO_lit_21d20).

   Addresses (B, from its disassembly): entry BASE + AF_sup_broadcast = 0x8b4f0. 19 instructions, a 32-byte real frame
   (ra, s0, s1), no side-stack frame, no inline ASan check (the image's function table: 0 reports; the slot's checks
   are record's, arg_line's and answer's), no loop, 0 UBSan trap sites (the UBSan trap-site table). Calls: record
   (0x8a728, `jal` at 0x8b508), arg_line (0x8b128, `jal` at 0x8b514), and the tail jump to answer (0x8aa10, `j` at
   0x8b538) after the frame is released, so answer runs at this function's entry stack pointer. s0 holds the line
   pointer pl (`mv s0,a0` 0x8b500) at both program calls and s1 the slot c (`mv s1,a0` 0x8b50c) after record. The line
   is a heap block (the line premise: inside a live block), below alloc_ceiling, so the frame chain from s0 at record
   and arg_line is achain's empty case; at the tail jump s0 is the caller's again, so answer's chain is afn_pre's
   entry chain (achain_chain_pre, YCbq.v:327; the survey of s0 at the allocating call sites). No presence of the stack
   up to ly_top is assumed. The stack-protector GOT word 0xa6bf8 and guard cell 0x604158, which the snprintf wrapper
   under answer reads (RtDefs.v's aguard_ok), come from CmdRecFacts' cmd_rec_cells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_line_c answer_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame (no realignment) above the deeper of record and arg_line;
   answer runs at the entry sp after the tail call, so its need is taken beside the frame. M: the image's function
   table gives 16608 = answer's 16608 (32 + record's 16560 = 16592 is below it) *)
Definition SUP_BROADCAST_STK : Z := Z.max (32 + Z.max RECORD_STK ARG_LINE_STK) ANSWER_STK.
(* the events: record()'s spill arm frees the spill's arguments (EV_RECORD R, CmdRep's rec_spill_frees R: 0 while
   the table holds fewer than 16 calls, recorder.c:210-215), then arg_line and answer. A function of the recorder
   state, as ev_calls is (this port's decision). *)
Definition EV_SUP_BROADCAST (R : rstate) : Z := EV_RECORD R + EV_ARG_LINE + EV_ANSWER.
(* the live bytes the call adds: the argument and answer's two copies of the text t (plain sup_broadcast_sizes) *)
Definition LIVE_SUP_BROADCAST (line t : list byte) : Z := LIVE_ARG_LINE line + LIVE_ANSWER t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, then arg_line's and answer's *)
Definition XM_SUP_BROADCAST (R : rstate) (line t : list byte) : Z :=
XM_RECORD MT R + XM_ARG_LINE MT line + XM_ANSWER MT t.
(* the callees' contracts, and the bridge for the addresses of g_rec, record.spill and the shape "resp 0" *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_broadcast_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pl : Z) (line : list byte) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_broadcast_m R line) in
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry (the snprintf wrapper under answer);
   apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for answer's side-stack frame (class 7); record and arg_line take none, and the tail jump releases this
   frame first *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the shape "resp 0" RO_lit_21d20 and what record, arg_line and answer read
   (the format "resp %d" RO_lit_21d40, the FNV basis RO_lit_10330). Their read-only position, which answer's
   astr_argA asks of the shape, is cmd_addr_b / cmd_hull_b / cmd_ro_ends by computation; the other conjuncts of
   its read-only branch are cif_ro_unowned. *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 ->
(* the line: a string of at most LMAX bytes inside a live block that is none of the recorder's (plain str_arg,
   sup_broadcast_c.v:54). The one caller, verbs_receive, passes its strndup line, so the block form, not astr_argA;
   arg_line's strlen reads its tail word by cmd_heap_tail_vis *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX -> blocks_bytes S + LIVE_SUP_BROADCAST line t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST R line t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md)
(apost_baseF SEGS B SUP_BROADCAST_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O),
    sup_broadcast_c.v:33) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_BROADCAST R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_broadcast_m R line = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_broadcast_c.v:30, :35) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call: a block of O'
    that was live at the entry is a block of O *)
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain
    sup_broadcast_c.v:36-43) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (* the caller's copy of the reply text: live after the call; if it was live at the entry it was one of the
    recorder's blocks that record()'s spill arm or answer freed first (the contrapositive freshness form) *)
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_BROADCAST line t /\
 mo_le MT S S' (XM_SUP_BROADCAST R line t))).
End e.
End f.
End d.
