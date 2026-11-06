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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 53 of its 79 lines of code are new or changed and 126 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/descriptors_get_c.v; 26 of its 68 lines of code are new or changed and 37 lines of the source are left out. *)
(* The contract of sup_remove_all on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the meter as cgif's (lib/YC7x.v:88, :92). Functional content: fuzz_command's own
   released plain contract lib/Prog/sup_remove_all_c.v:17-58 (sup_remove_all_sizes :17-18, sup_remove_all_ret
   :27-48, the contract :50-58) and the model lib/Prog/RecModel.v:121-122 (`sup_remove_all_m R = rec_stub R
   REC_REMOVE_ALL [] REC_MOD_HOST_SHAPE true`, with rec_stub :73-75, rec_record :38-39, rec_answer :47-50). The B
   twin of lib/A/Prog/sup_remove_all_c.v, re-derived on B's code, which differs from A's: B calls record()
   (lib/B/Prog/record_c.v) where A inlined it.
   sup_remove_all() (recorder.c:331-334) records the call REC_REMOVE_ALL with record(3) (a new slot of g_rec's
   table, or, when the table holds 16 calls, record.spill after rec_calls_free(&spill, 1) freed the spill's old
   arguments), records no argument, restores its frame and tail-calls answer(c, REC_MOD_HOST_SHAPE, 1) (`j answer`,
   0x8b458; the shape is the literal "resp 0" at 0x21d20, RO_lit_21d20).

   Addresses (B, its disassembly): entry BASE + AF_sup_remove_all = 0x8b434. 10 instructions, a 16-byte
   real frame (ra only), no side-stack frame, no inline ASan check (the function table: 0 reports; the slot's checks are
   record's and answer's), no loop, 0 UBSan trap sites (the trap-site table). Calls: record (0x8a728, `jal` at
   0x8b440), and the tail jump to answer (0x8aa10, `j` at 0x8b458) after the frame is released, so answer runs at
   this function's entry stack pointer. s0 is the caller's s0 at the record call and at the tail jump: the frame
   chains of record and answer come from afn_pre's chain (the entry chain when s0 is unchanged, carried by
   achain_lower, then achain_chain_pre, YCbq.v:327). No presence of the stack up to ly_top is
   assumed. The stack-protector GOT word 0xa6bf8 and guard cell 0x604158, which the snprintf wrapper under answer
   reads (RtDefs.v's aguard_ok), come from CmdRecFacts' cmd_rec_cells. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c answer_c.
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
(* the stack this call needs: its own 16-byte frame (no realignment) above record; answer runs at the entry sp
   after the tail call, so its need is taken beside the frame, not added to it. M: the function table gives 16608 =
   answer's 16608 (16 + record's 16560 = 16576 is below it) *)
Definition SUP_REMOVE_ALL_STK : Z := Z.max (16 + RECORD_STK) ANSWER_STK.
(* the events: record()'s spill arm frees the spill's arguments (EV_RECORD R, CmdRep's rec_spill_frees R: 0 while
   the table holds fewer than 16 calls, recorder.c:210-215), then answer. A function of the recorder state, as
   ev_calls is (the statements' rule for events). *)
Definition EV_SUP_REMOVE_ALL (R : rstate) : Z := EV_RECORD R + EV_ANSWER.
(* the live bytes the call adds: answer's two copies of the text t (plain sup_remove_all_sizes) *)
Definition LIVE_SUP_REMOVE_ALL (t : list byte) : Z := LIVE_ANSWER t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, then answer's *)
Definition XM_SUP_REMOVE_ALL (R : rstate) (t : list byte) : Z := XM_RECORD MT R + XM_ANSWER MT t.
(* the callees' contracts, and the bridge for the addresses of g_rec, record.spill and the shape "resp 0" *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_remove_all_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z)),
let t := snd (sup_remove_all_m R) in
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry (the snprintf wrapper under answer);
   apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for answer's side-stack frame (class 7); record takes none, and the tail jump releases this frame first *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the shape "resp 0" RO_lit_21d20 and what record and answer read (the format
   "resp %d" RO_lit_21d40, the FNV basis RO_lit_10330). Their read-only position, which answer's astr_argA asks of
   the shape, is cmd_addr_b / cmd_hull_b / cmd_ro_ends by computation; the other conjuncts of its read-only branch
   are cif_ro_unowned. *)
cmd_ro_ok (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE_ALL R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE_ALL t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE_ALL R t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove_all) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_ALL_STK
 (* g_rec's ncalls, call table and answer, g_rec.state, record.spill; the recorder's blocks (the spill's old
    arguments and the old answer may be freed; plain call_post_rec ... rec_area (map fst O),
    sup_remove_all_c.v:33) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
  (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_REMOVE_ALL R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_all_m R = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 (* the recorder's state after the call (plain sup_remove_all_c.v:30, :35) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call: a block of O'
    that was live at the entry is a block of O *)
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (* the blocks: the caller's kept, the recorder's new set, and the returned text (plain
    sup_remove_all_c.v:36-43) *)
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (* the caller's copy of the reply text: live after the call; if it was live at the entry it was one of the
    recorder's blocks that record()'s spill arm or answer freed first (the contrapositive freshness form) *)
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE_ALL t /\
 mo_le MT S S' (XM_SUP_REMOVE_ALL R t))).
End e.
End f.
End d.
