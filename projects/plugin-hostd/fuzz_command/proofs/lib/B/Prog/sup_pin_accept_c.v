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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 52 of its 78 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of sup_pin_accept on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92). Functional content: fuzz_command's own released plain
   contract lib/Prog/sup_pin_accept_c.v:28-64 and the model lib/Prog/RecModel.v:153 (`sup_pin_accept_m`, `rec_stub`
   of the REC id 13 with the arguments the verb carries, RecModel.v:73-75). The B twin of
   lib/A/Prog/sup_pin_accept_c.v, re-derived on B's code, which differs from A's: B calls record() and arg_s()
   (lib/B/Prog/record_c.v, arg_s_c.v) where A inlined record() and called xstrdup.
   sup_pin_accept (recorder.c:428-434) records the call with record(13) (a new slot of g_rec.calls, or record.spill
   with its arguments freed when the table already holds 16 calls), adds a copy of uri to the slot with arg_s, asks
   rec_shape_of for the reply shape the verb declares (daemon_shape "pin_accept", the image string at 0x21ea0, 10
   bytes) and tail-jumps to answer with changes = 1. It releases its own frame before the jump, so answer runs at
   this function's entry stack pointer.

   Addresses (B, the disassembly of sup_pin_accept): entry BASE + AF_sup_pin_accept = 0x8be78. 22 instructions, a
   32-byte real frame, no side-stack frame, no inline ASan check (the image's function table: 0 reports; the slot's
   checks are record's and arg_s's), no loop, 0 UBSan trap sites (the trap-site table). Calls: record (0x8a728, at
   0x8be90), arg_s (0x8a820, at 0x8be9c), rec_shape_of (0x896d4, at 0x8beac), and the tail jump to answer (0x8aa10, `j`
   at 0x8becc). s0 holds uri (0x8be88 `mv s0,a0`, a heap token below alloc_ceiling) at the three program calls, the
   slot is in s1: each callee's frame chain for it is the empty chain (achain_low), and at the tail jump s0 and sp
   are the caller's again (afn_pre's chain); no presence of the stack up to ly_top is assumed. The stack-protector
   GOT word 0xa6bf8 and
   guard cell 0x604158, which the snprintf wrapper under answer reads (aguard_ok, lib/B/Rt/RtDefs.v), come from
   CmdRecFacts' cmd_rec_cells; the tail of uri that arg_s's strlen wrapper reads (atail_vis, lib/B/Rt/RtDefs.v), from
   its heap block by cmd_heap_tail_vis. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c rec_shape_of_c answer_c.
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
(* the stack this call needs: its own 32-byte frame and the deepest callee reached with the frame up (record,
   arg_s, rec_shape_of); the tail jump `j answer` runs answer at this function's entry sp, so its need is not added to
   the frame but taken beside it. M: the image's function table gives 16608 = 32 + record's 16560 or answer's 16608 *)
Definition SUP_PIN_ACCEPT_STK : Z :=
  Z.max (32 + Z.max RECORD_STK (Z.max ARG_S_STK REC_SHAPE_OF_STK)) ANSWER_STK.
(* the allocator events: the frees of record()'s spill arm, arg_s's copy of uri, and answer's free of the old
   answer with the two copies of the reply text *)
Definition EV_SUP_PIN_ACCEPT (R : rstate) : Z := EV_RECORD R + EV_ARG_S + EV_ANSWER.
(* the live bytes the call adds at its peak: the recorded argument and answer's two copies of the text *)
Definition LIVE_SUP_PIN_ACCEPT (R : rstate) (uri : option (list byte)) : Z :=
  LIVE_ARG_S uri + LIVE_ANSWER (snd (sup_pin_accept_m R uri)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm, the recorded argument, and answer's *)
Definition XM_SUP_PIN_ACCEPT (R : rstate) (uri : option (list byte)) : Z :=
  XM_RECORD MT R + XM_ARG_S MT uri + XM_ANSWER MT (snd (sup_pin_accept_m R uri)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_pin_accept_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch -> (* astack_rd when it lands *)
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the verb name "pin_accept" (0x21ea0, 10 bytes), arg_s's
   default "(null)" (0x224c0) on the NULL path, which no caller takes, and what record, rec_shape_of and answer
   read *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(* uri: its one caller, verbs_receive, passes a token of its strdup'd copy (0x8d680 `ld a0,8(s3)`, tok[1]): a
   string in a live heap block that is none of the recorder's (record() and answer free the recorder's own blocks
   during the call) *)
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: answer takes one of class 7 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_PIN_ACCEPT R <= EV_MAX -> blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri <= LIVE_MAX ->
mo_ok MT S (XM_SUP_PIN_ACCEPT R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pin_accept) regs mem md)
(apost_baseF SEGS B SUP_PIN_ACCEPT_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_PIN_ACCEPT R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_pin_accept_c.v:28-50) *)
 sup_pin_accept_m R uri = (R', t) /\
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
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri /\
 mo_le MT S S' (XM_SUP_PIN_ACCEPT R uri))).
End e.
End f.
End d.
