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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 39 of its 65 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of lv2_refusals_forget on the ASan+UBSan build of plugin-hostd/fuzz_command
   (fuzz_command.asan-ubsan).
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/lv2_refusals_forget_c.v:27-48 and the model
   lib/Prog/RecModel.v:95 (`lv2_refusals_forget_m`, which is `rec_stub_mix` of the REC id 25, RecModel.v:81-82).
   The B twin of lib/A/Prog/lv2_refusals_forget_c.v, re-derived on B's code, which calls record() and arg_s()
   (lib/B/Prog/record_c.v, arg_s_c.v) where A inlined them.
   lv2_refusals_forget (recorder.c:563-569) records the call with record(25) (a new slot of g_rec.calls, or
   record.spill with its arguments freed when the table already holds 16 calls), adds the argument with arg_s (a
   copy of uri, or of the default "*", the image string at 0x21fe0, when it is NULL: 0x8cd74-0x8cd7c), folds the
   call into g_rec.state (g_rec + 944, reached as 0x5e3670 from the auipc at 0x8cd8c) with mix_call and returns no
   value: the adapter is asked again about what it refused, so the call changes the recorder's state digest.

   Addresses (B, its disassembly): entry BASE + AF_lv2_refusals_forget = 0x8cd54. 24 instructions, no
   inline ASan check (the function table: 0 reports), no loop, a 32-byte real frame and no side-stack frame anywhere
   below it, 0 UBSan trap sites (the trap-site table). Callees: record (0x8a728, at 0x8cd6c), arg_s (0x8a820, at
   0x8cd88), mix_call (0x8ad54, at 0x8cd98). s0 is the caller's at the record call (afn_pre's achain, carried by
   achain_lower) and the slot (record's result, in g_rec or record.spill, below the
   stack) at the arg_s and mix_call calls; the uri is in s1 (0x8cd64 `mv s1,a0`).
   The argument: both callers (verbs_receive and pin_set_words) pass NULL (a0 = 0, the return value pins_clear /
   pins_set just gave; lib/Spec/VerbsRun.v:32), so the argument keeps astr_argA's NULL case. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c mix_call_c.
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
(* the stack this call needs: its own 32-byte frame and the deepest callee.
   M: the image's function table gives 16592 = 32 + record's 16560 *)
Definition LV2_REFUSALS_FORGET_STK : Z := 32 + Z.max RECORD_STK (Z.max ARG_S_STK MIX_CALL_STK).
(* the allocator events: the frees of record()'s spill arm and the copy of the recorded argument *)
Definition EV_LV2_REFUSALS_FORGET (R : rstate) : Z := EV_RECORD R + EV_ARG_S.
(* the live bytes the call adds: the copy of the argument (uri, or "*" for NULL) *)
Definition LIVE_LV2_REFUSALS_FORGET (uri : option (list byte)) : Z :=
  LIVE_ARG_S (Some (darg uri (bstr "*"%string))).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: record()'s spill arm and the copy *)
Definition XM_LV2_REFUSALS_FORGET (R : rstate) (uri : option (list byte)) : Z :=
  XM_RECORD MT R + XM_ARG_S MT (Some (darg uri (bstr "*"%string))).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tlv2_refusals_forget_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the default "*" (0x21fe0) of a NULL argument, and the
   FNV-1a offset basis mix_call reads (0x10330) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(* the argument: NULL, a string in a live block that is none of the recorder's (record() frees the spill slot's
   blocks when the call table is full), or a read-only byte range of the image (the plain proof's str_arg,
   lib/Prog/RecKindB.v:164-175); for a string, the bytes after its terminator up to the end of that 8-byte word are
   readable (arg_s's strlen wrapper reads them, RtDefs.v's atail_vis) *)
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(forall x, uri = Some x -> atail_vis SEGS W mem (pu + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_LV2_REFUSALS_FORGET R <= EV_MAX -> blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri <= LIVE_MAX ->
mo_ok MT S (XM_LV2_REFUSALS_FORGET R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_lv2_refusals_forget) regs mem md)
(apost_base SEGS B LV2_REFUSALS_FORGET_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_LV2_REFUSALS_FORGET R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded and folded into the state digest
    (plain lib/Prog/lv2_refusals_forget_c.v:27-48) *)
 rec_repA B ly' S' (rdW W' mem') (lv2_refusals_forget_m R uri) O' /\
 (* the recorder owns what it owned, less what record() freed, plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri /\
 mo_le MT S S' (XM_LV2_REFUSALS_FORGET R uri))).
End e.
End f.
End d.
