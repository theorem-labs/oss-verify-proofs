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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/answer_c.v; 32 of its 68 lines of code are new or changed and 44 lines of the source are left out. *)
(* The contract of answer_code on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the side-stack frame as cgif's class-1 users take it (aj_stack_malloc_atS,
   lib/YC85.v:292-310). Functional content: fuzz_command's own released plain contract
   lib/Prog/answer_code_c.v:27-63 (answer_code_ret :27-50, the contract :52-63: a0 = the code, the recorder holds
   `fst (rec_answer_code R code)`, the old answer freed, one fresh block owned by the recorder) and the model
   lib/Prog/RecModel.v:52 (`rec_answer_code R code = (set_answer R (Some (resp code)), code)`), RecFacts.v:122
   (`resp c = "resp " ++ dec c`). The B twin of lib/A/Prog/answer_code_c.v, re-derived on B's code.
   answer_code(code) (recorder.c:501-508) writes "resp <code>" into a 32-byte buffer with the snprintf wrapper
   (`___interceptor_snprintf`, reached through the 4-byte jump `__interceptor_trampoline_snprintf`, format
   "resp %d" at 0x21d40), hands it to hand_back (which frees the old answer, keeps one copy and returns another),
   frees the returned copy and returns the code. The buffer lives in a class-1 side-stack frame of 96 bytes taken
   with `__asan_stack_malloc_1` (this port's decision: the side-stack branch only; the use-after-return flag, read
   through the GOT word 0xa5fa8 at 0xb0c40, is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193
   aso_const_law, so the real-stack fallback 0x8ca68-0x8ca80 and its page probe are not taken) and released inline
   by the flag store (0x8cb7c-0x8cb80, cgif's astack_free_law, lib/YG0d.v:309-317); its shadow bytes are marked
   usable for buf (00) and unusable around it (f1, f3, then f8 and f5 at the release). The stack-protector cells
   the musl body under the snprintf wrapper compares (RtDefs.v aguard_ok; B's GOT word 0xa6bf8 holds the guard cell
   0x604158) are cmd_rec_cells (CmdRecFacts).

   Addresses (B, answer_code's disassembly): entry BASE + AF_answer_code = 0x8c9f8. 124 instructions, no inline ASan
   check, no data loop, a 96-byte real frame realigned by `andi sp,sp,-32` (0x8ca24) and a class-1 side-stack
   frame (1:96, the function table), 0 UBSan trap sites (the trap summary). Calls: __asan_stack_malloc_1 (0x3fac8,
   at 0x8ca50), the snprintf wrapper (0x451d0, at 0x8cb04), hand_back (0x8a978, at 0x8cb0c), the free wrapper
   (0x589cc, at 0x8cb10). s0 is this call's frame pointer (0x8ca20 `addi s0,sp,96`, the entry sp) at every call, so
   its calls' frame chains come from afn_pre's chain (achain_push at the frame pointer;
   achain_chain_pre, YCbq.v:327, gives the wrappers' chain_pre); no presence of the stack up to ly_top is assumed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import hand_back_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 96-byte frame and the realignment `andi sp,sp,-32` (at most 16 more bytes,
   0x8ca24), then the deepest window below it: hand_back's need, the free wrapper's ASTACK (cgif lib/YG0d.v:17),
   the snprintf wrapper's 3 * ESTACK (measured) or __asan_stack_malloc_1's ESTACK.
   M: the image's function table gives 16544 = 96 + hand_back's 16448 (without the realignment's 16) *)
Definition ANSWER_CODE_STK : Z := 112 + Z.max HAND_BACK_STK (Z.max ASTACK (3 * ESTACK)).
(* hand_back's free and two mallocs, then the free of the returned copy *)
Definition EV_ANSWER_CODE : Z := EV_HAND_BACK + 1.
(* the live bytes the call adds at its peak: hand_back's two copies of "resp <code>" *)
Definition LIVE_ANSWER_CODE (code : Z) : Z := LIVE_HAND_BACK (resp code).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Definition XM_ANSWER_CODE (code : Z) : Z := XM_HAND_BACK MT (resp code) + mo_free MT.
(* the callee and the runtime entries this call reaches *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Definition tanswer_code_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (code old : Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B ANSWER_CODE_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the format string "resp %d" (B's literal at 0x21d40; its tail by cmd_tail_vis, its shadow by
   cmd_aread_ok_chk) and the GOT words of the use-after-return flag (0xa5fa8) and the shadow base (0xa5f50) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
(* the recorder's state; old is the answer it holds (0 or the start of one of its blocks O), a 64-bit word *)
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
(* room for one more side-stack frame (cgif's frame-count premise, lib/YC7x.v:75) *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_ANSWER_CODE <= EV_MAX -> blocks_bytes S + LIVE_ANSWER_CODE code <= LIVE_MAX ->
mo_ok MT S (XM_ANSWER_CODE code) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_answer_code) regs mem md)
(apost_baseF SEGS B ANSWER_CODE_STK
 ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
 regs ly S W mem md EV_ANSWER_CODE
(fun ly' S' W' regs' mem' md' => exists (p1 : Z) (O' : list (Z * Z)),
 let n := Z.of_nat (length (resp code)) + 1 in
 (* a0 = the code (plain answer_code_c.v:35) *)
 getr regs' 10 = w64 (snd (rec_answer_code R code)) /\
 (* one fresh block of |resp code| + 1 bytes, none of the blocks live at the entry that the call keeps (the old
    answer may be freed and its address reused); the old answer's block is gone, every other block stays *)
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n)) /\
 (forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n)) /\
 (* the recorder now holds "resp <code>" as its answer, in p1 (plain answer_code_c.v:42-43) *)
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer_code R code)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_ANSWER_CODE code /\
 mo_le MT S S' (XM_ANSWER_CODE code))).
End e.
End f.
End d.
