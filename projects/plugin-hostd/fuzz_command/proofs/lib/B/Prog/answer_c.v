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
(* The contract of answer on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh blocks as cgif's trawnew_specX states one (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/answer_c.v:18-81 (ans_entry :18-20, ans_shape :22-24, ans_writes :26-27, answer_ret :36-63, the contract
   :65-81) and the model lib/Prog/RecModel.v:45-50 (`rec_answer`, `hand_back`), lib/Prog/RecFacts.v:122, :262-264
   (`resp`, `inst`, `fits`). The B twin of lib/A/Prog/answer_c.v, re-derived on B's code.
   answer(c, shape, changes) (recorder.c:252-269, syntax_instantiate inlined, syntax.h:123-152) takes a side-stack
   frame for buf[PHD_LINE_MAX]. When the input refuses (g_rec.refuse != 0) it prints "resp <g_rec.code>" into buf;
   otherwise, when changes != 0, it folds the call c into g_rec.state (mix_call), and instantiates the shape into
   buf. Then it hands buf back (hand_back: the old answer freed, a fresh copy kept in g_rec.answer, another fresh
   copy returned) and releases the frame. The pre-condition `fits x` says that the instance fits buf, so
   syntax_instantiate does not fail and the abort edge (`__asan_handle_no_return` 0x8ad34, then abort) is not taken.
   The recording functions reach it by the tail call `j answer` after they have released their own frame, or by
   `jal answer` while they hold a side-stack frame of their own (B: 20 callers, 11 of them tail jumps,
   B's call tree), so the frame-count premise below accepts one caller frame.

   Addresses (B, answer's disassembly): entry BASE + AF_answer = 0x8aa10. 209 instructions, frame 128 bytes realigned by
   `andi sp,sp,-32` (0x8aa50); s0 is the frame pointer (0x8aa4c `addi s0,sp,128`, the entry sp) at the program calls:
   mix_call takes afn_pre_na and asks no chain; hand_back's chain for s0 is afn_pre's chain pushed at the frame
   pointer (achain_push, with ra and the caller's s0 saved at sp0 - 8 and sp0 - 16 by 0x8aa18 and 0x8aa1c).
   No presence of the stack up to ly_top is assumed. 3 inline ASan checks (load1 of the
   shape's bytes 0x8abd4, store1 of buf's bytes 0x8ac48, store1 of buf's terminator 0x8ac90; each reads the shadow
   byte at (a >> 3) + SHADOW_OFF through the shadow-base GOT word 0xa5f50; the shape's addressable bytes and the
   frame's usable buf leave the report paths 0x8ac68, 0x8ac74, 0x8ad40-0x8ad50 unreached); a side-stack frame of
   class 7 (`__asan_stack_malloc_7` 0x40290 at 0x8aa88, a0 = 4256; the shadow of buf set with `__asan_set_shadow_f8`
   0x5a65c at 0x8ab18 and `__asan_set_shadow_00` 0x5a53c at 0x8ab68 at entry, `__asan_set_shadow_f8` at 0x8acb8 at
   scope end; released by `__asan_stack_free_7` 0x4040c at 0x8acd8, a1 = 4256). The use-after-return flag is read
   through the GOT word 0xa5fa8; its real-stack fallback 0x8aaa0-0x8aac0 (the page probe that runs twice, 4256 >
   4096) and the matching release 0x8ace0-0x8ace8 are not taken (this port's decision: the flag is the record's const
   cell). Loops: syntax_instantiate's (one pass per byte of the shape, 0x8abcc-0x8ac60). Calls: the snprintf wrapper
   (0x451d0, at 0x8ab90, size 4096, format "resp %d" at 0x21d40), mix_call (0x8ad54, at 0x8aba4), hand_back
   (0x8a978, at 0x8aca8).

   UBSan (5 trap sites to the `unimp` at 0x8ad30, syntax.h:128-150; the `unimp` at 0x8ad3c follows `jal abort` and
   is not reached): 0x8abac shape = NULL (the pointer arithmetic `shape++` on a null base); 0x8ac08 the signed
   overflow of `depth++`; 0x8ac38 the pointer overflow of `buf + o` at the store `buf[o++] = c`; 0x8ac64 (a `j`) the
   pointer overflow of `shape++` wrapping to NULL; 0x8ac80 the pointer overflow of `buf + o` at `buf[o] = '\0'`. All
   run only when g_rec.refuse = 0 (0x8ab78 branches to the snprintf path otherwise). No new premise: the shape
   premise (astr_argA ... sh (Some x)) gives sh <> 0 (0x8abac), |x| + 1 <= LMAX + 1, so depth <= |x| < 2 ^ 31 - 1
   (0x8ac08), and the shape's bytes in a live block or the read-only image, both below 2 ^ 64 - 1, so the scan stops
   at the terminator before `shape` wraps (0x8ac64); buf is the class-7 frame + 32 and o < 4096 at both stores (the
   check `(o + 1) >> 12` at 0x8ac30 runs before 0x8ac38; at 0x8ac80 o is at most the last o + 1 that passed it), and
   AR's frame law places the frame's 4256 bytes inside the application range, so buf + o does not wrap (0x8ac38,
   0x8ac80). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import mix_call_c hand_back_c.
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
(* the stack this call needs: its own 128-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0
   at the entry, afn_pre's astk_ok), and the deepest callee: the side-stack and shadow-fill entries' window
   (ESTACK), the snprintf wrapper's (3 * ESTACK, measured), mix_call's and hand_back's own needs. A
   tail-caller enters with its own entry sp, so its <FN>_STK covers this one.
   M: the image's function table gives 16608 = 128 + mix_call's 16480 (without the realignment's 16) *)
Definition ANSWER_STK : Z := 128 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) (Z.max MIX_CALL_STK HAND_BACK_STK)).
(* hand_back's events: the free of the old answer and the two copies; mix_call and the frame spend none *)
Definition EV_ANSWER : Z := EV_HAND_BACK.
(* the live bytes the call adds: hand_back's two copies of the answer text t *)
Definition LIVE_ANSWER (t : list byte) : Z := LIVE_HAND_BACK t.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: hand_back's *)
Definition XM_ANSWER (t : list byte) : Z := XM_HAND_BACK MT t.
(* the callees' contracts, the runtime entries with this tree's names (the snprintf wrapper with B's stack-protector GOT
   word 0xa6bf8 and guard cell 0x604158), and the bridge for the addresses of g_rec and of the "resp %d" format *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC7 : forall fx0 : YK11.FPState, @astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Hypothesis ASTACK_FREE7 : forall fx0 : YK11.FPState, @astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Hypothesis ASET_SHADOW00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Definition tanswer_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c sh old : Z) (e : rcall) (x : list byte) (chg : bool)
  (R : rstate) (O : list (Z * Z)),
let t := snd (rec_answer R e x chg) in
afn_pre SEGS B ANSWER_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for one more side-stack frame of class 7 (count_cid 7 < fs_frames 7 = 128); a caller that holds one frame
   of its own when it calls (jal) entered with at most 7 *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the format "resp %d" is RO_lit_21d40 (its tail: cmd_tail_vis; its shadow:
   cmd_aread_ok_chk), the FNV basis mix_call reads RO_lit_10330. The stack-protector GOT word and guard cell that
   musl's printf chain behind the snprintf wrapper checks are CmdRecFacts' cmd_rec_cells. *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 sh -> 0 <= sh < 2 ^ 64 ->
chg = negb (bv_unsigned (getr regs 12) =? 0) ->
(* the recorder's state; old is the answer it holds (0 or the start of one of its blocks O), an 8-byte field read
   as a 64-bit value *)
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
(* not refused: the shape is a string of at most LMAX bytes (in the read-only image, or in a live block that is
   none of the recorder's), with addressable bytes for the load1 checks, and its instance fits buf (plain ans_shape,
   answer_c.v:22-24, :71). It excludes the UBSan traps 0x8abac (sh <> 0), 0x8ac08 (depth <= |x| <= LMAX) and
   0x8ac64 (the shape's bytes lie below 2 ^ 64 - 1), and `fits x` the abort edge 0x8ad34 *)
(r_refuse R = 0 -> astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O sh (Some x) /\ fits x) ->
(* not refused and changes: c is the call e just recorded, a slot of g_rec's call table or record.spill (plain
   ans_entry, answer_c.v:18-20, :72-73) *)
(r_refuse R = 0 -> chg = true ->
 (exists k, nth_error (r_calls R) k = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
 (c = A_REC_SPILL /\ e = r_spill R)) ->
st_nev S + EV_ANSWER <= EV_MAX -> blocks_bytes S + LIVE_ANSWER t <= LIVE_MAX ->
mo_ok MT S (XM_ANSWER t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_answer) regs mem md)
(apost_baseF SEGS B ANSWER_STK
 (* g_rec.answer and g_rec.state (plain ans_writes, answer_c.v:26-27), and the old answer's block, freed *)
 ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn => fst pn =? old) O))
 regs ly S W mem md EV_ANSWER
(fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
 (* two fresh blocks of |t| + 1 bytes: no block live at the entry other than the freed old answer is one of them
    (plain hand_back_c.v:43, answer_c.v:46-50; hand_back's first xmalloc may return old's address after free(old));
    the old answer's block is gone, every other block stays *)
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 (* the recorder's state after the call, which holds t in p1 (plain answer_c.v:53-54) *)
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer R e x chg)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 (* the caller gets the other copy of t (plain answer_c.v:58) *)
 astr_atR (rdW W' mem') p2 t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_ANSWER t /\
 mo_le MT S S' (XM_ANSWER t))).
End e.
End f.
End d.
