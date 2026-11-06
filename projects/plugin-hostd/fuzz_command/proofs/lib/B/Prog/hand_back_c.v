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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 44 of its 71 lines of code are new or changed and 125 lines of the source are left out. *)
(* The contract of hand_back on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh blocks as cgif's trawnew_specX states one (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/hand_back_c.v:25-75 (hand_back_ret :25-58, the contract :60-75) and the model lib/Prog/RecModel.v:45
   (`hand_back R t = (set_answer R (Some t), t)`). The B twin of lib/A/Prog/hand_back_c.v, re-derived on B's code:
   B inlines both xstrdup calls (strlen, xmalloc, __asan_memcpy each), where A called xstrdup and tail-called it.
   hand_back(text) (recorder.c:243-248, xstrdup inlined :97-102) frees the answer the recorder kept (g_rec.answer,
   g_rec + 912; free(NULL) when there is none), stores a fresh copy of text there, and returns a second fresh copy.
   Its callers (answer, sup_add, answer_code) hand it a buffer of their own side-stack frame.

   Addresses (B, its disassembly): entry BASE + AF_hand_back = 0x8a978. 38 instructions, frame 48 bytes (ra,
   s0-s3), no inline ASan check (g_rec.answer is read at 0x8a994 and written at 0x8a9c8 without a check), no loop,
   no side-stack frame; calls: the free wrapper (0x589cc, at 0x8a9a0), then twice the strlen wrapper (0x4517c, at
   0x8a9a8 and 0x8a9d0), xmalloc (0x899b4, at 0x8a9b4 and 0x8a9dc) and __asan_memcpy (0x5767c, at 0x8a9c4 and
   0x8a9ec). s0 holds text at both xmalloc calls: an object of a live side-stack frame, which AR's frame law places
   below ASAN_CEIL = alloc_ceiling (in_app), so the frame chain xmalloc's afn_pre asks of s0 is achain's empty case
   (achain_low). UBSan: 0 trap sites (the trap-site table). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c.
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
(* the stack this call needs: its own 48-byte frame (no realignment), and the deepest callee: the free wrapper's
   window (ASTACK, cgif lib/YG0d.v:17, afree04_rule), the strlen wrapper's and __asan_memcpy's (ESTACK), xmalloc's
   own need.
   M: the image's function table gives 16448 = 48 + xmalloc's 16400 *)
Definition HAND_BACK_STK : Z := 48 + Z.max ASTACK (Z.max ESTACK XMALLOC_STK).
(* one free and the two mallocs of the two copies *)
Definition EV_HAND_BACK : Z := 1 + EV_XMALLOC + EV_XMALLOC.
(* the live bytes the call adds: the two copies of x *)
Definition LIVE_HAND_BACK (x : list byte) : Z :=
  LIVE_XMALLOC (Z.of_nat (length x) + 1) + LIVE_XMALLOC (Z.of_nat (length x) + 1).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the free of the old answer (also when it is NULL, afree_null04_rule) and the two
   copies *)
Definition XM_HAND_BACK (x : list byte) : Z :=
  mo_free MT + XM_XMALLOC MT (Z.of_nat (length x) + 1) + XM_XMALLOC MT (Z.of_nat (length x) + 1).
(* the callee's contract, the runtime entries with this tree's and cgif's names, and the bridge for g_rec's address *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
Definition thand_back_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s old : Z) (x : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B HAND_BACK_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 s -> 0 <= s < 2 ^ 64 ->
(* the text: a string of at most LMAX bytes in an object of a live side-stack frame (the caller's buffer), whose
   bytes are marked usable, so the strlen wrapper and __asan_memcpy pass their checks, twice; the frame is not in
   any callee's footprint, so the second copy reads the same bytes *)
astr_atR (rdW W mem) s x -> Z.of_nat (length x) <= LMAX ->
afobj SEGS B ly S W mem s (Z.of_nat (length x) + 1) ->
(* the recorder's state; old is the answer it holds (0 or the start of one of its blocks O), an 8-byte field read
   as a 64-bit value *)
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
st_nev S + EV_HAND_BACK <= EV_MAX -> blocks_bytes S + LIVE_HAND_BACK x <= LIVE_MAX ->
mo_ok MT S (XM_HAND_BACK x) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_hand_back) regs mem md)
(apost_base SEGS B HAND_BACK_STK
 ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
 regs ly S W mem md EV_HAND_BACK
(fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let n := Z.of_nat (length x) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
 (* two fresh blocks of |x| + 1 bytes: no block live at the entry other than the freed old answer is one of them
    (plain hand_back_c.v:43; the first xmalloc may return old's address after free(old)); the old answer's block
    is gone, every other block stays *)
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 (* the recorder now holds the answer x in p1 (plain hand_back_c.v:46-47) *)
 rec_repA B ly' S' (rdW W' mem') (fst (hand_back R x)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 (* the caller gets the other copy (plain hand_back_c.v:52) *)
 astr_atR (rdW W' mem') p2 (snd (hand_back R x)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_HAND_BACK x /\
 mo_le MT S S' (XM_HAND_BACK x))).
End e.
End f.
End d.
