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
(* The contract of arg_s on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.
   arg_s reaches no printf wrapper (B's call tree: strlen, xmalloc -> malloc, __asan_memcpy), so its post is
   apost_base.
   The slot and the recorder are stated at recorder level (c = rec_slot R, rec_repA (rec_record R fn A) O before,
   rec_record R fn (A ++ [y]) after): a deliberate B class (this port's decision, relayed 2026-10-29), not
   A's raw form (slot, nargs, the two stores). lib/B/Prog/RecBridge.v proves the two forms equivalent:
   rec_bridge_slot / arep_bridge_slot (recorder -> raw) and rec_bridge_add / arep_bridge_add (raw -> recorder).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the meter
   as there (:88, :92). Functional content: the model lib/Prog/RecModel.v:38-39, :60-61 (`rec_record R fn A`, and
   `sarg`: a NULL string is recorded as "(null)"), over the representation lib/B/Prog/CmdRep.v (rec_repA). A has no
   arg_s function (it is inlined into arg_i and the sup_* functions there; the A side's arg_i statement,
   lib/A/Prog/arg_i_c.v, and xstrdup statement, lib/A/Prog/xstrdup_c.v, carry its parts). B keeps it as a function
   (37 call sites in B's call tree) and inlines xstrdup into it.
   arg_s(c, s) (recorder.c:223-227, xstrdup inlined :97-102): when c->nargs < REC_ARGS_MAX (6) it appends a copy of
   s, or of "(null)" when s is NULL, to the call c: strlen, xmalloc(len + 1), __asan_memcpy, then
   c->args[c->nargs++] = the copy. Every caller passes the slot record() returned (lib/B/Prog/record_c.v,
   `rec_slot R`) after record() and the earlier arg_s / arg_line calls of the same call, so the pre states the
   recorder as `rec_record R fn A` (A the arguments recorded so far) and the post as `rec_record R fn (A ++ [y])`.
   The string is in a live block, in the read-only image (the literals "-" and "*" sup_add and
   lv2_refusals_forget pass), or in an object of a live side-stack frame (the buffer of the arg_i code B inlines
   into its callers); NULL is recorded as "(null)" (RO_lit_224c0).

   Addresses (B, arg_s's disassembly): entry BASE + AF_arg_s = 0x8a820. 86 instructions, frame 64 bytes, no side-stack
   frame, no loop; 4 inline ASan checks, all on the slot: load4 of c->nargs (0x8a870, and again at 0x8a8b4),
   store4 of c->nargs (0x8a8c8), store8 of c->args[m] (0x8a900); each reads the shadow byte at (a >> 3) + SHADOW_OFF
   through the shadow-base GOT word 0xa5f50, the slot lies in g_rec or record.spill (cmd_addressable_chk), so the
   report paths 0x8a938-0x8a974 are not reached. Calls: the strlen wrapper (0x4517c, at 0x8a894), xmalloc (0x899b4,
   at 0x8a8a0), __asan_memcpy (0x5767c, at 0x8a8b0). s0 holds c + 4 at the xmalloc call: an image address, 4 mod 8,
   so the frame chain xmalloc's afn_pre asks of s0 is achain's empty case (achain_low: below alloc_ceiling).

   UBSan (5 trap sites, all to the one `unimp` at 0x8a934, recorder.c:225-226): 0x8a844 c = NULL and 0x8a850
   c mod 8 <> 0 (the member access c->nargs); 0x8a8c4 the signed overflow of `c->nargs++`; 0x8a8e0 the pointer
   overflow of `c->args + nargs` giving NULL, and 0x8a8f4 the same address wrapping past `c->args`. No new premise:
   c = rec_slot R is the constant g_rec + 16 + 56 k (k <= 15) or record.spill, nonzero and 8-aligned (0x8a844,
   0x8a850) and far from 2 ^ 64 (0x8a8e0, 0x8a8f4); rec_repA gives nargs = length A <= 6 (acall_at of the slot), the
   branch at 0x8a880 leaves only nargs <= 5, and the slot is outside the footprints of xmalloc and __asan_memcpy, so
   the value reloaded at 0x8a8bc is the same and nargs + 1 <= 6 (0x8a8c4). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c.
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
(* the stack this call needs: its own 64-byte frame (no realignment), and the deepest callee: xmalloc's need (the
   malloc wrapper's ASTACK), the strlen wrapper's and __asan_memcpy's windows (ESTACK).
   M: the image's function table gives 16464 = 64 + xmalloc's 16400 *)
Definition ARG_S_STK : Z := 64 + Z.max ESTACK XMALLOC_STK.
(* one allocator event: xmalloc's malloc (none when c->nargs = 6) *)
Definition EV_ARG_S : Z := EV_XMALLOC.
(* the live bytes the call adds: the copy of the recorded string y = sarg v and its terminator *)
Definition LIVE_ARG_S (v : option (list byte)) : Z := LIVE_XMALLOC (Z.of_nat (length (sarg v)) + 1).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xmalloc's malloc of |y| + 1 bytes *)
Definition XM_ARG_S (v : option (list byte)) : Z := XM_XMALLOC MT (Z.of_nat (length (sarg v)) + 1).
(* the callee's contract, the runtime entries with this tree's and cgif's names, and the bridge for the address of the
   default "(null)" *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
Definition targ_s_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c s fn : Z) (A : list (list byte)) (v : option (list byte))
  (R : rstate) (O : list (Z * Z)),
let y := sarg v in
afn_pre SEGS B ARG_S_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image: the default "(null)" RO_lit_224c0 that a NULL s is replaced by (its tail:
   cmd_tail_vis; its shadow: cmd_aread_ok_chk; unowned: cif_ro_unowned, so __asan_memcpy reads the same bytes after
   the malloc) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 s ->
(* c is the slot record() returned; the recorder holds the call (fn, A) in it (the arguments recorded so far).
   The slot's constant address excludes the UBSan traps 0x8a844, 0x8a850, 0x8a8e0, 0x8a8f4, and its nargs field
   = length A <= 6 (acall_at) with the branch at 0x8a880 excludes 0x8a8c4 *)
c = rec_slot R ->
rec_repA B ly S (rdW W mem) (rec_record R fn A) O ->
(* the string, of at most LMAX bytes: NULL, in a live block or the read-only image (astr_argA; arg_s frees
   nothing, so no block is excluded), or in an object of a live side-stack frame (the callers' inlined arg_i
   buffer) *)
(astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] s v \/
 (exists x, v = Some x /\ astr_atR (rdW W mem) s x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
  afobj SEGS B ly S W mem s (Z.of_nat (length x) + 1))) ->
(* the bytes after the terminator up to the end of its 8-byte word are readable: the strlen wrapper reads whole
   words (RtDefs.v atail_vis). A caller gets it by cmd_heap_tail_vis for a heap string, from the frame for a
   side-stack buffer, and by cmd_tail_vis for an image literal *)
(forall x, v = Some x -> atail_vis SEGS W mem (s + Z.of_nat (length x))) ->
st_nev S + EV_ARG_S <= EV_MAX -> blocks_bytes S + LIVE_ARG_S v <= LIVE_MAX ->
mo_ok MT S (XM_ARG_S v) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_s) regs mem md)
(apost_base SEGS B ARG_S_STK
 (* it writes c->nargs and c->args[m] (m = length A), and only when m < 6 *)
 (if Z.of_nat (length A) <? REC_ARGS_MAX
  then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
        (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A), c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
  else [])
 regs ly S W mem md EV_ARG_S
(fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S + LIVE_ARG_S v /\
 mo_le MT S S' (XM_ARG_S v) /\
 (* six arguments already: nothing changes *)
 ((Z.of_nat (length A) = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
   rec_repA B ly' S' (rdW W' mem') (rec_record R fn A) O) \/
  (* else one fresh block of |y| + 1 bytes, apart from every block that was live, holding y; the recorder now
     holds the call (fn, A ++ [y]) and owns the new block *)
  (Z.of_nat (length A) < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length y) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
    rec_repA B ly' S' (rdW W' mem') (rec_record R fn (A ++ [y])) ((p, n) :: O))))).
End e.
End f.
End d.
