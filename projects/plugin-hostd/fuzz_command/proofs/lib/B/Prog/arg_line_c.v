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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 40 of its 67 lines of code are new or changed and 125 lines of the source are left out. *)
(* The contract of arg_line on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.
   arg_line reaches no printf wrapper (B's call tree: strlen, rec_canonical -> xmalloc -> malloc), so its post is
   apost_base.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/arg_line_c.v:25-67 (arg_line_ret :25-49: the two cases m = 6 and m < 6, nargs := m + 1, args[m] := p,
   a block of |T| + 1 bytes that holds `canon T` and its terminator; the contract :51-67) and
   lib/Prog/RecFacts.v:154 (`canon`). The B twin of lib/A/Prog/arg_line_c.v (the same binders and premises),
   re-derived on B's code.
   arg_line(c, line) (recorder.c:229-233) appends rec_canonical(line, strlen(line)) to the call c when
   c->nargs < 6. c is a slot of g_rec's call table or record.spill (every caller passes record()'s result,
   lib/B/Prog/record_c.v `rec_slot R`). Its callers (sup_call, sup_connect, sup_broadcast, sup_host_setting,
   sup_instance_verb) pass their line, which verbs_receive takes from its strndup block (verbs.c:219).

   Addresses (B, arg_line's disassembly): entry BASE + AF_arg_line = 0x8b128. 76 instructions, frame 48 bytes, no loop,
   no side-stack frame; 4 inline ASan checks, all on the slot: load4 of c->nargs (0x8b170, and again at 0x8b198),
   store4 of c->nargs (0x8b1ac), store8 of c->args[m] (0x8b1e4); each reads the shadow byte at (a >> 3) +
   SHADOW_OFF through the shadow-base GOT word 0xa5f50 of a byte of g_rec or record.spill (CmdRecFacts'
   cmd_addressable_chk), so the report paths 0x8b214-0x8b254 are not reached. Calls: the strlen wrapper (0x4517c, at
   0x8b188), rec_canonical (0x897e8, at 0x8b194). s0 holds c + 4 at the rec_canonical call: an image address, 4 mod 8,
   so the frame chain rec_canonical's afn_pre asks of s0 is achain's empty case (achain_low: below alloc_ceiling).

   UBSan (5 trap sites, all to the one `unimp` at 0x8b210, recorder.c:231-232): 0x8b144 c = NULL and 0x8b150
   c mod 8 <> 0 (the member access c->nargs); 0x8b1a8 the signed overflow of `c->nargs++`; 0x8b1c4 the pointer
   overflow of `c->args + nargs` giving NULL, and 0x8b1d8 the same address wrapping past `c->args`. No new premise:
   the slot premise gives c = g_rec + 16 + 56 i (i < 16) or record.spill, nonzero and 8-aligned (0x8b144, 0x8b150)
   and far from 2 ^ 64 (0x8b1c4, 0x8b1d8); the nargs premise gives m <= 6, the branch at 0x8b180 leaves only m <= 5,
   and the slot is outside rec_canonical's footprint (it writes only its fresh block), so the value reloaded at
   0x8b1a0 is the same and m + 1 <= 6 (0x8b1a8). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_canonical_c.
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
(* the stack this call needs: its own 48-byte frame (no realignment), and the deeper of the strlen wrapper's window
   (ESTACK, RtString.v astrlen_realizes) and rec_canonical's own need.
   M: the image's function table gives 16480 = 48 + rec_canonical's 16432 *)
Definition ARG_LINE_STK : Z := 48 + Z.max ESTACK REC_CANONICAL_STK.
(* one allocator event: the malloc rec_canonical makes through xmalloc (none when c->nargs = 6) *)
Definition EV_ARG_LINE : Z := EV_REC_CANONICAL.
(* the live bytes the call adds: rec_canonical's block of |T| + 1 bytes *)
Definition LIVE_ARG_LINE (T : list byte) : Z := LIVE_REC_CANONICAL T.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: rec_canonical's malloc *)
Definition XM_ARG_LINE (T : list byte) : Z := XM_REC_CANONICAL MT T.
(* the callee's contract and the runtime entry, with this tree's name *)
Hypothesis TREC_CANONICAL : forall fx0 : YK11.FPState, @trec_canonical_spec fx0 rc SK PI B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Definition targ_line_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c pl m : Z) (T : list byte),
afn_pre SEGS B ARG_LINE_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 pl -> 0 <= pl < 2 ^ 64 ->
(* c is a slot of g_rec's call table or record.spill: program globals whose shadow is usable
   (cmd_addressable_chk), so the four checks pass; its constant address excludes the UBSan traps 0x8b144, 0x8b150,
   0x8b1c4 and 0x8b1d8 *)
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
(* nargs = m <= 6: with the branch at 0x8b180 it excludes the UBSan trap 0x8b1a8 *)
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 m -> 0 <= m <= REC_ARGS_MAX ->
(* the line: a string of at most LMAX bytes inside a live block (plain arg_line_c.v:58-62). Every caller (sup_call,
   sup_connect, sup_broadcast, sup_host_setting, sup_instance_verb) passes its own line, which verbs_receive takes
   from its strndup block (verbs.c:219), so the block form, not astr_argA. The strlen wrapper reads
   the bytes and the tail word after the terminator: CmdRecFacts' cmd_heap_tail_vis gives that tail from the block.
   arg_line frees nothing, so no block is excluded *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length T) + 1) -> astr_atR (rdW W mem) pl T ->
Z.of_nat (length T) + 1 <= LMAX + 1 ->
st_nev S + EV_ARG_LINE <= EV_MAX -> blocks_bytes S + LIVE_ARG_LINE T <= LIVE_MAX ->
mo_ok MT S (XM_ARG_LINE T) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_arg_line) regs mem md)
(apost_base SEGS B ARG_LINE_STK
 (* it writes c->nargs and c->args[m], and only when m < 6 *)
 (if m <? REC_ARGS_MAX
  then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
  else [])
 regs ly S W mem md EV_ARG_LINE
(fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S + LIVE_ARG_LINE T /\
 mo_le MT S S' (XM_ARG_LINE T) /\
 ((m = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
  (m < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length T) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (m + 1) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * m) 8 p /\
    astr_atR (rdW W' mem') p (canon T))))).
End e.
End f.
End d.
