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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 29 of its 57 lines of code are new or changed and 124 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_shape_of_c.v; 23 of its 54 lines of code are new or changed and 26 lines of the source are left out. *)
(* The contract of mix_call on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre_na
   (lib/B/Prog/PaNoChain.v, cgif's afn_pre without the frame-chain conjunct: the function reaches no allocator, no
   side-stack entry and no program function) at the entry, SRr of apost_base at the return. Functional content:
   fuzz_command's own released plain contract lib/Prog/mix_call_c.v:23-47 (the result `mixcall h fn (map snd args)`)
   and the model lib/Prog/RecFacts.v:224-229 (mix, mixcall: FNV-1a, 64 bits, over the 4 bytes of the call's function
   number and over each argument with its terminator). The plain contract takes the arguments as a list of
   (pointer, string) pairs; here they are the recorded call as the recorder's representation states it (`acall_at`,
   lib/B/Prog/CmdRep.v), so the strings are `snd e`. The B twin of lib/A/Prog/mix_call_c.v, re-derived on B's code.
   mix_call(h, c) (recorder.c:194-202, `mix` inlined, :180-192) reads c->fn byte by byte, c->nargs, each
   c->args[a], calls strlen on that argument and reads its bytes and its terminator. It writes nothing outside its
   own frame and allocates nothing (FP = [], no meter).

   Addresses (B, its disassembly): entry BASE + AF_mix_call = 0x8ad54. 120 instructions, frame 96 bytes (ra,
   s0-s10; no realignment), no side-stack frame, 3 loops (the 4 bytes of c->fn 0x8adc8-0x8adf8, the arguments
   0x8ae50-0x8ae94, the bytes of one argument 0x8ae9c-0x8aecc), 4 inline ASan checks (load1 on c->fn's bytes
   0x8add8, load4 on c->nargs 0x8ae18, load8 on c->args[a] 0x8ae64, load1 on the argument's bytes 0x8aeac; each
   reads the shadow byte at (a >> 3) + SHADOW_OFF through the shadow-base GOT word 0xa5f50; the report paths
   0x8ae00-0x8ae08, 0x8aed4-0x8aedc, 0x8af20-0x8af30 are not reached: the slot's shadow by cmd_addressable_chk, the
   argument bytes by AR's block facts), one wrapper call (strlen, `___interceptor_strlen` reached through the 4-byte
   jump `__interceptor_trampoline_strlen` 0x4517c, at 0x8ae74). The FNV offset basis is the read-only word at
   0x10330 (`ld s0,1416(a2)` at 0x8adb0, `ld s6,1416(a2)` at 0x8ae34).

   UBSan (6 trap sites, all to the one `unimp` at 0x8af1c, recorder.c:188-200): 0x8ad88 c = NULL and 0x8ad94
   c mod 8 <> 0 (the member access &c->fn); 0x8adcc the pointer overflow of `b++` over c->fn's 4 bytes; 0x8ae54 the
   pointer overflow of `c->args + a`; 0x8ae88 the signed overflow of `a++`; 0x8aea0 the pointer overflow of `b++`
   over an argument's bytes. No new premise: the slot premise gives c = g_rec + 16 + 56 i (i < 16) or record.spill,
   nonzero, 8-aligned and far from 2 ^ 64 (0x8ad88, 0x8ad94, 0x8adcc, 0x8ae54); acall_at gives nargs <= 6, so
   a < 6 (0x8ae88), and each argument inside a live block (In pn bl), which AR's block law places below the
   allocator ceiling, so its bytes and terminator do not wrap (0x8aea0). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
(* the stack this call needs: its own 96-byte frame (no realignment), and the window the strlen wrapper asks for
   (RtString.v's astrlen_realizes, PRE ESTACK) *)
Definition MIX_CALL_STK : Z := 96 + ESTACK.
Definition EV_MIX_CALL : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entry the call reaches, with RtString.v's name, and the bridge from the image's object addresses to the
   listing's atoms (the FNV word at 0x10330 is one of them) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tmix_call_spec B MT *)
#[using="MT"]
Definition tmix_call_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (h c : Z) (e : rcall) (P : list (Z * Z)),
afn_pre_na SEGS B MIX_CALL_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 h -> 0 <= h < 2 ^ 64 ->
getr regs 11 = w64 c ->
(* c is a slot of g_rec's call table or record.spill: program globals whose shadow is usable (CmdRecFacts'
   cmd_addressable_chk), so the checks on c->fn, c->nargs and c->args[a] pass; its constant address excludes the
   UBSan traps 0x8ad88, 0x8ad94, 0x8adcc and 0x8ae54 *)
((exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL) ->
(* the call it holds: function number, argument count, and each argument a string at the start of a live block;
   the strlen wrapper's reads of an argument: its bytes from acall_at, its tail word by cmd_heap_tail_vis (the
   terminator lies inside the argument's block). nargs <= 6 excludes the UBSan trap 0x8ae88, the arguments'
   blocks exclude 0x8aea0 *)
acall_at (ablocks B ly S) (rdW W mem) c e P ->
(* the read-only bytes of the image; the FNV-1a offset basis is RO_lit_10330 *)
cmd_ro_ok (rdW W mem) ->
st_nev S + EV_MIX_CALL <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_mix_call) regs mem md)
(apost_base SEGS B MIX_CALL_STK [] regs ly S W mem md EV_MIX_CALL
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (mixcall h (fst e) (snd e)) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(* no allocator call and no side-stack frame: the layout and the allocator state are the entry's (the frame form
   of meter class (a); it gives mo_le MT S S' 0 by mo_le_refl) *)
ly' = ly /\ S' = S)).
End e.
End f.
End d.
