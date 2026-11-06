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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 21 of its 48 lines of code are new or changed and 125 lines of the source are left out. *)
(* The contract of rec_code_declared on the ASan+UBSan build of plugin-hostd/fuzz_command (image
   fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre_na
   (lib/B/Prog/PaNoChain.v, cgif's afn_pre without the frame-chain conjunct: the function calls nothing) at the
   entry, SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_code_declared_c.v:15-27 (a0 = 1 when the code is declared, else 0) and its model
   lib/Prog/RecFacts.v:358-369 (rec_codes, declared), used as they are.
   The function (recorder.c:57-65) scans the 58 entries of the read-only table rec_codes (0x21be0, 232 bytes) and
   returns 1 at the first entry equal to the code, else 0. Each 4-byte load of an entry has an inline check; rec_codes
   is a registered global of 232 bytes (asan_globals descriptor, size_with_redzone 288), so its shadow bytes say
   usable (CmdRecFacts' cmd_addressable_chk, which the walk applies; no premise here) and the error path (a call of
   `__asan_report_load4`) is not reached. The table's bytes are RO_rec_codes of cmd_ro_ok (lib/B/Prog/CmdRo.v),
   which are the plain proof's rec_codes_bytes (lib/Prog/rec_code_declared_c.v:12-13); the function forms the
   table's address pc-relatively (auipc/addi at 0x8966c), with no GOT word.

   UBSan: no trap site and no `unimp` in the function (the trap-site summary); the loop counter and pointers step by
   plain adds without checks. B's instruction stream is A's with only the pc-relative offsets changed.

   Addresses: entry BASE + AF_rec_code_declared = 0x89658 (B, the pinned image). 31 instructions, frame 16 bytes,
   no side-stack frame, 1 inline check, 1 loop (58 iterations, `li a4,58` at 0x89674, back edge 0x896a0 ->
   0x8967c), no call, 0 UBSan trap sites. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
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
(* the stack this call needs: its own 16-byte frame; it calls nothing *)
Definition REC_CODE_DECLARED_STK : Z := 16.
Definition EV_REC_CODE_DECLARED : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_code_declared_spec B MT *)
#[using="MT"]
Definition trec_code_declared_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (c : Z),
afn_pre_na SEGS B REC_CODE_DECLARED_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the code, an int, sign-extended in a0 (plain rec_code_declared_c.v:18-19) *)
getr regs 10 = w64 c -> -2^31 <= c < 2^31 ->
(* the table rec_codes, among the image's read-only bytes (plain :20), and the bridge from the listing's object
   atoms to its address (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_REC_CODE_DECLARED <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_code_declared) regs mem md)
(apost_base SEGS B REC_CODE_DECLARED_STK [] regs ly S W mem md EV_REC_CODE_DECLARED
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (if declared c then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
