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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 43 of its 73 lines of code are new or changed and 122 lines of the source are left out. *)
(* The contract of check_reply_answer on the ASan+UBSan build of plugin-hostd/fuzz_command (image
   fuzz_command.asan-ubsan).
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre_na
   (lib/B/Prog/PaNoChain.v, cgif's afn_pre without the frame-chain conjunct: neither it nor sup_reply_code reaches
   the allocator or a side-stack entry) at the entry, SRr of apost_base at the return. Functional content:
   fuzz_command's own released plain contract lib/Prog/check_reply_answer_c.v:12-40 (answer_ok, void post), in the
   option form the harness property states it, lib/Prog/HarnessProps.v:12-16 (answer_ok_m), with the ASan value of
   sup_reply_code (reply_code_a, lib/B/Prog/sup_reply_code_c.v) in place of the plain reply_code.
   The function (fuzz_command.c:201-222) holds the reply to the answer of the call that answered, through the strcmp
   wrapper (`___interceptor_strcmp`, reached through the 4-byte jump `__interceptor_trampoline_strcmp`); when no call
   answered, it asks sup_reply_code for the reply's code and, when that is not negative, asks that the message be
   the single word quit (verb_is inlined: the strcspn wrapper with " \t", then the strncmp wrapper with "quit"). Each
   check failing calls abort(); the pre-condition answer_ok_mA is what the harness property gives, so no abort edge is
   taken. Its five inline checks read g_rec's answer and reply pointers (g_rec's shadow says usable by CmdRecFacts'
   cmd_addressable_chk), the words' count and array pointer on the caller's real stack (inside the stack window
   [spZ regs, ly_stk_hi ly), whose shadow AR's zshadow_ok keeps usable at every state, YG0n.v:188), and the first
   slot of the word array (a live block); so the error path (a call of `__asan_report_load4` or
   `__asan_report_load8`) is not reached. The literals " \t" (.str 0x210e0) and "quit" (.str.4 0x21140) are among
   the image's read-only bytes (cmd_ro_ok's RO_lit_210e0, RO_lit_21140; what the strcspn and strncmp wrappers ask
   of them comes from cmd_aread_ok_chk and cmd_tail_vis), and the GOT word of g_rec (0xa6bc8) is cmd_ro_ok's
   RO_ptr_a6bc8; the shadow base's GOT word (0xa5f50) is a const cell of the allocator record (YG0f.v:194). The
   stack-protector cells musl's strcspn and strtol read (aguard_ok), the replace_str flag byte the atoi wrapper under
   sup_reply_code reads and the errno cell it reads and may write come from cmd_rec_cells; none is a premise.
   The function keeps w in s0 across its one program call (0x8878c mv s0,a0; 0x887bc jal sup_reply_code); it
   allocates nothing, so it carries no frame-chain premise (sup_reply_code is a non-allocating callee).

   UBSan (trap mode: a failed check branches to the `unimp` at 0x88870, a machine fault in cgif's model,
   lib/Reusable/YP00.v; the same `unimp` follows the `jal abort` at 0x8886c): 3 trap sites, all at
   fuzz_command.c:220, each excluded by a premise below (named at the premise):
     0x887c8  w mod 8 <> 0, the alignment check of the load of w->n (struct words is 8-aligned);
     0x88804  w->w == NULL, the null check of the load of w->w[0] (reached only when w->n == 1);
     0x8880c  w->w mod 8 <> 0, the alignment check of the same load (reached only when w->n == 1).
   B against A: the three checks are new (81 against 75 instructions) and the abort block moved (the strcmp test
   branches with bnez to it); the ASan checks, calls and their order are A's.

   Addresses: entry BASE + AF_check_reply_answer = 0x88754 (B, the pinned image). 81 instructions, frame 32 bytes,
   no side-stack frame, 5 inline checks, no loop; one program callee (sup_reply_code), three wrapper calls (strcmp,
   strcspn, strncmp); 3 UBSan trap sites. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* where the reply comes from (plain check_reply_answer_c.v:12-14 answer_ok, in HarnessProps.v:12-16's option form
   answer_ok_m), with the ASan wrapper's code reply_code_a: a call answered and the reply is its answer, or none did
   and the reply is a refusal or the reply of a lone quit *)
Definition answer_ok_mA (ans : option (list byte)) (xr : list byte) (n : Z) (w0 : list byte) : Prop :=
  match ans with
  | Some xa => xr = xa
  | None => reply_code_a xr < 0 \/ (n = 1 /\ w0 = S_QUIT)
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame, and below it the deeper of the wrappers' window
   (ecall_pre_stk segs B (2 * ESTACK), lib/B/Rt/RtDefs.v) and sup_reply_code's need *)
Definition CHECK_REPLY_ANSWER_STK : Z := 32 + Z.max (2 * ESTACK) SUP_REPLY_CODE_STK.
Definition EV_CHECK_REPLY_ANSWER : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the program callee, and the runtime entries with this tree's names *)
Hypothesis SRC : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tcheck_reply_answer_spec B MT *)
#[using="MT"]
Definition tcheck_reply_answer_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (w ww p0 n rep ans : Z) (xr w0 : list byte)
  (R : rstate) (O : list (Z * Z)),
afn_pre_na SEGS B CHECK_REPLY_ANSWER_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* g_rec's GOT word, the literals " \t", "quit" and "resp " (sup_reply_code's), and the bridge from the listing's
   object atoms to their addresses (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 w -> 0 <= w < 2 ^ 64 ->
(* the recorder (plain check_reply_answer_c.v:24-30): its answer and its reply, each a string in a live block
   (rec_repA), the reply NUL-terminated, and the bytes after each terminator up to the end of that 8-byte word
   readable (the strcmp wrapper's musl loop reads them, RtDefs.v's atail_vis) *)
rec_repA B ly S (rdW W mem) R O ->
r_reply R = Some (xr ++ [Z_to_bv 8 0]) -> no0 xr ->
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 rep -> 0 <= rep < 2 ^ 64 ->
atail_vis SEGS W mem (rep + Z.of_nat (length xr)) ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 ans -> 0 <= ans < 2 ^ 64 ->
(forall xa, r_answer R = Some xa -> atail_vis SEGS W mem (ans + Z.of_nat (length xa))) ->
(* the harness's struct words on the caller's real stack, above this call's window and inside the stack window
   (plain :31-35): its array pointer w->w at w + 16 and its count w->n at w + 24. `w mod 8 = 0` also
   excludes the UBSan trap site 0x887c8 (the alignment check of the load of w->n). *)
w mod 8 = 0 -> spZ regs <= w -> w + WORDS_W + 12 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (w + WORDS_W) 8 ww -> 0 <= ww < 2 ^ 64 ->
aval_mem (rdW W mem) (w + WORDS_N) 4 n -> 0 <= n < 2 ^ 31 ->
(* when there is one word (plain :36, word_slot): the array's first slot in a live block, and the word, a string
   inside the `copy` block (a harness word). The slot's block excludes the UBSan trap site 0x88804 (ww is in a live
   block, so at least 4096 by AR, YG0d.v:433-434: not NULL); `ww mod 8 = 0` (NEW for B) excludes the trap site
   0x8880c (the alignment check of the load of w->w[0]); the harness's array is a malloc block start, 16-aligned
   by AR (YG0d.v:434), so check_reply's caller has it. *)
(n = 1 ->
 in_blockA (ablocks B ly S) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\
 0 <= p0 < 2 ^ 64 /\ in_blockA (ablocks B ly S) p0 (Z.of_nat (length w0) + 1) /\ astr_atR (rdW W mem) p0 w0 /\
 atail_vis SEGS W mem (p0 + Z.of_nat (length w0))) ->
(* what the harness property gives (plain :37) *)
answer_ok_mA (r_answer R) xr n w0 ->
st_nev S + EV_CHECK_REPLY_ANSWER <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_reply_answer) regs mem md)
(apost_base SEGS B CHECK_REPLY_ANSWER_STK [] regs ly S W mem md EV_CHECK_REPLY_ANSWER
(fun ly' S' W' regs' mem' md' =>
 (* it returns (plain :38, void_post): nothing written outside its frame and the errno cell *)
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame, nor does sup_reply_code: layout and allocator state
    unchanged (M6; mo_le_refl gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
