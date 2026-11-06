(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 58 of its 87 lines of code are new or changed and 44 lines of the source are left out. *)
(* The contract of check_reply on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the side-stack frame bound as cgif's taddframe/tclose (lib/YC21.v:38, :71).
   Functional content: fuzz_command's own released plain contract lib/Prog/check_reply_c.v:24-68 (reply_ok, the
   reply and word premises, fp_void_post) and the harness property's form of the same facts,
   lib/Prog/HarnessProps.v:18-26 (msg_props: one reply, x ++ [NUL], no NUL in x, answer_ok_m, reply_ok), with two
   changes the ASan build asks for: the code is the ASan value of sup_reply_code (reply_code_a,
   lib/A/Prog/sup_reply_code_c.v), and the shape is named by its bytes (shape_of, REC_MOD_HOST_SHAPE,
   lib/Prog/RecFacts.v:311-319), not by its address in the plain image (img_str (shape_addr n w0)).
   The function (fuzz_command.c:225-259) asks for one reply that ends in its NUL and holds no other (the memchr
   wrapper, `___interceptor_memchr`, reached through the 4-byte jump `__interceptor_trampoline_memchr`, on all but
   the last byte), calls check_reply_answer, then sup_reply_code. A negative code must be declared
   (rec_code_declared) and the reply must be "resp <code>" (the snprintf wrapper writes it into `refusal`, the strcmp
   wrapper compares). Otherwise the reply must have the shape of the message's verb (the strlen wrapper,
   rec_shape_of) or mod-host's "resp 0" (syntax_reply_matches, twice). Each failed check calls abort(); the
   pre-condition reply_okA, with answer_ok_mA, is what the harness property gives, so no abort edge is taken.

   Its ten inline checks read g_rec's fields nreplies, reply_size and reply (g_rec's shadow says usable by
   CmdRecFacts' cmd_addressable_chk), the reply's last byte (a live block), the words' count and array pointer on
   the caller's real stack (inside the stack window [spZ regs, ly_stk_hi ly), whose shadow AR's zshadow_ok keeps
   usable at every state, YG0n.v:188; the function only reads them), and the array's first slot (a live block); so
   the error path (a call of `__asan_report_load1/4/8`) is not reached. `refusal[32]` lies in a class-1 side-stack
   frame (`__asan_stack_malloc_1` with 96, descriptor "1 32 32 11 refusal:227" at 0x18ebf), released inline before
   the return (shadow 0xf8, then 0xf5, the flag byte cleared), so the post has no new frame. The literals
   "resp %d" (0x210c0) and "resp 0" (0x210e0), and every literal and table the callees read, are among the image's
   read-only bytes (cmd_ro_ok; what the snprintf wrapper asks of "resp %d" comes from cmd_aread_ok_chk and
   cmd_tail_vis; "resp 0" handed to syntax_reply_matches is astr_argA's read-only branch: cmd_ro_in,
   cmd_img_facts' cif_ro_unowned, cmd_addressable_chk, cmd_hull_vis_chk). The GOT words of g_rec (0xa7068) and of
   the use-after-return flag (0xa6448) are cmd_ro_ok's RO_ptr_a7068 / RO_ptr_a6448 (CmdRo.v:431-439). The heap
   strings' tails the wrappers read (the reply, the answer, the first word) come from cmd_heap_tail_vis where not
   stated. The stack-protector cells the snprintf, strcspn and strtol bodies read (aguard_ok), the replace_str flag
   byte and the errno cell the atoi wrapper under sup_reply_code reads come from cmd_rec_cells; none is a premise.
   The function's s0 is its own frame pointer (0x86db0 addi s0,sp,128), so it keeps no caller value in s0 at a
   program call; its calls' frame chains come from afn_pre's chain (achain_push at the frame pointer, the entry chain when s0 is
   unchanged, achain's empty case for a value below alloc_ceiling; the survey of s0 at every allocating call site).

   Addresses: entry BASE + AF_check_reply = 0x86d78 (M, the pinned image). 242 instructions, 10 inline checks, no
   loop on the walked path (the one CFG loop is the real-stack probe of the fallback branch, which the walk does
   not take: the use-after-return flag is pinned and the stack-malloc contract returns a frame). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the shape the reply must have (plain check_reply_c.v:21-25 img_str (shape_addr n w0)), by its bytes: the shape
   the message's verb declares, or mod-host's "resp 0" when the message has no word *)
Definition shape_strA (n : Z) (w0 : list byte) : list byte :=
  if n =? 0 then REC_MOD_HOST_SHAPE else shape_of w0.
(* the reply property (plain check_reply_c.v:29-32 reply_ok) with the ASan wrapper's code reply_code_a; refusal_text
   is the plain proof's own (check_reply_c.v:27) *)
Definition reply_okA (n : Z) (w0 xr : list byte) : Prop :=
  (reply_code_a xr < 0 -> declared (reply_code_a xr) = true /\ xr = refusal_text (reply_code_a xr)) /\
  (0 <= reply_code_a xr ->
     reply_matches (shape_strA n w0) xr = true \/ reply_matches REC_MOD_HOST_SHAPE xr = true).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 128-byte frame and up to 16 bytes of realignment (`andi sp,sp,-32` at
   0x86db4), and below that the deepest callee: check_reply_answer (32 + 3 * ESTACK), above the snprintf wrapper
   (3 * ESTACK: 6,672 bytes measured below its entry), syntax_reply_matches,
   rec_shape_of, sup_reply_code, rec_code_declared, the strcmp wrapper (2 * ESTACK), and the memchr and strlen
   wrappers and __asan_stack_malloc_1 (ESTACK) *)
Definition CHECK_REPLY_STK : Z :=
  144 + Z.max CHECK_REPLY_ANSWER_STK (Z.max (3 * ESTACK) (Z.max SYNTAX_REPLY_MATCHES_STK (Z.max REC_SHAPE_OF_STK
    (Z.max SUP_REPLY_CODE_STK (Z.max REC_CODE_DECLARED_STK (2 * ESTACK)))))).
Definition EV_CHECK_REPLY : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the program callees *)
Hypothesis CRA : forall fx0 : YK11.FPState, @tcheck_reply_answer_spec fx0 rc SK PI B MT.
Hypothesis SRC : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis RCD : forall fx0 : YK11.FPState, @trec_code_declared_spec fx0 rc SK PI B MT.
Hypothesis RSO : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis SRM : forall fx0 : YK11.FPState, @tsyntax_reply_matches_spec fx0 rc SK PI B MT.
(* the runtime entries, with this tree's and cgif's names: the class-1 side-stack frame and its inline release, and
   the wrappers *)
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState, @amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) A_SSP_GOT A_SSP_GUARD.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
(* `using MT`: the post has no meter conjunct (frame form, class (b)), so MT is named here to keep the uniform
   signature tcheck_reply_spec B MT *)
#[using="MT"]
Definition tcheck_reply_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (w ww p0 n rep ans : Z) (xr w0 : list byte)
  (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B CHECK_REPLY_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 7 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the GOT words, the literals "resp %d" and "resp 0" and every literal and table the callees read, each byte of
   them read-only (what astr_argA's read-only case asks when "resp 0" goes to syntax_reply_matches); and the bridge
   from the listing's object atoms to their addresses (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
getr regs 10 = w64 w -> 0 <= w < 2 ^ 64 ->
(* the recorder (plain check_reply_c.v:43-53; HarnessProps.v:24): one reply, a string in a live block that ends in
   its NUL and holds no other, and the answer, a string in a live block (rec_repA); the bytes after each terminator
   up to the end of that 8-byte word readable (the wrappers' musl loops read them, RtDefs.v's atail_vis) *)
rec_repA B ly S (rdW W mem) R O ->
r_nreplies R = 1 -> r_reply R = Some (xr ++ [Z_to_bv 8 0]) -> no0 xr ->
aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 rep -> 0 <= rep < 2 ^ 64 ->
atail_vis SEGS W mem (rep + Z.of_nat (length xr)) ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 ans -> 0 <= ans < 2 ^ 64 ->
(forall xa, r_answer R = Some xa -> atail_vis SEGS W mem (ans + Z.of_nat (length xa))) ->
(* the harness's struct words on the caller's real stack, above this call's window and inside the stack window
   (plain :54-58; read only): its array pointer w->w at w + 16 and its count w->n at w + 24 *)
w mod 8 = 0 -> spZ regs <= w -> w + WORDS_W + 12 <= ly_stk_hi ly ->
aval_mem (rdW W mem) (w + WORDS_W) 8 ww -> 0 <= ww < 2 ^ 64 ->
aval_mem (rdW W mem) (w + WORDS_N) 4 n -> 0 <= n < 2 ^ 31 ->
(* when there is a word (plain :59-63): the array's first slot in a live block, and the first word, a string inside
   the `copy` block (a harness word). The slot is 8-aligned: the B statement's conjunct `ww mod 8 = 0`
   (lib/B/Prog/check_reply_c.v:165, the UBSan trap 0x87064 of the asan-ubsan build, the 8-byte load w->w[0]),
   carried here so that the A and B statements agree (this port's decision); check_reply_answer asks it under n = 1.
   The harness's array is the malloc block words_of made (fuzz_command.c:121), whose start AR makes 16-aligned
   (YG0d.v:434), so the caller LLVMFuzzerTestOneInput has it *)
(n <> 0 ->
 in_blockA (ablocks B ly S) ww 8 /\ ww mod 8 = 0 /\ aval_mem (rdW W mem) ww 8 p0 /\
 0 <= p0 < 2 ^ 64 /\ in_blockA (ablocks B ly S) p0 (Z.of_nat (length w0) + 1) /\ astr_atR (rdW W mem) p0 w0 /\
 atail_vis SEGS W mem (p0 + Z.of_nat (length w0))) ->
(* what the harness property gives (plain :64-65; HarnessProps.v:25-26) *)
answer_ok_mA (r_answer R) xr n w0 -> reply_okA n w0 xr ->
st_nev S + EV_CHECK_REPLY <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_reply) regs mem md)
(apost_baseF SEGS B CHECK_REPLY_STK [] regs ly S W mem md EV_CHECK_REPLY
(fun ly' S' W' regs' mem' md' =>
 (* it returns (plain :66, fp_void_post): nothing written outside its frames and the errno cell *)
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* its only state change is the class-1 side-stack frame, taken and released; neither it nor a callee reaches the
    heap allocator (meter class (b): the caller chains the meter through ameter_fs_laws' set_fs laws) *)
 ly' = ly /\ exists f, S' = set_fs f S)).
End e.
End f.
End d.
