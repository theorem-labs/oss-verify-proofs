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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 86 of its 114 lines of code are new or changed and 124 lines of the source are left out. *)
(* The contract of LLVMFuzzerTestOneInput on the ASan+UBSan build of plugin-hostd/fuzz_command (image
   fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   This is the per-function contract of the entry function, in the same form as the 63 others: afn_pre at
   BASE + AF_LLVMFuzzerTestOneInput, SRr of apost_base at the return (cgif_file_fuzzer's lib/YC7x.v:72-167,
   lib/YC21.v:33-88). It is NOT the program interface: that is lib/B/YCfn.v (tfib_lib_pre_x / tfib_lib_post_x /
   tfib_lib_contract_x, with the call index j and the global invariant GI), which CmdLibX.v closes from this contract.
   The pre-condition takes what tfib_lib_pre_x gives in the same words (the driver's payload in a0/a1, the
   payload block or the empty object, garr8 of its bytes, frames S = [], GI_cmdA j); the post-condition gives the
   journal, a0 = 0, the blocks of the entry, the payload's bytes unchanged, GI_cmdA (S j) and the meter.

   What the function does (fuzz_command.c:505-539, fuzz.h:38-77): it refuses a payload of 2^26 bytes or more
   (0x8656c srli a1,a1,0x1a; 0x86570 bnez to the return 0x86b10, which the pre-condition excludes); calls
   rec_clear; zeroes g_rec.state and g_rec.host_settings with two inline 8-byte stores (0x865ac, 0x865d0, each
   behind an inline check; A called the memory-checking runtime's memset entry here, B does not); then runs at most
   32 = MESSAGES_MAX passes of the top loop (header 0x86654). Each pass reads a flags byte and a 16-bit length from
   the payload (fuzz_u8, fuzz_u16), takes at most min(length, 8192, rest) bytes (fuzz_take), sets g_rec.refuse =
   flags & 1 and g_rec.code = rec_codes[(flags >> 1) % rec_ncodes], calls send_message on the message, builds the
   message's words (words_of, inlined: three allocations of the wrapper malloc, text len+1 <= 8193 bytes at
   0x86778, copy len+1 <= 8193 at 0x86784, pointer array (len/2+2)*8 <= 32,784 at 0x86798; a trim loop 0x86800 and
   a split loop 0x868e4 that call the strspn and strcspn wrappers), calls check_reply, check_arity, check_words,
   check_refusal and check_round_trip, and frees the three blocks (words_free, inlined: 0x86a40, 0x86a48, 0x86a50).
   After the loop it calls rec_clear again, sets g_quitting = 0 and returns 0. Every block it or a callee allocates
   is freed before the return.

   Functional content, from fuzz_command's own released plain proof, used as it is:
   - the message decoding: lib/Prog/SlotSpec.v:28-37 (hdr_n, msg_len, msg_rf, msg_cd) and the words of a message,
     lib/Prog/SlotSpec.v:178-230 (Verbs.words (Verbs.line M));
   - the property of each message that rules out the 18 abort edges of the five checks, lib/Prog/HarnessProps.v:18-37
     (msg_props, harness_props), proved as harness_props_holds (lib/Prog/HarnessPropsProof.v:1479), with
     step_frame (:1363-1364) for "at most 2 recorded calls";
   - the loop invariant's recorder part, lib/Prog/SlotInv.v:230-234 (RF), here `cmd_rec_invA`, which the post
     states at the exit (after the second rec_clear, with no recorder block left and g_quitting = 0);
   - the global invariant, lib/Prog/Slot.v:19-21 (GI_cmd), here lib/B/YCfn.v's (CmdGlob's) GI_cmdA.

   The error paths: each of the 21 inline checks reads the shadow byte at (a >> 3) + 0x7fff8000 of a payload byte
   (in the payload block), of a byte of the text / copy / pointer-array blocks (fresh blocks of the malloc rule), of
   g_rec / g_quitting or of rec_ncodes / rec_codes (CmdRecFacts' cmd_addressable_chk), so no call of
   __asan_report_* is reached. The abort edge 0x86b54 (a NULL from malloc: 0x867a4, 0x867ac, 0x867b0) is not taken:
   cgif's amalloc04_rule returns a block at 4096 or above. The abort edges of the checks are excluded by the callees'
   pre-conditions, which the walk discharges from harness_props_holds.

   Facts of the per-binary record, not premises: the GOT words (0xa6bc8 g_rec, 0xa6bd0 rec_ncodes, 0xa6bd8
   rec_codes, 0xa6be0 g_quitting) are cmd_ro_ok's RO_ptr_* bytes; the stack-protector cells the strspn / strcspn
   bodies (here) and the atoi, strtol, snprintf, strtok_r bodies (in callees) read (aguard_ok, 0xa6bf8 / 0x604158),
   the replace_str flag byte and the errno cell come from cmd_rec_cells; what the strspn / strcspn wrappers ask of
   the set " \t" (0x210e0) comes from cmd_aread_ok_chk and cmd_tail_vis, and of the text block from its block
   (cmd_heap_tail_vis); g_rec / record.spill / g_quitting unowned and in the image from cmd_prog_unowned. Facts about
   its own frame and computation (the harness words' blocks, &w = sp + 120 in the stack window, 8-aligned) are the
   walk's, not premises. Its calls' frame chains come from afn_pre's chain (achain_chain_pre, YCbq.v:327): at the
   first rec_clear (0x86584) s0 is still the caller's, so the entry chain serves; from 0x865f0 (li s0,-1) s0 is -1 at
   every later program and allocator call, i.e. 2^64 - 1, misaligned and above ly_top - 16, so the chain is achain's
   empty case (YCbq.v:265). No presence of the stack up to ly_top is assumed.

   UBSan (trap mode: a failed check branches to the `unimp` at 0x86b50, a machine fault in cgif's model,
   lib/Reusable/YP00.v). 22 trap sites (the UBSan trap-site table), none needs a new premise:
   - fuzz.h:57 `*in->p++` (0x8665c, 0x8668c, 0x8688c: p + 1 <= 1, i.e. the cursor is null or p + 1 wraps) and
     fuzz.h:74 `in->p += n` (0x866c0: ~p < n, the sum wraps): the cursor runs over [p, p + n] of the payload block,
     and fuzz_u8 / fuzz_take run only while bytes remain (in.n > 0, so n > 0 and the payload is a live block, not
     A_EMPTY); AR puts that block in [4096, alloc_ceiling) (YG0d.v:433-434), so no sum wraps and none is <= 1.
     EXISTING premise `0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S)`.
   - fuzz_command.c:526 `% rec_ncodes` (0x8670c, division by zero) and `rec_codes[...]` (0x86720, the index times 4
     past the array's end): rec_ncodes is `const int` 58 at 0x21d00 and rec_codes its 58-entry array at 0x21be0 (M,
     the B ELF), both read-only bytes, so the divisor is 58 and the index (flags >> 1) % 58 < 58. EXISTING premise
     cmd_ro_ok (with cmd_val_objs).
   - fuzz_command.c:126-140, words_of over its own fresh blocks (0x867cc, 0x867dc, 0x867e0 text + len; 0x86808,
     0x86818, 0x8681c, 0x86844 the trim loop's text + len - 1; 0x868d0 copy null; 0x86900, 0x86990 t + strspn /
     strcspn; 0x86928 n++ overflow; 0x86944, 0x86958, 0x8695c w + 8n null / wrap; 0x86964 w + 8n misaligned;
     0x869b0 t == (char * ) -1 before t++): facts of its own computation, not premises: the three blocks come from
     amalloc04_rule (live, at 4096 or above, 16-aligned, of len + 1 and (len / 2 + 2) * 8 bytes, len < 8193), t and
     the word count stay inside them (n <= len / 2 + 1 < 2^31).
   The image's other `unimp`, 0x86b5c, follows `jal abort`; nothing reaches it.

   Addresses: entry BASE + AF_LLVMFuzzerTestOneInput = 0x86530 (B, the pinned image). 434 instructions, 21 inline
   checks (load1 8, load4 2, load8 2, store1 3, store4 3, store8 3), 22 UBSan trap sites, 3 loops, real frame 256
   bytes (no side-stack frame: `struct words w` is at sp + 120 on the real stack). Program calls: rec_clear (0x86584,
   0x86af0), send_message (0x8675c), check_reply (0x86a10), check_arity (0x86a18), check_words (0x86a20),
   check_refusal (0x86a28), check_round_trip (0x86a38). Runtime calls: the malloc wrapper x3, the free wrapper x3,
   strnlen (0x86768), strspn (0x868f8), strcspn (0x86988) wrappers, the memory-checking runtime's memcpy entry x2
   (0x867c0, 0x868c4); no memset entry. Objects of the listing it loads: A_OBJ 0, 2, 3, 4, 5, 6
   (the image's function table). Against A: the memset call became two checked stores, and the 22 trap sites are new. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The recorder part of the top loop's invariant: lib/Prog/SlotInv.v:230-234 (RF), over the ASan+UBSan reader and
   the allocator's blocks. g_rec and record.spill hold R, the recorder owns the blocks O, the spill holds no call
   (the record() spill arm is dead: at most 2 recorded calls, step_frame), g_quitting holds q, and the live blocks
   are the recorder's and the blocks bl0 that were live at the entry, and no other. *)
Definition cmd_rec_invA (B : asyms) (ly : alayout) (S : astate) (rd : reader) (bl0 : list (Z * Z))
  (R : rstate) (O : list (Z * Z)) (q : Z) : Prop :=
rec_repA B ly S rd R O /\ r_spill R = (0, []) /\ (length (r_calls R) <= 2)%nat /\
aval_mem rd A_G_QUITTING 4 q /\ 0 <= q < 2 ^ 32 /\
Permutation (ablocks B ly S) (O ++ bl0).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* The stack this call needs: its own 256-byte frame (addi sp,sp,-256 at 0x86530) and the deepest window below
   it: the program callees' own needs, the malloc and free wrappers' ASTACK (cgif lib/YG0d.v:17), the strnlen,
   strspn and strcspn wrappers' 2 * ESTACK, the memcpy entry's ESTACK. *)
Definition LTOI_NEED : Z :=
  256 + fold_right Z.max ASTACK
    [2 * ESTACK; ESTACK; REC_CLEAR_STK; SEND_MESSAGE_STK; CHECK_REPLY_STK; CHECK_ARITY_STK; CHECK_WORDS_STK;
     CHECK_REFUSAL_STK; CHECK_ROUND_TRIP_STK].
(* The window the contract states is the interface's, LLVMF_STK = 32768 (lib/B/YCfn.v), as cgif's own walk of
   its LLVMFuzzerTestOneInput runs in LLVMF_STK (lib/A/ACez.v:47, :60): then afn_pre and the journal are those of
   tfib_lib_pre_x / tfib_lib_post_x word for word. The walk shows LTOI_NEED <= LTOI_STK by computation
   (the image's function table measures 17,760 with every runtime window charged ASTACK). *)
Definition LTOI_STK : Z := LLVMF_STK.
(* The recorder state at the loop head of the first message: no call, no answer, no reply, the spill empty (GI_cmdA
   and rec_clear), g_rec.state and g_rec.host_settings zeroed (fuzz_command.c:514-515); refuse and code are written
   before each send. *)
Definition R_ENTRY : rstate := RState 0 0 [] (0, []) None 0 None 0 0.
(* g_rec.refuse and g_rec.code as the loop sets them before a send (fuzz_command.c:525-526) *)
Definition rec_set_rc (R : rstate) (rf cd : Z) : rstate :=
  RState rf cd (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) (r_state R) (r_host R).
(* The allocator events of the top loop over the payload, message by message, summing the callees' own counts at
   the recorder state and message each one is handed. A message is carved as the plain proof carves it
   (lib/Prog/SlotSpec.v:28-34: hdr_n header bytes, msg_len message bytes, msg_rf / msg_cd for refuse and code); its
   words are Verbs.words (Verbs.line D) (SlotSpec.v:205); the recorder after the first send is verbs_receive's run
   vr_runA on the cleared state (send_message's post). Per message: send_message, words_of's three mallocs and
   words_free's three frees, the five checks, check_round_trip at the state after the first send (its second send
   clears that state and leaves the same calls: rt_ok, lib/Prog/check_round_trip_c.v:26-29, which is why the next
   message starts from it). At most 32 messages (MESSAGES_MAX); the loop stops when the payload is used up. The
   result also carries the recorder state after the last message, whose arguments the final rec_clear frees. *)
Fixpoint ev_msgs (fuel : nat) (R : rstate) (pl : list byte) : Z * rstate :=
  match fuel with
  | O => (0, R)
  | S f =>
    match pl with
    | [] => (0, R)
    | _ :: _ =>
      let n := Z.of_nat (length pl) in
      let h := Z.to_nat (SlotSpec.hdr_n n) in
      let hdr := firstn h pl in
      let len := Z.to_nat (SlotSpec.msg_len n hdr) in
      let D := firstn len (skipn h pl) in
      let R0 := rec_set_rc R (SlotSpec.msg_rf hdr) (SlotSpec.msg_cd hdr) in
      let R1 := fst (fst (vr_runA (RecModel.rec_clear R0) D)) in
      let ws := Verbs.words (Verbs.line D) in
      let '(k, Rf) := ev_msgs f R1 (skipn (h + len) pl) in
      (EV_SEND_MESSAGE R0 D + (3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
       EV_CHECK_ROUND_TRIP R1 ws + k, Rf)
    end
  end.
(* The allocator events of one call: rec_clear at the entry (no call recorded, GI_cmdA), the 32-pass loop, and
   rec_clear at the exit. A function of the payload, because send_message's and check_round_trip's counts follow
   the route each message takes (verbs_receive_c.v ev_vr); a constant would charge every message the deepest
   route. B makes the same allocator entry calls on each route as A (the same C; UBSan moves calls between
   functions, not their number), so the worst case is A's measured 2,372 (32 x `pin_set a b c`);
   EV_LIB is 2,900 (lib/B/YCfn.v), so closing tfib_lib_contract_x needs
   `EV_LTOI pl <= EV_LIB` for every payload (lib/B/Prog/HarnessArgsEv.v, ev_ltoi_lib). *)
Definition EV_LTOI (pl : list byte) : Z :=
  let '(k, Rf) := ev_msgs 32 R_ENTRY pl in EV_REC_CLEAR R_ENTRY + k + EV_REC_CLEAR Rf.
(* The bytes live at once above the entry's blocks: the recorder's blocks between two messages (at most 2 calls
   of at most 6 arguments, the answer and the reply: 14 blocks of at most LMAX + 2 bytes, RecInv.v's bound), the
   three words blocks (8193 + 8193 + 32,784), and the largest need of a callee that allocates. *)
Definition LIVE_LTOI : Z :=
  14 * (LMAX + 2) + (8193 + 8193 + 32784) +
  Z.max LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* The meter: every one of the EV_LTOI pl allocator events charged the cost of the largest allocation of the
   program (the pointer array, 32,784 bytes) and of a free. The callees' own costs (XM_SEND_MESSAGE MT R D,
   XM_CHECK_WORDS MT ws, XM_CHECK_ROUND_TRIP MT R ws, XM_REC_CLEAR MT R) are each a sum of mo_malloc MT k
   (k <= 32,784) and mo_free MT over at most their own event count, so this bound dominates their sum by
   ameter_laws (mo_malloc_mono, mo_malloc_nonneg, mo_free_nonneg). *)
Definition XM_LTOI (pl : list byte) : Z := EV_LTOI pl * (mo_malloc MT 32784 + mo_free MT).
(* the program callees' contracts, never restated *)
Hypothesis HREC_CLEAR : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
Hypothesis HSEND_MESSAGE : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_REPLY : forall fx0 : YK11.FPState, @tcheck_reply_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_ARITY : forall fx0 : YK11.FPState, @tcheck_arity_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_WORDS : forall fx0 : YK11.FPState, @tcheck_words_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_REFUSAL : forall fx0 : YK11.FPState, @tcheck_refusal_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_ROUND_TRIP : forall fx0 : YK11.FPState, @tcheck_round_trip_spec fx0 rc SK PI B MT.
(* the runtime entries it reaches itself: the allocator rules (cgif lib/YC5d.v:56-96, without the trace premise,
   as in this tree's C5 conversion), the memory-checking runtime's memcpy entry (cgif lib/YG0d.v:317), the strnlen
   wrapper over a buffer that need hold no NUL (lib/Rt/StrnlenDef.v, the form proved at the trampoline, here B's
   0x45180, with musl memchr's constants 0x10358..0x10378 read through consts_view: B's memchr 0x9e59c loads them
   at 0x9e5f8 / 0x9e600, the same addresses and the same bytes as A's, M, both ELFs) and the strspn and strcspn
   wrappers (lib/B/Rt/RtString.v). No memset entry: B zeroes g_rec.state and g_rec.host_settings with two stores. *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRNLEN : forall fx0 : YK11.FPState, @astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Definition tLLVMFuzzerTestOneInput_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p n : Z) (pl : list byte) (j : nat),
afn_pre SEGS B LTOI_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the image's constants it and its callees read: the read-only bytes (the recorder GOT words, rec_ncodes,
   rec_codes, the " \t" literal, g_parsed, g_shapes, g_call_words, the verb tables, every literal) *)
cmd_ro_ok (rdW W mem) ->
(* the bridge from the listing's object atoms to the addresses named here (lib/B/Prog/CmdObj.v) *)
cmd_val_objs ->
(* the driver's arguments (tfib_lib_pre_x, lib/B/YCfn.v): the payload in a live block, or the empty object
   when it has no byte, and its bytes *)
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
n = Z.of_nat (length pl) ->
garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
frames S = [] ->
(* the global invariant at this call (lib/B/Prog/CmdGlob.v): the recorder holds no call, no answer, no reply,
   the spill no call, and g_quitting is 0 *)
GI_cmdA j (rdW W mem) ->
st_nev S + EV_LTOI pl <= EV_MAX -> blocks_bytes S + LIVE_LTOI <= LIVE_MAX ->
mo_ok MT S (XM_LTOI pl) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md)
(apost_baseF SEGS B LTOI_STK cmd_PG regs ly S W mem md (EV_LTOI pl)
(fun ly' S' W' regs' mem' md' =>
 (* it returns 0 *)
 getr regs' 10 = w64 0 /\
 (* every block it or a callee allocated is freed: the live blocks are the entry's *)
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* the payload's bytes are unchanged *)
 (forall i, 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (* the top loop's invariant at the exit, after the second rec_clear: the recorder is rec_clear of the last
    message's state, owns no block, holds no spilled call, and g_quitting is 0 *)
 (exists R : rstate, cmd_rec_invA B ly' S' (rdW W' mem') (ablocks B ly S) (RecModel.rec_clear R) [] 0) /\
 (* the global invariant for the next call *)
 GI_cmdA (Datatypes.S j) (rdW W' mem') /\
 (* the meter and the live bytes, chained by a caller *)
 mo_le MT S S' (XM_LTOI pl) /\ blocks_bytes S' <= blocks_bytes S + LIVE_LTOI)).
End e.
End f.
End d.
