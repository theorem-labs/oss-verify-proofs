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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 82 of its 108 lines of code are new or changed and 126 lines of the source are left out. *)
(* The contract of check_round_trip on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post: send_message's verbs_receive reaches
   the snprintf wrapper); the pre carries rounding mode 0. The callees' contracts are taken at every FP state
   (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (lib/YC7x.v:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/check_round_trip_c.v:23-78 (acted_m; rt_ok; the recorder's
   state after the call agrees with the one before on refuse, code, spill, state and host, and g_quitting is kept),
   with the ASan wrappers' values in the model (this port's decision: atoi_a and reply_code_a of
   lib/B/Prog/sup_reply_code_c.v in VerbsRun.run_receive, lib/Spec/VerbsRun.v:59, in place of the plain vr_run).
   check_round_trip(w, state_before, host_before) (H/fuzz_command.c:459-503) returns at once when the message has no
   word or the daemon did not act (acted() inlined: g_quitting || g_rec.ncalls > 0). Otherwise it copies the
   recorder's calls into first[] (rec_calls_copy, 0x8849c), notes g_quitting, the state and the host settings, copies
   the reply with the strdup wrapper (0x88528, `___interceptor_strdup`, reached through the 4-byte jump
   `__interceptor_trampoline_strdup`), puts back state_before and host_before, sends the words joined by one space
   again (joined 0x88558, send_message 0x88564, free 0x8856c), and checks that the calls (rec_calls_equal, 0x88594),
   the reply (the strcmp wrapper, 0x885b0), g_quitting, the state and the host settings are the same; then it frees
   the copies (rec_calls_free, 0x88600) and the reply's copy (0x88608). Every mismatch, and a null strdup result,
   goes to the abort edge (0x8868c: __asan_handle_no_return, then abort); the pre-condition rt_okA (the round trip
   holds in the model) and the strdup rule (a block at or above 4096) show that the edge is not taken. The callees'
   contracts are Section hypotheses, not restated.

   Frame: 256 bytes on the real stack (saves of ra, s0-s11; `andi sp,sp,-32` realigns, 0x88318, s1 = the realigned
   stack pointer), and first[16] (896 bytes) with len in a class-5 side-stack frame of 1056 bytes from
   `__asan_stack_malloc_5` (0x8834c), laid out with left redzone 0xf1 (shadow +0..3), `__asan_set_shadow_f8`
   (0x883d0) / `__asan_set_shadow_00` (0x88420) over shadow +4..115, right redzone 0xf3 (shadow +116..131); on
   return `__asan_set_shadow_f8` (0x8861c), the frame-done magic (0x88628) and `__asan_stack_free_5` (0x88638).
   Only the side-stack branch is stated: the use-after-return flag (the GOT word 0xa5fa8) is pinned by the allocator
   record (cgif lib/YG0f.v:188, lib/YG0d.v:464) and the stack-malloc contract returns a frame (lib/YC85.v:292-306),
   so the real-stack fallback (0x88364-0x8837c) is dead (this port's decision). first[] is at frame + 32 (0x88494) and
   len at s1 + 144 in the real-stack part (0x88550).

   Addresses: entry BASE + AF_check_round_trip = 0x882d8 (B, the pinned image). 287 instructions, 1 loop (the dead
   stack probe 0x88370), 14 inline checks, each a read of the shadow byte at (a >> 3) + SHADOW_OFF through the
   shadow base word (0xa5f50, a RELRO word arodata_okP keeps): load4 on w->n (0x88438), on g_quitting (0x88458,
   0x884a4, 0x885bc) and on g_rec.ncalls (0x8847c, 0x8857c); load8 on g_rec.state (0x884c8, 0x885d0),
   g_rec.host_settings (0x884e0, 0x885e4) and g_rec.reply (0x8850c, 0x8859c); store8 on g_rec.state (0x88534) and
   g_rec.host_settings (0x88544). The error path (a call of `__asan_report_*`) is not reached: w is on the caller's
   real stack, in the stack window, whose shadow AR's zshadow_ok keeps usable at every state (YG0n.v:188), and
   g_rec and g_quitting are registered globals, whose shadow is usable by `cmd_addressable_chk`. g_rec and
   g_quitting are loaded from the GOT words 0xa6bc8 and 0xa6be0 (cmd_ro_ok's RO_ptr entries), whose auipc atoms the
   walk ties to their addresses with cmd_val_objs. The flag byte, errno cell and stack guard that send_message's
   verbs_receive reaches come from `cmd_rec_cells`.
   The words are harness words, pointers into words_of's `copy` block (fuzz_command.c:120), read only by joined
   (0x88558), before send_message frees any recorder block, so they are stated as live blocks; rec_calls_equal gets
   the copies and g_rec's arguments, all live blocks. s0 is the frame pointer (0x88314 addi s0,sp,256) at every
   call: no caller value, no achain premise. joined gets len at s1 + 144, a slot of this frame's real stack part
   (below this entry's stack pointer, so below ly_top); joined's premise on len (its 8 bytes present; B's joined
   asks no frame chain from len, pass 5b) comes from this frame: afn_pre's window.

   UBSan (B only, 1 trap site, to the `unimp` at 0x88694): 0x88428 traps when `w` is not 8-aligned
   (fuzz_command.c:468, the read of w->n). The premise `W0 mod 8 = 0` below excludes it; LLVMFuzzerTestOneInput,
   the one caller, passes its own `struct words` on its real stack, which it aligns. Every other pointer this
   function forms is a constant offset of g_rec, of its own frame or of the class-5 frame, so no other check
   remains; the checks of the words and of the tables are inside joined, rec_calls_copy, rec_calls_equal and
   rec_calls_free, whose statements carry them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtAlloc04 RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c check_round_trip_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_reply_code_c joined_c send_message_c rec_calls_copy_c rec_calls_equal_c rec_calls_free_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PJoinR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.
Module PCrt := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_round_trip_c.
(* the plain proof's rt_ok (check_round_trip_c.v:26-30), with the daemon's run as this build computes it: the
   atoi wrapper's value and reply_code_a (lib/B/Prog/sup_reply_code_c.v) in VerbsRun.run_receive, which is
   vr_runA by definition (lib/B/Prog/verbs_receive_c.v:66-67), the run send_message's post states *)
Definition rt_okA (R : rstate) (q sb hb : Z) (ws : list (list byte)) : Prop :=
ws <> [] -> PCrt.acted_m R q = true ->
let '(R2, _, quit2) :=
  VerbsRun.run_receive atoi_a reply_code_a (rec_clear (set_host (set_state R sb) hb)) (join_sp ws) in
r_calls R2 = r_calls R /\ r_reply R2 = r_reply R /\ (if quit2 then 1 else 0) = q /\
r_state R2 = r_state R /\ r_host R2 = r_host R.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 256-byte frame, up to 16 bytes the realignment to 32 adds, and the deepest
   callee: send_message, or rec_calls_copy (160 + 16 + ASTACK), which also covers joined, rec_calls_free,
   rec_calls_equal and the strdup, free and strcmp wrappers (ASTACK, ASTACK, 2 * ESTACK) *)
Definition CHECK_ROUND_TRIP_STK : Z := 256 + 16 + Z.max SEND_MESSAGE_STK REC_CALLS_COPY_STK.
(* the allocator events of the path that does the round trip: the copies, the strdup (1), joined, send_message on
   the words joined by one space, free(line) (1), the frees of the copies (one for each argument, CmdRep.v ev_args),
   free(reply_first) (1). The side-stack frame spends none (cgif lib/YC85.v:305). send_message runs on
   set_host (set_state R sb) hb, whose calls are R's; its count reads only the calls (rec_clear's ev_args) and the
   message (verbs_receive's ev_vr), so it is EV_SEND_MESSAGE R (join_sp ws). *)
Definition EV_CHECK_ROUND_TRIP (R : rstate) (ws : list (list byte)) : Z :=
EV_REC_CALLS_COPY R + 1 + EV_JOINED + EV_SEND_MESSAGE R (join_sp ws) + 1 + ev_args R + 1.
(* the live bytes the call adds at its peak: the copies (at most 2 calls of at most 6 arguments of at most LMAX + 1
   bytes), the reply's copy (at most LMAX + 2 bytes, areply_at), joined's block, and send_message's peak *)
Definition LIVE_CHECK_ROUND_TRIP : Z := 2 * 6 * (LMAX + 1) + (LMAX + 2) + LIVE_JOINED + LIVE_SEND_MESSAGE.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the round-trip path spends: the copies, the strdup (at most LMAX + 2 bytes), joined, send_message (on a
   state with R's calls, and the words joined by one space), free(line), the frees of the copies (rec_calls_free's
   XM, one mo_free for each argument), free(reply_first) *)
Definition XM_CHECK_ROUND_TRIP (R : rstate) (ws : list (list byte)) : Z :=
XM_REC_CALLS_COPY MT R + mo_malloc MT (LMAX + 2) + XM_JOINED MT ws + XM_SEND_MESSAGE MT R (join_sp ws) + mo_free MT +
ev_args R * mo_free MT + mo_free MT.
(* the program callees' contracts *)
Hypothesis HSEND : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HRCC : forall fx0 : YK11.FPState, @trec_calls_copy_spec fx0 rc SK PI B MT.
Hypothesis HRCE : forall fx0 : YK11.FPState, @trec_calls_equal_spec fx0 rc SK PI B MT.
Hypothesis HRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
(* the runtime entries, with this tree's and cgif's names: the free, strdup and strcmp wrappers, the class-5
   side-stack frame and the shadow fills, and the side-stack laws cgif's frame walks take *)
(* the program counter the strdup entry gives the unwinder for its allocation (RtAPI.v PC_STRDUP_RA0) *)
Variable PC_STRDUP_RA0 : Z.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRDUP4 : forall fx0 : YK11.FPState, @astrdup04_rule fx0 rc SK SEGS B MT (SIG CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis ASF5 : forall fx0 : YK11.FPState, @astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5.
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASFL : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the bridge from the image's addresses to the listing's atoms *)
Hypothesis HVAL : cmd_val_objs.
Definition tcheck_round_trip_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (W0 sb hb arr q : Z) (wp : list Z) (ws : list (list byte))
  (R : rstate) (O rest : list (Z * Z)),
afn_pre SEGS B CHECK_ROUND_TRIP_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
(* room for this call's class-5 frame, and send_message's frame-depth bound with this frame added *)
count_cid 5 (frames S) < fs_frames 5 -> Z.of_nat (length (frames S)) <= 2 ->
getr regs 10 = w64 W0 -> getr regs 11 = w64 sb -> getr regs 12 = w64 hb ->
0 <= sb < 2 ^ 64 -> 0 <= hb < 2 ^ 64 ->
(* the struct words, on the caller's real stack above this call's window, read only: n at +24, w at +16 (plain
   check_round_trip_c.v:46-47). It is 8-aligned: UBSan checks that at 0x88428, and joined asks the same *)
spZ regs <= W0 + 16 -> W0 + 32 <= ly_stk_hi ly -> W0 mod 8 = 0 ->
length wp = length ws -> Z.of_nat (length ws) < 2 ^ 31 ->
aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)) ->
aval_mem (rdW W mem) (W0 + 16) 8 arr -> 0 <= arr < 2 ^ 64 ->
(* the live blocks: the recorder's O and the rest; the word array in a block of the rest, each word a string in a
   live block (plain :46-50); the array is 8-aligned (words_of's malloc), which joined's UBSan checks ask *)
arr mod 8 = 0 ->
Permutation (ablocks B ly S) (O ++ rest) ->
in_blockA rest arr (8 * Z.of_nat (length ws)) ->
(forall k, (k < length ws)%nat ->
 aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
 astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) ->
(* the message the round trip sends fits MESSAGE_MAX (plain :48) *)
PJoinR.join_need ws + 1 <= LMAX + 2 ->
(* the recorder, with at most 2 recorded calls per message (the plain proof's step_frame,
   lib/Prog/HarnessPropsProof.v:1363-1364), a declared refusal code, and a C string as reply when the daemon
   acted (plain :51-53) *)
rec_repA B ly S (rdW W mem) R O ->
(length (r_calls R) <= 2)%nat ->
(r_refuse R <> 0 -> declared (r_code R) = true) ->
(PCrt.acted_m R q = true -> exists X, r_reply R = Some (X ++ [Z_to_bv 8 0]) /\ no0 X) ->
(* g_quitting (plain :54-55) *)
0 <= q < 2 ^ 32 -> aval_mem (rdW W mem) A_G_QUITTING 4 q ->
(* what the caller has established: the round trip holds in the model (plain :60) *)
rt_okA R q sb hb ws ->
st_nev S + EV_CHECK_ROUND_TRIP R ws <= EV_MAX -> blocks_bytes S + LIVE_CHECK_ROUND_TRIP <= LIVE_MAX ->
mo_ok MT S (XM_CHECK_ROUND_TRIP R ws) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_round_trip) regs mem md)
(apost_baseF SEGS B CHECK_ROUND_TRIP_STK (ablocks_fp O ++ cmd_PG) regs ly S W mem md (EV_CHECK_ROUND_TRIP R ws)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (O' : list (Z * Z)),
 (* the recorder after the call: the same calls, reply, refuse, code, spill, state and host (plain :67-69, and
    rt_ok's equalities), and g_quitting kept (plain :70) *)
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 r_calls R' = r_calls R /\ r_reply R' = r_reply R /\
 r_refuse R' = r_refuse R /\ r_code R' = r_code R /\ r_spill R' = r_spill R /\
 r_state R' = r_state R /\ r_host R' = r_host R /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 q /\
 (* every block the call made is freed again; the rest is live and kept (plain :71-74) *)
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 (forall p n i, In (p, n) rest -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_CHECK_ROUND_TRIP /\
 mo_le MT S S' (XM_CHECK_ROUND_TRIP R ws))).
End e.
End f.
End d.
