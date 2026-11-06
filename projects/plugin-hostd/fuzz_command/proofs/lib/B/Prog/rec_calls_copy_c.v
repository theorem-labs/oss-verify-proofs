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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 43 of its 70 lines of code are new or changed and 125 lines of the source are left out. *)
(* The contract of rec_calls_copy on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh blocks and the meter as cgif's trawnew_specX states them
   (lib/YC7x.v:88, :92-101). Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_calls_copy_c.v:18-65 (rcc_args; the copies dst[i] hold the recorder's calls with fresh argument
   blocks, the recorder kept), over the model lib/Prog/RecModel.v and the representation lib/B/Prog/CmdRep.v
   (rec_repA, acall_at). rec_calls_copy(dst) (H/recorder.c:148-160) copies g_rec.calls[i].fn and .nargs to dst[i]
   and sets dst[i].args[a] = xstrdup(g_rec.calls[i].args[a]), for i < g_rec.ncalls; it returns g_rec.ncalls.
   In this build xstrdup is inlined (A calls it): the three steps are the strlen wrapper (0x89da8, reached through
   the 4-byte jump `__interceptor_trampoline_strlen`), the program function xmalloc (0x89db4, its contract
   lib/B/Prog/xmalloc_c.v is a Section hypothesis) and `__asan_memcpy` (0x89dc4) over |s| + 1 bytes.

   Addresses: entry BASE + AF_rec_calls_copy = 0x89c34 (B, the pinned image). 177 instructions, frame 160 bytes,
   2 loops (0x89cc4, 0x89d7c), no side-stack frame, 7 inline checks: load4 on g_rec.calls[i].fn and .nargs
   (0x89cec, 0x89d3c) and on dst[i].nargs (0x89de8), store4 on dst[i].fn and .nargs (0x89d20, 0x89d50), load8 on
   g_rec.calls[i].args[a] (0x89d90) and store8 on dst[i].args[a] (0x89dd8), each a read of the shadow byte at
   (a >> 3) + SHADOW_OFF through the shadow base word (0xa5f50, a RELRO word arodata_okP keeps). The error path
   (a call of `__asan_report_*`, 0x89e8c, 0x89ed4, 0x89ed8, 0x89ee0, 0x89ee4, 0x89eec, 0x89ef4) is not reached:
   g_rec is a registered global, whose shadow is usable by `cmd_addressable_chk`, and dst is an object of a live
   side-stack frame (afobj). g_rec's address is an auipc/addi pair (0x89c6c), so the walk needs cmd_val_objs.
   Each argument the inlined xstrdup reads is a live block of acall_at (its tail word by `cmd_heap_tail_vis`).
   s0 holds ~(&g_rec.calls[i].args[0]) at the xmalloc call (0x89d74, 0x89db4), a value at or above ly_top - 16
   and not 8-aligned, so achain's empty case (YCbq.v:264-265) gives the chain xmalloc's afn_pre asks for. Nothing
   is freed in the call, so the copies' freshness is the exact block equation below.

   UBSan (B only, 6 trap sites, all to the one `unimp` at 0x89ed0): 0x89cc8 is the array-index check of
   g_rec.calls[i] at recorder.c:154 (trap when i = 16 = REC_CALLS_MAX); 0x89cfc, 0x89d0c and 0x89d14 are the three
   checks of `dst[i]` at the same line (unsigned wrap of dst + 56i; the result null while dst is not; dst null or
   not 8-aligned); 0x89d7c and 0x89dc8 are the wrap of &g_rec.calls[i].args + 8a and of dst[i].args + 8a at
   recorder.c:157. No premise is added for them: the index check is excluded by `(length (r_calls R) <= 2)%nat`
   with rec_repA (the loop bound is g_rec.ncalls = |r_calls R| <= 2 < 16), the dst checks by the afobj premise
   (p mod 8 = 0, and AR_frames_law's in_app: 4096 <= frame_addr, frame_addr + bytes <= ASAN_CEIL,
   lib/Reusable/YG0d.v:455-463) with nargs <= 6 keeping args + 8a inside the entry, and the g_rec checks by the
   constants A_G_REC + OFF_CALLS .. A_G_REC + REC_SIZE. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PRcc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 160-byte frame and xmalloc's (which carries the malloc wrapper's ASTACK);
   the strlen wrapper's window and __asan_memcpy's (ESTACK each, the runtime contracts' final windows) are smaller *)
Definition REC_CALLS_COPY_STK : Z := 160 + XMALLOC_STK.
(* the allocator events: one xmalloc for each argument of each recorded call (CmdRep.v ev_args) *)
Definition EV_REC_CALLS_COPY (R : rstate) : Z := EV_XMALLOC * ev_args R.
(* the live bytes the call adds: one copy of |s| + 1 bytes for each argument *)
Definition LIVE_REC_CALLS_COPY (R : rstate) : Z :=
fold_right (fun x acc => Z.of_nat (length x) + 1 + acc) 0 (PRcc.rcc_args (r_calls R)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one xmalloc of |s| + 1 bytes for each argument *)
Definition XM_REC_CALLS_COPY (R : rstate) : Z :=
fold_right (fun x acc => XM_XMALLOC MT (Z.of_nat (length x) + 1) + acc) 0 (PRcc.rcc_args (r_calls R)).
(* the program callee's contract, the runtime entries the inlined xstrdup reaches, and the bridge from the image's
   addresses to the listing's atoms *)
Hypothesis HXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis HVAL : cmd_val_objs.
Definition trec_calls_copy_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (dst : Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B REC_CALLS_COPY_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 dst ->
(* the recorder's state, with at most 2 recorded calls per message (run_args,
   lib/B/Prog/HarnessArgs.v:80-82: after a whole message, run_receive including sup_after_reply, at most 2 calls
   and 5 arguments; the plain step_frame alone gives 3). The bound also excludes the UBSan array-index check of
   g_rec.calls[i] at 0x89cc8 (trap when i = 16) *)
rec_repA B ly S (rdW W mem) R O ->
(length (r_calls R) <= 2)%nat ->
(* the copy table: an object of a live side-stack frame, room for the recorded calls (plain :40-41). afobj's
   `dst mod 8 = 0` and its frame bounds also exclude the UBSan checks of dst[i] (0x89cfc, 0x89d0c, 0x89d14, 0x89dc8) *)
afobj SEGS B ly S W mem dst (CALL_SIZE * Z.of_nat (length (r_calls R))) ->
st_nev S + EV_REC_CALLS_COPY R <= EV_MAX -> blocks_bytes S + LIVE_REC_CALLS_COPY R <= LIVE_MAX ->
mo_ok MT S (XM_REC_CALLS_COPY R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_copy) regs mem md)
(apost_base SEGS B REC_CALLS_COPY_STK [(dst, dst + CALL_SIZE * Z.of_nat (length (r_calls R)))]
 regs ly S W mem md (EV_REC_CALLS_COPY R)
(fun ly' S' W' regs' mem' md' => exists qs : list (list (Z * Z)),
 (* the number of calls copied (plain :47) *)
 getr regs' 10 = w64 (Z.of_nat (length (r_calls R))) /\
 (* dst[i] holds call i, its arguments in fresh blocks of |s| + 1 bytes (plain :48-52) *)
 length qs = length (r_calls R) /\
 (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
   acall_at (ablocks B ly' S') (rdW W' mem') (dst + CALL_SIZE * Z.of_nat i) c P /\
   forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1) /\
 (* the new blocks are exactly the copies, distinct and apart from every block that was live (plain :53-55) *)
 Permutation (ablocks B ly' S') (ablocks B ly S ++ concat qs) /\
 NoDup (map fst (concat qs)) /\
 (forall pn q, In pn (concat qs) -> In q (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q) (snd q)) /\
 (* the blocks that were live are kept, and so is the recorder (plain :56, :58) *)
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 rec_repA B ly' S' (rdW W' mem') R O /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_COPY R /\
 mo_le MT S S' (XM_REC_CALLS_COPY R))).
End e.
End f.
End d.
