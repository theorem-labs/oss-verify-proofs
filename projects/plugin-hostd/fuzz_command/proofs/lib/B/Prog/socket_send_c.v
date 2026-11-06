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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 54 of its 80 lines of code are new or changed and 126 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/answer_c.v, with its module paths and module names changed; 37 of its 66 lines of code are new or changed and 51 lines of the source are left out. *)
(* The contract of socket_send on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/socket_send_c.v:27-65 (the recorder after the call is `fst (socket_send_m R x)`, a0 = size, the old
   reply freed, a fresh block of `size` bytes owned by the recorder when size > 0) and the model
   lib/Prog/RecModel.v:54-55, :84-85 (`rec_socket_send`, `socket_send_m`). The B twin of
   lib/A/Prog/socket_send_c.v, re-derived on B's code: B calls xmalloc (B-only, lib/B/Prog/xmalloc_c.v) where A
   inlined it, and B checks the counter's increment (UBSan).
   The function counts the reply (g_rec.nreplies + 1, a signed 32-bit increment that UBSan checks), frees the
   previous reply text (NULL or a block the recorder owns), zeroes reply and reply_size (one 16-byte call of the
   memory-checking runtime's memset entry) and, when size > 0, allocates `size` bytes with xmalloc, copies the
   buffer into them (the runtime's memcpy entry) and stores the pointer and the size. xmalloc's abort on a NULL
   malloc result is xmalloc's (its contract returns a block). The buffer is apart from every recorder block, so the
   free of the old reply does not touch it.

   Addresses (B, its disassembly): entry BASE + AF_socket_send = 0x8cdb4. 38 instructions, no inline ASan
   check (g_rec at constant offsets, reached by auipc), no loop, a 48-byte real frame and no side-stack frame.
   Calls: the free wrapper (__interceptor_trampoline_free 0x589cc, at 0x8cdf4), the memset entry (__asan_memset
   0x57b18, at 0x8ce04), xmalloc (0x899b4, at 0x8ce10), the memcpy entry (__asan_memcpy 0x5767c, at 0x8ce20).
   s0 holds size (0x8cdcc `mv s0,a2`) at every call: 0 <= size <= LMAX + 2, below alloc_ceiling, or a
   sign-extended negative int, at or above ly_top - 16; either way the frame chain is achain's empty case, and
   achain_chain_pre (YCbq.v:327) gives the wrappers' chain_pre; no presence of the stack up to ly_top is assumed.
   UBSan: 1 trap site (the trap-site summary and exclusion table): 0x8cde0 `blt a2,a0` -> unimp 0x8ce48, the signed
   overflow check of `g_rec.nreplies++` (recorder.c:576); excluded by `r_nreplies R < 2 ^ 31 - 1` below with
   rec_repA's `aval_mem (g_rec + OFF_NREPLIES) 4 (r_nreplies R)` and `0 <= r_nreplies R`. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj.
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
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 48-byte frame, and the deeper of xmalloc's need and the window the free
   wrapper asks for (cgif's afree04_rule, ASTACK, lib/YG0d.v:17); the memset and memcpy entries ask for ESTACK
   only. M: the image's function table gives 16448 = 48 + xmalloc's 16400 *)
Definition SOCKET_SEND_STK : Z := 48 + Z.max ASTACK XMALLOC_STK.
(* free(g_rec.reply) (an event also when the reply is NULL, cgif's afree_null04_rule) and xmalloc's malloc *)
Definition EV_SOCKET_SEND : Z := 1 + EV_XMALLOC.
(* the reply copy, at most LMAX + 2 bytes (the plain premise, socket_send_c.v:33) *)
Definition LIVE_SOCKET_SEND : Z := LMAX + 2.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the free, and xmalloc's malloc when size > 0 *)
Definition XM_SOCKET_SEND (size : Z) : Z := mo_free MT + (if 0 <? size then XM_XMALLOC MT size else 0).
(* the callee and the runtime entries this call reaches *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis VOBJS : cmd_val_objs.
Definition tsocket_send_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (buf size : Z) (x : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SOCKET_SEND_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* a0 (the destination) is not read; a1 = the buffer, a2 = its size as a 32-bit int *)
getr regs 11 = w64 buf -> 0 <= buf < 2 ^ 64 -> getr regs 12 = w64 size -> -2 ^ 31 <= size < 2 ^ 31 ->
rec_repA B ly S (rdW W mem) R O ->
(* UBSan site 0x8cde0 (signed overflow of nreplies + 1, recorder.c:576): with rec_repA's
   aval_mem (A_G_REC + OFF_NREPLIES) 4 (r_nreplies R) and 0 <= r_nreplies R, the `lw` gives a0 = r_nreplies R and
   the `addiw` a2 = r_nreplies R + 1 <= 2 ^ 31 - 1, so `blt a2,a0` is not taken *)
r_nreplies R < 2 ^ 31 - 1 ->
(* the bytes the call copies: inside a live block that none of the recorder's blocks overlaps *)
(0 < size ->
 size <= LMAX + 2 /\ Z.of_nat (length x) = size /\ abytes_atR (rdW W mem) buf x /\
 in_blockA (ablocks B ly S) buf size /\ Forall (fun qk => iv_apart buf size (fst qk) (snd qk)) O) ->
(size <= 0 -> x = []) ->
st_nev S + EV_SOCKET_SEND <= EV_MAX -> blocks_bytes S + LIVE_SOCKET_SEND <= LIVE_MAX ->
mo_ok MT S (XM_SOCKET_SEND size) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_socket_send) regs mem md)
(apost_base SEGS B SOCKET_SEND_STK ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) regs ly S W mem md
EV_SOCKET_SEND
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
getr regs' 10 = w64 size /\
rec_repA B ly' S' (rdW W' mem') (fst (socket_send_m R x)) O' /\
(* the recorder's new blocks are fresh; every other block is kept *)
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
blocks_bytes S' <= blocks_bytes S + LIVE_SOCKET_SEND /\
mo_le MT S S' (XM_SOCKET_SEND size))).
End e.
End f.
End d.
