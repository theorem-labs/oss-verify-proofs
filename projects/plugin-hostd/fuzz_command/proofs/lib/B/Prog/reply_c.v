(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_c.v, with its module paths and module names changed; 34 of its 62 lines of code are new or changed and 45 lines of the source are left out. *)
(* The contract of reply on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/reply_c.v:29-54 (the recorder after the call is `fst (socket_send_m R (X ++ [0]))` at :45, the text
   block freed at :46, the block accounting at :47-50) and the model lib/Prog/RecModel.v:84-85 (socket_send_m).
   The B twin of lib/A/Prog/reply_c.v, re-derived on B's code (its disassembly): the same 18 instructions at B
   addresses, calling B's socket_send (lib/B/Prog/socket_send_c.v).
   The function (L/src/verbs.c:118-122) sends the reply text: socket_send(fd, text, strlen(text) + 1), then
   free(text). The text is a block the handler returned (a fresh copy, none of the recorder's own blocks).

   Addresses (B, its disassembly): entry BASE + AF_reply = 0x8d9c4. 18 instructions, frame 32 bytes
   (`addi sp,sp,-32`, no realignment), no inline check, no loop, no side-stack frame. Calls: the strlen wrapper
   (`___interceptor_strlen`, through the 4-byte jump `__interceptor_trampoline_strlen` 0x4517c, at 0x8d9e0),
   socket_send (0x8cdb4, at 0x8d9f0), and a TAIL jump to the free wrapper after the frame is popped (`j 0x589cc` at
   0x8da08), so free runs with the entry stack pointer and returns straight to reply's caller. The size it passes is
   the 32-bit `addiw a2,a0,1` (0x8d9e4) of the length, at most 4097 here. The text stays in s0 across the call of
   socket_send (0x8d9d4 mv s0,a1; 0x8d9f0 jal socket_send); the text is a heap block, below alloc_ceiling, so the
   frame chain from s0 is achain's empty case (the survey of s0 at allocating calls). The bytes after the text's
   terminator up to the end of its 8-byte word, which the strlen wrapper's musl loop reads, are readable by CmdRecFacts'
   cmd_heap_tail_vis: the text is a live block.
   UBSan: 0 trap sites (the trap-site summary; the trap exclusion table has no row for reply). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import socket_send_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: below its own 32-byte frame, the strlen wrapper's window (RtDefs.v's ecall_pre_stk
   segs B ESTACK) or socket_send's need; and, from the entry stack pointer (the frame is popped before the tail
   jump), the free wrapper's ASTACK (cgif's afree04_rule, lib/YC5d.v:80). M: the image's function table gives 16480 =
   32 + socket_send's 16448 *)
Definition REPLY_STK : Z := Z.max (32 + Z.max ESTACK SOCKET_SEND_STK) ASTACK.
(* socket_send's events, and the free of the text *)
Definition EV_REPLY : Z := EV_SOCKET_SEND + 1.
(* the free returns the text's bytes, so the live growth is socket_send's *)
Definition LIVE_REPLY : Z := LIVE_SOCKET_SEND.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* socket_send of size bytes, then one free *)
Definition XM_REPLY (size : Z) : Z := XM_SOCKET_SEND MT size + mo_free MT.
(* the callee's contract, never restated *)
Hypothesis SOCKET_SEND : forall fx0 : YK11.FPState, @tsocket_send_spec fx0 rc SK PI B MT.
(* the runtime entries: the strlen wrapper, at the listing's call target, and the free wrapper *)
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis AFREE : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Definition treply_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (q nq : Z) (X : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B REPLY_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* a0 (the destination) is passed on unread; a1 = the text *)
getr regs 11 = w64 q -> 0 <= q < 2 ^ 64 ->
(* the text: a live block holding a string of at most 4096 bytes (plain :34-36), apart from every block the
   recorder owns — socket_send asks for the apartness, not only for non-membership, because it frees the previous
   reply while it reads this buffer *)
In (q, nq) (ablocks B ly S) -> ~ In (q, nq) O ->
Forall (fun qk => iv_apart q (Z.of_nat (length X) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) q X -> Z.of_nat (length X) + 1 <= nq -> Z.of_nat (length X) <= 4096 ->
(* the recorder (plain :37); socket_send's UBSan site 0x8cde0 asks the bound on the reply counter *)
rec_repA B ly S (rdW W mem) R O -> r_nreplies R < 2 ^ 31 - 1 ->
st_nev S + EV_REPLY <= EV_MAX -> blocks_bytes S + LIVE_REPLY <= LIVE_MAX ->
mo_ok MT S (XM_REPLY (Z.of_nat (length X) + 1)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reply) regs mem md)
(apost_base SEGS B REPLY_STK ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp ((q, nq) :: O)) regs ly S W mem md
EV_REPLY
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (fst (socket_send_m R (X ++ [Z_to_bv 8 0]))) O' /\
 (* the text is freed; the recorder's new blocks are fresh; every other block is kept (plain :46-50) *)
 ~ In (q, nq) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, nq) -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O /\ pn <> (q, nq)) \/ In pn O') /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REPLY /\
 mo_le MT S S' (XM_REPLY (Z.of_nat (length X) + 1)))).
End e.
End f.
End d.
