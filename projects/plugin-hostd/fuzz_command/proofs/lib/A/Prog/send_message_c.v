(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 40 lines of the source are left out. *)
(* The contract of send_message on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the side-stack frame bound as cgif's taddframe/tclose (lib/YC21.v:38, :71); the
   blocks as one Permutation (lib/YC21.v:84); the meter as cgif's (lib/YC7x.v:88, :92).
   Functional content: fuzz_command's own released plain contract lib/Prog/send_message_c.v:31-62 (the recorder
   after `vr_run (rec_clear R) D`, g_quitting = 1 if the message quit else 0, the recorder's blocks O replaced by
   O', every other block kept), over the model lib/Prog/RecModel.v:57-58 (rec_clear) and lib/Spec/VerbsRun.v
   (run_receive), with the ASan wrapper values of verbs_receive's contract (vr_runA, lib/A/Prog/verbs_receive_c.v:
   run_receive atoi_a reply_code_a) in place of the plain vr_run (lib/Prog/verbs_receive_c.v:22-23).
   The function (fuzz_command.c:180-191, fuzz_dup inlined from fuzz.h:81-91) builds the message in a class-1
   side-stack frame (`__asan_stack_malloc_1` with 96; descriptor "1 32 24 7 msg:182" at 0x18ead): sender 7, a copy
   of the bytes in a block of max(len, 1) bytes from the malloc wrapper (`__interceptor_trampoline_malloc`, then
   `__asan_memcpy` when len <> 0), and the length. It stores 0 to g_quitting, calls rec_clear and
   verbs_receive(&msg), frees the copy through the free wrapper (`__interceptor_trampoline_free`) and releases the
   frame inline (shadow 0xf8, then 0xf5, the flag byte cleared), so the post has no new frame and no new block of
   its own. The malloc rule returns a block at or above 4096, so the abort edge (`__asan_handle_no_return`, then
   abort) on a null result is not taken. Its one inline check is the 4-byte store to g_quitting (0x5e3c60, a
   registered global of 4 bytes whose shadow is usable by `cmd_addressable_chk`), so the error path (a call of
   `__asan_report_store4`) is not reached. The GOT word of g_quitting (0xa7080) is cmd_ro_ok's RO_ptr_a7080. The
   flag byte, errno cell and stack guard that the atoi, strtol and musl bodies under verbs_receive read come from
   `cmd_rec_cells`. s0 is the frame pointer (0x86b44 addi s0,sp,96) at every call: no caller value, no achain
   premise. verbs_receive gets the copy (malloc'd at 0x86c24 before rec_clear frees anything, so apart from the
   recorder's blocks) as its message block of exactly max n 1 bytes; nothing in this pre exists only for its
   former strndup tail premise.

   Addresses: entry BASE + AF_send_message = 0x86b10 (M, the pinned image). 154 instructions, 1 inline check, no
   loop on the walked path (the one CFG loop is the real-stack probe of the fallback branch, which the walk does not
   take: the use-after-return flag is pinned and the stack-malloc contract returns a frame). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c verbs_receive_c.
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
(* the stack this call needs: its own 96-byte frame and up to 16 bytes of realignment (`andi sp,sp,-32` at
   0x86b48), and below that the deepest of the malloc and free wrappers' window (ASTACK, cgif lib/YG0d.v:17;
   amalloc04_rule / afree04_rule ask ASTACK - o <= STK, lib/YC5d.v:60, :80), rec_clear's and verbs_receive's need;
   __asan_stack_malloc_1 and __asan_memcpy ask ESTACK only *)
Definition SEND_MESSAGE_STK : Z := 112 + Z.max ASTACK (Z.max REC_CLEAR_STK VERBS_RECEIVE_STK).
(* the allocator events: the copy's malloc and free, rec_clear's (a function of the recorder state it frees,
   CmdRep.v ev_args) and verbs_receive's (a function of the route the message takes, verbs_receive_c.v ev_vr, on
   the cleared recorder it is handed) *)
Definition EV_SEND_MESSAGE (R : rstate) (D : list byte) : Z :=
  2 + EV_REC_CLEAR R + ev_vr (RecModel.rec_clear R) D.
(* the live bytes the call adds at its peak: the copy (at most 8192 bytes, plain send_message_c.v:18-21) with
   verbs_receive's peak on top *)
Definition LIVE_SEND_MESSAGE : Z := 8192 + LIVE_VERBS_RECEIVE.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the copy's malloc (charged at its largest size, 8192; mo_malloc is monotone,
   cgif lib/YC5d.v:32) and free, and the callees' meters, verbs_receive's on the cleared recorder *)
Definition XM_SEND_MESSAGE (R : rstate) (D : list byte) : Z :=
  mo_malloc MT 8192 + mo_free MT + XM_REC_CLEAR MT R + XM_VERBS_RECEIVE MT (RecModel.rec_clear R) D.
(* the program callees *)
Hypothesis RCL : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
Hypothesis VR : forall fx0 : YK11.FPState, @tverbs_receive_spec fx0 rc SK PI B MT.
(* the runtime entries, with this tree's and cgif's names: the class-1 side-stack frame and its inline release, the
   malloc and free wrappers, __asan_memcpy *)
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Definition tsend_message_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z)),
afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* this call's frame and verbs_receive's class-4 frame come on top of the caller's (verbs_receive asks at most 4
   live frames at its entry) *)
Z.of_nat (length (frames S)) <= 3 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes verbs_receive and its callees read (among them g_quitting's GOT word), and that each of
   them is in the read-only range (verbs_receive asks both); the bridge from the listing's object atoms to their
   addresses (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* the message (plain send_message_c.v:35-38): n <= 8192 bytes D at src, inside a live block that is not one of the
   recorder's (rec_clear frees those before the copy is used up; both callers pass the fuzzer input or joined()'s
   fresh block); with n = 0 nothing is read *)
getr regs 10 = w64 src -> 0 <= src < 2 ^ 64 -> getr regs 11 = w64 n -> 0 <= n <= 8192 ->
Z.of_nat (length D) = n -> abytes_atR (rdW W mem) src D ->
(n <> 0 -> in_blockA rest src n) ->
Permutation (ablocks B ly S) (O ++ rest) ->
(* the recorder (plain :39-40): its state R over its own blocks O, at most 2 recorded calls (the plain proof's
   step_frame, lib/Prog/HarnessPropsProof.v:1363-1364; rec_clear's contract asks it), and a refusing recorder's code
   declared *)
rec_repA B ly S (rdW W mem) R O ->
(length (r_calls R) <= 2)%nat ->
(r_refuse R <> 0 -> declared (r_code R) = true) ->
(* the budgets (plain :45) *)
st_nev S + EV_SEND_MESSAGE R D <= EV_MAX -> blocks_bytes S + LIVE_SEND_MESSAGE <= LIVE_MAX ->
mo_ok MT S (XM_SEND_MESSAGE R D) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_send_message) regs mem md)
(* what it writes outside its own frames: the recorder's blocks O (rec_clear frees them, verbs_receive's verbs
   rewrite them) and the program's writable statics g_rec, record.spill and g_quitting (plain vr_writes,
   lib/Prog/verbs_receive_c.v:34-35) *)
(apost_baseF SEGS B SEND_MESSAGE_STK (ablocks_fp O ++ cmd_PG) regs ly S W mem md (EV_SEND_MESSAGE R D)
(fun ly' S' W' regs' mem' md' =>
 (* plain :52-54 *)
 let '(R', _, quit) := vr_runA (RecModel.rec_clear R) D in
 exists O',
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 (if quit then 1 else 0) /\
 (* plain :56-58: the recorder's blocks are O' now, the other blocks are kept, the copy is freed *)
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SEND_MESSAGE /\
 mo_le MT S S' (XM_SEND_MESSAGE R D))).
End e.
End f.
End d.
