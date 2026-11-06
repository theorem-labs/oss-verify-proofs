(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_c.v, with its module paths and module names changed; 46 of its 80 lines of code are new or changed and 39 lines of the source are left out. *)
(* The contract of chain_words on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/chain_words_c.v:30-66 (the recorder and the returned text at :53-56, the block accounting at :57-63)
   and its models lib/Spec/VerbsRun.v:40-44 (chain_run) and lib/Spec/Verbs.v:216-224 (chain_words_m, number_m).
   The function (L/src/verbs.c:106-116) handles `chain <chain> <instance> ...`: with fewer than 3 words, or when a
   word is not a whole number (number, into id and ids[0..ntok-2)), it returns sup_resp(-902); otherwise it returns
   sup_chain(id, ids, ntok - 2). It returns the text block the recorder call handed back.

   Where its arguments and locals live: tok is verbs_receive's tok[64] in verbs_receive's class-4 side-stack frame
   (hence `afobj`), the words are pointers into verbs_receive's strdup block `copy`; ids[64] is in this function's
   own class-3 side-stack frame (description `1 32 256 7 ids:108` at 0x1f254) and `id` on its real stack.

   Addresses: entry BASE + AF_chain_words = 0x8dfd4 (M, the pinned image). 279 instructions. Real frame 128 bytes
   (`addi sp,sp,-128`), then `andi sp,sp,-32` (0x8e014): at most 16 more bytes. Side-stack frame class 3 (352
   bytes requested in a 512-byte slot, `__asan_stack_malloc_3` at 0x8e044); its shadow is written inline
   (f1 x4, then f8 over ids, f3, then 00 over ids) and released by `__asan_set_shadow_f5` over 64 shadow bytes
   (0x8e320) and the flag byte store through frame[504] (0x8e324-0x8e328). Only the side-stack branch is stated
   (the use-after-return flag is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193 aso_const_law). One
   loop over the member words (header 0x8e234, ntok - 2 <= 62 passes) and the dead 4096-byte probe loop. Two inline
   checks: load8 of tok[1] (0x8e1f8) and of tok[n] in the loop (0x8e234), both in the frame object tok; the error
   paths (calls of `__asan_report_load8`, 0x8e428, 0x8e42c) are not reached. Calls: number (0x8e208, 0x8e244),
   sup_chain (0x8e270), sup_resp (0x8e27c), all with `jal` (the plain build tail-calls sup_resp; ASan must release
   the frame first). s0 is the frame pointer (0x8e010 addi s0,sp,128) at every call, so no argument needs a frame
   chain premise.
   The words it hands to number are heap strings of verbs_receive's `copy` block; their word tails, which the
   strtol wrapper reads, are readable by cmd_heap_tail_vis (lib/A/Prog/CmdRecFacts.v). The errno cell and the
   stack-protector cells number's strtol reaches are cmd_rec_cells; the GOT words the recorder callees load are in
   cmd_ro_ok (CmdRo.v:433-439).

   Resources: the plain proof's malloc budget, CW_MALLOCS = 6 allocations of at most CW_REQ = 8194 bytes
   (lib/Prog/chain_words_c.v:18-19). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c sup_chain_c sup_resp_c.
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
(* the stack this call needs: its own frame, 128 bytes and at most 16 of realignment, and below it the deepest
   callee: number, sup_chain or sup_resp (each its own <FN>_STK); __asan_stack_malloc_3 and __asan_set_shadow_f5
   ask ESTACK (cgif lib/YG0d.v:284-299; aset_shadow_realizes, lib/A/Rt/RtShadow.v), less than any of them *)
Definition CHAIN_WORDS_STK : Z := 128 + 16 + Z.max NUMBER_STK (Z.max SUP_CHAIN_STK SUP_RESP_STK).
(* one recorder call, sup_chain or sup_resp; number spends none. sup_chain's events depend on the recorder state at
   its entry (the spill arm of record(), `rec_spill_frees R`) *)
Definition EV_CHAIN_WORDS (R : rstate) : Z := Z.max (EV_SUP_CHAIN R) EV_SUP_RESP.
(* the plain proof's budget (lib/Prog/chain_words_c.v:18-19): 6 allocations of at most 8194 bytes *)
Definition CHAIN_WORDS_MALLOCS : Z := 6.
Definition CHAIN_WORDS_REQ : Z := 8194.
Definition LIVE_CHAIN_WORDS : Z := CHAIN_WORDS_MALLOCS * CHAIN_WORDS_REQ.
(* the recorder statics the recorder callees write: g_rec and record.spill *)
Definition CHAIN_WORDS_PG : list (Z * Z) := [(A_G_REC, A_G_REC + REC_SIZE); (A_REC_SPILL, A_REC_SPILL + SC_SIZE)].
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* at most 6 allocations of at most 8194 bytes, and no more frees than the recorder call's events *)
Definition XM_CHAIN_WORDS (R : rstate) : Z :=
CHAIN_WORDS_MALLOCS * mo_malloc MT CHAIN_WORDS_REQ + EV_CHAIN_WORDS R * mo_free MT.
(* the callees' contracts, never restated *)
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis SUP_CHAIN : forall fx0 : YK11.FPState, @tsup_chain_spec fx0 rc SK PI B MT.
Hypothesis SUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
(* the runtime entries: the class-3 side-stack frame (taken by a call; its shadow refilled with 0xf5 by
   __asan_set_shadow_f5, then released by the flag store), at the listing's call targets *)
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SHF5 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Definition tchain_words_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (tok ntok cb ncb : Z)
  (ptrs : list Z) (tks : list (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B CHAIN_WORDS_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 tok -> 0 <= tok < 2 ^ 64 -> getr regs 11 = w64 ntok ->
(* the words: tok[0..ntok) in verbs_receive's side-stack frame, each word in the block `copy`, none of the
   recorder's (plain :36-40) *)
afobj SEGS B ly S W mem tok (8 * ntok) ->
atoks_atA (rdW W mem) tok ptrs tks cb ncb -> In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
ntok = Z.of_nat (length tks) -> 1 <= ntok <= 64 -> nth_error tks 0 = Some Verbs.Lit.verb_chain ->
(* the recorder (plain :43); the one recorder call fits in its 16-call table (no spill) *)
rec_repA B ly S (rdW W mem) R O -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
(length (r_calls R) + 1 <= 16)%nat ->
(* the constants the recorder callees load (g_shapes among them, plain :45), that they are in the read-only range
   (sup_chain asks it), and the bridge from the listing's object atoms to their addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* room for this call's side-stack frame and its callees' *)
Z.of_nat (length (frames S)) <= 5 ->
st_nev S + EV_CHAIN_WORDS R <= EV_MAX -> blocks_bytes S + LIVE_CHAIN_WORDS <= LIVE_MAX ->
mo_ok MT S (XM_CHAIN_WORDS R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_chain_words) regs mem md)
(apost_baseF SEGS B CHAIN_WORDS_STK (CHAIN_WORDS_PG ++ ablocks_fp O) regs ly S W mem md (EV_CHAIN_WORDS R)
(fun ly' S' W' regs' mem' md' =>
 let '(R', x) := VerbsRun.chain_run R (tl tks) in
 exists (O' : list (Z * Z)) (p n : Z),
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the returned text: a fresh block of exactly its length and terminator, the caller's (none of the recorder's),
    apart from every block the call did not own (plain :55-57). Both sources return (q, |x| + 1): sup_chain's
    member text and sup_resp's refusal text; chain_words' walk proved it on every path (chain_words_exact.v) *)
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\ In (p, n) (ablocks B ly' S') /\ ~ In (p, n) O' /\
 astr_atR (rdW W' mem') p x /\ n = Z.of_nat (length x) + 1 /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> iv_apart (fst pn) (snd pn) p n) /\
 (* every block not the recorder's is kept; the others are the recorder's new blocks or the text (:59-61) *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (p, n)) /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_CHAIN_WORDS /\
 mo_le MT S S' (XM_CHAIN_WORDS R))).
End e.
End f.
End d.
