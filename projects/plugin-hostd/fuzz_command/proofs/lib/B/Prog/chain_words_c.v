(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 21 of its 73 lines of code are new or changed and 1835 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/joined_c.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_c.v, with its module paths and module names changed; 47 of its 81 lines of code are new or changed and 39 lines of the source are left out. *)
(* The contract of chain_words on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/chain_words_c.v:30-66 (the recorder and the returned text at :53-56, the block accounting at :57-63)
   and its models lib/Spec/VerbsRun.v:40-44 (chain_run) and lib/Spec/Verbs.v:216-224 (chain_words_m, number_m).
   The B twin of lib/A/Prog/chain_words_c.v, re-derived on B's code (chain_words' disassembly): the same C and the
   same callees as A, a larger real frame (160 bytes against A's 128) and UBSan's 5 check sites below.
   The function (L/src/verbs.c:106-116) handles `chain <chain> <instance> ...`: with fewer than 3 words, or when a
   word is not a whole number (number, into id and ids[0..ntok-2)), it returns sup_resp(-902); otherwise it returns
   sup_chain(id, ids, ntok - 2). It returns the text block the recorder call handed back.

   Where its arguments and locals live: tok is verbs_receive's tok[64] in verbs_receive's class-4 side-stack frame
   (hence `afobj`), the words are pointers into verbs_receive's strdup block `copy`; ids[64] is in this function's
   own class-3 side-stack frame (description at 0x1f29a; ids at frame+32, 0x8dce4) and `id` on its real stack
   (s1 + 52, the realigned frame, passed to number at 0x8dcd4).

   Addresses (B, chain_words' disassembly): entry BASE + AF_chain_words = 0x8da84. 298 instructions. Real frame 160
   bytes (`addi sp,sp,-160`), then `andi sp,sp,-32` (0x8dac4): at most 16 more bytes. Side-stack frame class 3 (352
   bytes requested in a 512-byte slot, `__asan_stack_malloc_3` at 0x8daf4); its shadow is written inline
   (f1 x4, then f8 over ids, f3, then 00 over ids, 0x8db60-0x8dc94) and released by f8 over ids (0x8dd84-0x8de00),
   the magic 0x45e0360e at frame+0 (0x8de0c), `__asan_set_shadow_f5` over 64 shadow bytes (0x8de1c) and the flag
   byte store through frame[504] (0x8de20-0x8de24). Only the side-stack branch is stated (the use-after-return flag,
   read through the GOT word 0xa5fa8, is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193
   aso_const_law), so the probe loop (0x8db18-0x8db20) and the inline release of the real-stack branch
   (0x8de2c-0x8ded8) are dead. One loop over the member words (0x8dcfc-0x8dd40, ntok - 2 <= 62 passes) and the
   dead 4096-byte probe loop. Two inline checks, each reading the shadow byte at (a >> 3) + shadow base (GOT word
   0xa5f50): load8 of tok[1] (0x8dcc0) and of tok[n] in the loop (0x8dd0c), both in the frame object tok; the error
   paths (calls of `__asan_report_load8`, 0x8df24, 0x8df28) are not reached. Calls: number (0x8dcd8, 0x8dd24),
   sup_chain (0x8dd54), sup_resp (0x8dd60, 0x8dd70), all with `jal` (the frame is released after them). s0 is the
   frame pointer (0x8dac0 addi s0,sp,160) at every call, so no argument needs a frame chain premise:
   each callee's chain is this call's afn_pre chain with its own frame record on top (ra at s0 - 8, the caller's s0
   at s0 - 16), and achain_chain_pre (YCbq.v:327) gives the runtime entries' chain_pre from it; no presence of the
   stack up to ly_top is assumed.
   The words it hands to number are heap strings of verbs_receive's `copy` block; their word tails, which the
   strtol wrapper reads, are readable by cmd_heap_tail_vis (CmdRecFacts). The errno cell and the stack-protector
   cells (B's GOT word 0xa6bf8 and guard 0x604158) number's strtol reaches are cmd_rec_cells; the GOT words and
   literals the recorder callees load are in cmd_ro_ok, and that they lie in the read-only range (sup_chain's
   cmd_ro_in) is the image's constant fact cmd_ro_in_img. The member array ids it hands to sup_chain is its own
   frame object: 4-aligned, non-null and inside a live frame (sup_chain's UBSan premises pids <> 0,
   pids mod 4 = 0 and its afobj arm), each member a 32-bit int by number's post.

   UBSan (trap mode: a failed check branches to the `unimp` at 0x8df20, a machine fault in cgif's model,
   lib/Reusable/YP00.v). 5 check sites (the trap-site tables), none taken on a path this statement
   allows, and none needs a premise of its own:
   - 0x8dca8 (tok + 8 wraps or is null, verbs.c:110) and 0x8dcfc (tok + 8n wraps, verbs.c:113): tok lies in a frame
     of frames S, below the layout's frame-area end (< 2 ^ 47), by the `afobj tok (8 * ntok)` premise;
   - 0x8dcb4 (tok + 8 not 8-aligned for the load of tok[1]): afobj's tok mod 8 = 0;
   - 0x8dd14 (the index n - 2 of &ids[n - 2] beyond ids[64], verbs.c:113): the loop runs for n - 2 <= ntok - 3
     <= 61, by the premise 1 <= ntok <= 64;
   - 0x8dd18 (ids + 4(n - 2) wraps): ids is this call's own class-3 frame + 32, which the SM3 rule returns inside
     the layout's frame area (below ly_stk_hi ly <= 2 ^ 47, afn_pre's astk_ok).

   Resources: the plain proof's malloc budget, CW_MALLOCS = 6 allocations of at most CW_REQ = 8194 bytes
   (lib/Prog/chain_words_c.v:18-19): sup_chain makes 6 (xmalloc, three arg_s copies, answer's two), sup_resp
   fewer. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c sup_chain_c sup_resp_c.
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
(* the stack this call needs: its own frame, 160 bytes and at most 16 of realignment, and below it the deepest
   callee: number, sup_chain or sup_resp (each its own <FN>_STK); __asan_stack_malloc_3 and __asan_set_shadow_f5
   ask ESTACK (cgif lib/YG0d.v:284-299; aset_shadow_realizes, lib/B/Rt/RtShadow.v), less than any of them.
   M: the image's function table gives 16960 = 160 + sup_chain's 16800 (without the realignment's 16) *)
Definition CHAIN_WORDS_STK : Z := 160 + 16 + Z.max NUMBER_STK (Z.max SUP_CHAIN_STK SUP_RESP_STK).
(* one recorder call, sup_chain or sup_resp; number spends none. sup_chain's events depend on the recorder state at
   its entry (record()'s spill arm, EV_RECORD R) *)
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
   __asan_set_shadow_f5, then released by the flag store), at the listing's call targets. UBSan: SM3's frame is the
   one ids lies in, so with afn_pre's layout bound it excludes the check site 0x8dd18 (ids + 4(n - 2) wraps) *)
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
   recorder's (plain :36-40). UBSan: afobj puts tok in a live side-stack frame (below 2 ^ 47) with tok mod 8 = 0,
   which excludes the check sites 0x8dca8 and 0x8dcfc (tok + 8n wraps) and 0x8dcb4 (tok + 8 misaligned) *)
afobj SEGS B ly S W mem tok (8 * ntok) ->
atoks_atA (rdW W mem) tok ptrs tks cb ncb -> In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
(* UBSan: ntok <= 64 bounds the member loop to n - 2 <= 61, which excludes the check site 0x8dd14 (&ids[n - 2]
   beyond ids[64]) *)
ntok = Z.of_nat (length tks) -> 1 <= ntok <= 64 -> nth_error tks 0 = Some Verbs.Lit.verb_chain ->
(* the recorder (plain :43); the one recorder call fits in its 16-call table (no spill) *)
rec_repA B ly S (rdW W mem) R O -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
(length (r_calls R) + 1 <= 16)%nat ->
(* the constants the recorder callees load (g_shapes among them, plain :45) and the bridge from the listing's
   object atoms to their addresses *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* room for this call's side-stack frame and its callees': with this call's class-3 frame a callee starts with at
   most 6 live frames (number asks <= 6, sup_chain <= 7, sup_resp <= 8) *)
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
    live after the call; if it was live at the entry it was one of the recorder's blocks that record()'s spill arm
    or answer freed first (the contrapositive freshness form), and it is apart from every block the call did not
    own (plain :55-57). Both sources return (q, |x| + 1): sup_chain's member text (its post, lib/B/Prog/
    sup_chain_c.v) and sup_resp's refusal text (lib/B/Prog/sup_resp_c.v); A's walk proved it on every path
    (chain_words_exact.v) *)
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\ In (p, n) (ablocks B ly' S') /\ ~ In (p, n) O' /\
 (In (p, n) (ablocks B ly S) -> In (p, n) O) /\
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
