(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module names changed; 63 of its 100 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words.v, with its module paths, module names and addresses changed; 50 of its 85 lines of code are new or changed and 65 lines of the source are left out. *)
(* The contract of check_words on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as there (:88, :92). Functional content: fuzz_command's own released
   plain contract lib/Prog/check_words_c.v:81-108, with its model (:19-72: witem, call_items, want, call_words_ok,
   words_prop) taken at the ASan atoi value: `words_prop_at atoi_a` is the plain words_prop with the atoi function
   as a parameter (lib/B/Prog/HarnessPropsA.v:68), and `atoi_a` (lib/B/Prog/sup_reply_code_c.v) is the value the
   atoi wrapper returns, bv_swrap 32 of musl's strtol value (aatoi_realizes, lib/B/Rt/RtNumber.v). This is
   what the image computes at fuzz_command.c:423, snprintf("%d", atoi(w->w[k])). The harness's word list is as
   lib/Prog/joined_c.v:20-21 (join_need), :36-46 (words_place, words_view) state it, and the recorder's state as
   lib/Prog/RecInv.v rep_at (here rec_repA, lib/B/Prog/CmdRep.v). The caller gets the premise
   `words_prop_at atoi_a R ws` from harness_props_holds_a (lib/B/Prog/HarnessPropsAProof.v), the ASan-atoi form of
   the plain lib/Prog/HarnessProps.v:28. The B twin of lib/A/Prog/check_words_c.v, re-derived on B's code.
   The function (fuzz_command.c:391-444) joins the words by one space (`joined`, one malloc), then, for every call
   the recorder kept, walks the item string g_call_words[fn] (fuzz_command.c:304-331; the plain proof's rows are
   lib/Prog/CwItems.v cw_tpl) one item per argument, works out the word the item names (the strspn, strcspn, atoi
   and snprintf wrappers `___interceptor_<f>`, reached through the 4-byte jumps `__interceptor_trampoline_<f>`),
   and compares it with the recorded argument (the strcmp wrapper); then it calls check_words_add,
   check_words_chain or check_words_pin_set for the calls add (fn 0), chain (fn 17) and pin_set (fn 20), and frees
   the joined line. Each mismatch ends in abort(); the premise `words_prop_at atoi_a R ws` and the callees'
   contracts are what make the abort edge (0x88170: `__asan_handle_no_return` 0x5f790, then abort 0x94ba8) not
   taken. B's code differs from A's: clang folded the `g_call_words[fn] ? .. : ""` test (every slot of the
   constant table is a string), the item pointer is read straight from the slot.
   The local number[16] lives in a side-stack frame of class 0 (64 bytes, __asan_stack_malloc_0 at 0x87b54; frame
   description "1 32 16 10 number:393", RO_lit_1b056): the function stores the frame header (magic 0x41b58ab3, the
   description, its own address 0x87ae8), marks the frame's 8 shadow bytes 0xf1 x4, 0x00 x2, 0xf3 x2 inline, and
   at the end marks number 0xf8, stores the magic 0x45e0360e, marks the 8 shadow bytes 0xf5 and sets the frame's
   flag byte (its address at frame + 56) to 0. Only the side-stack branch is stated: the use-after-return flag
   (read through the GOT word 0xa5fa8 from 0xb0c40) is a const cell of the allocator record (cgif lib/YG0f.v
   aso_const_law, a law of LAWS) and the stack-malloc rule returns a frame (lib/YC85.v:292-310) under the room
   premise below, so the real-stack fallback (0x87b5c, 0x87b68-0x87b84 with its stack probe loop 0x87b74-0x87b7c,
   and 0x8810c-0x88128) is not reached.
   17 inline ASan checks (shadow byte at (a >> 3) + the shadow base, read through the GOT word 0xa5f50 from the cell
   0xb0c38): w->n and w->w in the caller's struct words (real stack; w->w is read again before each of the three
   callee calls), g_rec.ncalls (twice), call->nargs (twice), call->fn (twice) in g_rec, the table slot
   g_call_words[fn], the item bytes (twice), the word slot w->w[k] in the heap array (twice), call->args[a]; each
   byte is marked usable (the struct words by AR's zshadow_ok over the stack window, YG0n.v:188; g_rec, the table
   and the item strings by `cmd_addressable_chk`; the heap slots by AR's block facts), so no error path (a call of
   `__asan_report_load1/4/8`) is reached.
   Strings handed to the wrappers: the harness words (words_of's `copy` block, fuzz_command.c:120) and the recorded
   arguments (blocks by acall_at) are live blocks, so the reads come from AR's block facts and each tail word from
   `cmd_heap_tail_vis`; the item strings and literals are read-only objects of CmdRo.v (reads `cmd_aread_ok_chk`,
   tails `cmd_tail_vis`). The flag byte, errno cell and stack guard the atoi, strspn, strcspn and snprintf entries
   read come from `cmd_rec_cells`.
   UBSan (trap mode; the UBSan trap-site tables): 15 trap sites, all branching to `unimp` 0x8816c (the
   `unimp` 0x88178 after `jal abort` is never reached): 0x87bf4 (w misaligned, for w->n), 0x87cb8 (index c of
   &g_rec.calls[c] past 16), 0x87cd0 (g_rec.calls + c wraps), 0x87cfc (index fn of g_call_words past 25), 0x87d08
   (g_call_words + fn wraps), 0x87da0, 0x87df4, 0x87ef4 (item + strspn / + 1 / + strcspn wraps), 0x87e78, 0x87ec0
   (w->w + k null or wraps), 0x87e7c, 0x87ec4 (w->w null at the load of w->w[k]), 0x87e84, 0x87ecc (w->w + k
   misaligned), 0x87f04 (call->args + a wraps). The three alignment sites are excluded by the premises
   `Wd mod 8 = 0` and `arr mod 8 = 0` below; the index sites by rec_repA (c < ncalls <= 16; 0 <= fn < 26); the
   others by the address ranges (g_rec and g_call_words are constants of the image, the item strings read-only
   objects ending in their NUL, a < nargs <= 6, 0 <= k < read <= length ws with the heap array's block and
   AR_blocks_law: 4096 <= block start, block end <= alloc_ceiling; k is a digit of an item string, 0 .. 3).
   s0 is the frame pointer (0x87b24 addi s0,sp,320) at every program call: no caller value, no achain premise.
   joined gets len at s1 + 208 (0x87c1c), a slot of this frame (real stack, below this entry's stack pointer and so
   below ly_top, 32-aligned by the realignment); joined's premise on len (its 8 bytes present; B's joined asks no
   frame chain from len, pass 5b) comes from this frame: afn_pre's window. joined's B premises for UBSan:
   `W0 mod 8 = 0` and `arr mod 8 = 0` are this call's `Wd mod 8 = 0` and `arr mod 8 = 0`; `0 < arr` and
   `arr + 8 * length ws < 2 ^ 64` follow from `in_blockA (ablocks B ly S) arr (8 * length ws)` with AR_blocks_law;
   `outp mod 8 = 0` from the realignment.

   Addresses (B, its disassembly): entry BASE + AF_check_words = 0x87ae8. 455 instructions, 3 loops (the
   call loop 0x87cb4-0x88058, the item loop 0x87d78-0x87f50, and the stack probe 0x87b74-0x87b7c of the real-stack
   fallback), frame 320 bytes (`addi sp,sp,-320`) realigned to 32 (`andi sp,sp,-32` at 0x87b28). Calls: joined
   (0x88b50, at 0x87c24), the strspn wrapper (0x45194, at 0x87d98), the atoi wrapper (0x45230, at 0x87dfc,
   0x87e9c), the snprintf wrapper (0x451d0, at 0x87eb8), the strcspn wrapper (0x45198, at 0x87ef0), the strcmp
   wrapper (0x45188, at 0x87f24), check_words_add (0x88eac, at 0x87fd4), check_words_chain (0x890e0, at 0x87ffc),
   check_words_pin_set (0x894cc, at 0x88028), the free wrapper (0x589cc, at 0x880b0). It reads g_rec's address
   from the GOT word 0xa6bc8 (cmd_ro_ok's RO_ptr_a6bc8), the table g_call_words 0xa5920 (RO_g_call_words) and its
   item strings 0x21900 .. 0x21ae0 (RO_lit_21900, RO_lit_21920, RO_lit_21940, RO_lit_21960, RO_lit_21980,
   RO_lit_219a0, RO_lit_219c0, RO_lit_219e0, RO_lit_21a00, RO_lit_21a20, RO_lit_21a40, RO_lit_21a60, RO_lit_21a80,
   RO_lit_21aa0, RO_lit_21ac0, RO_lit_21ae0; slots 3 and 8 hold "" 0x212c0), and the literals " " 0x21160
   (RO_lit_21160), "" 0x212c0 (RO_lit_212c0), "%d" 0x218e0 (RO_lit_218e0), all in lib/B/Prog/CmdRo.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA.
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
(* the stack this call needs: its own 320-byte frame and up to 16 bytes the realignment to 32 adds, and the
   largest window a callee asks for there: joined's JOINED_STK, the free wrapper's ASTACK (afree04_rule asks
   ASTACK - o <= STK, cgif lib/YC5d.v:81), check_words_chain's, check_words_add's and check_words_pin_set's own
   STK, and the atoi and snprintf wrappers' 3 * ESTACK (their final windows, lib/B/Rt/RtNumber.v:65,
   RtFormat.v:76); the strspn, strcspn and strcmp wrappers ask 2 * ESTACK and __asan_stack_malloc_0 ESTACK. *)
Definition CHECK_WORDS_STK : Z :=
320 + 16 + Z.max JOINED_STK (Z.max ASTACK (Z.max CHECK_WORDS_CHAIN_STK
  (Z.max CHECK_WORDS_ADD_STK (Z.max CWPS_STK (3 * ESTACK))))).
(* two allocator events: joined's malloc (EV_JOINED) and the free of its block (fuzz_command.c:443, 0x880b0);
   the three callees and the wrappers allocate nothing *)
Definition EV_CHECK_WORDS : Z := EV_JOINED + 1.
(* the live bytes the call adds at its peak: joined's block, freed again before the return *)
Definition LIVE_CHECK_WORDS : Z := LIVE_JOINED.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: joined's malloc of join_need ws + 1 bytes, and the free of that block *)
Definition XM_CHECK_WORDS (ws : list (list byte)) : Z := XM_JOINED MT ws + mo_free MT.
(* the program functions it calls, by their own contracts *)
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HADD : forall fx0 : YK11.FPState, @tcheck_words_add_spec fx0 rc SK PI B MT.
Hypothesis HCHAIN : forall fx0 : YK11.FPState, @tcheck_words_chain_spec fx0 rc SK PI B MT.
Hypothesis HPIN : forall fx0 : YK11.FPState, @tcwps_spec fx0 rc SK PI B MT.
(* the runtime entries it reaches, with cgif's and this tree's names. The strspn, strcspn, atoi and snprintf entries
   take the stack-protector GOT word 0xa6bf8 and guard 0x604158 (A_SSP_GOT, A_SSP_GUARD,
   lib/B/Rt/RtAPI.v:59-60), the atoi entry also the runtime's replace_str flag byte 0xae455 (A_FLAG_REPLACE_STR,
   RtAPI.v:56). *)
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Definition tcheck_words_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (Wd arr : Z) (wp : list Z) (ws : list (list byte))
  (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B CHECK_WORDS_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 Wd ->
(* the read-only bytes of the image (the table g_call_words, its item strings and the three literals; their
   shadow by `cmd_addressable_chk` / `cmd_aread_ok_chk`), among them the GOT word that holds g_rec's address, and
   the bridge from the listing's object atoms to those absolute addresses (lib/B/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* the harness's struct words, on the caller's real stack above this call's window, read only (plain :87-90):
   w->w at Wd + 16, w->n at Wd + 24 *)
spZ regs <= Wd + 16 -> Wd + 32 <= ly_stk_hi ly ->
(* UBSan 0x87bf4 (alignment of w, a struct words, for w->n): the caller LLVMFuzzerTestOneInput passes its local
   (sp + 120, 0x86a1c), a multiple of 8 *)
Wd mod 8 = 0 ->
aval_mem (rdW W mem) (Wd + 16) 8 arr -> 0 <= arr < 2 ^ 64 ->
aval_mem (rdW W mem) (Wd + 24) 4 (Z.of_nat (length ws)) ->
(* the word list (plain words_view and words_place, lib/Prog/joined_c.v:36-46): the heap array w->w, one slot per
   word, and each word a string inside the one `copy` block (fuzz_command.c:132-141). UBSan 0x87e78, 0x87ec0
   (w->w + k null or wraps) and 0x87e7c, 0x87ec4 (w->w null) by the array's block (0 <= k < read <= length ws;
   AR_blocks_law: 4096 <= block start, block end <= alloc_ceiling) *)
length wp = length ws -> Z.of_nat (length ws) < 2 ^ 31 ->
in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws)) ->
(* UBSan 0x87e84, 0x87ecc (alignment of the 8-byte load w->w[k]): w->w is a malloc block start (AR_blocks_law:
   mod 16 = 0); check_words_add, check_words_chain and check_words_pin_set get it as their `wp mod 8 = 0` *)
arr mod 8 = 0 ->
(forall k, (k < length ws)%nat ->
 aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
 astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) ->
(* the joined line fits one allocation (plain :91, as joined's contract states it) *)
join_need ws + 1 < MALLOC_MAX ->
(* the recorder's state (plain :92). UBSan 0x87cb8 (index c past 16) by its ncalls <= 16; 0x87cfc (index fn past
   25) by acall_at's 0 <= fn < REC_FN_COUNT; 0x87f04 (call->args + a wraps) by acall_at's nargs <= 6 *)
rec_repA B ly S (rdW W mem) R O ->
(* what the caller has checked (plain :95, at the ASan atoi value): every recorded call carries the words the
   message puts there *)
words_prop_at atoi_a R ws ->
(* room on the side stack for its own class-0 frame and for check_words_chain's class-4 frame (cgif
   lib/YG0d.v, lib/YC85.v:298) *)
count_cid 0 (frames S) < fs_frames 0 -> count_cid 4 (frames S) < fs_frames 4 ->
st_nev S + EV_CHECK_WORDS <= EV_MAX -> blocks_bytes S + LIVE_CHECK_WORDS <= LIVE_MAX ->
mo_ok MT S (XM_CHECK_WORDS ws) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_words) regs mem md)
(apost_baseF SEGS B CHECK_WORDS_STK [] regs ly S W mem md EV_CHECK_WORDS
(fun ly' S' W' regs' mem' md' =>
 (* joined's block is gone again (plain :101), and the recorder's state is unchanged (plain :106) *)
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 rec_repA B ly' S' (rdW W' mem') R O /\
 mo_le MT S S' (XM_CHECK_WORDS ws))).
End e.
End f.
End d.
