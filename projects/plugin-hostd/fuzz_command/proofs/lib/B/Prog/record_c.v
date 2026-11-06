(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_free on the ASan build of plugin-hostd/fuzz_command
   (0x8953c, 96 instructions, two loops), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1..ACh3.v: one
   statement per loop point, each proved by a run of the symbolic executor from a fresh seed) and of this unit's
   sup_reply_code.v / xstrdup.v: the executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the free calls through afree04_sub (PaCall.v).
   Loop points: OUTER at 0x895b4 (entry i of the table, its nargs address in s2), INNER at 0x895e8 (argument a of
   entry i), TAIL at 0x89624 (the nargs store of entry i); the entry 0x8953c and the epilogue 0x89668 are walked once.
   Section hypotheses beyond the statement's AFREE4: HB (the image's symbol record, whose ts_prog names the program
   statics and whose zero-shadow ranges cover g_rec's call table and record.spill, CmdZsh.v cmd_addressable_in), TL
   (the free trampoline is the free rule's entry), MTL (the meter laws), PRW (prog_rw, YCbq.v: the program statics
   are writable) and IMG (the image facts, cmd_img_facts, whose cif_prog_img says every byte of
   g_rec / record.spill / g_quitting is in the image; CmdRecFacts.v).
   The nargs store into a table in a caller's side-stack frame is the frames-of-S clause of awr_byte (YCbq.v). The
   recorder conjuncts of the post are reduced to the reader lemmas of rec_calls_free_rep.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_free.v, with its module paths and module names changed; 44 of its 85 lines of code are new or changed and 1442 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_free_c.v; 32 of its 63 lines of code are new or changed and 54 lines of the source are left out. *)
(* The contract of record on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan).
   The callee's contract is taken at every FP state (forall fx0), so a walk can use it at the fx' a call returns.
   record reaches no printf wrapper (the image's call tree: rec_calls_free -> free), so its post is apost_base.
   Its post states the recorder at recorder level (a0 = rec_slot R, rec_repA (rec_record R fn []) O'): a deliberate
   B class (this port's decision, 2026-10-29); lib/B/Prog/RecBridge.v's rec_bridge_slot gives the raw
   slot facts (slot disjunction, nargs, acall_at) from it.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the freed blocks in the footprint as cgif's journal asks (lib/YCbq.v:365-366),
   the meter as cgif's trawnew_specX (lib/YC7x.v:88, :92). Functional content: the model lib/Prog/RecModel.v:38-39
   (`rec_record R fn A`: the next slot of the call table while it holds fewer than 16 calls, else the spill slot)
   with no argument yet (A = []), over the representation lib/B/Prog/CmdRep.v (rec_repA). A has no record function:
   it is inlined into every recording function there (the A side's sup_* statements carry its part:
   lib/A/Prog/sup_remove_all_c.v:45-48, :56-58, :82-87). B keeps it as a function, called by the 26 recording
   functions (the image's call tree).
   record(fn) (recorder.c:205-221): when g_rec.ncalls = REC_CALLS_MAX (16) it frees the old arguments of the spill
   slot with rec_calls_free(&spill, 1) and takes the spill slot; otherwise it takes g_rec.calls[g_rec.ncalls++].
   It stores c->fn = fn and c->nargs = 0 and returns c. The slot it returns is `rec_slot R` below; every caller
   then hands that slot to arg_s / arg_line / mix_call / answer, whose statements take the slot in the same form.
   The recorder's block set O loses the spill's old argument blocks F (none in the table arm).

   Addresses (B, its disassembly): entry BASE + AF_record = 0x8a728. 62 instructions, frame 32 bytes (ra, s0, s1,
   s2), no side-stack frame, no loop; 2 inline ASan checks: store4 of c->fn (shadow byte read at 0x8a7bc, report
   path 0x8a800-0x8a80c) and store4 of c->nargs (0x8a7d4, report path 0x8a810-0x8a81c), each a read of the shadow
   byte at (a >> 3) + SHADOW_OFF through the shadow-base GOT word 0xa5f50 (PALib's shadow base); the slot is a byte
   range of g_rec or record.spill, whose shadow is usable (CmdRecFacts' cmd_addressable_chk), so neither report is
   reached. g_rec.ncalls is read (0x8a74c) and written (0x8a784) without a check. Callee: rec_calls_free (0x89a4c,
   call at 0x8a770, a0 = record.spill 0x5e3760, a1 = 1). s0 holds fn (< 26) at that call: below alloc_ceiling, so the
   frame chain rec_calls_free's afn_pre asks of s0 is achain's empty case (achain_low; the survey of s0 at allocating calls).

   UBSan (4 trap sites, all to the one `unimp` at 0x8a7fc, recorder.c:217-218): 0x8a77c the signed overflow of
   `g_rec.ncalls++` (trap when ncalls + 1 < ncalls); 0x8a788 the index bound of `g_rec.calls[ncalls]` (trap when
   ncalls >= 17 unsigned); 0x8a7a0 the pointer overflow of `g_rec.calls + ncalls` (trap when g_rec + 16 + 56 ncalls
   wraps); 0x8a7b0 the alignment of `c` for `c->fn` (trap when c mod 8 <> 0). No new premise: rec_repA gives
   ncalls = length (r_calls R) <= 16 (ag1_calls), and the table arm runs only for ncalls <> 16, so 0 <= ncalls <= 15
   there (0x8a77c, 0x8a788); g_rec is the constant A_G_REC = 0x5e32c0 (0x8a7a0); arep_at gives A_G_REC mod 8 = 0 and
   A_REC_SPILL mod 8 = 0, with CALL_SIZE = 56 (0x8a7b0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* the slot record() returns for the recorder state R (recorder.c:210-217, the arms of RecModel.v:39 rec_record):
   g_rec.calls[ncalls] while the table holds fewer than 16 calls, else record.spill *)
Definition rec_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16
then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
else A_REC_SPILL.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame (no realignment) above rec_calls_free's need.
   M: the image's function table gives 16560 = 32 + rec_calls_free's 16528 *)
Definition RECORD_STK : Z := 32 + REC_CALLS_FREE_STK.
(* the events: the spill arm's frees of the spill's old arguments (rec_calls_free's EV_REC_CALLS_FREE [l_spill Q],
   which is CmdRep's rec_spill_frees R: 0 in the table arm) *)
Definition EV_RECORD (R : rstate) : Z := rec_spill_frees R.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one free per old argument of the spill (rec_calls_free's XM_REC_CALLS_FREE MT
   [l_spill Q]) *)
Definition XM_RECORD (R : rstate) : Z := rec_spill_frees R * mo_free MT.
(* the callee's contract, and the bridge from the image's object addresses (g_rec, record.spill) to the listing's
   atoms *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition trecord_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (fn : Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B RECORD_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the function number: one of the REC_* ids (recorder.h), so the new call is a call of the model (acall_at's
   0 <= fst c < REC_FN_COUNT) *)
getr regs 10 = w64 fn -> 0 <= fn < REC_FN_COUNT ->
(* the recorder's state, with O the blocks it owns; it gives ncalls = length (r_calls R) <= 16, which with the
   branch at 0x8a75c excludes the UBSan traps 0x8a77c and 0x8a788, and the slots' alignment, which excludes
   0x8a7b0 (0x8a7a0: g_rec is a constant). The spill arm hands rec_calls_free the spill (at most 6 argument blocks,
   distinct, all live: acall_at and ag1_own) *)
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_RECORD R <= EV_MAX ->
mo_ok MT S (XM_RECORD R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_record) regs mem md)
(apost_base SEGS B RECORD_STK
 (* g_rec.ncalls, the slot's fn and nargs fields, and in the spill arm the spill's old argument blocks (among the
    recorder's blocks O) *)
 ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O))
 regs ly S W mem md (EV_RECORD R)
(fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
 (* a0 = the slot (recorder.c:220) *)
 getr regs' 10 = w64 (rec_slot R) /\
 (* the blocks F freed (the spill's old arguments, none in the table arm) are the recorder's; every other block
    stays *)
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
 Z.of_nat (length F) = rec_spill_frees R /\
 (forall pn, In pn F -> In pn O) /\
 (* the recorder after the call: the call (fn, []) in the slot, its blocks O without F *)
 rec_repA B ly' S' (rdW W' mem') (rec_record R fn []) O' /\
 (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
 blocks_bytes S' <= blocks_bytes S /\
 mo_le MT S S' (XM_RECORD R))).
End e.
End f.
End d.
