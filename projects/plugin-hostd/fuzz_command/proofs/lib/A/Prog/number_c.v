(* The contract of number on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/number_c.v:13-48 (the return value at :16, the result cell at :24) and its model lib/Spec/Verbs.v:150-154
   (number_m).
   The function (L/src/verbs.c:94-103) reads a whole number: v = strtol(word, &end, 10); it returns 0 when the word
   is empty, when bytes follow the number, or when v is outside [-1000000, 1000000], and otherwise stores (int) v
   at out and returns 1. strtol is the wrapper `___interceptor_strtol` (reached through the 4-byte jump
   `__interceptor_trampoline_strtol`), which calls musl's strtol and so returns the value musl's __intscan computes
   (RtNumber.v's astrtol_realizes, s10_val / s10_end) — the value the plain proof's number_m describes.

   Where the word points: both callers pass a word strtok_r cut out of verbs_receive's strdup block `copy`
   (verbs_receive at 0x8dcf4, chain_words at 0x8e208 and 0x8e244), so the word is a heap string; the
   bytes after its terminator up to the end of its 8-byte word, which the strtol wrapper's musl loop reads, are
   readable by cmd_heap_tail_vis (lib/A/Prog/CmdRecFacts.v).
   Where out points: chain_words passes &ids[n-2] (its side-stack frame, `1 32 256 7 ids:108`) and &id; verbs_receive
   passes &id. `id` is in neither side-stack description (ASan's stack-safety analysis left it on the real stack,
   measured on the image), so out may be a 4-byte cell of the CALLER's real stack, above this
   call's stack pointer. The footprint therefore names [out, out + 4); the journal admits that store through
   awr_byte's caller-stack clause `inFP FP a /\ sp0 <= a < ly_top ly` (YCbq.v:502), so the real-stack branch bounds
   out by ly_top; AR's zshadow_ok covers [ly_stk_lo, ly_stk_hi) at every state (YG0n.v:188), so the
   store4 check of that branch needs no shadow premise.

   Addresses: entry BASE + AF_number = 0x8e430 (M, the pinned image). 143 instructions. Real frame 96 bytes
   (`addi sp,sp,-96`), then `andi sp,sp,-32` (0x8e464): at most 16 more bytes. Side-stack frame class 0 (64 bytes,
   `__asan_stack_malloc_0` at 0x8e494, description `1 32 8 6 end:96` at 0x17f09), shadow written inline (f1 f1 f1 f1,
   00 f3 f3 f3) and released inline (0x45e0360e into frame[0], shadow f5, then the flag byte through frame[56],
   0x8e5b8-0x8e5e0). Only the side-stack branch is stated (the use-after-return flag is the record's const cell
   as_uar_cell = 1, cgif lib/YG0f.v:193 aso_const_law). One loop: the 4096-byte probe of the real-stack branch,
   which is dead. Three inline checks: load1 of word[0] (0x8e53c), load1 of *end (0x8e55c), store4 of out
   (0x8e58c); the error paths (calls of `__asan_report_load1` / `__asan_report_store4`, 0x8e648, 0x8e654, 0x8e668)
   are not reached: the word lies in a live block, end points into it, and out is marked usable (premises below).
   The errno cell strtol reads and writes is readable at the entry, and the stack-protector cells musl's
   __strtol_internal compares are readable: both cmd_rec_cells. The call reaches no allocator entry: its only state
   change is the side-stack frame it takes and releases, so its post gives `ly' = ly /\ exists f, S' = set_fs f S`
   (meter class (b)). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
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
(* the stack this call needs: its own frame, 96 bytes and at most 16 of realignment, and below it the deepest
   window of a runtime entry it calls: strtol's 3 * ESTACK (astrtol_realizes, lib/A/Rt/RtNumber.v);
   __asan_stack_malloc_0 asks ESTACK (cgif lib/YG0d.v:284-299) *)
Definition NUMBER_STK : Z := 96 + 16 + 3 * ESTACK.
Definition EV_NUMBER : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries: the class-0 side-stack frame (taken by a call, released inline by the flag store) and the
   strtol wrapper, at the listing's call targets *)
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis STRTOL : forall fx0 : YK11.FPState, @RtNumber.astrtol_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strtol) 0xa7098 0x6045d8.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tnumber_spec B MT *)
#[using="MT"]
Definition tnumber_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (w out : Z) (wd : list byte),
afn_pre SEGS B NUMBER_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 w -> 0 <= w < 2 ^ 64 -> getr regs 11 = w64 out -> 0 <= out < 2 ^ 64 ->
(* the word: a heap string, a word of verbs_receive's `copy` *)
in_blockA (ablocks B ly S) w (Z.of_nat (length wd) + 1) -> astr_atR (rdW W mem) w wd ->
Z.of_nat (length wd) + 1 <= LMAX + 1 ->
(* the result cell: 4-aligned and outside this call's stack window: inside a side-stack frame of frames S and
   marked usable, or a slot of the caller's real stack above the stack pointer, below ly_top, whose 4 bytes are
   present (a slot this call writes: writable_at; the caller gives it from its own afn_pre window) *)
out mod 4 = 0 ->
(((exists cid pos, In (cid, pos) (frames S) /\
   frame_addr ly cid pos <= out /\ out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
  range_addressable (rdW W mem) SHADOW_OFF out 4) \/
 (spZ regs <= out /\ out + 4 <= ly_top ly /\ (forall i, 0 <= i < 4 -> apresent (w_H W) mem (out + i)))) ->
(* strtol writes the errno cell, so out is apart from it *)
iv_apart out 4 (as_errno B) 4 ->
(* room for this call's side-stack frame *)
Z.of_nat (length (frames S)) <= 6 ->
st_nev S + EV_NUMBER <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_number) regs mem md)
(apost_base SEGS B NUMBER_STK [(out, out + 4)] regs ly S W mem md EV_NUMBER
(fun ly' S' W' regs' mem' md' =>
 match Verbs.number_m wd with
 | Some v => getr regs' 10 = w64 1 /\ aval_mem (rdW W' mem') out 4 v
 | None => getr regs' 10 = w64 0 /\ (forall i, 0 <= i < 4 -> rdW W' mem' (out + i) = rdW W mem (out + i))
 end /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* the layout is kept and only the side-stack frame state changes (meter class (b)) *)
 ly' = ly /\ (exists f, S' = set_fs f S))).
End e.
End f.
End d.
