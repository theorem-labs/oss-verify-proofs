(* The contract of number on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan).

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/number_c.v:13-48 (the return value at :16, the result cell at :24) and its model lib/Spec/Verbs.v:150-154
   (number_m). The B twin of lib/A/Prog/number_c.v, re-derived on B's disassembly of number; the contract is A's,
   B adds three UBSan checks that its premises already exclude.
   The function (L/src/verbs.c:94-103) reads a whole number: v = strtol(word, &end, 10); it returns 0 when the word
   is empty, when bytes follow the number, or when v is outside [-1000000, 1000000], and otherwise stores (int) v
   at out and returns 1. strtol is the wrapper `___interceptor_strtol` (reached through the 4-byte jump
   `__interceptor_trampoline_strtol`, 0x4522c), which calls musl's strtol and so returns the value musl's __intscan
   computes (RtNumber.v's astrtol_realizes, s10_val / s10_end) — the value the plain proof's number_m describes.

   Where the word points: both callers pass a word strtok_r cut out of verbs_receive's strdup block `copy`
   (verbs_receive at 0x8d638, chain_words at 0x8dcd8 and 0x8dd24), so the word is a heap string; the
   bytes after its terminator up to the end of its 8-byte word, which the strtol wrapper's musl loop reads, are
   readable by CmdRecFacts' cmd_heap_tail_vis.
   Where out points: chain_words passes &ids[n-2] (its class-3 side-stack frame, a1 = s6 + s9 at 0x8dd20) and &id
   (s1 + 52, 0x8dcd4, its realigned real frame); verbs_receive passes &id (s1 + 84, 0x8d634, its real frame). `id`
   is in neither side-stack description, so out may be a 4-byte cell of the CALLER's real stack, above this call's
   stack pointer. The footprint therefore names [out, out + 4); the journal admits that store through awr_byte's
   caller-stack clause `inFP FP a /\ sp0 <= a < ly_top ly` (YCbq.v:502), so the real-stack branch bounds out by
   ly_top; AR's zshadow_ok covers [ly_stk_lo, ly_stk_hi) at every state (YG0n.v:188), so the store4
   check of that branch needs no shadow premise.

   Addresses (B, its disassembly): entry BASE + AF_number = 0x8df2c. 148 instructions. Real frame 96 bytes
   (`addi sp,sp,-96`), then `andi sp,sp,-32` (0x8df60): at most 16 more bytes. Side-stack frame class 0 (64 bytes,
   `__asan_stack_malloc_0` at 0x8df90, description `1 32 8 6 end:96` at 0x17f1b, cmd_ro_ok's RO_lit_17f1b), shadow
   written inline (f1 f1 f1 f1, 00 f3 f3 f3, 0x8dffc-0x8e01c) and released inline (0x45e0360e into frame[0], shadow
   f5, then the flag byte through frame[56], 0x8e0b0-0x8e0ec). Only the side-stack branch is stated (the
   use-after-return flag is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193 aso_const_law; its GOT word
   0xa5fa8 and the shadow base's 0xa5f50 are const cells of the allocator record, YG0f.v:194). One loop: the
   4096-byte probe of the real-stack branch (0x8dfb4), which is dead. Three inline ASan checks: load1 of word[0]
   (0x8e040), load1 of *end (0x8e060), store4 of out (0x8e09c); the error paths (calls of `__asan_report_load1` /
   `__asan_report_store4`, 0x8e158, 0x8e164, 0x8e178) are not reached: the word lies in a live block, end points
   into it, and out is marked usable (premises below). The errno cell strtol reads and writes is readable at the
   entry, and the stack-protector cells musl's __strtol_internal compares (GOT word 0xa6bf8, guard cell 0x604158)
   are readable: both cmd_rec_cells. The call reaches no allocator entry: its only state change is the side-stack
   frame it takes and releases, so its post gives `ly' = ly /\ exists f, S' = set_fs f S` (meter class (b)).
   UBSan (trap mode; the trap-site table): 3 trap sites, all branching to `unimp` 0x8e148:
   0x8e030 (`beqz s4`: word null, the load of *word, verbs.c:99), excluded by in_blockA w (AR_blocks_law: a live
   block starts at or above 4096, lib/Reusable/YG0d.v:431-434); 0x8e054 (`beqz a0`: end null, the load of *end,
   verbs.c:99), excluded by strtol's post (end = w + s10_end wd, lib/B/Rt/RtNumber.v:94) with w >= 4096; 0x8e090
   (`andi a0,s3,3; bnez`: out misaligned for the int store, verbs.c:101), excluded by `out mod 4 = 0`. No new
   premise. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
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
   window of a runtime entry it calls: strtol's 3 * ESTACK (astrtol_realizes, lib/B/Rt/RtNumber.v);
   __asan_stack_malloc_0 asks ESTACK (cgif lib/YG0d.v:284-299) *)
Definition NUMBER_STK : Z := 96 + 16 + 3 * ESTACK.
Definition EV_NUMBER : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries: the class-0 side-stack frame (taken by a call, released inline by the flag store) and the
   strtol wrapper, at the listing's call targets; the span entry names B's stack-protector GOT word 0xa6bf8 and
   guard cell 0x604158 the musl body compares against *)
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis STRTOL : forall fx0 : YK11.FPState, @RtNumber.astrtol_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strtol) 0xa6bf8 0x604158.
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tnumber_spec B MT *)
#[using="MT"]
Definition tnumber_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (w out : Z) (wd : list byte),
afn_pre SEGS B NUMBER_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 w -> 0 <= w < 2 ^ 64 -> getr regs 11 = w64 out -> 0 <= out < 2 ^ 64 ->
(* the word: a heap string, a word of verbs_receive's `copy`. UBSan 0x8e030 (word null) and 0x8e054 (end null):
   the block holding it starts at or above 4096 (AR_blocks_law), and strtol leaves end inside it *)
in_blockA (ablocks B ly S) w (Z.of_nat (length wd) + 1) -> astr_atR (rdW W mem) w wd ->
Z.of_nat (length wd) + 1 <= LMAX + 1 ->
(* the result cell: 4-aligned (UBSan 0x8e090, the int store's alignment check) and outside this call's stack
   window: inside a side-stack frame of frames S and marked usable, or a slot of the caller's real stack above the
   stack pointer, below ly_top, whose 4 bytes are present (a slot this call writes: writable_at; the caller gives it
   from its own afn_pre window) *)
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
