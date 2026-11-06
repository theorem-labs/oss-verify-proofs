(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the number entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (atoi, strtol), in the form cgif_file_fuzzer's lib/YG0d.v states its interceptor contracts; the value each one returns and the cells it writes are the ones fuzz_command's own plain proof states for musl's strtol. *)
(* Modified by Theorem Labs, 2026-10: the contract of musl's strtol body (__strtol_internal) on plugin-hostd/fuzz_command's memory-checking image, which the atoi and strtol entries call through their REAL slot; the text of RtNumber.v's astrtol_realizes with the scratch window as a parameter. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
Import ListNotations.
Open Scope Z_scope.

Module PIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.__intscan_c.

(* musl's strtol, __strtol_internal 0x9e984 (the value of the REAL(strtol) slot 0xa8288), and the code under it:
   __shlim 0x9dd9c, __intscan 0x9de9c, __shgetc 0x9ddd4, __uflow 0x9ace0, __toread 0x9ad6c, __errno_location 0x95004.
   The atoi entry calls it at 0x4d178 (jalr a3) with a1 = its own local s0 - 96, the strtol entry at 0x4d0a0
   (jalr t1) with a1 = its own sp; both with a2 = 10. So the end-pointer cell lies in the caller's frame, above the
   callee's window, and is written through WR as the entry contract writes the caller's cell.

   Window: measured depth below the entry sp is 480 bytes (288 __strtol_internal + 80 __intscan + 32 __shgetc + 64
   __uflow + 16 __toread); the contract states ESTACK, so the atoi entry (frame 2,160) and the strtol entry (frame
   48, then StrtolFixAndCheck 2,144 and the range check's ESTACK) both fit in their 3 * ESTACK.

   No proof of this body exists in this model. The walks of the atoi and strtol entries take it as the named
   Section hypothesis MUSL_STRTOL : musl_strtol_ext segs B, below. *)
Definition MUSL_STRTOL_PC : Z := 0x9e984.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* strtol(nptr, endptr, 10), with the scratch window [stk] as a parameter: RtNumber.v's astrtol_realizes is this
   statement at 3 * ESTACK. *)
Definition amstrtol_realizes (stk pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x e str ev,
aguard_ok segs W mem gotw guard ->
PRE stk ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 e -> getr regs 12 = w64 10 -> 0 < x -> 0 < e ->
STR W mem x str -> x + astr_len str + 1 < 2 ^ 64 ->
RD stk W regs mem x (astr_len str + 1) ->
atail_vis segs W mem (x + astr_len str) ->
WR stk ly S W regs mem e 8 ->
(e + 8 <= x \/ x + astr_len str + 1 <= e) ->
(e + 8 <= as_errno B \/ as_errno B + 4 <= e) ->
rd32 (aview segs (w_H W) mem) (as_errno B) ev ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST stk ly S W regs mem md (fun a => (e <= a < e + 8) \/ aerrno_cell B a)
(fun regs' mem' => getr regs' 10 = w64 (PIS.s10_val str) /\
rdword (aview segs (w_H W) mem') e = Some (x + PIS.s10_end str) /\
rd32 (aview segs (w_H W) mem') (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev))))).

End c.

(* THE PIECE TO BE TAKEN FROM ELSEWHERE: musl's strtol body on this image, at its entry 0x9e984, with an ESTACK
   window and the stack-protector cells of RtAPI.v (0xa7098 -> 0x6045d8). *)
Definition musl_strtol_ext (segs : list Segment) (B : asyms) : Prop :=
amstrtol_realizes segs B ESTACK MUSL_STRTOL_PC 0xa7098 0x6045d8.

End b.
