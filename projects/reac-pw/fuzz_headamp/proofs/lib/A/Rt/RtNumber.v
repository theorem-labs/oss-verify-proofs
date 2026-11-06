(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the number entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (atoi, strtol), in the form cgif_file_fuzzer's lib/YG0d.v states its interceptor contracts; the value each one returns and the cells it writes are the ones fuzz_command's own plain proof states for musl's strtol. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtNumber.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 24 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4; the atoi contract and its comments left out (this image has no atoi interceptor); comments reworded for this image. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require __intscan_c.
Import ListNotations.
Open Scope Z_scope.

Module PIS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan_c.

(* The entry, on the pinned image: strtol 0x41c28 -> 0x47a58 -> StrtolFixAndCheck 0x51844. The interceptor calls
   musl's strtol through the slot at 0x9e1b0 (value 0x952f8), so it returns the value musl's __intscan computes
   with the saturation of a signed long: [s10_val] of the plain proof's lib/Prog/__intscan_c.v, and it leaves the
   errno cell at [s10_errno]. This image has no atoi interceptor, so the donor's atoi contract is not stated here.

   musl's __strtol_internal 0x952f8 is built with the stack protector (guard loads 0x95328 and 0x95380 against the
   object at 0x9cff8 -> 0x5f7d90), so the contract carries aguard_ok. The interceptor reads the runtime's
   replace_str flag byte (0xa25b8 + 29) and the strict_string_checks byte (0x1368e8 + 0xf5); on both branches of
   each it calls the same musl code and returns the same value; the flags change only which checks of the range
   run, and the walk reads both from the per-binary record's constant cells. *)
(* No environment reaches the runtime's flags in this image. The runtime parses ASAN_OPTIONS through its own
   GetEnv 0x64b60 (called from ParseStringFromEnv at 0x6393c), and that GetEnv first loads the word at 0x9c3b0 and
   returns NULL unless the word is zero (0x64b84 ld, 0x64b88 beqz, 0x64b8c li a0,0). The word is 1 in the image and
   lies in .got, read-only image data, so it is 1 for every run and every envp. The program's own getenv is sealed
   as well (__wrap_getenv 0x84f24 returns NULL), and __asan_default_options 0x80714 returns the fixed string at
   0x1ddf5. So the flag bytes are fixed after start-up for every run, and the walk takes them as const cells of the
   per-binary record, which the start-up certificate fixes. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* strtol(nptr, endptr, 10). fuzz_headamp's parse calls it at 0x84a0c (strtol(key + 13, &dot, 10)) with a live
   endptr and base 10. *)
Definition astrtol_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x e str ev,
aguard_ok segs W mem gotw guard ->
PRE (3 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 e -> getr regs 12 = w64 10 -> 0 < x -> 0 < e ->
STR W mem x str -> x + astr_len str + 1 < 2 ^ 64 ->
RD (3 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
atail_vis segs W mem (x + astr_len str) ->
WR (3 * ESTACK) ly S W regs mem e 8 ->
(* 8 bytes of band room past the endptr cell: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range e 16 ->
(e + 8 <= x \/ x + astr_len str + 1 <= e) ->
(e + 8 <= as_errno B \/ as_errno B + 4 <= e) ->
(* the walk covers the aligned end pointer only (I_strtolw.v:85, I_strtolfix.v:419, :477-478); the code itself
   does a plain sd, which LPS permits misaligned, and the one caller's end pointer is aligned *)
e mod 8 = 0 ->
(* the end pointer cell lies outside the image's span: the walk writes it through the cleaned store (no read-only
   byte), apart from the stack-protector guard (I_strtolw.v:97) and from [0x9c360, 0x1369de) (:99,
   I_strtolfix.v:421) *)
(forall a, e <= a < e + 8 -> ~ in_zr a (ly_img ly)) ->
(* the string does not hold the errno cell (I_strtolw.v:106) *)
(as_errno B + 4 <= x \/ x + astr_len str + 1 <= as_errno B) ->
rd32 (aview segs (w_H W) mem) (as_errno B) ev ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (3 * ESTACK) ly S W regs mem md (fun a => (e <= a < e + 8) \/ aerrno_cell B a)
(fun regs' mem' => getr regs' 10 = w64 (PIS.s10_val str) /\
rdword (aview segs (w_H W) mem') e = Some (x + PIS.s10_end str) /\
rd32 (aview segs (w_H W) mem') (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev))))).

End c.
End b.
