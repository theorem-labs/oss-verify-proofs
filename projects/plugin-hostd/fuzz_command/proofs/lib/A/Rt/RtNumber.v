(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the number entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (atoi, strtol), in the form cgif_file_fuzzer's lib/YG0d.v states its interceptor contracts; the value each one returns and the cells it writes are the ones fuzz_command's own plain proof states for musl's strtol. *)
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

(* The entries, on the pinned image: atoi 0x451e4 -> 0x4d10c, strtol 0x451e0 -> 0x4d048 -> StrtolFixAndCheck
   0x57168. Both interceptors call musl's strtol through the slot at 0xa8288 (value 0x9e984), so both return the
   value musl's __intscan computes with the saturation of a signed long: [s10_val] of fuzz_command's plain proof
   (lib/Prog/__intscan_c.v:36), and both leave the errno cell at [s10_errno] (:40).

   The atoi entry is NOT musl's atoi: it calls strtol with base 10 and truncates the result to int
   (ASan's atoi interceptor), where musl's atoi accumulates in int. The two agree on every string whose value fits
   in a signed long, and differ on a string of more than 18 digits, where strtol saturates. The contract therefore
   states the value of the entry as [bv_swrap 32 (s10_val str)], not as the plain proof's [atoi_val]
   (lib/Prog/atoi_c.v:13-21). A program walk that needs them to be the same value needs the digits of the string
   bounded; the difference is reported to this port. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* [flagb] is the address of the runtime's replace_str flag byte (the byte at 0xae8b8 + 29 of this image). The
   entry reads it and, when it is zero, calls musl's own atoi, which accumulates in int, instead of strtol, which
   saturates. The two values differ past a signed long, so the contract pins the byte: this is the only entry of
   fuzz_command whose RESULT depends on a flag. Both entries run musl's __strtol_internal 0x9e984, which is built
   with the stack protector (guard loads 0x9e9b4 and 0x9ea0c against the object at 0xa7098 -> 0x6045d8), so both
   carry aguard_ok. The others read a flag byte as well (strcmp 0x142be8 + 250,
   strlen + 251, strspn and strcspn + 247, strndup + 252, strncmp/strcat/strdup + 0, strcat/strdup/strtol/strcpy
   0xae8b8 + 29, vsnprintf/vsprintf + 84), but on both branches those entries call the same musl code and return
   the same value; the flag changes only which checks of the range run. *)
(* No environment reaches the runtime's flags in this image. The runtime parses ASAN_OPTIONS through its own
   GetEnv 0x6a484 (called from ParseStringFromEnv at 0x69260), and that GetEnv first loads the word at 0xa6430 and
   returns NULL unless the word is zero (0x6a4a8 ld, 0x6a4ac beqz, 0x6a4b0 li a0,0). The word is 1 in the image and
   lies in .got, read-only image data, so it is 1 for every run and every envp. The program's own getenv is sealed
   as well (__wrap_getenv 0x8e8d8 returns NULL), and __asan_default_options 0x86038 returns the fixed string at
   0x1df81, "allocator_may_return_null=1". So the byte is 1 after start-up for every run, and the premise below is
   a const cell of the per-binary record, which the start-up certificate fixes; a caller discharges it from the
   record. *)
Definition aatoi_realizes (pc flagb gotw guard : Z) : Prop :=
forall ly S W regs mem md x str ev,
aview segs (w_H W) mem flagb = Some 1 ->
aguard_ok segs W mem gotw guard ->
PRE (3 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> 0 < x ->
STR W mem x str ->
RD (3 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
atail_vis segs W mem (x + astr_len str) ->
rd32 (aview segs (w_H W) mem) (as_errno B) ev ->
(* the string does not hold the errno cell (the walk's premise I_atoiw.v:242; aread_ok carries no ownership) *)
(x + astr_len str + 1 <= as_errno B \/ as_errno B + 4 <= x) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (3 * ESTACK) ly S W regs mem md (aerrno_cell B)
(fun regs' mem' => getr regs' 10 = w64 (bv_swrap 32 (PIS.s10_val str)) /\
rd32 (aview segs (w_H W) mem') (as_errno B) (bv_unsigned (PIS.s10_errno str (Z_to_bv 64 ev))))).

(* strtol(nptr, endptr, 10). fuzz_command calls it from [number] with a live endptr and base 10. *)
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
   byte), apart from the stack-protector guard (I_strtolw.v:97) and from [0xa63e0, 0x142cde) (:99,
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
