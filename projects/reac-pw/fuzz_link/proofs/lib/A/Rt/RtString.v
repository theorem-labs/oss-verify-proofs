(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the string entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (strlen, strcmp, strncmp, strspn, strcspn, strcat and musl's strtok_r), in the form cgif_file_fuzzer's lib/YG0d.v states its memcmp, bcmp, memchr and strnlen contracts; the value each one returns is the one fuzz_command's own plain proof states for the same entry. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
Import ListNotations.
Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec.StrFun.

(* The entries, on the pinned image. Each program call goes to the one-instruction trampoline, which jumps to the
   interceptor; the contract is stated of the trampoline, as cgif_file_fuzzer states its interceptor contracts of
   pc_wrap_memcmp and friends (lib/A/AF0l.v:13-15).

     strlen  0x43044 -> 0x430e0    strcmp  0x4304c -> 0x4360c    strncmp 0x43050 -> 0x43b40

   Each interceptor reads the shadow of the range it touches (__asan_region_is_poisoned on the slow path, an
   8-byte-aligned shadow word pair on the fast path), so every contract carries [aread_ok], which holds
   range_addressable and shadow_hull_vis, exactly as the memcmp contract does.

   The scratch window: the interceptors allocate 2032 + 160 bytes of their own frame, so a window of 2 * ESTACK
   covers the entry and the musl body it calls. strtok_r calls two of them under its own frame, so its window is
   4 * ESTACK. The windows are of the same kind as the 2 * ESTACK of cgif_file_fuzzer's bcmp and strnlen
   contracts (YG0d.v:355, :404).

   The value each entry returns is the one fuzz_command's plain proof states for the same libc entry:
   strlen lib/Prog/strlen_c.v:5-11, strcmp strcmp_c.v:16-20, strncmp strncmp_c.v (strncmp_model, Spec/StrFun.v:157),
   strspn strspn_c.v (spn_len :13-18), strcspn strcspn_c.v (cspn_len :11-16), strcat strcat_c.v:8-26,
   strtok_r strtok_r_c.v (tok_ret, tok_save, tok_cut :9-19). The interceptors return the sign of the first
   difference where musl returns the byte difference, so the comparison contracts state which return words are
   zero, as cgif_file_fuzzer's memcmp and bcmp contracts do (YG0d.v:349, :369). *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* The range check the interceptors call on every check of more than 64 bytes: __asan_region_is_poisoned,
   trampoline-free entry 0x55b30, 209 instructions, the same code as cgif's own copy. It is on the SUCCESS path of
   those checks, not only on an error path, so the walks step through it; it is proved once here and used by every
   check, which is how the released bluez and bzip2 walks factor the same entry. The conclusion is the case the
   walks need: a range whose shadow says "usable" gives the answer 0.
   The size premise is `64 < n`, not `0 < n`, and that is not a convenience: with a range of a few bytes at the
   very top of a memory band the entry rounds its start up to the next multiple of 8, the rounded address leaves
   the band, and the shadow conversion at 0x55c08 fails its own check and calls CheckFailed (measured by the walk:
   0x556fc and 0x55700 decide it, for x in [2^47-7, 2^47-2] or [0x7fff7ff9, 0x7fff7ffe]). Every caller of this
   entry in this image calls it only for a range of more than 64 bytes, because the inline check handles the
   shorter ones, so the contract states that. *)
Definition aregion_poisoned_zero_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n,
PRE ESTACK ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 64 < n < 2 ^ 32 -> 0 < x ->
RD ESTACK W regs mem x n ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST ESTACK ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0)).

Definition astrlen_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x s,
PRE (ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> 0 < x ->
STR W mem x s ->
RD (ESTACK) W regs mem x (astr_len s + 1) ->
atail_vis segs W mem (x + astr_len s) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 (astr_len s))).

(* memchr(x, 0, n) when the range holds no zero byte: the entry returns 0. cgif_file_fuzzer's
   amemchr0_realizes (lib/YG0d.v:383-400) states the case where the zero byte is found at k < n, which is the case
   check_reply uses; this is the other case of the same entry (trampoline 0x43060). The premise is cgif's own
   first_byte with k = n, which says that none of the n bytes is zero. musl's memchr runs its word loop only while
   n >= 8 bytes are left, so this contract needs no premise about the bytes after x + n.  *)
Definition amemchr0_nf_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n,
PRE (ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x ->
first_byte segs W mem x n 0 n ->
RD (ESTACK) W regs mem x n ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0)).

Definition astrcmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y sx sy,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
STR W mem x sx -> STR W mem y sy ->
RD (2 * ESTACK) W regs mem x (astr_len sx + 1) ->
RD (2 * ESTACK) W regs mem y (astr_len sy + 1) ->
atail_vis segs W mem (x + astr_len sx) -> atail_vis segs W mem (y + astr_len sy) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0 <-> sx = sy)).

Definition astrncmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n sx sy,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> 0 < y ->
STR W mem x sx -> STR W mem y sy ->
RD (2 * ESTACK) W regs mem x (Z.min n (astr_len sx + 1)) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len sx + 8) ->
RD (2 * ESTACK) W regs mem y (Z.min n (astr_len sy + 1)) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/A/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sy + 8) ->
atail_vis segs W mem (x + astr_len sx) -> atail_vis segs W mem (y + astr_len sy) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0 <->
PStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0)).

End c.
End b.
