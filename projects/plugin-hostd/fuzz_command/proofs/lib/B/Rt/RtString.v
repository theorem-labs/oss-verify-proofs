(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the string entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (strlen, strcmp, strncmp, strspn, strcspn, strcat and musl's strtok_r), in the form cgif_file_fuzzer's lib/YG0d.v states its memcmp, bcmp, memchr and strnlen contracts; the value each one returns is the one fuzz_command's own plain proof states for the same entry. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtString.v for fuzz_command.asan-ubsan: module paths and the runtime's addresses in that image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c strtok_r_c.
Import ListNotations.
Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.
Module PSpn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.
Module PCspn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Module PTok := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strtok_r_c.

(* The entries, on the pinned image. Each program call goes to the one-instruction trampoline, which jumps to the
   interceptor; the contract is stated of the trampoline, as cgif_file_fuzzer states its interceptor contracts of
   pc_wrap_memcmp and friends (lib/A/AF0l.v:13-15).

     strlen  0x4517c -> 0x45234    strcmp  0x45188 -> 0x45a70    strncmp 0x4518c -> 0x45fa4
     strspn  0x45194 -> 0x4685c    strcspn 0x45198 -> 0x46ce4    strcat  0x45220 -> 0x4c0ac
     strtok_r 0x9f360 (musl, no interceptor; it calls the strspn and strcspn trampolines)

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
   trampoline-free entry 0x5a1f8, 209 instructions, the same code as cgif's own copy. It is on the SUCCESS path of
   those checks, not only on an error path, so the walks step through it; it is proved once here and used by every
   check, which is how the released bluez and bzip2 walks factor the same entry. The conclusion is the case the
   walks need: a range whose shadow says "usable" gives the answer 0.
   The size premise is `64 < n`, not `0 < n`, and that is not a convenience: with a range of a few bytes at the
   very top of a memory band the entry rounds its start up to the next multiple of 8, the rounded address leaves
   the band, and the shadow conversion at 0x5a2d0 fails its own check and calls CheckFailed (measured by the walk:
   0x59dc4 and 0x59dc8 decide it, for x in [2^47-7, 2^47-2] or [0x7fff7ff9, 0x7fff7ffe]). Every caller of this
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
   check_reply uses; this is the other case of the same entry (trampoline 0x451a4). The premise is cgif's own
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
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len sx + 8) ->
RD (2 * ESTACK) W regs mem y (Z.min n (astr_len sy + 1)) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sy + 8) ->
atail_vis segs W mem (x + astr_len sx) -> atail_vis segs W mem (y + astr_len sy) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 0 <->
PStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0)).

Definition astrspn_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x y str set,
aguard_ok segs W mem gotw guard ->
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
STR W mem x str -> STR W mem y set ->
RD (2 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
RD (2 * ESTACK) W regs mem y (astr_len set + 1) ->
(* 8 bytes of band room past the set: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len set + 8) ->
atail_vis segs W mem (x + astr_len str) -> atail_vis segs W mem (y + astr_len set) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PSpn.spn_len set str)))).

Definition astrcspn_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md x y str set,
aguard_ok segs W mem gotw guard ->
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
STR W mem x str -> STR W mem y set ->
RD (2 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
RD (2 * ESTACK) W regs mem y (astr_len set + 1) ->
(* 8 bytes of band room past the set: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len set + 8) ->
atail_vis segs W mem (x + astr_len str) -> atail_vis segs W mem (y + astr_len set) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCspn.cspn_len set str)))).

(* The end of the range [p, p + n) rounded up to a multiple of 8. musl's strcpy and strcat read the source's last
   WORD, so the walks state the source with its slack to that end (lib/B/Bz/A/I_strcpyw.v:427-429,
   I_strcatw.v:541-545), and a destination must not start inside it. *)
Definition aword_end (p n : Z) : Z := p + n + (- (p + n)) mod 8.

(* strcat(to, from): the bytes of [from] and its terminator go to to + |dstr|; the entry returns [to]. *)
Definition astrcat_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d x dstr str,
PRE (2 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> 0 < d -> 0 < x ->
STR W mem d dstr -> STR W mem x str ->
RD (2 * ESTACK) W regs mem d (astr_len dstr + 1) ->
(* 8 bytes of band room past the destination string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range d (astr_len dstr + 8) ->
RD (2 * ESTACK) W regs mem x (astr_len str + 1) ->
(* 8 bytes of band room past the source string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len str + 8) ->
WR (2 * ESTACK) ly S W regs mem (d + astr_len dstr) (astr_len str + 1) ->
(* 8 bytes of band room past the written range: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range (d + astr_len dstr) (astr_len str + 8) ->
(* the written range holds no read-only image byte: the walk writes through the cleaned store, which holds nothing at
   a read-only image address (lib/B/Rt/RtBzClean.v:118, :301); writable_at alone allows a stale byte there. Only the
   low band can hold one (every load segment of this image ends at 0x606000). *)
(forall a, d + astr_len dstr <= a < d + astr_len dstr + astr_len str + 1 -> a < kLowMemEnd -> ~ in_rom segs a) ->
atail_vis segs W mem (d + astr_len dstr) -> atail_vis segs W mem (x + astr_len str) ->
(d + astr_len dstr + astr_len str + 1 <= x \/ x + astr_len str + 1 <= d) ->
(* the destination tail does not start inside the source's last word (see aword_end) *)
(d + astr_len dstr + astr_len str + 1 <= x \/ aword_end x (astr_len str + 1) <= d + astr_len dstr) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (2 * ESTACK) ly S W regs mem md
(fun a => d + astr_len dstr <= a < d + astr_len dstr + astr_len str + 1)
(fun regs' mem' => getr regs' 10 = w64 d /\
abytes_at segs W mem' d (dstr ++ str ++ [Z_to_bv 8 0]))).

(* strcpy(d, x): musl's strcat calls it, so its contract is needed for strcat's walk. Trampoline 0x45224,
   interceptor 0x4c7ac. The entry copies the string and its terminator and returns the destination. Its window is
   ESTACK, not 2 * ESTACK: measured depth 2,216 bytes, and strcat calls it at depth 2,208 under its own window, so
   a wider window would not compose (2,208 + 8,192 > 8,192). Same reason as strlen's. *)
Definition astrcpy_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d x s,
PRE (ESTACK) ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> 0 < d -> 0 < x ->
STR W mem x s ->
RD (ESTACK) W regs mem x (astr_len s + 1) ->
(* 8 bytes of band room past the source string: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range x (astr_len s + 8) ->
WR (ESTACK) ly S W regs mem d (astr_len s + 1) ->
(* 8 bytes of band room past the written range: the kit's chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range d (astr_len s + 8) ->
(* the written range holds no read-only image byte (as for strcat) *)
(forall a, d <= a < d + astr_len s + 1 -> a < kLowMemEnd -> ~ in_rom segs a) ->
atail_vis segs W mem (x + astr_len s) ->
(* the destination does not start inside the source's last word (see aword_end) *)
(d + astr_len s + 1 <= x \/ aword_end x (astr_len s + 1) <= d) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (ESTACK) ly S W regs mem md (fun a => d <= a < d + astr_len s + 1)
(fun regs' mem' => getr regs' 10 = w64 d /\ abytes_at segs W mem' d (s ++ [Z_to_bv 8 0]))).

(* musl's strtok_r(s, sep, p). [C] is the string it walks: [s], or the saved pointer at [p] when s is null. It
   writes the saved pointer at [p], and one terminator inside the string when it cuts a token out of it. *)
Definition astrtok_r_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md s y p pv sep str C,
aguard_ok segs W mem gotw guard ->
PRE (4 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 s -> getr regs 11 = w64 y -> getr regs 12 = w64 p -> 0 < y -> 0 < p ->
rdword (aview segs (w_H W) mem) p = Some pv ->
C = (if s =? 0 then pv else s) ->
STR W mem y sep ->
RD (4 * ESTACK) W regs mem y (astr_len sep + 1) ->
(* 8 bytes of band room past the separator set: the strspn and strcspn calls' chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range y (astr_len sep + 8) ->
atail_vis segs W mem (y + astr_len sep) ->
WR (4 * ESTACK) ly S W regs mem p 8 ->
(C <> 0 ->
0 < C /\ STR W mem C str /\
RD (4 * ESTACK) W regs mem C (astr_len str + 1) /\
(* 8 bytes of band room past the string: the strspn and strcspn calls' chk_ok needs region_in_mem p 8 (lib/B/Bz/A/I_consts.v:20-21) *)
amem_range C (astr_len str + 8) /\
WR (4 * ESTACK) ly S W regs mem C (astr_len str + 1) /\
atail_vis segs W mem (C + astr_len str) /\
(C + astr_len str + 1 <= p \/ p + 8 <= C) /\
(C + astr_len str + 1 <= y \/ y + astr_len sep + 1 <= C)) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (4 * ESTACK) ly S W regs mem md
(fun a => (p <= a < p + 8) \/ (C <> 0 /\ C <= a < C + astr_len str + 1))
(fun regs' mem' =>
getr regs' 10 = w64 (PTok.tok_ret C sep str) /\
rdword (aview segs (w_H W) mem') p = Some (PTok.tok_save C sep str) /\
(C <> 0 -> abytes_at segs W mem' C (PTok.tok_cut sep str ++ [Z_to_bv 8 0])))).

End c.
End b.
