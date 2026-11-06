(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Each `*_realizes pc` below is the contract of one runtime entry at its code address pc, stated in the shape of
   YG0d.v's aintrin_realizes / abcmp_realizes / astrnlen_realizes and of W_contract.v's astrlen_realizes:
   - pre: `ecall_pre` (the allocator state, a code return address, the stack and gp/tp), the scratch the entry may
     use below sp present, the argument registers, and the bytes the entry reads as `aview` facts; an interceptor
     (one that checks shadow) also gets `range_addressable` / `shadow_hull_vis` over exactly the ranges it checks.
     Every interceptor and intrinsic form takes `rom_view SEGS W mem` (the donor's premise, YG0d.v:406, :425):
     measured on fuzz_reply.asan, each interceptor's and intrinsic's prologue loads the pattern-init word at 0x103d0,
     and musl strlen / memchr load their masks at 0x10350 / 0x10368.  asnprintf_realizes keeps a Theorem Labs lane's narrower
     rt_rom_view (rt_rom_view_of_rom_view gives it from rom_view).  The libc entries (__errno_location, the mutex
     pair) read no .rodata and take none;
   - post: the world is unchanged, the entry returns to ra with the callee-saved registers kept, the allocator state
     is the one it was called with (AR at the same ly S), the model changes only by materialisation, the result
     register, the bytes it writes, every other byte outside its scratch unchanged, and presence kept.
   The runtime lanes prove these; a walk takes the ones it calls as Section hypotheses at `SIGMA WS_<entry>`.
   Not here, by ruling: the donor's own closed forms (amalloc, afree, aintrin OCpy/OSet, abcmp, amemchr0,
   astrnlen, astack_malloc_realizes at any class, YG0d.v:266-432), which the relocated core proves; strlen
   (W_contract.v:223 astrlen_realizes); memchr and strnlen in general, whose texts are shared (memchr:
   lib/Rt/MemchrDef.v amemchr_realizesM; strnlen: a Theorem Labs lane's StrnlenDef); and every entry that allocates
   (malloc, realloc, free, strndup), which goes on the allocator parameter of GUIDE section 3.1.
   Stack: libc entries called directly (pthread_mutex_lock/unlock, __errno_location) use ESTACK below sp, the
   interceptors 2 * ESTACK, snprintf 3 * ESTACK (a Theorem Labs lane's statement; the deepest snprintf path measured on
   fuzz_reply.asan is 7,824 bytes). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_kit W_journal W_contract.
(* The printf model (format pieces, arguments, text) is the plain proof's pure one; it is Required, not Imported,
   because Prog/printf_facts_c.v Imports lib/Lib, whose getr/mkst/seg_rom differ from YK11's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Section c.
Variable B : asyms.

(* The common post of an entry that keeps the allocator state: W unchanged, back at ra, AR at the same ly S, the
   callee-saved registers kept, the model changed only by materialisation, the result Pr on the new registers and
   memory, every byte outside the written set Wr and the scratch [sp - stk, sp) unchanged, presence kept. *)
Definition aentry_post (stk : Z) ly S (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at SEGS (raZ regs) regs' mem' md' /\
AR SEGS B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Pr regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (spZ regs - stk <= a < spZ regs) ->
 aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* The pre every entry shares beyond ecall_pre: stk bytes of present scratch below sp, above the stack's floor. *)
Definition ascratch_ok (stk : Z) ly (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
ly_stk_lo ly + stk <= spZ regs /\ (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a).

(* Bytes [x, x + n) are visible and outside the scratch [sp - stk, sp). *)
Definition ain_ok (stk : Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (x n : Z) : Prop :=
forall a, x <= a < x + n -> aview SEGS (w_H W) mem a <> None /\ ~ (spZ regs - stk <= a < spZ regs).

(* What an interceptor checks of a range it reads or writes: in application memory, and its shadow addressable and
   visible (YG0d.v's amem_range / range_addressable / shadow_hull_vis, guarded for an empty range). *)
Definition achecked (W : world SEGS) (mem : word -> option byte) (x n : Z) : Prop :=
amem_range x n /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n).

(* ---- pthread_mutex_lock (musl, a libc PCall: no shadow check). ----
   Plain contract: lib/Prog/pthread_mutex_lock_c.v.  A normal mutex (low nibble of its type byte 0) that is free
   (lock word at A + 4 zero) is taken by one CAS: the lock word becomes EBUSY = 16, nothing else is written. *)
Definition alock_realizes (pc : Z) : Prop :=
forall ly S W regs mem md A tb,
ecall_pre SEGS B ly S W regs mem md ->
getr regs 10 = w64 A -> 0 < A -> A mod 4 = 0 -> A + 12 <= 2 ^ 63 ->
aview SEGS (w_H W) mem A = Some tb -> tb mod 16 = 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (A + 4) 4 0 ->
ain_ok ESTACK W regs mem A 8 ->
dest_ok SEGS B ly S W regs mem (A + 4) 4 ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post ESTACK ly S W regs mem md (fun a => A + 4 <= a < A + 8)
 (fun _ mem' => val_mem SEGS (mrestrict (w_H W) mem') (A + 4) 4 16)).

(* ---- pthread_mutex_unlock (musl, a libc PCall). ----
   Plain contract: lib/Prog/pthread_mutex_unlock_c.v.  The normal mutex at A held by this thread (type 0, lock word
   16, no waiters) is released: the lock word becomes 0, nothing else is written, a0 = 0. *)
Definition aunlock_realizes (pc : Z) : Prop :=
forall ly S W regs mem md A,
ecall_pre SEGS B ly S W regs mem md ->
getr regs 10 = w64 A -> 0 < A -> A mod 4 = 0 -> A + 12 <= 2 ^ 63 ->
val_mem SEGS (mrestrict (w_H W) mem) A 4 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (A + 4) 4 16 ->
val_mem SEGS (mrestrict (w_H W) mem) (A + 8) 4 0 ->
ain_ok ESTACK W regs mem A 12 ->
dest_ok SEGS B ly S W regs mem (A + 4) 4 ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post ESTACK ly S W regs mem md (fun a => A + 4 <= a < A + 8)
 (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W) mem') (A + 4) 4 0)).

(* ---- __errno_location (musl, a libc PCall: `mv a0,tp; addi a0,a0,-164; ret`). ----
   Returns the thread's errno cell, tp - 164; writes nothing.  A walk that needs `as_errno B` relates the two by
   the instance fact `as_errno B = as_tp B - 164` (ecall_pre gives tp = as_tp B). *)
Definition aerrno_realizes (pc : Z) : Prop :=
forall ly S W regs mem md,
ecall_pre SEGS B ly S W regs mem md ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post ESTACK ly S W regs mem md (fun _ => False)
 (fun regs' _ => getr regs' 10 = w64 (as_tp B - 164))).

(* ---- strncmp (an interceptor). ----
   Plain contract: lib/Prog/strncmp_c.v.  kx (ky) is where x (y) holds its NUL within n, or n; the interceptor and
   the real strncmp read at most min(n, kx + 1) bytes of x and min(n, ky + 1) of y, and the interceptor checks the
   shadow of what it read.  The result is 0 exactly when the two strings agree up to n. *)
Definition astrn_agree (W : world SEGS) (mem : word -> option byte) (x y n : Z) : Prop :=
forall i, 0 <= i < n -> (forall j, 0 <= j < i -> aview SEGS (w_H W) mem (x + j) <> Some 0) ->
aview SEGS (w_H W) mem (x + i) = aview SEGS (w_H W) mem (y + i).
Definition astrncmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n kx ky,
ecall_pre SEGS B ly S W regs mem md -> ascratch_ok (2 * ESTACK) ly W regs mem ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 63 -> n <= 2 ^ 40 -> 0 < x -> 0 < y ->
first_byte SEGS W mem x n 0 kx -> first_byte SEGS W mem y n 0 ky ->
x + Z.min n (kx + 1) <= 2 ^ 63 -> y + Z.min n (ky + 1) <= 2 ^ 63 ->
ain_ok (2 * ESTACK) W regs mem x (Z.min n (kx + 1)) -> ain_ok (2 * ESTACK) W regs mem y (Z.min n (ky + 1)) ->
achecked W mem x (Z.min n (kx + 1)) -> achecked W mem y (Z.min n (ky + 1)) -> rom_view SEGS W mem ->
amem_range x 8 /\ amem_range y 8 ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post (2 * ESTACK) ly S W regs mem md (fun _ => False)
 (fun regs' _ => getr regs' 10 = w64 0 <-> astrn_agree W mem x y n)).

(* ---- strcmp (an interceptor). ----
   Plain contract: lib/Prog/strcmp_c.v.  x holds its NUL at kx, y at ky; both strings are read up to and including
   their NUL at most.  The result is 0 exactly when the two strings are equal. *)
Definition astrcmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y kx ky,
ecall_pre SEGS B ly S W regs mem md -> ascratch_ok (2 * ESTACK) ly W regs mem ->
getr regs 10 = w64 x -> getr regs 11 = w64 y ->
0 < x -> 0 < y -> 0 <= kx -> 0 <= ky -> x + kx + 1 <= 2 ^ 63 -> y + ky + 1 <= 2 ^ 63 -> kx + 1 <= 2 ^ 40 ->
first_byte SEGS W mem x (kx + 1) 0 kx -> first_byte SEGS W mem y (ky + 1) 0 ky ->
ain_ok (2 * ESTACK) W regs mem x (kx + 1) -> ain_ok (2 * ESTACK) W regs mem y (ky + 1) ->
achecked W mem x (kx + 1) -> achecked W mem y (ky + 1) -> rom_view SEGS W mem ->
amem_range x 8 /\ amem_range y 8 ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post (2 * ESTACK) ly S W regs mem md (fun _ => False)
 (fun regs' _ => getr regs' 10 = w64 0 <->
  kx = ky /\ forall i, 0 <= i < kx -> aview SEGS (w_H W) mem (x + i) = aview SEGS (w_H W) mem (y + i))).

(* ---- strrchr (an interceptor). ----
   Plain contract: lib/Prog/strrchr_c.v.  x holds its NUL at k; the interceptor checks the k + 1 bytes it reads.
   The result is the address of the last byte equal to c in [x, x + k] (the NUL itself when c = 0), or 0. *)
Definition astrrchr_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x c k,
ecall_pre SEGS B ly S W regs mem md -> ascratch_ok (2 * ESTACK) ly W regs mem ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 <= c < 256 ->
0 < x -> 0 <= k -> x + k + 1 <= 2 ^ 63 -> k < 2 ^ 40 ->
first_byte SEGS W mem x (k + 1) 0 k ->
ain_ok (2 * ESTACK) W regs mem x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None) -> rom_view SEGS W mem ->
achecked W mem x (k + 1) -> amem_range x 8 ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post (2 * ESTACK) ly S W regs mem md (fun _ => False)
 (fun regs' _ =>
  ((forall i, 0 <= i <= k -> aview SEGS (w_H W) mem (x + i) <> Some c) /\ getr regs' 10 = w64 0) \/
  (exists i, 0 <= i <= k /\ aview SEGS (w_H W) mem (x + i) = Some c /\
   (forall j, i < j <= k -> aview SEGS (w_H W) mem (x + j) <> Some c) /\ getr regs' 10 = w64 (x + i)))).

(* ---- __asan_memmove (an ASan intrinsic). ----
   YG0d.v's aintrin_realizes OCpy without its disjointness conjunct: the ranges may overlap, and each byte of the
   destination gets the source byte as it was at entry.  n = 0 is allowed.  The rom_view and the 8-byte ranges are
   the premises of pcap's Bz walk (a working branch, Bz/A/I_amemmovew.v:409-415: its range checks take
   region_in_mem x n, Bz/A/I_consts.v:20, only when n > 0), of which this form is to be the relocated instance. *)
Definition amemmove_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d x n,
ecall_pre SEGS B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok SEGS B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok SEGS W regs mem x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n) ->
rom_view SEGS W mem -> (0 < n -> amem_range d 8 /\ amem_range x 8) ->
(forall a, d <= a < d + n -> ~ in_img SEGS a) ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post ESTACK ly S W regs mem md (fun a => d <= a < d + n)
 (fun regs' mem' => getr regs' 10 = w64 d /\
  forall i, 0 <= i < n -> aview SEGS (w_H W) mem' (d + i) = aview SEGS (w_H W) mem (x + i))).

(* ---- __asan_memcpy onto itself (an ASan intrinsic). ----
   Plain contract: lib/Prog/memcpy_same_c.v.  YG0d.v's aintrin_realizes OCpy needs disjoint ranges; a struct
   assignment of an element to itself (relay.c's `g_src[i] = g_src[--g_nsrc]` when i is the last index) calls
   __asan_memcpy with d = x, which ASan does not check for overlap (to == from).  The bytes are unchanged. *)
Definition amemcpy_same_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d n,
ecall_pre SEGS B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 d -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok SEGS B ly S W regs mem d n -> src_ok SEGS W regs mem d n -> achecked W mem d n -> rom_view SEGS W mem ->
(0 < n -> amem_range d 8) -> (forall a, d <= a < d + n -> ~ in_img SEGS a) ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(aentry_post ESTACK ly S W regs mem md (fun _ => False) (fun regs' _ => getr regs' 10 = w64 d)).

(* The length bound of the Bz-derived forms: `n <= 2 ^ 40` on astrncmp, `kx + 1 <= 2 ^ 40` on astrcmp and
   `k < 2 ^ 40` on astrrchr, each right after the form's size premise (the Bz range check rng_ok, Bz/A/I_qck.v:27,
   I_consts.v:27).  DO NOT TIGHTEN IT: the measured worst case at the inputs the statement covers (EvBound) is
   list_drop's memmove (inlined at 7 sites), (n - i - 1) * 16 up to 536,870,896 = 2^29 - 16 (under amemmove's
   n < 2^32); a bound of 2^24 or 2^16 would break it. *)

(* ---- snprintf (an interceptor), general in its format: a Theorem Labs lane's statement. ----
   The statement is plugin-hostd/fuzz_command's (a working branch b273dd49dab, lib/A/Rt/RtFormat.v:72-90), with its
   helper definitions (lib/A/Rt/RtDefs.v) copied below under the same names, at fuzz_reply's addresses: the walk of
   the entry is written once, against that statement, and relocated.  On fuzz_reply.asan the chain is
   ___interceptor_snprintf -> ___interceptor_vsnprintf (printf_common, then musl's vsnprintf -> vfprintf ->
   printf_core -> pad); the musl bodies are built with the stack protector and read the guard through the GOT word
   0x9e658 -> __stack_chk_guard 0x5f94b0 (vsnprintf 0x95e54), hence aguard_ok; printf_core reads its state table and
   the "-+   0X0x" prefix in .rodata, hence rt_rom_view; the scratch window is 3 * ESTACK (each reused interceptor
   contract asks 2 * ESTACK at its own entry; the deepest path measured is 7,824 bytes).  The text is the plain
   printf model (Prog/printf_facts_c.v): the format parses to pieces ps, the variadic arguments are a3..a7, the text
   is T; snprintf writes min(n - 1, |T|) bytes of T and a NUL at d and returns |T|. *)
Definition ascratch_stk (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop := spZ regs - stk <= a < spZ regs.
Definition ecall_pre_stk (stk : Z) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ecall_pre SEGS B ly S W regs mem md /\
ly_stk_lo ly + stk <= spZ regs /\
(forall a, ascratch_stk stk regs a -> apresent (w_H W) mem a).
Definition aread_ok (stk : Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (x n : Z) : Prop :=
0 <= x /\ x + n <= 2 ^ 63 /\ 0 <= n < 2 ^ 32 /\
(forall a, x <= a < x + n -> aview SEGS (w_H W) mem a <> None /\ ~ ascratch_stk stk regs a) /\
amem_range x n /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n).
Definition awrite_ok (stk : Z) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (d n : Z) : Prop :=
0 <= d /\ d + n <= 2 ^ 63 /\ 0 <= n < 2 ^ 32 /\
(forall a, d <= a < d + n ->
writable_at SEGS (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ ascratch_stk stk regs a) /\
amem_range d n /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF d n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) d n).
Definition atail_vis (W : world SEGS) (mem : word -> option byte) (e : Z) : Prop :=
forall a, e < a < e - e mod 8 + 8 -> aview SEGS (w_H W) mem a <> None.
Definition abytes_at (W : world SEGS) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall i, (i < length l)%nat -> aview SEGS (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Definition astr_at (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list byte) : Prop :=
abytes_at W mem a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s.
Definition art_post (stk : Z) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at SEGS (raZ regs) regs' mem' md' /\
AR SEGS B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Q regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a -> ~ E a ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(forall a, ascratch_stk stk regs a -> apresent (w_H W) mem' a).
Definition aguard_ok (W : world SEGS) (mem : word -> option byte) (gotw guard : Z) : Prop :=
rdword (aview SEGS (w_H W) mem) gotw = Some guard /\
(exists can, rdword (aview SEGS (w_H W) mem) guard = Some can).
Definition aerrno_cell (a : Z) : Prop := as_errno B <= a < as_errno B + 4.
Definition rt_rom_view (W : world SEGS) (mem : word -> option byte) : Prop :=
forall a, in_rom SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aerrno_cell a ->
aview SEGS (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a)).
Definition apf_arg_ok (stk : Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
(D n : Z) (r : word) (a : printf_facts_c.pf_arg) : Prop :=
match a with
| printf_facts_c.AInt v => -2^31 <= v < 2^31 /\ bv_unsigned r mod 2^32 = v mod 2^32
| printf_facts_c.AU64 u => bv_unsigned r = u
| printf_facts_c.APtr s =>
Forall (fun c => 0 < c < 256) s /\
0 < bv_unsigned r /\
astr_at W mem (bv_unsigned r) (printf_facts_c.pf_bytes s) /\
aread_ok stk W regs mem (bv_unsigned r) (Z.of_nat (length s) + 1) /\
atail_vis W mem (bv_unsigned r + Z.of_nat (length s)) /\
(bv_unsigned r + Z.of_nat (length s) + 1 <= D \/ D + n <= bv_unsigned r)
end.
Fixpoint apf_args_ok (stk : Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
(D n : Z) (rs : list word) (args : list printf_facts_c.pf_arg) : Prop :=
match args, rs with
| [], _ => True
| a :: args', r :: rs' => apf_arg_ok stk W regs mem D n r a /\ apf_args_ok stk W regs mem D n rs' args'
| _ :: _, [] => False
end.
(* fuzz_reply.asan's stack-protector cells: the GOT word and __stack_chk_guard. *)
Definition FR_GOT_GUARD : Z := 0x9e658.
Definition FR_GUARD : Z := 0x5f94b0.
(* image A's top, the bound of asnprintf_realizes's destination premise below: the end of fuzz_reply.asan's image, its
   last PT_LOAD's end rounded up to a page (W_kit.v pa_img_range's bound), GXA's GLOBALS_TOP at image A.  The number
   of lib/A/RT_pf_Tbl.v's PF_GLOBALS_TOP (SnpNarrowSites.v PF_GLOBALS_TOP_tbl proves the two equal). *)
Definition PF_GLOBALS_TOP : Z := 0x5fb000.
Definition asnprintf_realizes (pc gotw guard : Z) : Prop :=
forall ly S W regs mem md d n f fmt ps args T,
aguard_ok W mem gotw guard ->
ecall_pre_stk (3 * ESTACK) ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
1 <= n < 2 ^ 31 -> 0 < d -> 0 < f ->
astr_at W mem f (printf_facts_c.pf_bytes fmt) ->
printf_facts_c.pf_parse fmt = Some ps ->
(* The four premises from `ps = ..` to `PF_GLOBALS_TOP <= d` NARROW the contract (a Theorem Labs lane's ruling, SNP-ROUTE.md
   section 7.5; the location premises on the same ground, 2026-10-30), in the text of a working branch
   8f558767590a lib/A/RT_pf_snp_srr.v asnprintf_realizes_xn, so that its proof plugs this contract by exact:
   - the pieces are reply's one format "%s %d ";
   - (M1) the format lies in the image's read-only data below the GOT word: 65536 <= f, f + |fmt| + 1 <= FR_GOT_GUARD;
   - (M3) the %s string (the first argument, a3 = getr regs 13, its bytes by apf_arg_ok's astr_at) likewise, with the
     8 bytes past its NUL: 65536 <= r13, r13 + |s| + 1 + 8 <= FR_GOT_GUARD;
   - (M2) the destination lies above the image: PF_GLOBALS_TOP <= d.
   Every walked application satisfies all four literally: W_rig_top.v snp_call, W_LLVMFuzzerTestOneInput_gone_p1.v
   and _gone_p1_x.v pass "%s %d " at f = VAL (A_OBJ 20) = 0x20f80, the %s string "param_gesture" at
   VAL (A_OBJ 21) = 0x20f20 and a buffer in a live fake frame (frame_addr ly 1 fpos + 32); SnpNarrowSites.v proves
   each premise from those applications' own facts (W_rig_top.v, generic over the placement, takes the two literals'
   location as its Section hypothesis HLITGOT, which SnpNarrowSites.v HLITGOT_PB_fr proves at PB_fr).  The other
   callers of the trampoline 0x421dc in fuzz_reply.asan are on no proved path and are walked nowhere in lib/A:
   libunwind UnwindCursor::getFunctionName (0x87528), vsyslog (0x91278) and __strftime_fmt_1 (0x9bc64, 0x9bc88).  If
   one of them is ever walked at another format or location, these premises are where it bites. *)
ps = [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32] ->
65536 <= f -> f + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD ->
(forall s, hd_error args = Some (printf_facts_c.APtr s) ->
  65536 <= bv_unsigned (getr regs 13) /\ bv_unsigned (getr regs 13) + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD) ->
PF_GLOBALS_TOP <= d ->
printf_facts_c.pf_text ps args = Some T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
aread_ok (3 * ESTACK) W regs mem f (Z.of_nat (length fmt) + 1) ->
atail_vis W mem (f + Z.of_nat (length fmt)) ->
apf_args_ok (3 * ESTACK) W regs mem d n
[getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
awrite_ok (3 * ESTACK) ly S W regs mem d n ->
(* seven bytes past the buffer in application memory: the shared snprintf route's final text (a Theorem Labs lane's
   working branch 3e35620c52e, sh_asnprintf_realizes(U)) asks amem_range d (sn_len (n - 1) T + 8), and
   sn_len (n - 1) T + 8 can reach n + 7; amem_range is NUMERIC (YG0d.v:329), so amem_range d n above does NOT give it
   near a memory boundary.  Do not tidy this back to n: the bridge from fm's instance needs it (amem_range_le). *)
amem_range d (n + 7) ->
rt_rom_view W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(art_post (3 * ESTACK) ly S W regs mem md (fun a => d <= a < d + n)
(fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
abytes_at W mem' d (printf_facts_c.pf_bytes (firstn (Z.to_nat (n - 1)) T ++ [0])))).
(* art_post gives aentry_post (it adds the scratch's presence); ecall_pre_stk is ecall_pre and ascratch_ok. *)
Lemma aentry_post_of_art_post : forall stk ly S W regs mem md E Q W' c',
art_post stk ly S W regs mem md E Q W' c' -> aentry_post stk ly S W regs mem md E Q W' c'.
Proof.
intros stk ly S W regs mem md E Q W' c' (-> & regs' & mem' & md' & Hc & HAR & HP & Hs & HQ & Hfr & Hpr & _).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact HAR|]. split; [exact HP|].
split; [exact Hs|]. split; [exact HQ|]. split; [|exact Hpr].
intros a Ha HE Hs2. exact (Hfr a Ha Hs2 HE).
Qed.
Lemma ecall_pre_stk_of : forall stk ly S W regs mem md,
ecall_pre SEGS B ly S W regs mem md -> ascratch_ok stk ly W regs mem -> ecall_pre_stk stk ly S W regs mem md.
Proof. intros stk ly S W regs mem md H1 [H2 H3]. split; [exact H1|]. split; [exact H2 | exact H3]. Qed.
(* rom_view (every other W_sites form's premise, and the walks' entry fact) gives a Theorem Labs lane's narrower rt_rom_view. *)
Lemma rt_rom_view_of_rom_view : forall W mem, rom_view SEGS W mem -> rt_rom_view W mem.
Proof. intros W mem H a Ha _ _. exact (H a Ha). Qed.

End c.

(* ---- The journal lifting of every entry above, over W_journal.v's ajournal_gx. ----
   A walk at a call to one of these entries holds an ajournal_gx from its own entry; the entry's contract is
   about ecall_pre.  aj_gx_entry_at turns the one into the other: given the contract already applied to its
   arguments (so only ecall_pre and the scratch remain), the call ends back at ra with the same journal, the
   result, the frame and presence.  The entry's written bytes Wr must be ones the journal allows: a byte of the
   walk's globals G (visible, aview <> None, before the call: a .bss global such as g_lock reads through seg_rom
   until first stored, so presence is not asked), or an awr_byte of the walk's own window outside its out-cells.
   Proof: the donor's ajournal_after_write for the bytes outside G (the allocator state is kept at the bytes
   memory sees outside G, by AR_frame_law, since G holds no aowned byte), then W_journal.v's ajournal_rebase for
   the bytes of G. *)
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma aview_wrap64 : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.
Lemma aj_gx_entry_at : forall G XO OUT (stk pc : Z) (Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop)
  W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
@ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= stk -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> inG G a -> aview SEGS (w_H W) memT a <> None) ->
(forall a, Wr a -> ~ inG G a ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) ->
(ecall_pre SEGS B lyc Sc W regsT memT mdc -> ascratch_ok stk lyc W regsT memT ->
 SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (aentry_post B stk lyc Sc W regsT memT mdc Wr Pr)) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 @ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ Pr regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (sp0 + o - stk <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HG HX16 HJ Hsp Hal Hneg Hstk Hbud Hgp Htp Hra Hraw HWd HWg HWa AM.
pose proof pa_segs_low as Hsegs.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k regsT (o - XO) HJi);
  [lia | rewrite <- Zminus_mod_idemp_r, HX16, Z.sub_0_r; exact Hal | lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HSC : ascratch_ok stk lyc W regsT memT).
{ split; [rewrite Eslo, Hsp; lia|]. intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
eapply SRr_mono; [exact (AM HPRE HSC)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & HPr & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* the memory that is the call's outside G and the caller's on G *)
set (memM := fun x : word => if inGb G (bv_unsigned x) then memT x else mem2 x).
assert (MG : forall x, inGb G (bv_unsigned x) = false -> memM x = mem2 x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (MT : forall x, inGb G (bv_unsigned x) = true -> memM x = memT x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (GLO : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (inG_low SEGS B Hsegs G a HG Ha)).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) memT a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MT; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact HGa. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem2 a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply inGb_false. exact HGa. }
(* the scratch lies in the stack, far above every global *)
assert (SCG : forall a, inG G a -> ~ (sp0 + o - stk <= a < sp0 + o)) by (intros a Ha Hs; pose proof (GLO a Ha); unfold kLowMemEnd in *; lia).
assert (HARM : AR SEGS B lyc Sc W memM md2).
{ eapply (al_frame _ _ LAWS lyc Sc W mem2 md2 memM md2 HAR2); [| | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros HGa. destruct (HG a HGa) as (Hi & Hno & _).
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hg.
    + apply inGb_spec in Hg. rewrite (AVT a' Ra Hg). destruct (HWd a') as [HW | HW].
      * exact (HWg a' HW Hg).
      * rewrite <- (Hfr a' Ra HW (SCG a' Hg)). exact Hv.
    + rewrite (AV2 a' Ra ltac:(apply inGb_false; exact Hg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hg; [|reflexivity].
    exfalso. apply inGb_spec in Hg. pose proof (proj1 (HG _ Hg)) as Hi.
    rewrite (hidden_not_img SEGS W _ Hi) in Hh. discriminate. }
(* (i) the writes outside G, by the donor's ajournal_after_write *)
assert (HJM : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memM md2 k).
{ eapply (ajournal_after_write SEGS B LAWS Hsegs (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k memM md2
    (fun a => (Wr a /\ ~ inG G a) \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJi).
  - intros a Ha Hn. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. exact (AVT a Ha Hg).
    + assert (HnG : ~ inG G a) by (apply inGb_false; exact Hg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | | intros Hs; apply Hn; right; exact Hs].
      intros HW. apply Hn. left. split; [exact HW | exact HnG].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a [[HW HnG] | Hs]; left.
    + destruct (HWa a HW HnG) as [[Hs | Hrest] _]; [left; lia | right; exact Hrest].
    + left. lia.
  - exact HARM.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
(* (ii) the writes to G, by W_journal.v's ajournal_rebase, and (iii) the repack *)
assert (HJ2 : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 (gover G memS mem2) md own lyc Sc W mem2 md2 k).
{ apply (ajournal_rebase SEGS B LAWS Hsegs G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros x Hx. symmetry. exact (MG x Hx).
  - intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Hh; [exact Hx|].
    destruct (inGb G (bv_unsigned x)) eqn:Hg; [|rewrite (MG x Hg) in Hx; exact Hx].
    rewrite (MT x Hg) in Hx. destruct (memT x) as [b|] eqn:Eb; [|exfalso; exact (Hx eq_refl)].
    assert (Hp : apresent (w_H W) memT (bv_unsigned x)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hp) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k (gover G memS mem2) HSTK HXO HJ2).
  - intros x Hx. unfold mrestrict, gover in *. rewrite Hx. exact (Hag x Hx).
  - intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply Hfr; [lia | | lia].
    intros HW. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. pose proof (GLO a Hg). unfold kLowMemEnd in *. lia.
    + destruct (HWa a HW ltac:(apply inGb_false; exact Hg)) as [_ Hn]. exact (Hn Ha). }
split; [exact HP2|]. split; [exact HPr|]. split; [exact Hfr | exact Hgr].
Qed.

(* The two donor-shaped entries whose posts are not aentry_post, lifted through aj_gx_entry_at:
   strlen (W_contract.v astrlen_realizes) and bcmp (Reusable/YG0d.v abcmp_realizes).  Every entry of this file
   is lifted by aj_gx_entry_at directly, with its contract applied to its arguments. *)
Lemma aj_strlen_gx_at : forall pc, astrlen_realizes B pc ->
forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
@ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= kk -> kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte SEGS W memT x (kk + 1) 0 kk ->
src_ok SEGS W regsT memT x (kk + 1) ->
(forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (kk + 1) -> amem_range x 8 ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (kk + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) x (kk + 1) ->
(forall a, x + kk < a < x + kk - (x + kk) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
rom_view SEGS W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 @ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ getr regs2 10 = w64 kk /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AST G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk o raw
HG HX16 HJ Ha0 Hx0 Hk0 Hk32 Hxk Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hm8 Hrx Hhx Htail Hrom.
eapply SRr_mono.
{ apply (aj_gx_entry_at G XO OUT (2 * ESTACK) pc (fun _ => False) (fun regs' _ => getr regs' 10 = w64 kk)
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HG HX16 HJ Hsp Hal Hneg
    ltac:(unfold ESTACK; lia) Hbud Hgp Htp Hra Hraw).
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE [Hlo Hpres]. eapply SRr_mono.
    { exact (AST lyc Sc W regsT memT mdc x kk HPRE Hlo Hpres Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsx
        ltac:(rewrite Hsp; exact Hbx) Hmx Hm8 Hrx Hhx Htail Hrom). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros a Ha _ Hs; exact (Hfr a Ha Hs) | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hres|].
split; [intros a Ha Hs; exact (Hfr a Ha (fun H => H) Hs) | exact Hpres2].
Qed.
Lemma aj_bcmp_gx_at : forall pc, abcmp_realizes SEGS B pc ->
forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
@ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x n -> src_ok SEGS W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 @ajournal_gx _ SK SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
 (v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc ABC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HG HX16 HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
eapply SRr_mono.
{ apply (aj_gx_entry_at G XO OUT (2 * ESTACK) pc (fun _ => False)
    (fun regs' _ => exists v, getr regs' 10 = v /\
      (v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)))
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HG HX16 HJ Hsp Hal Hneg
    ltac:(unfold ESTACK; lia) Hbud Hgp Htp Hra Hraw).
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE [Hlo Hpres]. eapply SRr_mono.
    { exact (ABC lyc Sc W regsT memT mdc x y n HPRE Hlo Hpres Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
        ltac:(rewrite Hsp; exact Hbx) ltac:(rewrite Hsp; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [exists v; split; [exact Hres | exact Hcmp]|].
    split; [intros a Ha _ Hs; exact (Hfr a Ha Hs) | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (v & Hres & Hcmp) & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hres|]. split; [exact Hcmp|].
split; [intros a Ha Hs; exact (Hfr a Ha (fun H => H) Hs) | exact Hpres2].
Qed.
End d.
End b.
End a.
