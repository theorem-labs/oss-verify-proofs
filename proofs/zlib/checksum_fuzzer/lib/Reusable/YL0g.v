(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition in_ro_img (B : malloc_syms) (a : Z) : Prop :=
(exists s, In s (ms_segs B) /\ seg_writable s = false /\
Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) /\
~ static_owned B a.
Definition rodata_ok (B : malloc_syms) (mem : word -> option byte) : Prop :=
forall a, in_ro_img B a -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Section c.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Definition lib_scratch (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop :=
(spZ regs - stk <= a < spZ regs) \/ (errno_addr B <= a < errno_addr B + 4).
Definition lib_pre (stk empty : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ra p n : Z) : Prop :=
MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
getr regs 1 = Z_to_bv 64 ra /\
spZ regs mod 16 = 0 /\ alloc_ceiling + stk <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall a, spZ regs - stk <= a < spZ regs -> writable_at segs mem a) /\
getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
getr regs 10 = Z_to_bv 64 p /\ getr regs 11 = Z_to_bv 64 n /\
((n = 0 /\ p = empty) \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)) /\
rodata_ok B mem.
Definition lib_post (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : Z)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch stk regs a -> writable_at segs mem' a).
Definition lib_contract (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n,
lib_pre stk empty L A regs mem md ra p n ->
frm_zero fp_csr ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post stk L A regs mem md p L' A' regs' mem' md').
End c.
Definition LIB_STACK : Z := 16384.
Definition LIB_STACK_RGB : Z := 61440.
End b.
Definition lib_contract_all {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (pc ra empty stk : Z) : Prop :=
forall fx : FPState, @lib_contract fx rc B API pc ra empty stk.
