(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL0g YI16 YI06 YI14.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Definition lib_preS (stk empty : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ra p n : Z) : Prop :=
lib_pre B API stk empty L A regs mem md ra p n /\
sink_none B mem md /\ spZ regs <= 2 ^ 47 /\ Fs.fs_sorted (m_fs md) = true.
Definition lib_postS (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : Z)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
regs_preserved regs regs' /\
os_step [sink_token] md md' /\ sink_none B mem' md' /\ Fs.fs_sorted (m_fs md') = true /\
(forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ (sk_ofl_head <= a < sk_ofl_head + 8) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a).
Definition lib_contractS (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n,
lib_preS stk empty L A regs mem md ra p n ->
frm_zero fp_csr ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_postS stk L A regs mem md p L' A' regs' mem' md').
End b.
Definition lib_contractS_all {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(pc ra empty stk : Z) : Prop :=
forall fx : FPState, @lib_contractS fx rc B API SH SK pc ra empty stk.
