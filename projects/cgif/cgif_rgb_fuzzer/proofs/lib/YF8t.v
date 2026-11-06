(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YQ0b YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03 YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Definition A_Refill {imgk : img} : Z := (0x3670c + D_150).
Definition A_ALLOCATOR {imgk : img} : Z := (0xa6b58 + D_10c0).
Definition RSTACK : Z := 1024.
Definition refill_tree (c : Z) : M unit := init_cache_if_needed ;; refill_if_empty c.
Section d. Context {imgk : img}.
Variable B : asyms.
Definition refill_pre {imgk : img} (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z) : Prop :=
AR tfxsegs B ly S W mem md /\ A_bytes (w_A W) + EV_A <= abudget S /\
refill_reg S c /\
qloose S /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + RSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - RSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 (ly_T ly + t_cache + 80 * c) /\
getr regs 12 = w64 A_ALLOCATOR /\ getr regs 13 = w64 c /\
1 <= c <= 31 /\ pc_chunks (cache S c) = [].
Definition refill_leaf {imgk : img} (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B RSTACK ly S W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end).
Definition tfx_refill_spec {imgk : img} : Prop :=
forall ly S W regs mem md c,
refill_pre ly S W regs mem md c ->
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs mem md) (refill_leaf ly S W regs mem md c).
End d.
End b.
