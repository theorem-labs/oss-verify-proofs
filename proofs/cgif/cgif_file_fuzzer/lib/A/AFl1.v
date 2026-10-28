(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK0i YP09 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Definition A_Refill : Z := 0x36104.
Definition A_ALLOCATOR : Z := 0xa2998.
Definition RSTACK : Z := 1024.
Definition refill_tree (c : Z) : M unit := init_cache_if_needed ;; refill_if_empty c.
Section d.
Variable B : asyms.
Definition refill_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z) : Prop :=
AR tfibsegs B ly S W mem md /\ A_bytes (w_A W) + EV_A <= abudget S /\
refill_reg S c /\
qloosem S /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + RSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - RSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 (ly_T ly + t_cache + 80 * c) /\
getr regs 12 = w64 A_ALLOCATOR /\ getr regs 13 = w64 c /\
1 <= c <= 31 /\ pc_chunks (cache S c) = [].
Definition refill_leaf (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B RSTACK ly S W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end).
Definition tfib_refill_spec : Prop :=
forall ly S W regs mem md c,
refill_pre ly S W regs mem md c ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leaf ly S W regs mem md c).
End d.
End b.
