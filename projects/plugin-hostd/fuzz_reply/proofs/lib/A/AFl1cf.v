(* copied from cgif_file lib/A/AFl1.v by rules r1,r2,r3,r6,r9, generator 50bc5f410abb74cbd38e547f6cb04cbe54d2a34c9ce77dad775db661299db5a2 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFl1.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (2 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00cf YG0dcf YG0ncf YGcfNames.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
Variable Hp : list Z.

Local Open Scope am_scope.
Definition A_Refill : Z := 0x369c8.
Definition A_ALLOCATOR : Z := 0xa2a58.
Definition RSTACK : Z := 1024.
Definition refill_tree (c : Z) : M unit := init_cache_if_needed ;; refill_if_empty_cf c.
Section d.
Variable B : asyms.
Definition refill_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z) : Prop :=
ARcf tfibsegs B ly S Hp W mem md /\
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
acall_post_cf tfibsegs B RSTACK ly S Hp W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end).
Definition tfib_refill_spec : Prop :=
forall ly S W regs mem md c,
refill_pre ly S W regs mem md c ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leaf ly S W regs mem md c).
End d.
End b.
