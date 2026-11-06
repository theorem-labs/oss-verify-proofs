(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of the ASan strcmp interceptor (and of the one-`j` trampoline
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/AStrcmpDef.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
   __interceptor_trampoline_strcmp = __wrap_strcmp that enters it), in the form of abcmp_realizes
   (proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) over the asan-state definitions of that proof as libreac/fuzz_grant holds
   them. The interceptor compares byte by byte up to the first index k where the bytes differ or s1's byte is 0, checks
   [s1, s1 + k + 1) and [s2, s2 + k + 1) with the READ_RANGE checks (QuickCheck below 64 bytes, else
   __asan_region_is_poisoned), calls the empty weak hook, and returns CharCmpX (-1, 0 or 1). Target-independent: every
   address comes from the layout or the registers. R1: the strings are disjoint from the callee's stack window
   [sp - 2 ESTACK, sp). R2: not stated, because this interceptor does not touch the AddrHashMap metadata (no FILE
   object). It subsumes the literal instance of libreac/fuzz_pcap lib/A/Rt/StrcmpDef.v (x = y, k = the literal's
   length, c1 = c2 = 0, result 0). *)
(* Registry (a Theorem Labs lane's final ruling, 2026-10-29 03:15Z): ONE strcmp text, lifted to user-poisoned heads:
   Reusable/AStrcmpDefU.v astrcmp_realizesU. This file's astrcmp_realizes is its U = [] instance
   (AStrcmpDefU.astrcmp_realizes_of_U) and stays as it is, so its consumers rebuild nothing. A unit with poisoned heads
   at a strcmp call proves astrcmp_realizesU for its image (fuzz_state does, from its own walk); every other unit uses
   this text. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* sanitizer_common's CharCmpX. *)
Definition strcmp_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.

(* The compare stops at index k: the bytes before k are equal and nonzero; at k they differ or s1's byte is 0. *)
Definition str_meet (W : world segs) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
  0 <= k /\
  (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                     aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
  aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
  (c1 <> c2 \/ c1 = 0).

Definition astrcmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  str_meet W mem x y k c1 c2 ->
  src_ok segs W regs mem x (k + 1) -> src_ok segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
(* Donor (provenance of this file, origin first): libreac/fuzz_grant lib/Reusable/AStrcmpDef.v (file sha256 d277b0470b05; donor not released), copied, module paths changed. *)
(* Its contract is stated in the form of abcmp_realizes of cgif/cgif_file_fuzzer lib/YG0d.v (released in 6eb657611b9d). *)
