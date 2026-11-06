(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build. *)
(* Modified by Theorem Labs, 2026-10: relocated to reac-repacer/fuzz_wire's asan build: addresses and numbers moved by symbol to its asan image; module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* __asan_memmove of libreac/fuzz_pcap's v1.9.0 ASan build (0x51310, 880 B), STATEMENT ONLY, as its own contract in
   cgif_file's interceptor vocabulary (YG0d.v ecall_pre / dest_ok / src_ok / range_addressable / shadow_hull_vis /
   amem_range). It is YG0d.v's aintrin_realizes OCpy without the disjointness premise (d + n <= x \/ x + n <= d):
   the source and the destination may overlap, and the bytes written are the bytes of the OLD memory (memmove
   semantics). YG0d's memop / aintrin_realizes are not changed. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition amemmove_realizes (pc : Z) : Prop :=
forall ly S W regs mem md d x n,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End s.
