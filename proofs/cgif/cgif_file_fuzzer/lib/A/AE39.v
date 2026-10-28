(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1w AE3a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition MC_LO : Z := tfib_D_const_HIGHS_0x8080808080808080.
Definition MC_HI : Z := tfib_D_const_ONES_0x0101010101010100 + 8.
Definition mconsts_view (W : world tfibsegs) (mem : word -> option byte) : Prop :=
forall a, MC_LO <= a < MC_HI -> aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Lemma mc_bounds : MC_LO = 0x10350 /\ MC_HI = 0x10370.
Proof. split; reflexivity. Qed.
Lemma mc_in_rom : forall a, MC_LO <= a < MC_HI -> in_rom tfibsegs a.
Proof.
intros a Ha. pose proof mc_bounds as [B1 B2]. unfold in_rom.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity)    .
destruct tfibsegs as [|s1 rest]; [discriminate|].
cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. split; [exact P3|]. lia.
Qed.
Lemma mconsts_of_rom_view : forall W mem, rom_view tfibsegs W mem -> mconsts_view W mem.
Proof. intros W mem Hr a Ha. apply Hr. apply mc_in_rom. exact Ha. Qed.
Lemma mconsts_view_keep : forall (W : world tfibsegs) mem mem',
mconsts_view W mem -> (forall a, MC_LO <= a < MC_HI -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
mconsts_view W mem'.
Proof. intros W mem mem' Hr Heq a Ha. rewrite (Heq a Ha). exact (Hr a Ha). Qed.
Definition amemchr0_realizesM (B : asyms) (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfibsegs W mem x n 0 k ->
src_ok tfibsegs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition astrnlen_realizesM (B : asyms) (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfibsegs W mem x n 0 k ->
src_ok tfibsegs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Lemma amemchr0_of_M : forall B pc, amemchr0_realizesM B pc -> amemchr0_realizes tfibsegs B pc.
Proof.
intros B pc HM ly S W regs mem md x n k H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 Hrom.
exact (HM ly S W regs mem md x n k H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 (mconsts_of_rom_view W mem Hrom)).
Qed.
Lemma astrnlen_of_M : forall B pc, astrnlen_realizesM B pc -> astrnlen_realizes tfibsegs B pc.
Proof.
intros B pc HM ly S W regs mem md x n k H1 Hs1 Hs2 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 Hsb H13 H14 H15 H16 Hrom.
exact (HM ly S W regs mem md x n k H1 Hs1 Hs2 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 Hsb H13 H14 H15 H16 (mconsts_of_rom_view W mem Hrom)).
Qed.
End c.
