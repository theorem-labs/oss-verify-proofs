(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE39.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE39.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AB1w AE3a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
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
Lemma mc_bounds : MC_LO = 0x10340 /\ MC_HI = 0x10360.
Proof. split; reflexivity. Qed.
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
End c.
