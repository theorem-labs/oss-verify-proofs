(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/ACf0.v, with its module paths changed; 60 of its 96 lines of code are new or changed and 43 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Open Scope Z_scope.

(* The strnlen interceptor (trampoline 0x45134) and the found case of the memchr interceptor (trampoline 0x45158)
   with the read-only premise of the runtime entries (RtDefs.v rt_rom_view) in place of the global rom_view, and strnlen with its
   window as a parameter.

   astrnlen_realizes (Reusable/YG0d.v:410-428) states strnlen at 2 * ESTACK. The measured chain on the pinned
   image: ___interceptor_strnlen 0x4547c holds 2032 + 112 = 2144 bytes and calls musl strnlen 0x9f6c8 (frame 32),
   which calls the memchr trampoline at 0x9f6e8, at depth 2176. memchr writes 2200 bytes below its own entry sp
   (frame 2032 + 96, then TryAsanInitFromRtl or the range check), so strnlen writes 4376 bytes, and its walk
   through the memchr contract, which asks for ESTACK below the callee sp, needs 2176 + ESTACK. That is
   STRNLEN_E_MIN = 6272; [astrnlen_stk_realizes] holds for every window from it up ([astrnlen_win_realizes]). The
   contract the format chain uses is [astrnlen_w_realizes], the donor text with the window fixed at 6272
   ([astrnlen_w_of_win]); the donor's 2 * ESTACK form follows as well ([astrnlen_of_stk]). The memchr contract the
   walk calls is [amemchr0_realizesR], cgif's amemchr0_realizes (YG0d.v:392-409) with rt_rom_view in place of
   rom_view; it gives the AsanAPI form ([amemchr0_of_rt]). *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Definition STRNLEN_E_MIN : Z := ESTACK + 2176.

Definition amemchr0_realizesR (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Definition astrnlen_stk_realizes (stk pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + stk <= spZ regs -> (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - stk <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - stk <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Definition astrnlen_win_realizes (pc : Z) : Prop :=
forall stk, STRNLEN_E_MIN <= stk -> astrnlen_stk_realizes stk pc.

Definition astrnlen_w_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 6272 <= spZ regs -> (forall a, spZ regs - 6272 <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 6272 <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rt_rom_view segs B W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 6272 <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma astrnlen_w_of_win : forall pc, astrnlen_win_realizes pc -> astrnlen_w_realizes pc.
Proof.
intros pc H. assert (HS : STRNLEN_E_MIN <= 6272) by (unfold STRNLEN_E_MIN, ESTACK; lia).
exact (H 6272 HS).
Qed.

Lemma rt_rom_of_rom : forall W mem, rom_view segs W mem -> rt_rom_view segs B W mem.
Proof. intros W mem Hv a Ha _ _. exact (Hv a Ha). Qed.

Lemma amemchr0_of_rt : forall pc, amemchr0_realizesR pc -> amemchr0_realizes segs B pc.
Proof.
intros pc H ly S W regs mem md x n k HPRE G10 G11 G12 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail Hrom.
exact (H ly S W regs mem md x n k HPRE G10 G11 G12 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Ham Hra Hhull Htail
  (rt_rom_of_rom W mem Hrom)).
Qed.

Lemma astrnlen_of_stk : forall pc, astrnlen_win_realizes pc -> astrnlen_realizes segs B pc.
Proof.
intros pc H ly S W regs mem md x n k HPRE Hlo Hpres G10 G11 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hns Ham Hra Hhull Htail Hrom.
assert (HS : STRNLEN_E_MIN <= 2 * ESTACK) by (unfold STRNLEN_E_MIN, ESTACK; lia).
exact (H (2 * ESTACK) HS ly S W regs mem md x n k HPRE Hlo Hpres G10 G11 Hn Hx Hk0 Hk8 Hk32 Hxk Hfb Hsrc Hns Ham
  Hra Hhull Htail (rt_rom_of_rom W mem Hrom)).
Qed.

End c.
End b.
