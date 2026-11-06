(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the shadow-hull visibility of a range homed on the
   REAL STACK, over YCbqG.v's generic allocator invariant ARx with LAWS : AR_laws_x. rule 24: proves no function (kind:
   engine lemma). Consumer: h-walk-identity's S8a pieces 3, 4, 7 (prhex_tree's `shadow_hull_vis .. v 56` for a root on
   the real stack after a program call, lib/A/PRH_FnEx.v prhex_home's third disjunct).
   Source: AR_laws_x field 13 alone (alx_zshadow_byte, YCbqG.v ARx_zshadow_byte_law: the shadow byte of every address of
   [ly_stk_lo, ly_stk_hi) reads 0). shadow_hull_vis (YG0d.v) asks the shadow of [v, v + n) rounded OUT to 64 bytes (8
   shadow bytes, the 8-aligned shadow granule), so the hull lies in field 13's range iff the rounded range lies in the
   window. stack_hull_vis_x_rng states exactly that (no alignment); stack_hull_vis_x states it from v and v + n in the
   window plus both stack bounds 64-aligned: with `v + n <= ly_stk_hi ly` alone and ly_stk_hi not 64-aligned the top
   granule's shadow is outside every AR_laws_x field, so that form is not provable over a generic ARx. AR_laws_x gives no
   alignment (YCbqG.v's comment at field 13); the instance has it from layout_ok's lo_top (YG0f.v: page_aligned
   ly_stk_lo / ly_stk_hi), a conjunct of ARcf (amc_layout) and of cgif's AR (am_layout): stack_hull_vis_x_lo.
   Numerals: 8 and 64 are LENGTH (the shadow scale and the shadow granule's application span), 4096 is LENGTH (the page,
   inside page_aligned). No address literal; SHADOW_OFF is YG0f.v's name. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The 8-aligned shadow granule of an address, read in application bytes: SHADOW_OFF is a multiple of 64. *)
Lemma shadow_granule_64 : forall x, shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8.
Proof.
intro x. unfold shadow_addr, SHADOW_OFF.
replace (2147450880 + x / 8) with (268431360 * 8 + x / 8) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.
Section h. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* THE WEAKEST FORM: the 64-byte rounding of [v, v + n) inside the real-stack window. No alignment, any n. *)
Lemma stack_hull_vis_x_rng : forall ly S Hp W mem md v n,
ARx ly S Hp W mem md ->
ly_stk_lo ly <= v / 64 * 64 -> (v + n - 1) / 64 * 64 + 64 <= ly_stk_hi ly ->
shadow_hull_vis (aview segs (w_H W) mem) v n.
Proof.
intros ly S Hp W mem md v n HAR Hlo Hhi s Hs.
rewrite !shadow_granule_64 in Hs.
assert (Hb : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly) by lia.
pose proof (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md _ HAR Hb) as Z0.
assert (E : SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8 = s) by (rewrite (Z.mul_comm 8), Z.div_mul by lia; lia).
rewrite E in Z0. rewrite Z0. discriminate.
Qed.
(* THE CONSUMER'S FORM: v and v + n in the real-stack window [ly_stk_lo, ly_stk_hi), both bounds 64-aligned. *)
Lemma stack_hull_vis_x : forall ly S Hp W mem md v n,
ARx ly S Hp W mem md ->
ly_stk_lo ly mod 64 = 0 -> ly_stk_hi ly mod 64 = 0 ->
ly_stk_lo ly <= v -> v + n <= ly_stk_hi ly ->
shadow_hull_vis (aview segs (w_H W) mem) v n.
Proof.
intros ly S Hp W mem md v n HAR Hla Hha Hv Hvn.
apply (stack_hull_vis_x_rng ly S Hp W mem md v n HAR); Z.div_mod_to_equations; lia.
Qed.
(* THE INSTANCE FORM: the alignment from layout_ok's lo_top (page_aligned ly_stk_lo / ly_stk_hi). *)
Lemma stack_hull_vis_x_lo : forall ly S Hp W mem md v n,
ARx ly S Hp W mem md -> layout_ok ly ->
ly_stk_lo ly <= v -> v + n <= ly_stk_hi ly ->
shadow_hull_vis (aview segs (w_H W) mem) v n.
Proof.
intros ly S Hp W mem md v n HAR HL Hv Hvn.
pose proof (lo_top ly HL) as T. unfold page_aligned in T.
apply (stack_hull_vis_x ly S Hp W mem md v n HAR); [| | exact Hv | exact Hvn]; Z.div_mod_to_equations; lia.
Qed.
End h.
