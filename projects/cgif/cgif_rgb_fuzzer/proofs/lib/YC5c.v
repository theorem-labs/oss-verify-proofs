(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC1a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma rg_stack_shadow : forall (W : world trasegs) ly S mem md a n,
AR trasegs B ly S W mem md ->
ly_stk_lo ly + 64 <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF a n /\
(0 < n -> shadow_hull_vis (aview trasegs (w_H W) mem) a n).
Proof.
intros W ly S mem md a n HAR Ha Han Hn.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz.
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Ha Han Hn. lia.
- intros Hn0 s Hs.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn0 Lplo Lphi Ha Han Hn. unfold SHADOW_OFF in *. lia.
Qed.
Lemma rg_stack_amem : forall (W : world trasegs) ly S mem md a n,
AR trasegs B ly S W mem md -> ly_stk_lo ly <= a -> a + n < ly_stk_hi ly -> amem_range a n.
Proof.
intros W ly S mem md a n HAR Ha Han.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.

End b.
