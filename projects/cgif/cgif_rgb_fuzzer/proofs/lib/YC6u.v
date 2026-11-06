(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0f YC04 YC07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Lemma aftok_fresh : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n,
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
~ In (res, n) (ablocks B lyc Sc) -> aftok FP (ablocks B ly S) (res, n).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n HJ Hc H0 i Hi. cbn [fst snd] in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
exact (Hgone res n i H0 Hc Hi).
Qed.
Lemma awr_fresh_any : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n blc i lyq ownq,
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
~ In (res, n) (ablocks B lyc Sc) -> In (res, n) blc -> 0 <= i < req_size n ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k res n blc i lyq ownq HJ Hc Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B ly S)) as [H0 | H0].
- right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | lia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
End b.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AREALLOC : arealloc_realizes trasegs B 0x53108 0x53640.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variable s1v : Z.
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + ASTACK <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis Htop32 : sp0 + 32 <= ly_top ly.
Variables (rav s0v : Z) (ch0 : list (Z * Z * Z)).
Hypothesis HCH0 : achain ly (aview trasegs (w_H W0) mem0) sp0 s0v ch0.
Hypothesis Hrav : rav = 0x81368.
Hypothesis Hspine : spine ch0 = [] \/ spine ch0 = [0x80ea8].
Hypothesis Hs0v : 0 <= s0v < 2 ^ 64.
Definition hk_ch : list (Z * Z * Z) := (sp0, rav, s0v) :: ch0.
Lemma hk_achain : forall lyc Sc W mem md k,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 496) 8 s0v -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 504) 8 rav ->
achain lyc (aview trasegs (w_H W) mem) (sp0 - 512) sp0 hk_ch.
Proof.
intros lyc Sc W mem md k HJ V496 V504.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Qal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
replace (32 * (sp0 / 32)) with ((4 * (sp0 / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HUP : forall a, sp0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem a = aview trasegs (w_H W0) mem0 a).
{ intros a Ha. apply F1; [clear - Ha Hceil Hslo HSTK Has; lia | clear - Ha; lia]. }
apply (achain_ly_top ly lyc _ _ _ _ Etop).
unfold hk_ch. apply (achain_push ly _ _ sp0 s0v rav ch0 (sp0 - 512) HCH0); [clear - Htop H47; lia | exact HUP | | | rewrite Hrav; clear; lia | | exact Qal8 | | clear; lia].
- replace (sp0 - 8) with (s1v + 504) by (rewrite Hs1; lia). apply (rdword_of_val_mem trasegs _ _ _ _ V504). rewrite Hrav. clear. lia.
- replace (sp0 - 16) with (s1v + 496) by (rewrite Hs1; lia). exact (rdword_of_val_mem trasegs _ _ _ _ V496 Hs0v).
- clear - Hceil Hslo HSTK Has. lia.
- clear - Htop32. lia.
Qed.
Lemma hk_chain : forall lyc Sc W (regs : bvmap 5 word) mem md k,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 496) 8 s0v -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 504) 8 rav ->
getr regs 2 = Z_to_bv 64 s1v -> getr regs 8 = Z_to_bv 64 (s1v + 512) -> 4096 <= raZ regs ->
chain_pre lyc (aview trasegs (w_H W) mem) regs hk_ch.
Proof.
intros lyc Sc W regs mem md k HJ V496 V504 G2 G8 Hra.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Has : ASTACK = 16384) by reflexivity.
assert (Qal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
replace (32 * (sp0 / 32)) with ((4 * (sp0 / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HUP : forall a, sp0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem a = aview trasegs (w_H W0) mem0 a).
{ intros a Ha. apply F1; [clear - Ha Hceil Hslo HSTK Has; lia | clear - Ha; lia]. }
assert (Hch1 : achain ly (aview trasegs (w_H W) mem) (sp0 - 512) sp0 hk_ch).
{ unfold hk_ch. apply (achain_push ly _ _ sp0 s0v rav ch0 (sp0 - 512) HCH0); [clear - Htop H47; lia | exact HUP | | | rewrite Hrav; clear; lia | | exact Qal8 | | clear; lia].
- replace (sp0 - 8) with (s1v + 504) by (rewrite Hs1; lia). apply (rdword_of_val_mem trasegs _ _ _ _ V504). rewrite Hrav. clear. lia.
- replace (sp0 - 16) with (s1v + 496) by (rewrite Hs1; lia). exact (rdword_of_val_mem trasegs _ _ _ _ V496 Hs0v).
- clear - Hceil Hslo HSTK Has. lia.
- clear - Htop32. lia. }
assert (Usp : spZ regs = sp0 - 512).
{ unfold spZ. rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTK Has; lia). exact Hs1. }
apply (achain_chain_pre lyc _ (sp0 - 512) sp0 _ _ (achain_ly_top ly lyc _ _ _ _ Etop Hch1)).
- rewrite Usp. clear - Hceil Hslo HSTK Has. lia.
- unfold s0Z. rewrite G8, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTK Has; lia). rewrite Hs1. lia.
- exact Hra.
Qed.
Lemma hk_trace_in : forall pc0 (regs : bvmap 5 word) ret,
raZ regs = ret ->
memZL (firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) [ret; 0x81368])) TRACES_cgif_rgb_addframe = true ->
memZL (firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) [ret; 0x81368; 0x80ea8])) TRACES_cgif_rgb_addframe = true ->
In (call_trace0 pc0 regs hk_ch) (as_universe B).
Proof.
intros pc0 regs ret Hret M1 M2. rewrite call_trace_of_spine. unfold hk_ch. cbn [spine map fst snd]. fold (spine ch0). rewrite Hret, Hrav.
apply (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; assumption.
Qed.
End c.
