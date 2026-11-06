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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma aregs_get : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. specialize (HP (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_tra.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variable s1v : Z.
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + 2 * ESTACK <= STK.
Lemma hk_bcmp_call : forall lyc Sc W (regs : bvmap 5 word) mem md k (x y n : Z) (raw : word) bx nx by_ ny,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 10 = Z_to_bv 64 x -> getr regs 11 = Z_to_bv 64 y -> getr regs 12 = Z_to_bv 64 n -> 0 < n < 2 ^ 32 ->
getr regs 2 = Z_to_bv 64 s1v -> getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 (as_tp B) ->
getr regs 1 = raw -> YK0s.ret_ok raw ->
In (bx, nx) (ablocks B lyc Sc) -> bx <= x -> x + n <= bx + req_size nx ->
In (by_, ny) (ablocks B lyc Sc) -> by_ <= y -> y + n <= by_ + req_size ny ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_bcmp_tra) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\ getr regs2 10 = v /\
(v = Z_to_bv 64 0 <-> forall i, 0 <= i < n -> aview trasegs (w_H W) mem (x + i) = aview trasegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < s1v) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)).
Proof.
intros lyc Sc W regs mem md k x y n raw bx nx by_ ny HJ G10 G11 G12 Hn G2 G3 G4 Gra Hraw Hbx Hx0 Hx1 Hby Hy0 Hy1.
pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W mem md bx nx HAR Hbx) as (_ & Hx4096 & Hxceil & _ & Hxpres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md by_ ny HAR Hby) as (_ & Hy4096 & Hyceil & _ & Hypres & _).
assert (Usp : spZ regs = sp0 + -512).
{ unfold spZ. rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTK Hes; lia). rewrite Hs1. lia. }
eapply SRr_mono.
{ eapply (aj_bcmp_at trasegs B LAWS Hsegs A_bcmp_tra ABCMP W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k x y n (-512) raw HJ G10 G11 G12).
- clear - Hn; lia.
- clear - Hx4096 Hx0; lia.
- clear - Hx1 Hxceil C1; lia.
- clear - Hy4096 Hy0; lia.
- clear - Hy1 Hyceil C1; lia.
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- intros a Ha. split; [apply (aview_some_of_apresent trasegs); apply (proj1 (Hxpres a ltac:(clear - Ha Hx0 Hx1; lia)))|].
rewrite Usp, Hes. clear - Ha Hx1 Hxceil Hceil Hslo HSTK Hes. lia.
- intros a Ha. split; [apply (aview_some_of_apresent trasegs); apply (proj1 (Hypres a ltac:(clear - Ha Hy0 Hy1; lia)))|].
rewrite Usp, Hes. clear - Ha Hy1 Hyceil Hceil Hslo HSTK Hes. lia.
- intros a Ha. rewrite Hes. clear - Ha Hx1 Hxceil Hceil Hslo HSTK Hes. lia.
- intros a Ha. rewrite Hes. clear - Ha Hy1 Hyceil Hceil Hslo HSTK Hes. lia.
- apply (amem_range_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption.
- apply (amem_range_of_block trasegs B LAWS lyc Sc W mem md by_ ny _ _ HAR Hby); assumption.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption.
- intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md by_ ny _ _ HAR Hby); assumption.
- intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W mem md by_ ny _ _ HAR Hby); assumption. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
split; [exact Hcmp|]. split; [|exact Hpres2].
intros a Ha Hn'. apply Hout2; [exact Ha|]. rewrite Hes, Hs1 in *. clear - Hn' Hceil Hslo HSTK Hes. lia.
Qed.
Lemma hk_memcpy_call : forall lyc Sc W (regs : bvmap 5 word) mem md k (d x n : Z) (raw : word) bd nd bx nx,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 n -> 0 < n < 2 ^ 32 ->
getr regs 2 = Z_to_bv 64 s1v -> getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 (as_tp B) ->
getr regs 1 = raw -> YK0s.ret_ok raw ->
In (bd, nd) (ablocks B lyc Sc) -> bd <= d -> d + n <= bd + req_size nd ->
(forall blc lyq ownq i, In (bd, nd) blc -> 0 <= i < req_size nd -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (bd + i)) ->
In (bx, nx) (ablocks B lyc Sc) -> bx <= x -> x + n <= bx + req_size nx ->
(d + n <= x \/ x + n <= d) ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_asan_memcpy) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall i, 0 <= i < n -> aview trasegs (w_H W) mem2 (d + i) = aview trasegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (alloc_ceiling <= a < s1v) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)).
Proof.
intros lyc Sc W regs mem md k d x n raw bd nd bx nx HJ G10 G11 G12 Hn G2 G3 G4 Gra Hraw Hbd Hd0 Hd1 Hperm Hbx Hx0 Hx1 Hdis.
pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W mem md bd nd HAR Hbd) as (_ & Hd4096 & Hdceil & _ & Hdpres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md bx nx HAR Hbx) as (_ & Hx4096 & Hxceil & _ & Hxpres & _).
assert (Usp : spZ regs = sp0 + -512).
{ unfold spZ. rewrite G2, unsigned_lit_small by (rewrite Hs1; clear - Hceil Hslo Hshi H47 C1 HSTK Hes; lia). rewrite Hs1. lia. }
eapply SRr_mono.
{ eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k d x n (-512) raw HJ G10 G11 G12).
- clear - Hn; lia.
- clear - Hd4096 Hd0; lia.
- clear - Hd1 Hdceil C1; lia.
- exact Usp.
- reflexivity.
- clear; lia.
- clear - HSTK Hes; lia.
- exact G3.
- exact G4.
- exact Gra.
- exact Hraw.
- intros a Ha. split.
+ replace a with (bd + (a - bd)) by lia. apply Hperm; [exact Hbd | clear - Ha Hd0 Hd1; lia].
+ rewrite Hes. clear - Ha Hd1 Hdceil Hceil Hslo HSTK Hes. lia.
- apply (amem_range_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W mem md bd nd _ _ HAR Hbd); assumption.
- split; [clear - Hx4096 Hx0; lia|]. split; [clear - Hx1 Hxceil C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trasegs); apply (proj1 (Hxpres a ltac:(clear - Ha Hx0 Hx1; lia)))|].
rewrite Usp, Hes. clear - Ha Hx1 Hxceil Hceil Hslo HSTK Hes. lia. }
split; [exact Hdis|].
split; [apply (amem_range_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption|].
split; [apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption|].
intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS lyc Sc W mem md bx nx _ _ HAR Hbx); assumption. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcp & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact Hcp|]. split; [|exact Hpres2].
intros a Ha Hnd Hn'. apply Hout2; [exact Ha | exact Hnd|]. rewrite Hes, Hs1 in *. clear - Hn' Hceil Hslo HSTK Hes. lia.
Qed.
End b.
