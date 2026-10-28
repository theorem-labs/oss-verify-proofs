(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0s YK18 YM02 YP0m YP09 YK04 YA0i YA0n YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AD1t AD20 AD1v AD2h AD2f AD1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YG08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition aread_check_stmt (B : asyms) : Prop :=
forall ly S W regs mem md n p,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 p -> 0 < n < 2 ^ 31 -> 0 <= p -> p + n <= 2 ^ 63 ->
amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\ getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Lemma layout_of_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md -> layout_ok ly.
Proof. intros ly S W mem md (HM & _). exact (am_layout _ _ _ _ HM). Qed.
Lemma acall_pre_of_drv : forall ly S W regs mem md,
drv_pre B ly S W regs mem md -> acall_pre tfibsegs B ly S W regs mem md [].
Proof.
intros ly S W regs mem md (HAR & [Elo Ehi] & Hnev & Hret & Hra & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp & Hs0 & Hqt).
pose proof (layout_of_AR _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
split; [exact HAR|]. split; [exact (aregime_small _ Hnev)  |]. split; [exact Hret|]. split; [exact Hal|].
split; [unfold ly_bot, kStackSpan, ASTACK in *; lia|]. split; [unfold ly_bot, kStackSpan in *; lia|]. split; [rewrite Ehi; unfold kHighMemEnd; lia|].
split; [exact Hpres|]. split; [exact Hgp|]. split; [exact Htp|].
split; [| exact (conj Hqt (mroom_of_regime (as_universe B) S (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid S (aregime_small _ Hnev)) (qtight_qloose S Hqt)))].
unfold chain_pre. split; [exact Hra|].
destruct (frame0_ok ly regs); [| reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|].
symmetry. unfold bad_next. apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. left. apply Z.leb_le. pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold kStackSpan in *. lia.
Qed.
Lemma call_trace_drv : forall ly regs pc0, call_trace ly pc0 regs [] = [pc0; raZ regs] \/ call_trace ly pc0 regs [] = [pc0].
Proof.
intros ly regs pc0. unfold call_trace. destruct (frame0_ok ly regs); [| right; reflexivity].
unfold unwind_of_chain. cbn [flat_map app]. destruct (raZ regs =? pc0) eqn:E.
- right. reflexivity.
- left. reflexivity.
Qed.
Theorem tfib_free_site : afree_realizes tfibsegs B -> free_site_tfa B.
Proof.
intros AFREE ly S W regs mem md p n HPRE Hin Ha0 Htr2 Htr1.
pose proof (acall_pre_of_drv _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & Hnev & _).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (ml_free _ ML S p n (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF Hnev (or_intror Hin) Htr) as HTOK.
pose proof (AFREE ly S W regs mem md p n [] HAP (or_intror Hin) Ha0 Htr) as HREAL.
eapply SRr_mono; [exact (amreal_SRr tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (ly' & regs' & mem' & md' & -> & HPOST & _)). cbn [snd] in HPOST.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HE. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |]. intros [_ X]. exact (HE X).
Qed.
Theorem tfib_free_null_site : afree_realizes tfibsegs B -> free_null_site_tfa B.
Proof.
intros AFREE ly S W regs mem md HPRE Ha0 Htr2 Htr1.
pose proof (acall_pre_of_drv _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & Hnev & _).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (ml_free _ ML S PNull 0 (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF Hnev (or_introl eq_refl) Htr) as HTOK.
pose proof (AFREE ly S W regs mem md PNull 0 [] HAP (or_introl eq_refl) Ha0 Htr) as HREAL.
eapply SRr_mono; [exact (amreal_SRr tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (ly' & regs' & mem' & md' & -> & HPOST & _)). cbn [snd] in HPOST.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs _. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |]. intros [X _]. exact (X eq_refl).
Qed.
Lemma ecall_pre_of_drv : forall ly S W regs mem md,
drv_epre B ly S W regs mem md -> ecall_pre tfibsegs B ly S W regs mem md.
Proof.
intros ly S W regs mem md (HAR & [Elo Ehi] & Hret & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp).
unfold sp_window_lo, sp_window_hi in *.
split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
pose proof (lo_top _ (layout_of_AR _ _ _ _ _ HAR)) as (T1 & T2 & _).
split; [unfold ly_bot, kStackSpan, ESTACK in *; lia|]. split; [rewrite Ehi; unfold kHighMemEnd; lia|].
split; [exact Hpres|]. exact (conj Hgp Htp).
Qed.
Theorem tfib_memcpy_site : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) -> memcpy_site_tfa B.
Proof.
intros AICPY ly S W regs mem md d x n HPRE R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv Hx0 Hx1 Hsrc Hdisj Hxm Hrax Hhvx.
exact (AICPY ly S W regs mem md d x n (ecall_pre_of_drv _ _ _ _ _ _ HPRE) R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv
(conj Hx0 (conj Hx1 (conj Hsrc (conj Hdisj (conj Hxm (conj Hrax Hhvx))))))).
Qed.
Theorem tfib_read_check : aread_check_stmt B -> read_check_tfa B.
Proof.
intros ARD ly S W regs mem md n ptr HPRE R10 R9 Hn Hp0 Hp1 Ham Hra Hhv.
exact (ARD ly S W regs mem md n ptr (ecall_pre_of_drv _ _ _ _ _ _ HPRE) R10 R9 Hn Hp0 Hp1 Ham Hra Hhv).
Qed.
End c.
End b.
