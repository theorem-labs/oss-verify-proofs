(* copied from cgif_file lib/A/YD1i.v by rules r1,r2,r3,r4,r6,rC, generator c03cd3ee83e0f39cd4fe9d090fe9d53155314a0005789c623a860de97ecb6274 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: P'' (the Univ trace carrier, commit 94ab015e127b): the model-law / realizes premises take the trace as admits; the trace fact stays `In _ (as_universe B)` and is converted at each use by admits_fix. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0s YK18 YM02 YP0m YP09 YK04 YA0i YA0n YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCe5 YB1v YF0l YF0m YD1t YD20 YD1vcf YD2h YD2f YD1wcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k YD1ucf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG03dcf YG0d2cf YG0dcf YG0ncf YG0ucf YGcfNames YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00cf YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR YGcfRehidePost.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Definition aread_check_stmt (B : asyms) : Prop :=
forall ly S Hp W regs mem md n p,
ecall_pre_cf tfibsegs B ly S Hp W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 p -> 0 < n < 2 ^ 31 -> 0 <= p -> p + n <= 2 ^ 63 ->
amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
ARcf tfibsegs B ly S Hp W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\ getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Hypothesis ML : model_laws_cf (as_universe B).
(* field round 3 of the cf layer (part 3c: no memnorm): acall_pre_cf ends with cf_hull_ok S /\ arodata_ok_cf segs B mem
   (Reusable/YG0dcf.v), and drv_pre (B/YD1vcf.v) carries both, the hull admission and the read-only RELRO bytes. *)
Lemma layout_of_AR : forall ly S Hp W mem md, ARcf tfibsegs B ly S Hp W mem md -> layout_ok ly.
Proof. intros ly S Hp W mem md (HM & _). exact (amc_layout _ _ _ _ _ HM). Qed.
(* the donor's acall_pre_of_drv over ARcf: the event regime gives way to ROOM_cf (carried by drv_pre), and
   qmeter_cf / the free-array headroom come from YGcfRoomPre.acall_pre_cf_intro; round 3's hull admission and RELRO
   bytes are drv_pre's cf_hull_ok / arodata_ok_cf conjuncts *)
Lemma acall_pre_of_drv : forall ly S Hp W regs mem md,
drv_pre B ly S Hp W regs mem md -> acall_pre_cf tfibsegs B ly S Hp W regs mem md [].
Proof.
intros ly S Hp W regs mem md HPRE.
destruct HPRE as (HAR & [Elo Ehi] & [_ Hroom] & Hret & Hra & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp & Hs0 & Hqt & HHO & HAD).
pose proof (layout_of_AR _ _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
apply (acall_pre_cf_intro tfibsegs B ly S Hp W regs mem md [] HAR Hqt Hroom HHO HAD Hret Hal);
[unfold ly_bot, kStackSpan, ASTACK in *; lia | unfold ly_bot, kStackSpan in *; lia | rewrite Ehi; unfold kHighMemEnd; lia
| exact Hpres | exact Hgp | exact Htp |].
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
(* ROW T (route R): the free site from the primed free contract (lib/B/YG0dcfR.v afree_realizes_cf_rh, free(NULL)
   inside it): its run amreal' over RZ_cf gives the step relation SRrG at R := wle' RZ_cf (amreal'_SRr'), its leaf
   free_leaf_cf_rh the primed post acall_post_cf_rh *)
Theorem tfib_free_site : YG0dcfR.afree_realizes_cf_rh tfibsegs B -> free_site_tfa B (wle' tfibsegs YGcfRehidePost.RZ_cf).
Proof.
intros AFREE ly S Hp W regs mem md p n HPRE Hin Ha0 Htr2 Htr1.
pose proof (acall_pre_of_drv _ _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & [HHp Hroom] & _).
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as HWF.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (mlr_free_cf _ ML S p n (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF (proj2 (proj2 Hroom)) (or_intror Hin) (admits_fix _ _ _ (ts_universe B HB) Htr)) as HTOK.
pose proof (AFREE ly S Hp W regs mem md p n [] HAP (or_intror Hin) Ha0 ltac:(rewrite HHp; intros [])  (admits_fix _ _ _ (ts_universe B HB) Htr)) as HREAL.
eapply SRrG_mono; [exact (amreal'_SRr' tfibsegs YGcfRehidePost.RZ_cf _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (ly' & regs' & mem' & md' & -> & HPOST & _)). cbn [snd] in HPOST.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HE HD. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs | | exact HD]. intros [_ X]. exact (HE X).
Qed.
Theorem tfib_free_null_site : YG0dcfR.afree_realizes_cf_rh tfibsegs B ->
  free_null_site_tfa B (wle' tfibsegs YGcfRehidePost.RZ_cf).
Proof.
intros AFREE ly S Hp W regs mem md HPRE Ha0 Htr2 Htr1.
pose proof (acall_pre_of_drv _ _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & [HHp Hroom] & _).
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as HWF.
assert (Htr : In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B)).
{ destruct (call_trace_drv ly regs (pc_free_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (mlr_free_cf _ ML S PNull 0 (call_trace ly (pc_free_ra0 (as_code B)) regs []) HWF (proj2 (proj2 Hroom)) (or_introl eq_refl) (admits_fix _ _ _ (ts_universe B HB) Htr)) as HTOK.
pose proof (AFREE ly S Hp W regs mem md PNull 0 [] HAP (or_introl eq_refl) Ha0 ltac:(rewrite HHp; intros []) (admits_fix _ _ _ (ts_universe B HB) Htr)) as HREAL.
eapply SRrG_mono; [exact (amreal'_SRr' tfibsegs YGcfRehidePost.RZ_cf _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK))|].
cbv beta. intros W' c' _ ([[] S'] & tr & Hpath & (ly' & regs' & mem' & md' & -> & HPOST & _)). cbn [snd] in HPOST.
exists ly', S', regs', mem', md', (call_trace ly (pc_free_ra0 (as_code B)) regs []), tr.
split; [exact Htr|]. split; [exact Hpath|]. split; [reflexivity|].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs _ HD. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs | | exact HD]. intros [X _]. exact (X eq_refl).
Qed.
Lemma ecall_pre_of_drv : forall ly S Hp W regs mem md,
drv_epre B ly S Hp W regs mem md -> ecall_pre_cf tfibsegs B ly S Hp W regs mem md.
Proof.
intros ly S Hp W regs mem md (HAR & [Elo Ehi] & Hret & Hal & [Wlo Whi] & [Tlo Thi] & Hpres & Hgp & Htp).
unfold sp_window_lo, sp_window_hi in *.
split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
pose proof (lo_top _ (layout_of_AR _ _ _ _ _ _ HAR)) as (T1 & T2 & _).
split; [unfold ly_bot, kStackSpan, ESTACK in *; lia|]. split; [rewrite Ehi; unfold kHighMemEnd; lia|].
split; [exact Hpres|]. exact (conj Hgp Htp).
Qed.
Theorem tfib_memcpy_site : aintrin_realizes_cf tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) -> memcpy_site_tfa B.
Proof.
intros AICPY ly S Hp W regs mem md d x n HPRE R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv Hx0 Hx1 Hsrc Hdisj Hxm Hrax Hhvx.
exact (AICPY ly S Hp W regs mem md d x n (ecall_pre_of_drv _ _ _ _ _ _ _ HPRE) R10 R11 R12 Hn Hd0 Hd1 Hdest Hdm Hra Hhv
(conj Hx0 (conj Hx1 (conj Hsrc (conj Hdisj (conj Hxm (conj Hrax Hhvx))))))).
Qed.
Theorem tfib_read_check : aread_check_stmt B -> read_check_tfa B.
Proof.
intros ARD ly S Hp W regs mem md n ptr HPRE R10 R9 Hn Hp0 Hp1 Ham Hra Hhv.
exact (ARD ly S Hp W regs mem md n ptr (ecall_pre_of_drv _ _ _ _ _ _ _ HPRE) R10 R9 Hn Hp0 Hp1 Ham Hra Hhv).
Qed.
End c.
End b.
