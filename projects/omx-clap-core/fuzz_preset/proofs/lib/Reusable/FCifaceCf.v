(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area interface (FCiface.v) at the second allocator instance, image-free.
   fs_iface_ARcf: ARcf segs B (YG0ncf.v) satisfies fs_iface, given AR_laws_cf segs B (YG0dcf.v). ARcf takes its
   arguments in ARx's order (ly S Hp W mem md after segs B), so ARx := ARcf segs B with no wrapper.
   Each field is a projection, as in cgif's fs_iface_AR (FCiface.v:173):
   - fi_hints, fi_layout, fi_tsd, fi_const, fi_flags: ARmcf's amc_wf (Wf_cf's wfc_fakestack), amc_layout, amc_tsd,
     amc_const, amc_flags (YG0ncf.v:89-116);
   - fi_fs_cells: amc_cells, fs_cells S being the sixth block of acells_cf (YG0ncf.v:50-53);
   - fi_area_F, fi_area_Fsh: amc_areas, the two frame-area items of aareas (YG0n.v:137-139);
   - fi_img: ALedger_cf's alc_img (YG0ncf.v:228);
   - fi_own_F_low: YG0qcf.own_F_low_cf;
   - fi_own_free_frame, fi_own_free_frame_shadow: YF0v.v:37 and :64 have no cf twin, so their two proofs are
     ported below to ARmcf (own_free_frame_cf, own_free_frame_shadow_cf, local), with cgif's ARm lemmas replaced
     by their YG0scf / YG0qcf twins of the same statement (chunk_facts_cf, user_in_extent_cf, chunk_vs_F_cf,
     frame_facts_cf);
   - fi_malloc_law: YG0tcf.astack_malloc_law_ok_cf (its statement astack_malloc_law_cf, YG0dcf.v:244, is
     FCiface's astack_malloc_law_x at ARx := ARcf segs B, by conversion);
   - fi_stack, fi_frame, fi_frames: AR_laws_cf's alc_stack, alc_frame, alc_frames.
   No address and no image numeral appears in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0s YG0q YF0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section p.
Variable B : asyms.
(* YF0v.v:37-63 with ARm B ly S rd -> ARmcf B ly S Hp rd. *)
Local Lemma own_free_frame_cf : forall ly S Hp rd cid pos a, ARmcf B ly S Hp rd -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> aowned B ly S a.
Proof.
intros ly S Hp rd cid pos a M Hc Hp0 NIN Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FA. cbn [fst snd] in FA.
pose proof FA as [F1 F2].
pose proof (frame_off_bounds cid pos Hc Hp0) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof Ha as Ha0. unfold frame_addr in Ha.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
split.
- right. left. apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto|].
unfold in_zr, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd]. lia.
- intros [(k & Hk & Hst & Hr) | (cp' & Hcp & [Hr|Hr])].
+ pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & _ & _ & _ & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
pose proof (user_in_extent_cf B ly S Hp rd k a M Hk Hr) as HE. pose proof (chunk_vs_F_cf B ly S Hp rd k M Hk) as D.
unfold zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in D. lia.
+ destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd c2 p2 M Hcp) as (C1 & C2 & _).
assert (NE : (c2, p2) <> (cid, pos)) by (intros E; rewrite E in Hcp; exact (NIN Hcp)).
pose proof (frames_apart c2 p2 cid pos C1 C2 Hc Hp0 NE) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
+ destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & P3 & P4 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
refine (app_vs_shadow (ly_F ly) kFakeStackSize (frame_addr ly c2 p2) (fs_frame_bytes c2) a FA _ ltac:(lia) _ Hr).
* apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia.
* unfold kFakeFramesOff, kFakeStackSize in *. lia.
Qed.

(* YF0v.v:64-121 with ARm B ly S rd -> ARmcf B ly S Hp rd. *)
Local Lemma own_free_frame_shadow_cf : forall ly S Hp rd cid pos a, ARmcf B ly S Hp rd -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 -> aowned B ly S a.
Proof.
intros ly S Hp rd cid pos a M Hc Hp0 NIN Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof ASAN_CEIL_range as [CR _].
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FA. cbn [fst snd] in FA.
pose proof FA as [F1 F2].
pose proof (frame_off_bounds cid pos Hc Hp0) as (A1 & A2 & A3 & A4 & A5 & A6).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
assert (FA8 : frame_addr ly cid pos mod 8 = 0).
{ unfold frame_addr. apply Z.mod_divide; [lia|]. apply Z.mod_divide in FAL as [q Hq]; [|lia]. apply Z.mod_divide in A3 as [q' Hq']; [|lia]. exists (q * 512 + q' * 8). lia. }
assert (FIN : in_app (frame_addr ly cid pos) (fs_frame_bytes cid)).
{ apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia. }
split.
- right. right. right. right. apply Exists_exists.
destruct F2 as [FLO|[FH1 FH2]].
+ exists lm_zone. split; [rewrite !in_app_iff; cbn; tauto|].
unfold in_zr, lm_zone. cbn [fst snd].
assert (D1 : 0 / 8 <= frame_addr ly cid pos / 8) by (apply Z.div_le_mono; [lia | unfold frame_addr, kFakeFramesOff in *; lia]).
assert (D2 : frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8 <= (snd lm_zone + 7) / 8).
{ apply Z.mod_divide in FA8 as [q Hq]; [|lia]. pose proof A5 as A5'. apply Z.mod_divide in A5' as [m Hm]; [|lia].
rewrite Hq, Hm. replace (m * 64) with ((m * 8) * 8) by lia. rewrite !Z.div_mul by lia.
apply Z.div_le_lower_bound; [lia|]. unfold lm_zone. cbn [snd]. unfold frame_addr, kFakeFramesOff, kLowShadowBeg, kLowMemEnd in *. lia. }
unfold shadow_addr in *. unfold lm_zone in D2. cbn [snd] in D2. lia.
+ exists hm_zone. split; [rewrite !in_app_iff; cbn; tauto|].
pose proof (shadow_range_below (frame_addr ly cid pos) (fs_frame_bytes cid) ltac:(unfold frame_addr, kHighMemBeg, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(unfold frame_addr, kHighMemEnd, kFakeFramesOff, kFakeStackSize in *; lia)) as SB.
assert (SLO : kHighShadowBeg <= shadow_addr (frame_addr ly cid pos)).
{ unfold shadow_addr. pose proof (Z.div_le_mono kHighMemBeg (frame_addr ly cid pos) 8 ltac:(lia) ltac:(unfold frame_addr, kHighMemBeg, kFakeFramesOff in *; lia)) as X.
unfold kHighShadowBeg, kHighMemBeg, SHADOW_OFF in *. change (17594333495296 / 8) with 2199291686912 in X. lia. }
unfold in_zr. cbn [fst snd]. rewrite (proj2 hm_zone_shadow), (proj1 hm_zone_shadow). unfold kHighShadowEnd. unfold kHighMemBeg in SB. lia.
- intros [(k & Hk & Hst & Hr) | (cp' & Hcp & [Hr|Hr])].
+
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
refine (app_vs_shadow (ck_base B ly k) (ck_extent k) (frame_addr ly cid pos) (fs_frame_bytes cid) a G1 FIN ltac:(lia) _ Ha).
unfold ck_n in Hr. lia.
+
destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
refine (app_vs_shadow (frame_addr ly c2 p2) (fs_frame_bytes c2) (frame_addr ly cid pos) (fs_frame_bytes cid) a _ FIN ltac:(lia) Hr Ha).
apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia.
+ destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf B ly S Hp rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & P3 & P4 & P5 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
assert (NE : (c2, p2) <> (cid, pos)) by (intros E; rewrite E in Hcp; exact (NIN Hcp)).
pose proof (frames_apart c2 p2 cid pos C1 C2 Hc Hp0 NE) as D.
assert (FA8' : frame_addr ly c2 p2 mod 8 = 0).
{ unfold frame_addr. apply Z.mod_divide; [lia|]. apply Z.mod_divide in FAL as [q Hq]; [|lia]. pose proof P3 as P3'. apply Z.mod_divide in P3' as [q' Hq']; [|lia]. exists (q * 512 + q' * 8). lia. }
assert (D' : zdisjoint (frame_addr ly c2 p2, fs_frame_bytes c2) (frame_addr ly cid pos, fs_frame_bytes cid)).
{ unfold zdisjoint, frame_addr in *. cbn [fst snd] in *. lia. }
pose proof (shadow_apart (frame_addr ly c2 p2) (fs_frame_bytes c2) (frame_addr ly cid pos) (fs_frame_bytes cid) ltac:(unfold frame_addr, kFakeFramesOff in *; lia) ltac:(unfold frame_addr, kFakeFramesOff in *; lia) FA8' FA8
ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in P5 as [q Hq]; [|lia]; exists (q * 8); lia)
ltac:(apply Z.mod_divide; [lia|]; pose proof A5 as A5'; apply Z.mod_divide in A5' as [q Hq]; [|lia]; exists (q * 8); lia)
ltac:(lia) ltac:(lia) D') as SD.
unfold zdisjoint in SD. cbn [fst snd] in SD. lia.
Qed.
End p.

Lemma fs_iface_ARcf : forall segs B, AR_laws_cf segs B -> fs_iface segs B (ARcf segs B).
Proof.
intros segs B LAWS. constructor; unfold ARcf.
- intros ly S Hp W mem md HAR. exact (wfs_hints _ (wfc_fakestack _ _ _ _ _ (amc_wf _ _ _ _ _ (proj1 HAR)))).
- intros ly S Hp W mem md HAR. exact (amc_layout _ _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md sg HAR Hsg. exact (alc_img _ _ _ _ (proj1 (proj2 HAR)) sg Hsg).
- intros ly S Hp W mem md HAR. exact (amc_tsd _ _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. exact (amc_const _ _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. apply Forall_forall. intros c Hc.
apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ (proj1 HAR))).
unfold acells_cf. rewrite !in_app_iff. right; right; right; right; right; left. exact Hc.
- intros ly S Hp W mem md HAR. exact (amc_flags _ _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. apply (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ (proj1 HAR))).
unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- intros ly S Hp W mem md HAR. apply (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ (proj1 HAR))).
unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- intros ly S Hp W mem md cid pos a HAR. exact (own_free_frame_cf B ly S Hp _ cid pos a (proj1 HAR)).
- intros ly S Hp W mem md cid pos a HAR. exact (own_free_frame_shadow_cf B ly S Hp _ cid pos a (proj1 HAR)).
- intros ly S Hp W mem md a HAR. exact (own_F_low_cf B ly S Hp _ a (proj1 HAR)).
- exact (astack_malloc_law_ok_cf segs B).
- exact (alc_stack _ _ LAWS).
- exact (alc_frame _ _ LAWS).
- exact (alc_frames _ _ LAWS).
Qed.

End a.
