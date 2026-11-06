(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: module names for libreac/fuzz_grant. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Lemma shadow_apart : forall x1 n1 x2 n2, 0 <= x1 -> 0 <= x2 -> x1 mod 8 = 0 -> x2 mod 8 = 0 -> n1 mod 8 = 0 -> n2 mod 8 = 0 -> 0 <= n1 -> 0 <= n2 ->
zdisjoint (x1, n1) (x2, n2) -> zdisjoint (shadow_addr x1, n1 / 8) (shadow_addr x2, n2 / 8).
Proof.
intros x1 n1 x2 n2 P1 P2 A1 A2 B1 B2 N1 N2 D. unfold zdisjoint, shadow_addr in *. cbn [fst snd] in *.
apply Z.mod_divide in A1 as [q1 ->]; [|lia]. apply Z.mod_divide in A2 as [q2 ->]; [|lia].
apply Z.mod_divide in B1 as [m1 ->]; [|lia]. apply Z.mod_divide in B2 as [m2 ->]; [|lia].
rewrite !Z.div_mul by lia. nia.
Qed.
Lemma app_vs_shadow : forall x n y m a, in_app x n -> in_app y m -> 0 <= m -> x <= a < x + n ->
~ (shadow_addr y <= a < shadow_addr y + m / 8).
Proof.
intros x n y m a [X0 XZ] [Y0 YZ] Hm Ha Hs. pose proof ASAN_CEIL_range as [CR _].
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)) as D0.
pose proof (shadow_range_below y m ltac:(lia) Hm ltac:(unfold kHighMemEnd, kLowShadowBeg in *; lia)) as SB.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma own_free_frame : forall ly S rd cid pos a, ARm B ly S rd -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> aowned B ly S a.
Proof.
intros ly S rd cid pos a M Hc Hp NIN Ha. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FA. cbn [fst snd] in FA.
pose proof FA as [F1 F2].
pose proof (frame_off_bounds cid pos Hc Hp) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof Ha as Ha0. unfold frame_addr in Ha.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
split.
- right. left. apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto|].
unfold in_zr, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd]. lia.
- intros [(k & Hk & Hst & Hr) | (cp & Hcp & [Hr|Hr])].
+ pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & G4 & _ & _ & _ & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
pose proof (user_in_extent B ly S rd k a M Hk Hr) as HE. pose proof (chunk_vs_F B ly S rd k M Hk) as D.
unfold zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in D. lia.
+ destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd c2 p2 M Hcp) as (C1 & C2 & _).
assert (NE : (c2, p2) <> (cid, pos)) by (intros E; rewrite E in Hcp; exact (NIN Hcp)).
pose proof (frames_apart c2 p2 cid pos C1 C2 Hc Hp NE) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
+ destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & P3 & P4 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
refine (app_vs_shadow (ly_F ly) kFakeStackSize (frame_addr ly c2 p2) (fs_frame_bytes c2) a FA _ ltac:(lia) _ Hr).
* apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia.
* unfold kFakeFramesOff, kFakeStackSize in *. lia.
Qed.
Lemma own_free_frame_shadow : forall ly S rd cid pos a, ARm B ly S rd -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ In (cid, pos) (frames S) ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 -> aowned B ly S a.
Proof.
intros ly S rd cid pos a M Hc Hp NIN Ha. pose proof (am_layout _ _ _ _ M) as LO. pose proof ASAN_CEIL_range as [CR _].
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FA. cbn [fst snd] in FA.
pose proof FA as [F1 F2].
pose proof (frame_off_bounds cid pos Hc Hp) as (A1 & A2 & A3 & A4 & A5 & A6).
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
- intros [(k & Hk & Hst & Hr) | (cp & Hcp & [Hr|Hr])].
+
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
refine (app_vs_shadow (ck_base B ly k) (ck_extent k) (frame_addr ly cid pos) (fs_frame_bytes cid) a G1 FIN ltac:(lia) _ Ha).
unfold ck_n in Hr. lia.
+
destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
refine (app_vs_shadow (frame_addr ly c2 p2) (fs_frame_bytes c2) (frame_addr ly cid pos) (fs_frame_bytes cid) a _ FIN ltac:(lia) Hr Ha).
apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | | lia |]; unfold frame_addr, kFakeFramesOff in *; lia.
+ destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd c2 p2 M Hcp) as (C1 & C2 & _ & _ & _ & P1 & P2 & P3 & P4 & P5 & _).
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)) as CN2.
assert (NE : (c2, p2) <> (cid, pos)) by (intros E; rewrite E in Hcp; exact (NIN Hcp)).
pose proof (frames_apart c2 p2 cid pos C1 C2 Hc Hp NE) as D.
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
End c.
End b.
