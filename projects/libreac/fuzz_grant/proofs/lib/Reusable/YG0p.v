(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0p.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition AR_extra_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> Exists (in_zr a) (ly_extra ly) ->
~ aowned B ly S a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames S) ->
~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8)) /\
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_img segs a /\ ~ (SHADOW_OFF <= a < kHighShadowEnd) /\ app_addr a.
Lemma extra_entry : forall ly e a, layout_ok ly -> In e (ly_extra ly) -> in_zr a e ->
app_addr a /\ ~ (SHADOW_OFF <= a < kHighShadowEnd) /\
(forall z, In z (static_extents ly) -> zdisjoint e z).
Proof.
intros ly e a LO He Ha. pose proof (lo_extra _ LO) as (_ & HF & PD).
pose proof (proj1 (Forall_forall _ _) HF e He) as (E1 & E2 & E3 & E4 & E5). unfold in_zr in Ha.
split; [|split].
- unfold app_addr. pose proof (@ASAN_CEIL_range rc) as [CR _]. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *. pose proof (@ASAN_CEIL_range rc) as [CR _]. unfold ASAN_CEIL in *. lia.
- intros z Hz. exact (pairwise_In zdisjoint _ e z (ly_extra ly) (static_extents ly) eq_refl PD He Hz).
Qed.
Theorem AR_extra_law_ok : AR_extra_law.
Proof.
intros ly S W mem md a HAR HX. pose proof HAR as (M & L & _).
pose proof (am_layout _ _ _ _ M) as LO. apply Exists_exists in HX as (e & He & Ha).
pose proof (extra_entry ly e a LO He Ha) as (APP & NSH & DZ). unfold in_zr in Ha.
assert (ST : forall z, In z (owned_extents ly) \/ z = (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) \/ z = ly_img ly ->
~ (fst z <= a < fst z + snd z)).
{ intros z Hz Hin. assert (Hs : In z (static_extents ly)).
{ unfold static_extents. apply in_app_iff. destruct Hz as [Hz|[->| ->]]; [left; exact Hz | right; left; reflexivity | right; right; left; reflexivity]. }
pose proof (DZ z Hs) as D. unfold zdisjoint in D. lia. }
assert (SX : forall m len, In (m, len) (sec_extents ly S) -> ~ (m <= a < m + len)).
{ intros m len Hin Hr. pose proof (al_secx _ _ _ _ L (m, len) e Hin ltac:(unfold perm_maps; apply in_app_iff; right; exact He)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (NB : forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
{ intros p n Hin Hr. apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn). subst p n.
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (HE : ck_base B ly k <= a < ck_base B ly k + ck_extent k).
{ eapply (user_in_extent B ly S _ k a M Hk). rewrite G4 in Hr. unfold ck_n in Hr. lia. }
destruct (extent_zone B ly S _ k M Hk) as [[P1 P2] | (m & len & Hin & Hm & Hl)].
- apply (ST (ly_prim ly, kPrimResvSize)); [left; unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (SX m len Hin). unfold kPage in *. lia. }
assert (SRE : forall f n, 0 <= n -> shadow_addr f + n / 8 <= shadow_addr (f + n)).
{ intros f n Hn. unfold shadow_addr.
pose proof (Z.div_mod f 8 ltac:(lia)). pose proof (Z.mod_pos_bound f 8 ltac:(lia)).
pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
assert (f / 8 + n / 8 <= (f + n) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (NF : forall cid pos, In (cid, pos) (frames S) ->
~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8)).
{ intros cid pos Hf. pose proof (frame_facts B ly S _ cid pos M Hf) as (C1 & C2 & F1 & F2 & F3 & P1 & P2 & M1 & M2 & M3 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CNN. unfold in_app, kFakeFramesOff in *.
pose proof (@ASAN_CEIL_range rc) as [CR1 CR2]. unfold ASAN_CEIL in *.
split.
- intros Hr. apply (ST (ly_F ly, kFakeStackSize)); [left; unfold owned_extents; cbn; tauto | cbn [fst snd]].
unfold frame_addr in *. lia.
- intros Hr. apply NSH. unfold frame_addr in Hr.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB1 _].
pose proof (SRE (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(lia)) as SB2.
assert (HH : ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid <= kHighMemEnd).
{ unfold kHighMemEnd, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (SB3 : shadow_addr (ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid) <= kHighShadowEnd).
{ unfold shadow_addr, SHADOW_OFF, kHighShadowEnd, kHighMemEnd in *.
assert ((ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid) / 8 <= 140737488355328 / 8) by (apply Z.div_le_mono; lia).
change (140737488355328 / 8) with 17592186044416 in H. lia. }
unfold SHADOW_OFF, kHighShadowEnd in *. lia. }
split; [|split; [exact NB | split; [exact NF | split; [| split; [| split; [exact NSH | exact APP]]]]]].
-
intros [[O|[O|[O|[O|O]]]] _].
+ apply Exists_exists in O as (z & Hz & [Hr1 Hr2]).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) z ltac:(apply in_app_iff; left; exact Hz)) as [S1 S2].
apply (ST (ly_img ly)); [right; right; reflexivity | lia].
+ apply Exists_exists in O as (z & Hz & Hr). exact (ST z (or_introl Hz) Hr).
+ apply (ST (ly_C ly, 256)); [left; unfold owned_extents; cbn; tauto | exact O].
+ apply Exists_exists in O as ([m len] & Hz & Hr). exact (SX m len Hz Hr).
+ pose proof (owned_shadow_bound B ly S _ a M O). unfold SHADOW_OFF, kHighShadowEnd, kHighMemBeg in *. lia.
- intros Hr. apply (ST (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)); [right; left; reflexivity | cbn [fst snd]; lia].
- intros (sg & Hsg & Hr). pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2].
apply (ST (ly_img ly)); [right; right; reflexivity | unfold in_zr in *; lia].
Qed.
End c.
End b.
