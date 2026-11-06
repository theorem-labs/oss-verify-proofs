(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfExtra.v, sha256 e497e670cc4065d2a4a55c559f9422ecdd984a4cbef477ae7361a22aa2353e24.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib (and, at line 126, a blob id re-cited by file sha256). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the walk kit's extra-area law at
   the cf walk relation ARcf /\ xs_placed_cf.
   ARx_extra_law below is the walk kit's ARx_extra_law (proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqG.v:80-87
   at b092d73a858), its body copied verbatim; the parameters are the Section variables that body uses, in their
   declaration order (segs B ARx), the order Coq gives YCbqG.ARx_extra_law when its section closes. This file does
   not Require the kit.
   It is not the kit's ARx_xs_law (YGcallx.v:221-226 at f3963d079661): ARx_xs_law speaks of an address in the
   error-buffer extent XS (a < alloc_ceiling, app_addr, outside the image, the blocks, the frames and ly_extra);
   ARx_extra_law speaks of an address in ly_extra (not owned, outside the blocks, the frames and their shadow, the
   stack, the image and the shadow range, app_addr).
   ARx_extra_law_ok_ARcf: the law at ARcf ALONE. The proof is cgif's AR_extra_law_ok (YG0p.v:39) over ARcf, as
   c-omx-alloc's YGcallcf.v:132-189 at f3963d079661 ports it: ARm -> ARmcf, ALedger -> ALedger_cf, chunk_facts /
   frame_facts / owned_shadow_bound / extent_zone -> their _cf forms (YG0scf.v, YG0qcf.v); the frame-shadow bound
   is YG0s.shadow_addr_bounds, so no derived shadow numeral is written. xs_placed_cf is not needed: aowned is
   cgif's (YG0n.v:236-242), which does not name the error-buffer extent.
   ARx_extra_law_ok_cf: the law at the walk relation ARcf /\ xs_placed_cf, from the ARcf form. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d YG0s YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section E. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------- *)
(* 1. The kit's ARx_extra_law (YCbqG.v:80-87 at b092d73a858), body verbatim.    *)
Section x.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition ARx_extra_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md -> Exists (in_zr a) (ly_extra ly) ->
~ aowned B ly S a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames S) ->
~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8)) /\
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_img segs a /\ ~ (SHADOW_OFF <= a < kHighShadowEnd) /\ app_addr a.
End x.

Section J. Context {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* 2. The law at ARcf alone.                                                      *)
Theorem ARx_extra_law_ok_ARcf : ARx_extra_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof.
intros ly S Hp W mem md a HAR HX. pose proof HAR as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LO. apply Exists_exists in HX as (e & He & Ha).
pose proof (extra_entry ly e a LO He Ha) as (APP & NSH & DZ). unfold in_zr in Ha.
assert (ST : forall z, In z (owned_extents ly) \/ z = (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) \/ z = ly_img ly ->
~ (fst z <= a < fst z + snd z)).
{ intros z Hz Hin. assert (Hs : In z (static_extents ly)).
  { unfold static_extents. apply in_app_iff.
    destruct Hz as [Hz|[->| ->]]; [left; exact Hz | right; left; reflexivity | right; right; left; reflexivity]. }
  pose proof (DZ z Hs) as D. unfold zdisjoint in D. lia. }
assert (SX : forall m len, In (m, len) (sec_extents ly S) -> ~ (m <= a < m + len)).
{ intros m len Hin Hr.
  pose proof (alc_secx _ _ _ _ L (m, len) e Hin ltac:(unfold perm_maps; apply in_app_iff; right; exact He)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (NB : forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
{ intros p n Hin Hr. apply (In_ablocks B) in Hin as (k & Hk & Hst & Hu & Hn). subst p n.
  pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  assert (HE : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by (rewrite G4 in Hr; lia).
  destruct (extent_zone_cf B ly S Hp _ k M Hk) as [[P1 P2] | (m & len & Hin & Hm & Hl)].
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
{ intros cid pos Hf.
  pose proof (frame_facts_cf B ly S Hp _ cid pos M Hf) as (C1 & C2 & F1 & F2 & F3 & P1 & P2 & M1 & M2 & M3 & _).
  pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CNN. unfold in_app, kFakeFramesOff in *.
  pose proof (@ASAN_CEIL_range rc) as [CR1 CR2]. unfold ASAN_CEIL in *.
  split.
  - intros Hr. apply (ST (ly_F ly, kFakeStackSize)); [left; unfold owned_extents; cbn; tauto | cbn [fst snd]].
    unfold frame_addr in *. lia.
  - intros Hr. apply NSH. unfold frame_addr in Hr.
    pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB1 _].
    pose proof (SRE (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(lia)) as SB2.
    assert (HH : ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid + 7 <= kHighMemEnd).
    { unfold kHighMemEnd, kLowShadowBeg, kHighMemBeg in *. lia. }
    pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid) ltac:(lia)) as [_ SB3].
    specialize (SB3 HH).
    unfold SHADOW_OFF, kHighShadowEnd, kHighMemBeg in *. lia. }
split; [|split; [exact NB | split; [exact NF | split; [| split; [| split; [exact NSH | exact APP]]]]]].
- intros [[O|[O|[O|[O|O]]]] _].
  + apply Exists_exists in O as (z & Hz & [Hr1 Hr2]).
    pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) z ltac:(apply in_app_iff; left; exact Hz)) as [S1 S2].
    apply (ST (ly_img ly)); [right; right; reflexivity | lia].
  + apply Exists_exists in O as (z & Hz & Hr). exact (ST z (or_introl Hz) Hr).
  + apply (ST (ly_C ly, 256)); [left; unfold owned_extents; cbn; tauto | exact O].
  + apply Exists_exists in O as ([m len] & Hz & Hr). exact (SX m len Hz Hr).
  + pose proof (owned_shadow_bound_cf B ly S Hp _ a M O). unfold SHADOW_OFF, kHighShadowEnd, kHighMemBeg in *. lia.
- intros Hr. apply (ST (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)); [right; left; reflexivity | cbn [fst snd]; lia].
- intros (sg & Hsg & Hr). pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2].
  apply (ST (ly_img ly)); [right; right; reflexivity | unfold in_zr in *; lia].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The law at the walk relation ARcf /\ xs_placed_cf.                          *)
Theorem ARx_extra_law_ok_cf :
ARx_extra_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Proof. intros ly S Hp W mem md a [H _]. exact (ARx_extra_law_ok_ARcf ly S Hp W mem md a H). Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The kit's AR_laws_x field 16, ARx_const_cells_law (YCbqG.v sha256 6fb5b8d6f2a9; internal record), at ARcf: a PROJECTION of   *)
(*    ARmcf's verbatim field amc_const (YG0ncf.v:219). ARcf's first conjunct is ARmcf over exactly            *)
(*    rd := aview segs (w_H W) mem (YG0ncf.v:610-612), the view the law names, so nothing is converted.      *)
(*    Stated without Requiring the kit: our tree's YCbqG.v is the older 754-line version.                   *)
Theorem ARcf_const_cells_cf : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Proof. intros ly S Hp W mem md HAR. exact (amc_const _ _ _ _ _ (proj1 HAR)). Qed.

End J.
End E.
