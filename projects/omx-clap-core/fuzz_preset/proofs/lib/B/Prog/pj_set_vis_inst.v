(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_set's image-B walk (fuzz_preset asan-ubsan), THE INSTANCE of the MARKED shadow-visibility
   kit facts lib/B/Prog/pj_set_defs.v pjs_g_vis, at the instance lib/B/Prog/pj_free_top.v Section inst uses:
   cp := CfParamsPreset.CfParams_preset, B := YD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB.
   - conjunct 1 (ARx_frame_hull_vis): YGcfFsVis.v ARx_frame_hull_vis_cf_ok at YG0lawscf.v AR_laws_ok_cf.
   - conjunct 3 (the shadow map of [IMG_LO_B, IMG_TOP_B) is present): YImgShadowCoverCf.v img_shadow_vis_cf_at_of_cover at
     image B's generated lists (lib/Reusable/YF0m.v Tfib_zero_shadow / Tfib_const_shadow), with the cover check
     pjsv_img_cover (vm_compute) and the two inclusions from YD2l.v TfibB_syms (YF0m.v TfibSyms ts_zsh / ts_const).
   - conjunct 2 (a range inside one registered zero-shadow range is addressable and its shadow hull is present): ARcf's
     zero-shadow field (YG0ncf.v amc_zshadow, read by YImgShadowCover.v shv_zshadow_ok_in) gives the shadow bytes 0 of
     the range's granules; the range witness pjsv_zs_geom (vm_compute: every range of Tfib_zero_shadow is 8-aligned in
     base and length and lies in [IMG_LO_B, IMG_TOP_B)) makes every granule of [a, a + n) one of them; the bounds witness
     pjsv_img_al (vm_compute: IMG_LO_B and IMG_TOP_B are 64-aligned) keeps the 64-byte hull inside the image, whose shadow
     conjunct 3 gives.
   - pjs_hull_preset (pj_set_defs.v pjs_g_hull at CfParams_preset): preset's request bound 2 ^ 28 + 2 ^ 27 is at most
     2 ^ 30, and lib/A/PresetHullPay.v hull_budget_of_room_pos is the budget at a run position of at most 4 calls.
   proves no function (kind: instance facts). No ADDRESS numeral in the proofs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfFsVis YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ================================================================ THE INSTANCE WITNESSES (vm_compute at image B) *)
(* WITNESS 1, the cover check: every 8-byte granule of [IMG_LO_B, IMG_TOP_B) has its shadow byte inside the shadow of one
   range of image B's zero-shadow list or at a byte of one of image B's const shadow cells (YImgShadowCover.v
   img_shadow_cover; the lists of lib/Reusable/YF0m.v, the image-B binding YD2l.v TfibB reads). *)
Lemma pjsv_img_cover :
  img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow YImgTop.IMG_LO_B YImgTop.IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

(* WITNESS 2, the range check: every range (q, m) of image B's zero-shadow list has q and m multiples of 8 and lies
   in [IMG_LO_B, IMG_TOP_B). *)
Definition pjsv_zs_ok (r : Z * Z) : bool :=
  ((fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (YImgTop.IMG_LO_B <=? fst r) && (fst r + snd r <=? YImgTop.IMG_TOP_B))%bool.
Lemma pjsv_zs_geom : forallb pjsv_zs_ok YF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

(* WITNESS 3, the bounds check: both image bounds are multiples of 64 (one shadow granule of 8 shadow bytes). *)
Lemma pjsv_img_al : YImgTop.IMG_LO_B mod 64 = 0 /\ YImgTop.IMG_TOP_B mod 64 = 0.
Proof. split; vm_compute; reflexivity. Qed.

(* the two list inclusions at the real binding, from YD2l.v TfibB_syms (YF0m.v TfibSyms ts_zsh / ts_const) *)
Lemma pjsv_zs_incl : incl YF0m.Tfib_zero_shadow (as_zero_shadow YD2l.TfibB).
Proof. rewrite (YF0m.ts_zsh YD2l.TfibB YD2l.TfibB_syms). apply incl_refl. Qed.
Lemma pjsv_cs_incl : forall ly, incl YF0m.Tfib_const_shadow (as_const YD2l.TfibB ly).
Proof.
intros ly. rewrite (YF0m.ts_const YD2l.TfibB YD2l.TfibB_syms ly). unfold YF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

(* witness 2 read at a range of TfibB's zero-shadow list *)
Lemma pjsv_zs_in : forall q m, In (q, m) (as_zero_shadow YD2l.TfibB) ->
  q mod 8 = 0 /\ m mod 8 = 0 /\ YImgTop.IMG_LO_B <= q /\ q + m <= YImgTop.IMG_TOP_B.
Proof.
intros q m Hin. rewrite (YF0m.ts_zsh YD2l.TfibB YD2l.TfibB_syms) in Hin.
pose proof (proj1 (forallb_forall _ _) pjsv_zs_geom (q, m) Hin) as Hb. unfold pjsv_zs_ok in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
repeat split; assumption.
Qed.

(* ================================================================ ARITHMETIC (no image fact) *)
(* a byte of [a, a + n) inside an 8-aligned range (q, m) has its granule among the range's m / 8 granules *)
Lemma pjsv_ra_arith : forall q m a n x, q mod 8 = 0 -> m mod 8 = 0 -> q <= a -> a + n <= q + m ->
  a <= x < a + n -> 0 <= x / 8 - q / 8 < m / 8.
Proof. intros q m a n x Hq Hm H1 H2 Hx. Z.div_mod_to_equations. lia. Qed.

(* the shadow hull of [a, a + n) inside [L, H) with L, H multiples of 64: each byte s of the hull is the shadow byte
   of the address (s - SHADOW_OFF) * 8, which lies in [L, H) *)
Lemma pjsv_hull_arith : forall L H a n s, L mod 64 = 0 -> H mod 64 = 0 -> L <= a -> a + n <= H -> 0 < n ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  L <= (s - SHADOW_OFF) * 8 < H /\ shadow_addr ((s - SHADOW_OFF) * 8) = s.
Proof. intros L H a n s HL HH H1 H2 Hn Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.

(* ================================================================ THE INSTANCE *)
Section inst. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (rc := rc) (cp := CP) rsegs TB).

(* conjunct 3: the shadow map of [IMG_LO_B, IMG_TOP_B) at every ARcf state (witness 1 and the two inclusions) *)
Lemma pjsv_img_vis : forall ly S Hp (W : world rsegs) mem md a, ARI ly S Hp W mem md ->
  YImgTop.IMG_LO_B <= a < YImgTop.IMG_TOP_B -> aview rsegs (w_H W) mem (shadow_addr a) <> None.
Proof.
exact (img_shadow_vis_cf_at_of_cover (rc := rc) (cp := CP) rsegs TB YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
  YImgTop.IMG_LO_B YImgTop.IMG_TOP_B pjsv_img_cover pjsv_zs_incl pjsv_cs_incl).
Qed.

(* conjunct 2: a range inside one registered zero-shadow range (in_zs) is addressable (ARcf's amc_zshadow gives its
   granules' shadow bytes 0, witness 2 makes every granule one of them) and its shadow hull is present (witness 2 and
   witness 3 keep the hull inside the image, conjunct 3) *)
Lemma pjsv_zs_vis : forall ly S Hp (W : world rsegs) mem md a n, ARI ly S Hp W mem md -> in_zs TB a n -> 0 < n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md a n HA (q & m & Hin & Hq & Hqm) Hn.
destruct (pjsv_zs_in q m Hin) as (G1 & G2 & G3 & G4).
pose proof HA as (M & _).
pose proof (shv_zshadow_ok_in TB ly _ (q, m) (amc_zshadow _ _ _ _ _ M) Hin) as Z0. cbn [fst snd] in Z0.
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  pose proof (Z0 (x / 8 - q / 8) (pjsv_ra_arith q m a n x G1 G2 Hq Hqm Hx)) as E. unfold shadow_of_addr in E |- *.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + q / 8 + (x / 8 - q / 8)) by ring. exact E.
- intros s Hs. destruct pjsv_img_al as [AL AH].
  destruct (pjsv_hull_arith YImgTop.IMG_LO_B YImgTop.IMG_TOP_B a n s AL AH ltac:(lia) ltac:(lia) Hn Hs) as [Hy Es].
  rewrite <- Es. exact (pjsv_img_vis ly S Hp W mem md _ HA Hy).
Qed.

(* THE INSTANCE: pj_set_defs.v pjs_g_vis at rc, B := TfibB, ARx := ARcf rsegs TfibB at CfParams_preset *)
Theorem pjs_g_vis_preset :
  pjs_g_vis (rc := rc) YD2l.TfibB (YG0ncf.ARcf (rc := rc) (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB).
Proof.
unfold pjs_g_vis. split; [|split].
- exact (ARx_frame_hull_vis_cf_ok (rc := rc) (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (rc := rc) (cp := CP) rsegs TB)).
- exact pjsv_zs_vis.
- exact pjsv_img_vis.
Qed.
End inst.

(* THE HULL BUDGET AT A RUN POSITION at preset's CfParams (pj_set_defs.v pjs_g_hull) *)
Theorem pjs_hull_preset : @pjs_g_hull CfParamsPreset.CfParams_preset.
Proof.
split; [cbn [cf_malloc_max CfParamsPreset.CfParams_preset]; lia|].
exact PresetHullPay.hull_budget_of_room_pos.
Qed.
