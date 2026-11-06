(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_set's image-A' walk (fuzz_preset asan), THE INSTANCE of the MARKED shadow-visibility
   kit facts lib/A/Prog/pj_setA_defs.v pjsA_g_vis, at the A' allocator instance of lib/A/PALibA.v:
   cp := CfParamsPreset.CfParams_preset, B := AD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB.
   - conjunct 1 (ARx_frame_hull_vis): YGcfFsVis.v ARx_frame_hull_vis_cf_ok at YG0lawscf.v AR_laws_ok_cf.
   - conjunct 3 (the shadow map of [IMG_LO, IMG_TOP) is present): YImgShadowCoverCf.v img_shadow_vis_cf_at_of_cover at
     image A's generated lists (lib/A/AF0m.v Tfib_zero_shadow / Tfib_const_shadow), with the cover check
     pjsvA_img_cover (lib/A/AImgShadowVis.v tfib_img_shadow_cover, a vm_compute at image A) and the two inclusions
     from AD2l.v TfibB_syms (AF0m.v TfibSyms ts_zsh / ts_const).
   - conjunct 2 (a range inside one registered zero-shadow range is addressable and its shadow hull is present): ARcf's
     zero-shadow field (YG0ncf.v amc_zshadow, read by YImgShadowCover.v shv_zshadow_ok_in) gives the shadow bytes 0 of
     the range's granules; the range witness pjsvA_zs_geom (vm_compute: every range of Tfib_zero_shadow is 8-aligned in
     base and length and lies in [IMG_LO, IMG_TOP)) makes every granule of [a, a + n) one of them; the bounds witness
     pjsvA_img_al (vm_compute: IMG_LO and IMG_TOP are 64-aligned) keeps the 64-byte hull inside the image, whose shadow
     conjunct 3 gives.
   proves no function (kind: instance facts). No ADDRESS numeral in the proofs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfFsVis YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AD2l AImgShadowVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import pj_setA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ================================================================ THE INSTANCE WITNESSES (vm_compute at image A') *)
(* WITNESS 1, the cover check: every 8-byte granule of [IMG_LO, IMG_TOP) has its shadow byte inside the shadow of one
   range of image A's zero-shadow list or at a byte of one of image A's const shadow cells (YImgShadowCover.v
   img_shadow_cover over the lists of lib/A/AF0m.v, which AD2l.v TfibB reads): AImgShadowVis.v's vm_compute. *)
Lemma pjsvA_img_cover :
  img_shadow_cover AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow YImgTop.IMG_LO YImgTop.IMG_TOP = true.
Proof. exact AImgShadowVis.tfib_img_shadow_cover. Qed.

(* WITNESS 2, the range check: every range (q, m) of image A's zero-shadow list has q and m multiples of 8 and lies
   in [IMG_LO, IMG_TOP). *)
Definition pjsvA_zs_ok (r : Z * Z) : bool :=
  ((fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (YImgTop.IMG_LO <=? fst r) && (fst r + snd r <=? YImgTop.IMG_TOP))%bool.
Lemma pjsvA_zs_geom : forallb pjsvA_zs_ok AF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

(* WITNESS 3, the bounds check: both image bounds are multiples of 64 (one shadow granule of 8 shadow bytes). *)
Lemma pjsvA_img_al : YImgTop.IMG_LO mod 64 = 0 /\ YImgTop.IMG_TOP mod 64 = 0.
Proof. split; vm_compute; reflexivity. Qed.

(* the two list inclusions at the real binding, from AD2l.v TfibB_syms (AF0m.v TfibSyms ts_zsh / ts_const) *)
Lemma pjsvA_zs_incl : incl AF0m.Tfib_zero_shadow (as_zero_shadow AD2l.TfibB).
Proof. rewrite (AF0m.ts_zsh AD2l.TfibB AD2l.TfibB_syms). apply incl_refl. Qed.
Lemma pjsvA_cs_incl : forall ly, incl AF0m.Tfib_const_shadow (as_const AD2l.TfibB ly).
Proof.
intros ly. rewrite (AF0m.ts_const AD2l.TfibB AD2l.TfibB_syms ly). unfold AF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

(* witness 2 read at a range of TfibB's zero-shadow list *)
Lemma pjsvA_zs_in : forall q m, In (q, m) (as_zero_shadow AD2l.TfibB) ->
  q mod 8 = 0 /\ m mod 8 = 0 /\ YImgTop.IMG_LO <= q /\ q + m <= YImgTop.IMG_TOP.
Proof.
intros q m Hin. rewrite (AF0m.ts_zsh AD2l.TfibB AD2l.TfibB_syms) in Hin.
pose proof (proj1 (forallb_forall _ _) pjsvA_zs_geom (q, m) Hin) as Hb. unfold pjsvA_zs_ok in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
repeat split; assumption.
Qed.

(* ================================================================ ARITHMETIC (no image fact) *)
(* a byte of [a, a + n) inside an 8-aligned range (q, m) has its granule among the range's m / 8 granules *)
Lemma pjsvA_ra_arith : forall q m a n x, q mod 8 = 0 -> m mod 8 = 0 -> q <= a -> a + n <= q + m ->
  a <= x < a + n -> 0 <= x / 8 - q / 8 < m / 8.
Proof. intros q m a n x Hq Hm H1 H2 Hx. Z.div_mod_to_equations. lia. Qed.

(* the shadow hull of [a, a + n) inside [L, H) with L, H multiples of 64: each byte s of the hull is the shadow byte
   of the address (s - SHADOW_OFF) * 8, which lies in [L, H) *)
Lemma pjsvA_hull_arith : forall L H a n s, L mod 64 = 0 -> H mod 64 = 0 -> L <= a -> a + n <= H -> 0 < n ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  L <= (s - SHADOW_OFF) * 8 < H /\ shadow_addr ((s - SHADOW_OFF) * 8) = s.
Proof. intros L H a n s HL HH H1 H2 Hn Hs. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.

(* ================================================================ THE INSTANCE *)
Section inst. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (rc := rc) (cp := CP) rsegs TB).

(* conjunct 3: the shadow map of [IMG_LO, IMG_TOP) at every ARcf state (witness 1 and the two inclusions) *)
Lemma pjsvA_img_vis : forall ly S Hp (W : world rsegs) mem md a, ARI ly S Hp W mem md ->
  YImgTop.IMG_LO <= a < YImgTop.IMG_TOP -> aview rsegs (w_H W) mem (shadow_addr a) <> None.
Proof.
exact (img_shadow_vis_cf_at_of_cover (rc := rc) (cp := CP) rsegs TB AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow
  YImgTop.IMG_LO YImgTop.IMG_TOP pjsvA_img_cover pjsvA_zs_incl pjsvA_cs_incl).
Qed.

(* conjunct 2: a range inside one registered zero-shadow range (in_zs) is addressable (ARcf's amc_zshadow gives its
   granules' shadow bytes 0, witness 2 makes every granule one of them) and its shadow hull is present (witness 2 and
   witness 3 keep the hull inside the image, conjunct 3) *)
Lemma pjsvA_zs_vis : forall ly S Hp (W : world rsegs) mem md a n, ARI ly S Hp W mem md -> in_zs TB a n -> 0 < n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md a n HA (q & m & Hin & Hq & Hqm) Hn.
destruct (pjsvA_zs_in q m Hin) as (G1 & G2 & G3 & G4).
pose proof HA as (M & _).
pose proof (shv_zshadow_ok_in TB ly _ (q, m) (amc_zshadow _ _ _ _ _ M) Hin) as Z0. cbn [fst snd] in Z0.
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  pose proof (Z0 (x / 8 - q / 8) (pjsvA_ra_arith q m a n x G1 G2 Hq Hqm Hx)) as E. unfold shadow_of_addr in E |- *.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + q / 8 + (x / 8 - q / 8)) by ring. exact E.
- intros s Hs. destruct pjsvA_img_al as [AL AH].
  destruct (pjsvA_hull_arith YImgTop.IMG_LO YImgTop.IMG_TOP a n s AL AH ltac:(lia) ltac:(lia) Hn Hs) as [Hy Es].
  rewrite <- Es. exact (pjsvA_img_vis ly S Hp W mem md _ HA Hy).
Qed.

(* THE INSTANCE: pj_setA_defs.v pjsA_g_vis at rc, B := TfibB, ARx := ARcf rsegs TfibB at CfParams_preset *)
Theorem pjsA_g_vis_preset :
  pjsA_g_vis (rc := rc) AD2l.TfibB (YG0ncf.ARcf (rc := rc) (cp := CfParamsPreset.CfParams_preset) rsegs AD2l.TfibB).
Proof.
unfold pjsA_g_vis. split; [|split].
- exact (ARx_frame_hull_vis_cf_ok (rc := rc) (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (rc := rc) (cp := CP) rsegs TB)).
- exact pjsvA_zs_vis.
- exact pjsvA_img_vis.
Qed.
End inst.
