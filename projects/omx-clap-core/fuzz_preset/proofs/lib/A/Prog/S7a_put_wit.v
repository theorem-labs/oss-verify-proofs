(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the INSTANCE WITNESSES of put's image premises at image A' (the #102 asan pin 1be0f53d; unit
   ruling a Theorem Labs lane 16:45Z), self-contained (no walk file of another function in its Require closure). Instance: B :=
   AD2l.TfibB, PA := PI_prog_A (the A' listing v3: PAImg_prog.v blob 505a51ff7d08), PI := prh_img_A (PRH_Img.v blob
   934516a622e8, SEVEN static cells), cp := CfParams_preset, the segments lib/A/Img0.rsegs named FULLY QUALIFIED
   (RSEGS_A; the short name can resolve to the PLAIN image's lib/Img0.v, CrcBp's measurement) and tied to the walk's
   segments by s7p_segs_A (reflexivity). NO ADDRESS IS TYPED: A_OBJ 0 / 12 and the statics are read from the listing and
   from prh_img_A and checked by vm_compute. S7a_put.v's Section hypotheses and their witnesses:
   - Hent: A_entry_put (PAImg_prog.v), restated as s7p_ent_A.
   - Hobj: s7p_obj_A. The 8 bytes at A_OBJ 0 and at A_OBJ 12 lie in segments of RSEGS_A (vm_compute).
   - HPST: s7p_pst_A. Every static of prh_img_A lies in a segment of RSEGS_A (vm_compute over prh_pst).
   - HPSTRO: s7p_pstro_A. The statics lie outside both read-only segments and outside the relro range (vm_compute over
     prh_pst; S7a_indent_wit.v's s7w_pstro_A states the same at indent's walk).
   - HZSA: s7p_zs_aligned_A. The image's zero-shadow ranges are granule-aligned (vm_compute over Tfib_zero_shadow).
   - HW (prh_head_wide): s7p_head_wide (cf_head CfParams_preset).
   - HPAB: s7p_pab_A. PI_prog_A's pa_lo / pa_hi are YImgTop's IMG_LO / IMG_TOP (vm_compute on the closed goal).
   Not image facts (callee texts or allocator-relation laws, discharged where the relation is fixed): HREAL
   (tfuzz_realloc_specX), AMC (aintrin_realizes_xm), HIMGSH (ARx_img_shadow_vis: at ARcf by AImgShadowVisCf, whose
   image content is AImgShadowVis.tfib_img_shadow_cover, vm_compute), HFRSH (ARx_frame_hull_vis, YGcfFsVis at ARcf).
   Every vm_compute here is on a closed goal.
   Numerals: 0, 12 (INDEX: the A_OBJ table), 8 (LENGTH: a word; head width bound). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S7a_put.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the A' segments, FULLY QUALIFIED (never the short name Img0.rsegs) *)
#[local] Notation RSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.

(* ---- closed facts ---- *)
Lemma s7p_ent_c : A_prog_sigma AS_put = A_prog_val A_TEXT + S7a_put.PUT_K.
Proof.
destruct A_entry_put as (E1 & E2). unfold S7a_put.PUT_K, S7a_put.PUT_SLOT. rewrite E1, E2. vm_compute. reflexivity.
Qed.

(* a segment holds the whole range [b, b + w) *)
Definition s7p_rng_b (segs : list Segment) (r : Z * Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
    segs.
Lemma s7p_rng_b_sound : forall segs r, s7p_rng_b segs r = true -> forall a, fst r <= a < fst r + snd r ->
  exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros segs r H a Ha. apply existsb_exists in H as (sg & Hin & H). cbv beta in H.
apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
Qed.

Lemma s7p_obj_c : s7p_rng_b RSEGS_A (A_prog_val (A_OBJ 0), 8) = true /\
  s7p_rng_b RSEGS_A (A_prog_val (A_OBJ 12), 8) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7p_pst_c : forallb (s7p_rng_b RSEGS_A) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* the image's zero-shadow ranges are granule-aligned *)
Lemma s7p_zs_aligned_c : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s7p_zs_aligned_A : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow AD2l.TfibB).
Proof.
apply Forall_forall. intros r Hr. pose proof s7p_zs_aligned_c as H. rewrite forallb_forall in H.
specialize (H r Hr). apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
split; [exact H1 | exact H2].
Qed.

(* the statics against the read-only bytes: each one outside every read-only segment and outside the relro range *)
Definition s7p_pst_clear_b (segs : list Segment) (lo hi : Z) (l : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun sg => seg_writable sg || (fst r + snd r <=? Z.of_N (seg_base sg)) ||
                                       (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) segs &&
                    ((fst r + snd r <=? lo) || (hi <=? fst r))) l.
Lemma s7p_pst_clear_sound : forall segs lo hi l, s7p_pst_clear_b segs lo hi l = true ->
  forall a, in_roP segs lo hi a -> ~ Exists (in_zr a) l.
Proof.
intros segs lo hi l H a Hro HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
unfold s7p_pst_clear_b in H. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_true_iff in H as [Hs Hrel]. rewrite forallb_forall in Hs.
destruct Hro as [(sg & Hin & Hw & Hb) | Hb].
- specialize (Hs sg Hin). rewrite Hw in Hs. cbn [orb] in Hs.
  apply orb_true_iff in Hs as [H1 | H1]; apply Z.leb_le in H1; lia.
- apply orb_true_iff in Hrel as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.
Lemma s7p_pst_clear_c : s7p_pst_clear_b RSEGS_A A_prog_relro_lo A_prog_relro_hi (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- the witnesses ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).

(* THE GUARD: the segments every closed fact above is stated over are the walk's own (PI_prog_A's pa_segs) *)
Lemma s7p_segs_A : @pa_segs rc A_prog_listing PA = RSEGS_A.
Proof. reflexivity. Qed.

(* Hent *)
Lemma s7p_ent_A : @pa_sigma rc A_prog_listing PA AS_put = @pa_val rc A_prog_listing PA A_TEXT + S7a_put.PUT_K.
Proof. exact s7p_ent_c. Qed.

(* Hobj *)
Lemma s7p_obj_A : forall i, 0 <= i < 8 ->
  in_img SEGS (@pa_val rc A_prog_listing PA (A_OBJ 0) + i) /\ in_img SEGS (@pa_val rc A_prog_listing PA (A_OBJ 12) + i).
Proof.
intros i Hi. destruct s7p_obj_c as (O1 & O2). split.
- exact (s7p_rng_b_sound RSEGS_A _ O1 (A_prog_val (A_OBJ 0) + i) ltac:(cbn [fst snd]; lia)).
- exact (s7p_rng_b_sound RSEGS_A _ O2 (A_prog_val (A_OBJ 12) + i) ltac:(cbn [fst snd]; lia)).
Qed.

(* HPST *)
Lemma s7p_pst_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img SEGS a.
Proof.
intros a HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
pose proof s7p_pst_c as H. rewrite forallb_forall in H.
exact (s7p_rng_b_sound RSEGS_A r (H r Hr) a Hz).
Qed.

(* HPSTRO *)
Lemma s7p_pstro_A : forall a,
  in_roP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) a ->
  ~ Exists (in_zr a) (@prh_pst prh_img_A).
Proof. exact (s7p_pst_clear_sound RSEGS_A A_prog_relro_lo A_prog_relro_hi _ s7p_pst_clear_c). Qed.

(* HPAB *)
Lemma s7p_pab_A : IMG_LO <= @pa_lo rc A_prog_listing PA /\ @pa_hi rc A_prog_listing PA <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
End w.

(* HW *)
Lemma s7p_head_wide : prh_head_wide (cp := CfParams_preset).
Proof. unfold prh_head_wide. apply Z.leb_le. vm_compute. reflexivity. Qed.

Print Assumptions s7p_ent_A.
Print Assumptions s7p_obj_A.
Print Assumptions s7p_pst_A.
Print Assumptions s7p_head_wide.
Print Assumptions s7p_pab_A.
Print Assumptions s7p_pstro_A.
Print Assumptions s7p_zs_aligned_A.
(* put's top: its premises and the image it is stated at (rule 7's check: every PA / L / PI argument names image A) *)
Set Printing Implicit.
Unset Printing Notations.
About S7a_put.put_holds.
Print Assumptions S7a_put.put_holds.
Set Printing Notations.
Unset Printing Implicit.
(* which modules the short image names resolve to in this file's context (CrcBp's wrong-image trap) *)
Locate Img0.rsegs.
Locate rsegs.
Locate A_prog_listing.
