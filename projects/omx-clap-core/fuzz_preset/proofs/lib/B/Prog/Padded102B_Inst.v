(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 479 of its 545 lines of code are new or changed and 448 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_S1.v, with its module names changed; 21 of its 68 lines of code are new or changed and 498 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_Link.v; 196 of its 235 lines of code are new or changed and 29 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): the INSTANCE WITNESS of the walk of padded's
   image record pd_img (Padded102B.v) at the real instance PI_prog_B (lib/B/PAImg_prog.v 15fab93fe702, rsegs of
   lib/B/Img0.v), owner ruling 16:45Z. rule 24: no function proved (kind: instance witness).
   Every IMAGE field of pd_img is closed here by computation at PI_prog_B or by S1ImgA.v's image-free checkers
   (copied below), vm_compute over rsegs and prh_img_B. The four fields about the SYMBOL BINDING B - pdi_pst_owned
   (as_owned_static B), pdi_pst_errno (as_errno B), pdi_malloc (pc_wrap_malloc (as_code B)), pdi_env (api_env) - are
   facts of the concrete asyms of B', so they stay the premises of pd_img_B. Each is a one-line computation from the
   B' TfibSyms fields ts_owned / ts_errno / ts_code / ts_universe_drv (lib/Reusable/YF0m.v (sha256 b9ab0e46c6c4; internal record), the version for
   building), now written below (pdi_*_of_tfib, pd_img_B_tb). They waited while that file did not build
   yet, because its closure YF0l.v -> YImgCellsB.v then asserted IMG_TOP_B = 6291456 (it asserts 0x601000 now, :22), false at the B' pins' IMG_TOP_B =
   0x601000 (measured: the internal file build-20261029T165556Z.log), until the per-instance bounds
   (IMG_TOP_B) landed; pdi_malloc additionally waited on the tx_put B' walk's check of the B' code record
   against PI_prog_B's SIGMA (the A' record was found relocated, off by 0x94). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B Padded102B_Home Padded102B_Link
  Padded102B_S1 Padded102B_S2 Padded102B_S3 Padded102B_S4 Padded102B_S5 Padded102B_S6.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YF0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YGcfAroBridge.
(* the B' image's cf read-only rows (relro_seg_t / errno_relro_t / the 2^64 top / the non-writable reads) at CfImg_B *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB CfAroPresetB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image-free checkers, COPIED body for body from lib/A/Prog/S1ImgA.v:24-63 (and the three B lemmas from
   lib/B/Prog/S1ImgB.v:17-39), NOT Required: S1ImgA.v Requires lib/A/PRH_Img.v, which does not build on this base
   (the kit's new PRH_Base has F_read_members, which that PRH_Img.v lacks; measured,
   the internal file build-20261029T164837Z.log). Same statements, same proofs, renamed pdi_*. ---- *)
Definition pdi_wv_b (segs : list Segment) (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition pdi_in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition pdi_in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
  || ((rlo <=? a) && (a <? rhi)).
Definition pdi_pst_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.
Lemma pdi_pst_allb_sound : forall f P a, pdi_pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold pdi_pst_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Lemma pdi_writable_of_wv_b : forall segs (m : word -> option byte) a, pdi_wv_b segs a = true -> writable_at segs m a.
Proof.
intros segs m a H. unfold writable_at. apply (seg_win_wview segs a 1 m a); [| lia | lia].
change (pdi_wv_b segs a && true = true). rewrite H. reflexivity.
Qed.
Lemma pdi_in_img_b_sound : forall segs a, pdi_in_img_b segs a = true -> in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
Lemma pdi_in_ro_b_complete : forall segs rlo rhi a, in_roP segs rlo rhi a -> pdi_in_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a [(s & Hs & Hw & Hr) | Hr]; unfold pdi_in_ro_b; apply orb_true_intro; [left | right].
- apply existsb_exists. exists s. split; [exact Hs|]. rewrite Hw. cbn [negb andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma pdi_pst_wv : pdi_pst_allb (pdi_wv_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pdi_pst_img : pdi_pst_allb (pdi_in_img_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pdi_pst_ro :
  pdi_pst_allb (fun a => negb (pdi_in_ro_b rsegs PAImg_prog.B_prog_relro_lo PAImg_prog.B_prog_relro_hi a))
    (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pdi_pst_writable : forall (m : word -> option byte) a,
  Exists (in_zr a) (@prh_pst prh_img_B) -> writable_at rsegs m a.
Proof. intros m a Ha. apply pdi_writable_of_wv_b. exact (pdi_pst_allb_sound _ _ a pdi_pst_wv Ha). Qed.
Lemma pdi_pst_in_img : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img rsegs a.
Proof. intros a Ha. apply pdi_in_img_b_sound. exact (pdi_pst_allb_sound _ _ a pdi_pst_img Ha). Qed.
Lemma pdi_pst_not_ro : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ in_roP rsegs PAImg_prog.B_prog_relro_lo PAImg_prog.B_prog_relro_hi a.
Proof.
intros a Ha Hro. pose proof (pdi_pst_allb_sound _ _ a pdi_pst_ro Ha) as H. cbv beta in H.
rewrite (pdi_in_ro_b_complete _ _ _ _ Hro) in H. discriminate.
Qed.


(* ---- the two PST facts of the binding, from the B' TfibSyms (lib/Reusable/YF0m.v (sha256 b9ab0e46c6c4; internal record), the version for
   BUILDING; its ts_owned / ts_errno are YF0m's own #102 values).
   pdi_malloc / pdi_env stay named stand-ins: YF0m's code record (Tfib_code, via YF0l.v ac4053c456c9) is the OLD pin's,
   off by 0xfc (the tx_put B' walk's table, relayed 17:0xZ, routed to YF0m.v's author), so ts_code would make them vacuous. ---- *)
Definition pdi_in_zr_b (a : Z) (r : Z * Z) : bool := (fst r <=? a) && (a <? fst r + snd r).
Lemma pdi_in_zr_b_complete : forall a P, Exists (in_zr a) P -> existsb (pdi_in_zr_b a) P = true.
Proof.
intros a P H. apply existsb_exists. apply Exists_exists in H as (r & Hr & Ha). exists r. split; [exact Hr|].
unfold pdi_in_zr_b, in_zr in *. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma pdi_pst_owned_chk :
  pdi_pst_allb (fun a => negb (existsb (pdi_in_zr_b a) YF0m.Tfib_owned_static)) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pdi_pst_errno_chk :
  pdi_pst_allb (fun a => negb ((YF0m.TFIB_ERRNO <=? a) && (a <? YF0m.TFIB_ERRNO + 4))) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pdi_pst_owned_of_tfib : forall B, YF0m.TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B TB a Ha Ho. rewrite (YF0m.ts_owned B TB) in Ho.
pose proof (pdi_pst_allb_sound _ _ a pdi_pst_owned_chk Ha) as H. cbv beta in H.
rewrite (pdi_in_zr_b_complete a _ Ho) in H. discriminate.
Qed.
Lemma pdi_pst_errno_of_tfib : forall B, YF0m.TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha He. rewrite (YF0m.ts_errno B TB) in He.
pose proof (pdi_pst_allb_sound _ _ a pdi_pst_errno_chk Ha) as H. cbv beta in H.
assert (E : (YF0m.TFIB_ERRNO <=? a) && (a <? YF0m.TFIB_ERRNO + 4) = true)
  by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
rewrite E in H. discriminate.
Qed.

(* ---- IMGVIS (Padded102B_Link.v's Hypothesis, = Padded102B_S1.v pd1_img_vis) at the real instance, from TB: the cover
   check of the B' generated lists (YF0m f82202ebccdf's own #102 Tfib_zero_shadow / Tfib_const_shadow) over the
   INSTANCE bounds [pa_lo, pa_hi) of PI_prog_B (the kit's kept_at image arm), by vm_compute, with
   lib/Reusable/YImgShadowCoverCf.v img_shadow_vis_cf_at_of_cover - image A's way (A/AImgShadowVis.v,
   A/AImgShadowVisCf.v). The same check over B' own bounds [IMG_LO_B, IMG_TOP_B) is stated too. Image A's bounds are
   not used. At the rebind this cites the allocator-model owner's per-instance img_shadow_vis_cf (ci := CfImg_B). ---- *)
Lemma pdi_img_shadow_cover : forall {rc : YM05.RunCeil},
  img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
    (@pa_lo _ B_prog_listing (@PAImg_prog.PI_prog_B rc)) (@pa_hi _ B_prog_listing (@PAImg_prog.PI_prog_B rc)) = true.
Proof. intros rc. vm_compute. reflexivity. Qed.
Lemma pdi_img_shadow_cover_B : img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance prh_img_B.
Variable B : asyms.
Theorem pd_img_B :
  (forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ Exists (in_zr a) (as_owned_static B)) ->
  (forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> ~ (as_errno B <= a < as_errno B + 4)) ->
  @pa_sigma _ B_prog_listing PAImg_prog.PI_prog_B AS___wrap_malloc = pc_wrap_malloc (as_code B) ->
  api_env (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) B ->
  pd_img (PA := PAImg_prog.PI_prog_B) B.
Proof.
intros Ho He Hm Hv. constructor.
- reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- pose proof (PAImg_prog.B_prog_obj_img 13 ltac:(lia)) as [H1 H2]. cbn [pa_val PAImg_prog.PI_prog_B]. lia.
- exact PAImg_prog.B_alias_hints_ok.
- exact pdi_pst_not_ro.
- exact pdi_pst_in_img.
- exact Ho.
- exact He.
- exact Hm.
- exact Hv.
- exact pdi_pst_writable.
Qed.
(* The tx_put A' walk / the lead (17:0xZ) asked whether TB and pdi_malloc are contradictory (as on A', where AF0l's code record
   was off by 0x94). MEASURED: NO, for B'. At YF0m f82202ebccdf (code record YF0l.Tfib_code, YF0l ac4053c456c9)
   vm_compute gives pc_wrap_malloc Tfib_code = 342052 = B_prog_sigma AS___wrap_malloc (0x53824),
   pc_wrap_free Tfib_code = 342048 = B_prog_sigma AS___wrap_free, pc_malloc_ra0 Tfib_code = 342724 (0x53ac4) and
   pc_free_ra0 Tfib_code = 342372 (0x53964), the two singleton traces of YF0m's DRV_TRACES. So `TB -> ~ pdi_malloc`
   is REFUTED, and pdi_malloc / pdi_env FOLLOW from TB by computation (the two lemmas below). PLANTED CONTROL
   (the lead, 17:1xZ): the same computation with pc_wrap_malloc + 4 must FAIL, and does (pdi_ctl_malloc_plus4 below, a
   `Fail`). With all four TB lemmas holding on the record pair, the instance is switched to ONE TB (pd_img_B_tb,
   padded_B_at_PI_prog_B below), the lead, 17:1xZ. *)
Theorem pdi_malloc_of_tfib : YF0m.TfibSyms B ->
  @pa_sigma _ B_prog_listing PAImg_prog.PI_prog_B AS___wrap_malloc = pc_wrap_malloc (as_code B).
Proof. intros TB. rewrite (YF0m.ts_code B TB). vm_compute. reflexivity. Qed.
(* PLANTED CONTROL: the wrapper entry moved by 4 is NOT the record's - this must fail, and the build checks it fails *)
Fail Example pdi_ctl_malloc_plus4 :
  @pa_sigma _ B_prog_listing PAImg_prog.PI_prog_B AS___wrap_malloc = pc_wrap_malloc YF0l.Tfib_code + 4 :=
  ltac:(vm_compute; reflexivity).
Lemma pdi_errno_img : zallb (pdi_in_img_b rsegs) YF0m.TFIB_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem pdi_env_of_tfib : YF0m.TfibSyms B -> api_env (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) B.
Proof.
intros TB. unfold api_env. rewrite (YF0m.ts_errno B TB), (YF0m.ts_code B TB).
split; [split; apply Z.leb_le; vm_compute; reflexivity|].
split.
- intros a Ha. apply pdi_in_img_b_sound. apply (zallb_sound _ 4 YF0m.TFIB_ERRNO a pdi_errno_img). cbn. lia.
- split; apply (YF0m.ts_universe_drv B TB); vm_compute; repeat (first [left; reflexivity | right]).
Qed.
Theorem pd_imgvis_of_tfib {ci : CfImg} : YF0m.TfibSyms B ->
  forall ly S Hp (W : world (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B)) mem md a,
  (fun ly S Hp W mem md => ARcf (cp := CfParams_preset) (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) B ly S Hp W mem md
     /\ xs_placed_cf ly S) ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PAImg_prog.PI_prog_B <= a < @pa_hi _ B_prog_listing PAImg_prog.PI_prog_B ->
  aview (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) (w_H W) mem (shadow_addr a) <> None.
Proof.
intros TB ly S Hp W mem md a [HAR _] Ha.
refine (img_shadow_vis_cf_at_of_cover (cp := CfParams_preset) _ B YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
  (@pa_lo _ B_prog_listing PAImg_prog.PI_prog_B) (@pa_hi _ B_prog_listing PAImg_prog.PI_prog_B)
  pdi_img_shadow_cover _ _ ly S Hp W mem md a HAR Ha).
- rewrite (YF0m.ts_zsh B TB). apply incl_refl.
- intros ly0. rewrite (YF0m.ts_const B TB). unfold YF0m.Tfib_const. apply incl_appr, incl_appr, incl_refl.
Qed.
(* ---- THE INSTANCE AT ONE TB (the lead, 17:1xZ): every binding fact of pd_img and IMGVIS from TB on the record pair ---- *)
Theorem pd_img_B_tb : YF0m.TfibSyms B -> pd_img (PA := PAImg_prog.PI_prog_B) B.
Proof.
intros TB. exact (pd_img_B (pdi_pst_owned_of_tfib B TB) (pdi_pst_errno_of_tfib B TB) (pdi_malloc_of_tfib TB)
  (pdi_env_of_tfib TB)).
Qed.
End i.

(* ---- AROLINK (Padded102B_Link.v's Hypothesis, = Padded102B_S1.v pd1_aro) at the real instance: PI_prog_B's RELRO
   bounds B_prog_relro_lo / _hi are CfImg_B's cf_relro_lo / _hi (both PT_GNU_RELRO of the B' twin, equal by
   computation) and rsegs is AU's tfibsegs (both AsanUbsan.M.loaded_segments), so YGcfAroBridge.arodata_ok_cf_of_P at
   CfImg_B over lib/AU/CfAroPresetB.v's four rows gives it from TB. A consumer at ci := CfImg_B passes it to
   padded_B_at_PI_prog_B below. ---- *)
Section aro. Context {rc : YM05.RunCeil}.
Theorem pdi_aro_link_B : forall B, YF0m.TfibSyms B ->
  forall (W : world (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B)) (mem : word -> option byte),
  arodata_okP (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) (@pa_relro_lo _ _ PAImg_prog.PI_prog_B)
    (@pa_relro_hi _ _ PAImg_prog.PI_prog_B) B (aview (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) (w_H W) mem) ->
  arodata_ok_cf (ci := CfImgB.CfImg_B) (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B) B mem.
Proof.
intros B TB W mem H.
exact (YGcfAroBridge.arodata_ok_cf_of_P (ci := CfImgB.CfImg_B) _ B W mem CfAroPresetB.relro_seg_preset_AU
  (CfAroPresetB.errno_relro_preset_AU B TB) CfAroPresetB.relro_top_preset_AU CfAroPresetB.ro_reads_nw_preset_AU H).
Qed.
End aro.

(* ---- THE WALK'S THEOREM AT THE REAL INSTANCE PI_prog_B: the kit's tpadded_specX VERBATIM (padded_B) with pd_img and
   IMGVIS discharged from TB; what remains are the three callee texts (AMALLOC: the keep text
   YGcfMallocComposeKeep.amalloc_realizes_cf_keep; AI_cpy / AI_set: the runtime rows), the read-only link AROLINK at the
   generic ci (at ci := CfImg_B it is pdi_aro_link_B above) and TB itself (the unit's symbol binding of B', which the
   top supplies) ---- *)
Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance pd_RL.
#[local] Notation PA := PAImg_prog.PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PAImg_prog.PI_prog_B).
#[local] Notation ARc B := (fun ly S Hp W mem md => ARcf (cp := CfParams_preset) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Theorem pdi_img_band : 0 <= @pa_lo _ B_prog_listing PAImg_prog.PI_prog_B /\
  @pa_hi _ B_prog_listing PAImg_prog.PI_prog_B <= 2 ^ 47.
Proof. split; [apply Z.leb_le | apply Z.leb_le]; vm_compute; reflexivity. Qed.
Theorem padded_B_at_PI_prog_B : forall B, YF0m.TfibSyms B ->
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CfParams_preset) SEGS B ->
  aintrin_realizes_xm SEGS B (ARc B) OCpy (@pa_sigma _ B_prog_listing PA AS___asan_memcpy) ->
  aintrin_realizes_xm SEGS B (ARc B) OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset) ->
  (forall (W : world SEGS) (mem : word -> option byte),
     arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
     arodata_ok_cf SEGS B mem) ->
  forall CTX0, tpadded_specX (fx := fx) (rc := rc) (ci := ci) (cp := CfParams_preset) (PI := prh_img_B) (RL := pd_RL)
    (L := B_prog_listing) (PA := PA) B (ARc B) SK CTX0.
Proof.
intros B TB AM ACP AST ARO CTX0.
exact (padded_B (fx := fx) (ci := ci) (SK := SK) (PA := PA) B AM ACP AST pdi_img_band (pd_imgvis_of_tfib B TB)
  ARO (pd_img_B_tb B TB)
  CTX0).
Qed.
End top.
(* THE TOP WITH EVERY IMPLICIT ARGUMENT SHOWN (the build log carries it; the instance is PI_prog_B, and PI_prog_A
   must not occur) *)
Set Printing Implicit.
Check @padded_B_at_PI_prog_B.
Unset Printing Implicit.
Print Assumptions pd_img_B.
Print Assumptions pd_imgvis_of_tfib.
Print Assumptions pdi_malloc_of_tfib.
Print Assumptions pdi_env_of_tfib.
Print Assumptions pd_img_B_tb.
Print Assumptions pdi_aro_link_B.
Print Assumptions padded_B_at_PI_prog_B.
