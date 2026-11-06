(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_parse_inst.v, with its module paths and module names changed; 102 of its 147 lines of code are new or changed and 16 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the INSTANCE facts of pj_parse's image-A' walk: B := AD2l.TfibB (A', the generated image
   binding, TfibB_syms), ARx := ARcf with the error-buffer extents placed (YGcallcf.v's ARxs, the ARcfx of the walk
   segments), PA := PI_prog_A at the A' listing, cp := CfParamsPreset.CfParams_preset. PORTED from the image-B'
   walk's lib/B/Prog/pj_parse_inst.v (sha256 eee3418ed953; internal record): the same four facts, at image A''s generated names (AF0m / AD2l /
   AImgShadowVis instead of YF0m / YD2l and B''s own cover witness).
   - pjp_inst_laws: the walk's LAWS, YGcallcf.AR_laws_x_xs over YG0lawscf.v's AR_laws_ok_cf (no image premise).
   - pjp_inst_frame_hull: pjp_g_vis' first conjunct, ARx_frame_hull_vis_cf_ok (no image premise).
   - pjp_inst_img_vis: pjp_g_vis' third conjunct at the instance, from A''s cover check
     (AImgShadowVis.tfib_img_shadow_cover over [IMG_LO, IMG_TOP) = [pa_lo, pa_hi) of PI_prog_A, by vm_compute there) and
     YImgShadowCoverCf.v img_shadow_vis_cf_at_of_cover with TfibB_syms' list equations (ts_zsh, ts_const).
   - pjp_inst_zs_gran / pjp_inst_zs_aligned: pjp_g_vis' second conjunct, every zero-shadow range of A' (AF0m.v
     Tfib_zero_shadow, = as_zero_shadow TfibB by ts_zsh) starts and ends on a granule boundary, by vm_compute (the
     WITNESS).
   So pjp_g_vis holds at the instance with no premise; PjParseA_top.v pj_parse_holds_A uses it.
   THE CALLEE ROWS DISCHARGED AT THE INSTANCE (each a citation of a walk on the cut or on the S6 base):
   - pjp_inst_ams: __asan_memset's m-form row, lib/A/PRowSet.v prow_asan_memset_xm_A_lit (through
     pjp_w_aim, S6ImgWit.v's s6w_aim restated);
   - pjp_inst_ff: fuzz_free, lib/A/Prog/FuzzFree.v fuzz_free_holds at ARcfx, its stand-ins PAL by lib/A/PALibA.v palib_A,
     pal_pst_ok by lib/A/Prog/FuzzAllocAccInst102.v acc_pal_pst_ok_A and TB by AD2l.TfibB_syms; its callee rows stay
     premises: AF, the free row in its keep form YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (FuzzFree reads the keep),
     and AU;
   - pjp_inst_pf: pj_free at every depth, lib/A/Prog/S6PjFreeTop.v pj_free_holds (the S6 A' walk, by path
     from S6PjFreeTop.v (sha256 2bf4c7a74674; internal record)), its image premises by the pjp_w_* witnesses below (S6ImgWit.v's, restated) and
     S1ImgA.v pst_in_img_A / pst_not_ro_A, LAWS / VISF / TL as above, FREE := pjp_inst_ff.
   proves no function (kind: instance witnesses and citations). One address numeral, 0x52880, the A' listing's
   pc of __asan_memset, checked by vm_compute in pjp_w_aim (as S6ImgWit.v states it). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YGcfFsVis YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfImgA AD2l AF0m AImgShadowVis PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v PRowSet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfHp YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck S6PjFree S6PjFreeTop FuzzFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require FuzzAllocAccInst102.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* every zero-shadow range of image A''s generated list is whole granules (the vm_compute witness) *)
Lemma pjp_inst_zs_gran :
  forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pjp_inst_zs_aligned : forall q m, In (q, m) (as_zero_shadow AD2l.TfibB) -> q mod 8 = 0 /\ m mod 8 = 0.
Proof.
intros q m Hin. rewrite (AF0m.ts_zsh AD2l.TfibB AD2l.TfibB_syms) in Hin.
pose proof (proj1 (forallb_forall _ _) pjp_inst_zs_gran (q, m) Hin) as W. cbn [fst snd] in W.
apply andb_prop in W as [W1 W2]. apply Z.eqb_eq in W1, W2. exact (conj W1 W2).
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation ARI :=
  (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

Lemma pjp_inst_laws : AR_laws_x SEGS TB ARI (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma pjp_inst_frame_hull : ARx_frame_hull_vis SEGS TB ARI.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (ARx_frame_hull_vis_cf_ok (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)
  ly S Hp W mem md cid pos HA Hin).
Qed.

Lemma pjp_inst_img_vis : forall ly S Hp W mem md a, ARI ly S Hp W mem md ->
  @pa_lo _ A_prog_listing PA <= a < @pa_hi _ A_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HA _] Ha.
exact (img_shadow_vis_cf_at_of_cover (cp := CP) SEGS TB AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow IMG_LO IMG_TOP
  AImgShadowVis.tfib_img_shadow_cover
  (AImgShadowVis.tfib_zsh_incl TB (AF0m.ts_zsh TB AD2l.TfibB_syms))
  (AImgShadowVis.tfib_const_shadow_incl TB (AF0m.ts_const TB AD2l.TfibB_syms))
  ly S Hp W mem md a HA Ha).
Qed.
End i.

(* ---- the image premises of the S6 A' pj_free walk at the instance: lib/A/Prog/S6ImgWit.v's s6w_ent_pj_free / s6w_obj
   / s6w_pab / s6w_pst_img / s6w_pst_ro / s6w_ret_free / s6w_aim, restated here with the same proofs. S6ImgWit itself
   is not Required: it also Requires S6PjString / S6PjGet / S6PjGetStr, and the cut's S6PjString.v (blob 6d3473b40a23)
   does not compile on the cut (:88, `prh_univ_closure B CTX0` applied to DW); its green version is
   S6PjString.v (sha256 e4f382e2591f; internal record), outside this walk's closure ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pjp_w_ent_pj_free :
  @pa_sigma _ A_prog_listing PI_prog_A AS_pj_free = @pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjFree.AF_pf.
Proof. cbn [pa_sigma pa_val PI_prog_A]. unfold S6PjFree.AF_pf. vm_compute. reflexivity. Qed.

Lemma pjp_w_obj : forall i, 0 <= i < 8 ->
  in_img (@pa_segs _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A (A_OBJ 0) + i) /\
  in_img (@pa_segs _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A (A_OBJ 12) + i).
Proof.
cbn [pa_segs pa_val PI_prog_A].
assert (Hb : forallb (fun i => S1ImgCheck.in_img_b OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs
                                 (A_prog_val (A_OBJ 0) + i) &&
                               S1ImgCheck.in_img_b OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs
                                 (A_prog_val (A_OBJ 12) + i)) [0; 1; 2; 3; 4; 5; 6; 7] = true)
  by (vm_compute; reflexivity).
intros i Hi. rewrite forallb_forall in Hb.
assert (Hin : In i [0; 1; 2; 3; 4; 5; 6; 7]) by (cbn [In]; lia).
specialize (Hb i Hin). apply andb_prop in Hb as [H1 H2].
split; [exact (S1ImgCheck.in_img_b_sound _ _ H1) | exact (S1ImgCheck.in_img_b_sound _ _ H2)].
Qed.

Lemma pjp_w_pab : @pa_lo _ A_prog_listing PI_prog_A = IMG_LO.
Proof. reflexivity. Qed.

(* pal_pst_img / pal_pst_ro: alloc.c's statics are image bytes and no read-only bytes: lib/A/Prog/S1ImgA.v
   pst_in_img_A / pst_not_ro_A, cited directly in pjp_inst_pf *)

Lemma pjp_w_ret_free : forall off, In off [200; 252; 276; 304] ->
  In (@pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjFree.AF_pf + off) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free).
Proof.
cbn [pa_val PI_prog_A].
assert (Hb : forallb (fun off => existsb (Z.eqb (A_prog_val A_TEXT + S6PjFree.AF_pf + off))
                                   (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free)) [200; 252; 276; 304] = true)
  by (vm_compute; reflexivity).
intros off Hoff. rewrite forallb_forall in Hb. specialize (Hb off Hoff).
apply existsb_exists in Hb as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.

(* the A' memset row: PRowSet.v prow_asan_memset_xm_A_lit (the segments of PI_prog_A are AB1v.tfibsegs
   by delta; the listing's pc of __asan_memset is the row's, by vm_compute on the closed term) *)
Lemma pjp_w_aim : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world (@pa_segs _ A_prog_listing PI_prog_A) -> (word -> option byte) -> Model -> Prop)
    (hl : Z),
  YCbqG.AR_laws_x (@pa_segs _ A_prog_listing PI_prog_A) B ARx hl -> AF0m.TfibSyms B ->
  YGcallMxmn.aintrin_realizes_xm (@pa_segs _ A_prog_listing PI_prog_A) B ARx YG0d.OSet
    (@pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset).
Proof.
intros B ARx hl HL HS.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset = 0x52880)
  by (cbn [pa_sigma PI_prog_A]; lazymatch goal with |- A_prog_sigma AS___asan_memset = _ => vm_compute; reflexivity end).
rewrite E. exact (PRowSet.prow_asan_memset_xm_A_lit B ARx hl HL HS).
Qed.
End w.

(* ---- the callee rows at the instance (header) ---- *)
Section r. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance prh_img_A.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation ARI :=
  (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).

Lemma pjp_inst_ams : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TB ARI OSet (@pa_sigma _ A_prog_listing PA AS___asan_memset).
Proof. intros fy. exact (pjp_w_aim (fx := fy) TB ARI cf_head pjp_inst_laws AD2l.TfibB_syms). Qed.

Lemma pjp_inst_ff
  (AF : forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TB)
  (AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) SEGS TB) :
  forall fy : YK11.FPState,
  tfuzz_free_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA) TB ARI SK.
Proof.
intros fy. eapply FuzzFree.fuzz_free_holds;
  first [exact (AF fy) | exact (AU fy) | exact PALibA.palib_A | exact FuzzAllocAccInst102.acc_pal_pst_ok_A
        | exact AD2l.TfibB_syms].
Qed.

Lemma pjp_inst_pf
  (AF : forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TB)
  (AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) SEGS TB) :
  forall (fy : YK11.FPState) CTX0 n,
  tpj_free_specX (fx := fy) (ci := CfImgA.CfImg_A) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA)
    TB ARI SK CTX0 n.
Proof.
intros fy CTX0 n.
eapply (S6PjFreeTop.pj_free_holds (fx := fy) (ci := CfImgA.CfImg_A) (RL := RLa8) SK (PA := PA) TB ARI);
  first [exact pjp_inst_laws | exact PALibA.palib_A | exact pjp_inst_frame_hull | exact pjp_w_ent_pj_free
        | exact pjp_w_obj | exact pjp_w_pab | exact S1ImgA.pst_in_img_A | exact S1ImgA.pst_not_ro_A
        | exact pjp_w_ret_free | exact (pjp_inst_ams fy) | exact (pjp_inst_ff AF AU fy)].
Qed.
End r.

Print Assumptions pjp_inst_laws.
Print Assumptions pjp_inst_frame_hull.
Print Assumptions pjp_inst_img_vis.
Print Assumptions pjp_inst_zs_gran.
Print Assumptions pjp_inst_zs_aligned.
Print Assumptions pjp_inst_ams.
Print Assumptions pjp_inst_ff.
Print Assumptions pjp_inst_pf.
