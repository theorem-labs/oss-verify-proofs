(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43): the
   walk of parse_string (PSB_Top.v parse_string_holds_B, the KIT TEXT tparse_string_specX of the announced the kit cut
   7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd) at the B' INSTANCE, with every static
   image premise DISCHARGED. Lane PstrBp of a Theorem Labs lane.
   rule 24: no function proved. rule 24: proves no function (kind: merge).
   parse_string_holds_B_inst is parse_string_holds_B at
   - B := YD2l.TfibB, PI := prh_img_B, L := B_prog_listing, PA := PI_prog_B, cp := CfParams_preset,
     RL := prh_room_live_a8 at CfParams_preset;
   - ARx := ARcf /\ xs_placed_cf at CfParams_preset over PI_prog_B's segments: a Theorem Labs lane's B' instance relation
     (lib/B/Prog/FuzzAllocAccInstB102.v, its ARcfx), the one CrcBInstLive.v names, word for word;
   with:
   - LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (as CrcBInstLive.v);
   - TL by PALibB.exvi_eh_palib (lib/B/PALibB.v 5baa19c890f7);
   - HW by PALibB.exvi_eh_head (prh_head_wide is `8 <= cf_head`, PRH_Base.v:241);
   - PST_ok by psbi_pst_check below (vm_compute at the B' instance: every byte of prh_img_B's prh_pst cells is in a
     segment of image B and in no range of TfibB's as_owned_static);
   - ZSA by TfibB_ok's aso_zshadow (YD2l.v, asyms_ok: every zero-shadow range is granule-aligned);
   - IMGV from a Theorem Labs lane's img_shadow_vis_cf at ARcf ALONE (the relation implies ARcf), through psbi_bounds
     (vm_compute: PI_prog_B's pa_lo / pa_hi ARE CfImg_B's cf_img_lo / cf_img_top, lib/AU/CfImgB.v); the fact itself is
     a Theorem Labs lane's tfib_img_shadow_vis_cf_B (lib/AU/AImgShadowVisCfB.v 18b6de6fa4e8, in the cut) at SEGS TB from
     YD2l.TfibB_syms;
   - HHEX4 by the hex4 B' row (a Theorem Labs lane, a working branch a155ed742e1c; lib/B/Prog/S3_Hex4Bridge.v
     277864a3be81, in the cut): its generic hex4_holds_B at THIS relation ARcfx with LAWS / TL / HW as below (its
     instance corollary hex4_holds_Bp is stated at ARcf alone, so the generic theorem is the one that fits ARcfx);
   - HPUTU by a Theorem Labs lane's pb_put_utf8X_Bp (lib/B/Prog/ExUtf8WB.v 0f95856d9f20, a working branch
     preset-tree-at-2026-10-29T23-19-11Z.tsv (sha256 7d271a61f0a1; internal record); its LAWS and TL are this instance's, TL through YC1fP.palib_core).
   - HFREE by a Theorem Labs lane's fuzz_free_holds_B (lib/B/Prog/FuzzFreeB.v 2cbfdff44651, in the cut, GREEN there): the kit's
     tfuzz_free_specX at image B, B_prog_listing / PI_prog_B, CfParams_preset, prh_room_live_a8 and THIS relation
     ARcf /\ xs_placed_cf, generic in B, so instantiated at TfibB; its PAL by PALibB.exvi_eh_palib, its pal_pst_ok by
     psbi_pst_errno_check (vm_compute: prh_img_B's statics miss TfibB's owned statics and its errno word) and its
     pal_unpoison by psbi_unpoison (vm_compute: the listing's __asan_unpoison_memory_region entry is CfImg_B's
     cf_pc_unpoison). Its AUNPOISON (aunpoison_realizes_cf, YGcfHp.v) by a Theorem Labs lane's preset_aunpoison_cf_B102
     (lib/AU/CfPoisonB102.v 7fda7f2b8c56 of the landing base 415c6c3e2969, on a Theorem Labs lane's
     combine6 preset-tree-at-2026-10-30T06-33-29Z.tsv (sha256 77f91e8d2d45; internal record) = the cut + int102 preset-tree-at-2026-10-30T06-08-22Z.tsv (sha256 6794eb3075a2; internal record), which carries the lib/A/CfApiPreset.v 52dd4f5cf200 it
     Requires and its YGcfHp.v cdd6715c8029 / YG0scf.v cfa6d6d22fb1 from int102; the cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) does not, so
     this citation lands with combine6): no stand-in left, at TfibB from
     YG0lawscf.AR_laws_ok_cf and YD2l.TfibB_syms (its tfibsegs is AsanUbsan.M.loaded_segments, the same constant as
     lib/B/Img0.rsegs = pa_segs PI_prog_B). Its AFREE (afree_realizes_cf, the free wrapper's contract, YG0dcf.v; owner
     two Theorem Labs lanes; MIGRATION 26e: the set's afree_realizes_cf_of_parts_m is not evidence until a Theorem Labs lane's
     fixed ARX lands) stays a premise, in the form PItems_final.v carries it (at every FPState, the shape of
     CfApiPresetB.v's field pa_free_cf_B).
   The premises left: tfuzz_malloc_specX at this instance (a Theorem Labs lane's AL2, FuzzMallocB_p102_holds.v, red on the cut)
   and fuzz_free_holds_B's own stand-in AFREE above. The depot's NoDup (the cursor free's admission)
   is AR_laws_x field 25, inside LAWS (YGcallcf.v 8645fa6a514f proves it at ARcf); no DEPOT premise. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf YD2l YC1fP YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Src PSB_Top.
(* put_utf8 at image B' (a Theorem Labs lane); hex4 at image B' (the hex4 B' row); image B's shadow visibility (a Theorem Labs lane) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExUtf8WB S3_Hex4Bridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AImgShadowVisCfB.
(* fuzz_free at image B' (a Theorem Labs lane) and the contracts it names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzFreeB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfHp.
(* __asan_unpoison_memory_region at image B' (a Theorem Labs lane, no stand-in) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfPoisonB102.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.

(* image B's segments, FULLY QUALIFIED (CrcBp's trap: the closure also loads PLAIN image files) *)
#[local] Notation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
(* ---- image-free checkers (the same as lib/A/Prog/S1ImgA.v's, stated here so no image-A file is loaded) ---- *)
Definition psbi_in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition psbi_off_b (O : list (Z * Z)) (a : Z) : bool :=
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) O).
Definition psbi_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.

Lemma psbi_allb_sound : forall f P a, psbi_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold psbi_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Lemma psbi_in_img_b_sound : forall (segs : list Segment) a, psbi_in_img_b segs a = true ->
  exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
Lemma psbi_off_b_sound : forall O a, psbi_off_b O a = true -> ~ Exists (in_zr a) O.
Proof.
intros O a H Hx. unfold psbi_off_b in H. apply negb_true_iff in H.
apply Exists_exists in Hx as (r & Hr & Ha). unfold in_zr in Ha.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) O = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite E in H. discriminate.
Qed.

(* ---- PST_ok at the B' instance, by computation ---- *)
Lemma psbi_pst_check :
  psbi_allb (fun a => psbi_in_img_b SEGS_B a && psbi_off_b (as_owned_static YD2l.TfibB) a) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* fuzz_free_holds_B's pal_pst_ok at the B' instance, by computation: the statics also miss TfibB's errno word *)
Lemma psbi_pst_errno_check :
  psbi_allb (fun a => psbi_off_b (as_owned_static YD2l.TfibB) a &&
                      negb ((as_errno YD2l.TfibB <=? a) && (a <? as_errno YD2l.TfibB + 4))) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma psbi_pst_errno : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ Exists (in_zr a) (as_owned_static YD2l.TfibB) /\ ~ (as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4).
Proof.
intros a Ha. pose proof (psbi_allb_sound _ _ a psbi_pst_errno_check Ha) as H.
apply andb_prop in H as [H1 H2]. split; [exact (psbi_off_b_sound _ a H1)|].
apply negb_true_iff, andb_false_iff in H2. intros [L1 L2].
destruct H2 as [H2 | H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* image B's CfImg for the implicit ci of ARcf, the kit texts and the allocator rows (this file loads no other image) *)
#[local] Existing Instance CfImgB.CfImg_B.
(* the guard: the segments the walk is over (pa_segs PI_prog_B) ARE image B's *)
Lemma psbi_segs_B : @pa_segs _ B_prog_listing PI_prog_B = SEGS_B.
Proof. reflexivity. Qed.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation RLI := (prh_room_live_a8 (cp := CP)).
#[local] Abbreviation CI := CfImgB.CfImg_B.

(* image B's bounds: the listing instance's (per-instance since preset-tree-at-2026-10-29T17-47-10Z.tsv (sha256 9d6fcfaf6b8e; internal record)) ARE the CfImg's *)
Lemma psbi_bounds : @pa_lo _ B_prog_listing PI_prog_B = @cf_img_lo CI /\ @pa_hi _ B_prog_listing PI_prog_B = @cf_img_top CI.
Proof. split; vm_compute; reflexivity. Qed.
(* fuzz_free_holds_B's pal_unpoison: the listing's __asan_unpoison_memory_region entry is CfImg_B's unpoison pc *)
Lemma psbi_unpoison : @pa_sigma _ B_prog_listing PI_prog_B AS___asan_unpoison_memory_region = @cf_pc_unpoison CI.
Proof. vm_compute. reflexivity. Qed.

Theorem parse_string_holds_B_inst : forall SK : YI16.sink_head,
  tfuzz_malloc_specX (cp := CP) (RL := RLI) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK ->
  (* fuzz_free_holds_B's own stand-in (AFREE of FuzzFreeB.v's Section f: the primed free with the memnorm keep), at every
     FPState *)
  (forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (cp := CP) SEGS TB) ->
  forall CTX CW,
  tparse_string_specX (ci := CI) (cp := CP) (RL := RLI) (PI := prh_img_B)
    (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX CW.
Proof.
intros SK HMALLOC AF CTX CW.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)) as LAWSx.
(* image B's shadow visibility at its own bounds (a Theorem Labs lane, in the cut) *)
pose proof (AImgShadowVisCfB.tfib_img_shadow_vis_cf_B (cp := CP) SEGS TB YD2l.TfibB_syms) as IV.
eapply (parse_string_holds_B (ci := CI) (cp := CP) (RL := RLI) TB ARcfx SK).
- exact LAWSx.
- exact PALibB.exvi_eh_palib.
- intros a Ha. pose proof (psbi_allb_sound _ _ a psbi_pst_check Ha) as H.
  apply andb_prop in H as [H1 H2]. split.
  + exact (psbi_in_img_b_sound SEGS a H1).
  + exact (psbi_off_b_sound _ a H2).
- intros q m H.
  destruct (proj1 (Forall_forall _ _) (aso_zshadow TB YD2l.TfibB_ok) (q, m) H) as (_ & _ & H1 & H2 & _).
  exact (conj H1 H2).
- intros ly S Hp W mem md a [HAR _] Ha. destruct psbi_bounds as [E1 E2].
  apply (IV ly S Hp W mem md a HAR). rewrite <- E1, <- E2. exact Ha.
- exact PALibB.exvi_eh_head.
- exact HMALLOC.
- (* fuzz_free at B' (a Theorem Labs lane's FuzzFreeB), its image premises discharged here *)
  (* its AUNPOISON by preset_aunpoison_cf_B102 at TfibB (the allocator laws and the image binding of the instance) *)
  exact (FuzzFreeB.fuzz_free_holds_B (fx := fx) (SK := SK) TB (AF fx)
           (CfPoisonB102.preset_aunpoison_cf_B102 (fx := fx) TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)
              YD2l.TfibB_syms)
           PALibB.exvi_eh_palib psbi_pst_errno psbi_unpoison YD2l.TfibB_syms).
- (* hex4 at B' (the hex4 B' row's generic theorem at this relation) *)
  exact (S3_Hex4Bridge.hex4_holds_B (cp := CP) (RL := RLI) TB ARcfx SK LAWSx PALibB.exvi_eh_palib
           PALibB.exvi_eh_head).
- (* put_utf8 at B' (a Theorem Labs lane's walk), at this instance's laws and shadow-base binding *)
  exact (ExUtf8WB.pb_put_utf8X_Bp (RL := RLI) TB ARcfx SK LAWSx
           (YC1fP.palib_core (PI := PI_prog_B) TB PALibB.exvi_eh_palib)).
Qed.
End i.

(* the wrong-image check of the rebind brief (rule 7) *)
Set Printing Implicit. Unset Printing Notations.
About parse_string_holds_B_inst.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions parse_string_holds_B_inst.
