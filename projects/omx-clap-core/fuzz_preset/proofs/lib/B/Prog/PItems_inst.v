(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 106 of its 134 lines of code are new or changed and 486 lines of the source are left out. *)
(* Theorem Labs, 2026-10: INSTANCE WITNESSES for the image facts at parse_items' image-B' top (lane PItemsB, owner;
   a Theorem Labs lane's UNIT RULING 16:45Z: every premise stating a fact about the image needs a lemma closed by computation at
   the real instance). Instance: B := YD2l.TfibB (image B', asan-ubsan pin d663f82d7f48, twin c90d4fa54d43), the
   listing B_prog_listing / PI_prog_B, PrhImg prh_img_B, CfImg CfImg_B (lib/AU/CfImgB.v), allocator relation of record
   ARcfx = (ARcf pa_segs TfibB /\ xs_placed_cf).
     pii_unpoison  pa_sigma AS___asan_unpoison_memory_region = cf_pc_unpoison at CfImg_B   (vm_compute: 348644 both)
     pii_pst_ok    pal_pst_ok at TfibB: the program statics prh_pst miss TfibB's owned statics and errno (vm_compute of
                   an interval-disjointness check, then a soundness argument)
     pii_hsh_x     pi_hshadow_law at ARcfx (an allocator law, not an image fact: lifted from a Theorem Labs lane's
                   YGcfHeadSh.ARx_hshadow_law_cf_ok at ARcf through the conjunction)
   THE IMAGE BOUNDS ARE PER INSTANCE (a Theorem Labs lane's ruling 18:56Z): every window below is the listing's own
   pa_lo / pa_hi at PI_prog_B (lib/B/PAImg_prog.v: IMG_LO_B / IMG_TOP_B = 0x10000 / 0x601000), never image A's.
   Rule 24: proves no function (kind: instance witness). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YP0b YC4aP YPsym YGcfNames YG0f YG0n YG0d YD2l YG0ncf YG0lawscf YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YCbqG YGcallcf YA0n YK04 YA0i YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgShadowCover YImgShadowCoverCf YF0m YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_kept.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

Section inst. Context {rc : YM05.RunCeil}.

(* __asan_unpoison_memory_region's entry in the listing is CfImg_B's unpoison pc (0x551e4) *)
Lemma pii_unpoison :
  @pa_sigma rc B_prog_listing (@PI_prog_B rc) AS___asan_unpoison_memory_region = @cf_pc_unpoison CfImg_B.
Proof. vm_compute. reflexivity. Qed.

(* two (base, length) ranges are apart *)
Definition pii_disjb (r s : Z * Z) : bool := (fst r + snd r <=? fst s) || (fst s + snd s <=? fst r).

Lemma pii_disjb_sound : forall r s a, pii_disjb r s = true -> in_zr a r -> ~ in_zr a s.
Proof.
intros r s a H Hr Hs. unfold pii_disjb, in_zr in *. apply orb_true_iff in H.
destruct H as [H | H]; apply Z.leb_le in H; lia.
Qed.

(* pal_pst_ok at TfibB: the program's statics are neither runtime-owned statics nor errno *)
Lemma pii_pst_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4).
Proof.
intros a Ha.
assert (HB : forallb (fun r => forallb (pii_disjb r) (as_owned_static TfibB) && pii_disjb r (as_errno TfibB, 4))
               (@prh_pst prh_img_B) = true) by (vm_compute; reflexivity).
apply Exists_exists in Ha. destruct Ha as (r & Hr & Hz).
rewrite forallb_forall in HB. specialize (HB r Hr). apply andb_true_iff in HB. destruct HB as [H1 H2].
rewrite forallb_forall in H1. split.
- intros Hs. apply Exists_exists in Hs. destruct Hs as (s & Hs & Hz').
  exact (pii_disjb_sound r s a (H1 s Hs) Hz Hz').
- intros He. apply (pii_disjb_sound r (as_errno TfibB, 4) a H2 Hz). unfold in_zr. cbn [fst snd]. exact He.
Qed.

End inst.

Section lawx. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation ARX := (fun ly S Hp W mem md => ARcf SEGS TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

(* the harness-block shadow law at the relation of record, from a Theorem Labs lane's at ARcf *)
Lemma pii_hsh_x : pi_hshadow_law (L := B_prog_listing) (PA := @PI_prog_B rc) TfibB ARX cf_head.
Proof.
intros ly S Hp W mem md b n [H _] Hb Hin.
exact (ARx_hshadow_law_cf_ok SEGS TfibB (AR_laws_ok_cf SEGS TfibB) ly S Hp W mem md b n H Hb Hin).
Qed.

End lawx.

(* ---- HZS and HIMG at the relation of record (a Theorem Labs lane 17:0xZ). Restated from PValueB's lib/B/Prog/PvB_Inst.v
   (a working branch 32128e0aad52, blob 25ca37197437): pvI_zs_al, pvI_cover, pvI_const_incl,
   pvI_img_vis copied with TB := TfibB; that file cannot be Required on this base (it Requires PValueB's walk files,
   which are on the superseded parse text). pvh_hull_img (PvB_A_Home.v) is SHARPENED: its window
   lo + 64 <= a /\ a + n + 64 <= hi becomes lo <= a /\ a + n <= hi, valid because both bounds are 64-aligned
   (pa_lo = 65536 = 1024 * 64, pa_hi = 6295552 = 98368 * 64). That covers TfibB's two edge zero-shadow ranges,
   (65536, 69472) and (6151712, 143840), which start at pa_lo and end at pa_hi exactly, so pi_zs_law needs NO edge
   premise. Every window is the listing's own [pa_lo, pa_hi) (PLO / PHI below), the bounds kept_img states.
   OWNER of the image-shadow visibility: a Theorem Labs lane, lib/AU/AImgShadowVisCfB.v tfib_img_shadow_vis_cf_B (not on this
   base); until it lands pii_cover / pii_img_vis are this file's own witness, and pii_img_vis then becomes a citation
   of it. ---- *)
Section shx. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation ARX := (fun ly S Hp W mem md => ARcf SEGS TfibB ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation PLO := (@pa_lo rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PHI := (@pa_hi rc B_prog_listing (@PI_prog_B rc)).

(* the listing's image bounds at B' (vm_compute: 65536 / 6295552, i.e. 0x10000 / 0x601000) *)
Lemma pii_pa_bounds : PLO = YImgTop.IMG_LO_B /\ PHI = YImgTop.IMG_TOP_B.
Proof. split; vm_compute; reflexivity. Qed.

(* TfibB's zero-shadow ranges are granule-aligned (PvB_Inst.v pvI_zs_al) *)
Lemma pii_zs_al : forall r, In r (as_zero_shadow TfibB) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.
Proof.
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0))%bool (as_zero_shadow TfibB) = true)
  by (vm_compute; reflexivity).
intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. split; [exact H1 | exact H2].
Qed.

(* ... and lie inside [pa_lo, pa_hi] *)
Lemma pii_zs_win : forall r, In r (as_zero_shadow TfibB) -> PLO <= fst r /\ fst r + snd r <= PHI.
Proof.
assert (H : forallb (fun r => (PLO <=? fst r) && (fst r + snd r <=? PHI))%bool (as_zero_shadow TfibB) = true)
  by (vm_compute; reflexivity).
intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2].
Qed.

(* PvB_Inst.v pvI_cover / pvI_const_incl / pvI_img_vis *)
Lemma pii_cover : YImgShadowCover.img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow PLO PHI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pii_const_incl : forall ly, incl YF0m.Tfib_const_shadow (as_const TfibB ly).
Proof.
intros ly. change (as_const TfibB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

Lemma pii_img_vis : forall ly S Hp (W : world SEGS) mem md a, ARcf SEGS TfibB ly S Hp W mem md ->
  PLO <= a < PHI -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
exact (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover (cp := CfParams_preset) SEGS TfibB YF0m.Tfib_zero_shadow
  YF0m.Tfib_const_shadow PLO PHI pii_cover (incl_refl _) pii_const_incl).
Qed.

(* PvB_A_Home.v pvh_hull_img, with the window sharpened to the image's own 64-aligned bounds *)
Lemma pii_hull_img : forall a n s, 0 < n -> PLO <= a -> a + n <= PHI ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ PLO <= 8 * (s - SHADOW_OFF) < PHI.
Proof.
intros a n s Hn Hlo Hhi Hs. destruct pii_pa_bounds as [EL EH]. rewrite EL in Hlo |- *. rewrite EH in Hhi |- *.
unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. unfold shadow_addr in *.
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as Ha64. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as Ha64b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod ((a + n - 1) / 8) 8 ltac:(lia)) as Hb64.
pose proof (Z.mod_pos_bound ((a + n - 1) / 8) 8 ltac:(lia)) as Hb64b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* the laws at ARX (YGcallcf.v:242) *)
#[local] Notation LAWSX := (AR_laws_x_xs SEGS TfibB (AR_laws_ok_cf SEGS TfibB)).

(* HZS: every zero-shadow range of TfibB is addressable with a visible hull, in every ARX state; NO edge premise *)
Lemma pii_hzs_x : pi_zs_law (L := B_prog_listing) (PA := @PI_prog_B rc) TfibB ARX.
Proof.
intros ly S Hp W mem md a n HA (q & m & Hin & Hq & Hqm) Hn.
destruct (pii_zs_al (q, m) Hin) as [Z3 Z4]. destruct (pii_zs_win (q, m) Hin) as [W1 W2]. cbn [fst snd] in Z3, Z4, W1, W2.
pose proof (alx_zshadow _ _ _ LAWSX ly S Hp W mem md (q, m) HA
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz. cbn [fst snd] in Hz.
split.
- apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m a n); [|exact Hq | exact Hqm].
  exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz).
- intros s Hs. destruct (pii_hull_img a n s Hn ltac:(clear - W1 Hq; lia) ltac:(clear - W2 Hqm; lia) Hs) as [E Hr]. rewrite E.
  exact (pii_img_vis ly S Hp W mem md _ (proj1 HA) Hr).
Qed.

(* kept_img / kept_at are PER-INSTANCE since kit-oldpin 7176c4125950 (pa_lo + 64 <= p /\ p + n + 64 <= pa_hi of the
   Section's PA); at PA := PI_prog_B they are exactly the PLO / PHI of the window lemmas above, so no rewrite *)

(* HIMG: a kept image string is addressable with a visible hull, in every ARX state. The hull: PvB_Inst.v pvI_hkimg's
   argument (the sharpened pii_hull_img and pii_img_vis). The addressability (not in pvI_hkimg): kept_img's per-byte
   ro_shadow_ok - either the byte's granule is in a zero-shadow range (alx_zshadow) or its shadow cell is a const cell
   of value v with v = 0 \/ x mod 8 < v < 8, which ARcf's const-cell law amc_const (YG0ncf.v) makes the shadow byte *)
Lemma pii_himg_x : pi_img_law (L := B_prog_listing) (PA := @PI_prog_B rc) TfibB ARX.
Proof.
intros ly S Hp W mem md a n HA (Hlo & Hhi & Hb) Hn. split.
- intros x Hx. destruct (Hb x Hx) as (_ & _ & _ & Hro). pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
  destruct Hro as [(q & m & Hin & Hq & Hqm) | (v & Hc & Hv)].
  + destruct (pii_zs_al (q, m) Hin) as [Z3 Z4]. cbn [fst snd] in Z3, Z4.
    pose proof (alx_zshadow _ _ _ LAWSX ly S Hp W mem md (q, m) HA
      ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz. cbn [fst snd] in Hz.
    exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
  + pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ (proj1 (proj1 HA))) _ (Hc ly)) as Hcell.
    unfold cell_holds in Hcell. cbn [c_at c_val c_w z1 c1 aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). cbn [Z.of_nat] in Hcell. rewrite Z.add_0_r in Hcell.
    exists v. split.
    * unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
      unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
      rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity.
    * unfold saddr_ok. lia.
- intros s Hs. destruct (pii_hull_img a n s Hn ltac:(clear - Hlo; lia) ltac:(clear - Hhi; lia) Hs) as [E Hr]. rewrite E.
  exact (pii_img_vis ly S Hp W mem md _ (proj1 HA) Hr).
Qed.

End shx.
