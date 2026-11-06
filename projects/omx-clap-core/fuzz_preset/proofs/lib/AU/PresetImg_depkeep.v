(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_depkeep.v (commit 4d286b2e618d, file sha256 c93d654ed088) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 2 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 5 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (fm port, row img-depkeep-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for the cf layer at
   plugin-hostd/fuzz_reply). The B twin of a prior worker's lib/A/PresetImg_depkeep.v (
   depkeep-a 7c7e587ea49), mirrored line for line: same helper names, same Section c form, same premises.
   rule 24: no function proved (kind: image row; the constant cells and the depot's cells against the kept zones, at
   reply's image B, fuzz_reply.asan-ubsan).

   The row is the cf layer's image premise dep_keep_img B KEEP (lane F1, YGcfInstDepot.v:154 at 
   a8ad57cefdc; the table text is the internal file CF-UNIT-HYPS-F1.md row 7), at its two zone pairs:
   - Allocate:   KEEP := fun ly a => ag_dzone ly a \/ ag_czone ly a                    ([dep_keep_a_B]);
   - Deallocate: KEEP := fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)   ([dep_keep_d_B]).
   cgif's discharge is YGcfInstF1Wcgif.v:96 dep_keep_a_cgif / :109 dep_keep_d_cgif.  Reply does not carry the layer's
   YGcfInstDepot.v yet, so each theorem states dep_keep_img's body, KEEP applied, at reply B's instances (ImgBase.AImg at
   AImg_cgif, B/AGif2cgif.v:24; ImgBaseAG.AGImg at AGImg_cgif, B/AGif0cgif.v:116; ImgBaseDG.DImg at DImg_cgif,
   B/DGif0cgif.v:30), and a consumer closes the layer's row by `exact` once the layer is on reply.
   The depot premise is the layer head's `depot_fits (as_universe B) (st_depot S)` (YG01.v:153, the P'' depot model):
   preset's universe has wild prefixes (Reusable/YCej.v Tfib_wild), so its depot need not list only fixed traces.

   The section-c helpers (const_cells_zone, CZONE_range, DZONE_range, cell_holds_agree, aview_agree, depot_ids_bound,
   depot_mem_ok_agree) are preset's AU/AGix.v Section c, same section variables, cited here; const_kept's loop is
   inline in the two theorems, as in dep_keep_d_cgif; CLdepotcgif.const_noizone with its helpers (cgif
   lib/CLdepotcgif.v:43-112) is re-run below at image B'.  Each table check is
   a vm_compute on reply B's own constant tables (Tfib_const_abs / Tfib_const_shadow / Tfib_const, B/YF0m.v); reply B's
   constant-cell zone CZONE is AGif0cgif.CZONE (B/AGif0cgif.v:63, image to 0x601000 and high shadow cells up to
   0x800b8200); the depot zone is AGis.DZONE (B/AGis.v:231) = DGgi.DZONE (B/DGgi.v:515); the internal allocator's zone
   is DGgi.IZONE (B/DGgi.v:517), at TFIB_IAL_LO / TFIB_IAL_HI / TFIB_IAL_FLAG = 0xac900 / 0x128870 / 0x1360c8
   (B/YF0m.v:18-19). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif DGif0cgif.
(* Used qualified: their names (DZONE, IZONE, the class fields) would clash with each other. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis DGgi. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGix.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H;
  pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END,
  kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The table checks (by vm_compute on reply's tables).                                                              *)

(* CLdepotcgif.noial / const_noial: a cell's bytes miss [TFIB_IAL_LO, TFIB_IAL_HI) and [TFIB_IAL_FLAG, + 4); the
   thread, context and D objects are checked by offset and placed off the image by the layout ([zoneTCD]). *)
Definition noial (a w : Z) : bool :=
(a + w <=? TFIB_IAL_LO) || ((TFIB_IAL_HI <=? a) && (a + w <=? TFIB_IAL_FLAG)) || (TFIB_IAL_FLAG + 4 <=? a).
Definition const_noial (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => noial a w
| ATsd k => noial (TFIB_TSD + k) w
| ATp k => noial (TFIB_TP + k) w
| AInst k => noial (TFIB_INST + k) w
| AT k => (0 <=? k) && (k + w <=? 80)
| AC k => (0 <=? k) && (k + w <=? 256)
| AD k => (0 <=? k) && (k + w <=? 4096)
| _ => false
end.
Lemma Tfib_const_noial : forall ly, forallb const_noial (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma noial_ok : forall a w i, noial a w = true -> 0 <= i < w ->
~ (TFIB_IAL_LO <= a + i < TFIB_IAL_HI \/ TFIB_IAL_FLAG <= a + i < TFIB_IAL_FLAG + 4).
Proof.
intros a w i K Hi. unfold noial in K.
apply Bool.orb_true_iff in K. destruct K as [K|K].
- apply Bool.orb_true_iff in K. destruct K as [K|K].
  + apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
  + apply Bool.andb_true_iff in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
- apply Z.leb_le in K. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.
(* The thread object, the context object and the D page are off the image (CLdepotcgif.zoneTCD). *)
Lemma zoneTCD : forall ly, layout_ok ly -> img_cover ly ->
zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
intros ly LY IMG.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (AGis.Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (AGis.Forall_nth' _ _ 6 _ HA eq_refl) as IC.
pose proof (AGis.Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbn beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
split; [exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT
  (AGis.pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl))|].
split; [exact (zone3_intro ly (ly_C ly) 256 IMG ltac:(lia) IC (AGis.pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl))|].
exact (zone3_intro ly (ly_D ly) 4096 IMG ltac:(lia) ID (AGis.pairwise_ij _ _ 7 1 _ _ HD eq_refl eq_refl)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The constant cells and the depot at one layout (cgif's AGix Section c at reply's image).                        *)
(* Every lemma of Section c is abstracted over all of its variables, in their declaration order (as cgif's AGix). *)
Local Set Default Proof Using "All".
Section c.
Variables (B : asyms) (ly : alayout).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
(* const_cells_zone, CZONE_range, DZONE_range, cell_holds_agree, aview_agree, depot_ids_bound and depot_mem_ok_agree:
   preset states them in AU/AGix.v Section c; the two theorems below cite them. *)








(* CLdepotcgif.const_noizone at reply: no constant cell's byte is in the internal allocator's zone. *)
Lemma const_noizone : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
~ DGgi.IZONE (aeval B ly (c_at c) + k).
Proof.
intros c k Hin Hk.
rewrite (ts_const B TS ly) in Hin.
pose proof (proj1 (forallb_forall _ _) (Tfib_const_noial ly) c Hin) as K. unfold const_noial in K.
destruct (zoneTCD ly LY IMG) as (ZT & ZC & ZD).
unfold zone3, zone3cases in ZT, ZC, ZD.
unfold DGgi.IZONE.
destruct (c_at c) eqn:Ea; cbn [aeval]; try discriminate K.
- exact (noial_ok _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg,
  kThreadObjSize in *. lia.
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
- rewrite HTSD. exact (noial_ok _ _ k K Hk).
- rewrite (ts_inst B TS). exact (noial_ok _ _ k K Hk).
- rewrite (ts_tp B TS). exact (noial_ok _ _ k K Hk).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The row: dep_keep_img B KEEP (YGcfInstDepot.v:154), its body at reply's instances, at the two zone pairs.       *)

(* Allocate (YGcfInstF1Wcgif.v:96 dep_keep_a_cgif's twin): KEEP := ag_dzone \/ ag_czone, i.e. AGis.DZONE \/
   AGif0cgif.CZONE at AGImg_cgif. *)
Theorem dep_keep_a_B : forall B, @im_syms AImg_cgif B ->
forall ly S (W : world (@im_segs AImg_cgif)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B ->
depot_fits (as_universe B) (st_depot S) ->
Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem0) ->
(forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem).
Proof.
intros B TS ly S W mem0 mem LY IMG TSD DF CST DEP MEQ. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply Forall_forall. intros c Hc.
  apply (AGix.cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0)); [| exact (proj1 (Forall_forall _ _) CST c Hc)].
  intros k Hk. pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
  pose proof (AGix.CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
  apply (AGix.aview_agree W mem0 mem _ R). apply MEQ. rewrite unsigned_lit_small by exact R. right. exact Z1.
- apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S DF). lia.
  + intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (AGix.aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

(* Deallocate (YGcfInstF1Wcgif.v:109 dep_keep_d_cgif's twin): KEEP := dg_dzone \/ (dg_czone /\ ~ dg_izone), i.e.
   DGgi.DZONE \/ (AGif0cgif.CZONE /\ ~ DGgi.IZONE) at DImg_cgif. *)
Theorem dep_keep_d_B : forall B, @im_syms AImg_cgif B ->
forall ly S (W : world (@im_segs AImg_cgif)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B ->
depot_fits (as_universe B) (st_depot S) ->
Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem0) ->
(forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/
  (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem).
Proof.
intros B TS ly S W mem0 mem LY IMG TSD DF CST DEP MEQ. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
split.
- apply Forall_forall. intros c Hc.
  apply (AGix.cell_holds_agree B ly TS LY IMG HTSD (aview tfibsegs (w_H W) mem0)); [| exact (proj1 (Forall_forall _ _) CST c Hc)].
  intros k Hk. pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hc Hk) as Z1.
  pose proof (AGix.CZONE_range B ly TS LY IMG HTSD _ Z1) as R.
  apply (AGix.aview_agree W mem0 mem _ R). apply MEQ. rewrite unsigned_lit_small by exact R. right.
  split; [exact Z1 | exact (const_noizone B ly TS LY IMG HTSD c k Hc Hk)].
- apply (AGix.depot_mem_ok_agree B ly TS LY IMG HTSD S (aview tfibsegs (w_H W) mem0)).
  + pose proof (AGix.depot_ids_bound B ly TS LY IMG HTSD S DF). lia.
  + intros a Ha. pose proof (AGix.DZONE_range B ly TS LY IMG HTSD a Ha) as Ra.
    apply (AGix.aview_agree W mem0 mem a Ra). apply MEQ. rewrite unsigned_lit_small by exact Ra. left. exact Ha.
  + exact DEP.
Qed.

End d.
