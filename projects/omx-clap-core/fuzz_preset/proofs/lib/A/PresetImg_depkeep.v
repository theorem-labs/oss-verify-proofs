(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_depkeep.v (commit eb934de95d13, blob f06eb40b21d5) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); the depot premise is the layer's depot_fits (preset's universe has wild prefixes, Reusable/YCej.v Tfib_wild); the section-c helpers are AGix's (one text per fact). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA ADIfaceA.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGis DGgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGix.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H;
  pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END,
  kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].

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

Local Set Default Proof Using "All".
Section c.
Variables (B : asyms) (ly : alayout).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.

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

Theorem dep_keep_a_A : forall B, @im_syms AImg_A B ->
forall ly S (W : world (@im_segs AImg_A)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B ->

depot_fits (as_universe B) (st_depot S) ->
Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem0) ->
(forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem).
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

Theorem dep_keep_d_A : forall B, @im_syms AImg_A B ->
forall ly S (W : world (@im_segs AImg_A)) (mem0 mem : word -> option byte),
layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B ->

depot_fits (as_universe B) (st_depot S) ->
Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem0) ->
(forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/
  (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem).
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
