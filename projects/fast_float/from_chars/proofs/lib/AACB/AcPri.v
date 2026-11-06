(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.

Module AcDepSep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition DT_LO : Z := 0x1c78c0.  Definition DT_HI : Z := 0x5c8a80.
Definition DF_LO : Z := 0x1b78c0.  Definition DF_HI : Z := 0x1b8a80.
Lemma downed_cases : forall D1 B1 x, downed D1 B1 x ->
  (DT_LO <= x < DT_HI) \/ (DF_LO <= x < DF_HI) \/ (D1 <= x < D1 + 1048576) \/ (B1 <= x < B1 + 8388608).
Proof. intros D1 B1 x H. unfold downed, DT_LO, DT_HI, DF_LO, DF_HI in *. lia. Qed.

Definition img_sep_b (fs : list fact) (gs : list (lin * lin * gkind)) (j0 : nat) (sp : lin) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some z => ((Z.leb (b + z) DF_LO || Z.leb DF_HI b) && (Z.leb (b + z) DT_LO || Z.leb DT_HI b))%bool
  | _, _ => (sep_grant_acc fs gs j0 O R || sep_band_b fs sp R || sep_shadow_b fs R)%bool
  end.
Definition dep_sep_b (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jD1 jB1 : nat) (sp D1l B1l : lin)
    (R : region) : bool :=
  (img_sep_b fs gs jD1 sp R && (sep_app2_b fs gs jD1 sp D1l 1048576 R || sep_res_b res R) &&
   (sep_app2_b fs gs jB1 sp B1l 8388608 R || sep_res_b res R))%bool.

(* [comment removed for export] *)
Lemma dep_res : in_res_b (segments_reserved ASEGS) DT_LO DT_HI = true /\ in_res_b (segments_reserved ASEGS) DF_LO DF_HI = true.
Proof. split; vm_compute; reflexivity. Qed.

Section DepSep.
Variable E : valu.
Variable fs : list fact.
Variable gs : list (lin * lin * gkind).
Variable model : Model.
Variable sp : lin.
Variable BL : list (word * word).        (* [comment removed for export] *)
Hypothesis HF : Forall (fact_ok E) fs.
Hypothesis Hmaps : vm_maps (m_vmmaps model) = lden_maps E BL gs.
Hypothesis Hpd : pdisj (vm_maps (m_vmmaps model)).
Hypothesis Hgsh : Forall (gshape_ok E) gs.
Hypothesis Hgtop : Forall (fun g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) gs.
Hypothesis Hsp : vm_init_sp (m_vmmaps model) = lden E sp.
Hypothesis Hsphi : bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi.
Hypothesis Hspok : init_sp_ok (m_vmmaps model).
Hypothesis Hmres : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_reserved (m_vmmaps model)) x = false.
Hypothesis Hres : vm_reserved (m_vmmaps model) = segments_reserved ASEGS.

#[using="Hres"] Lemma res_pts : forall x, (DT_LO <= x < DT_HI) \/ (DF_LO <= x < DF_HI) -> covered (vm_reserved (m_vmmaps model)) x = true.
Proof. LiaFast.lf_pins (fun (Hres : LiaFast.U) => LiaFast.u0).
  intros x Hx. rewrite Hres. destruct dep_res as [R1 R2].
  destruct Hx as [Hx|Hx]; [exact (in_res_sound _ _ _ x R1 Hx) | exact (in_res_sound _ _ _ x R2 Hx)].
Qed.
#[using="model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres Hres"] Lemma img_sep_sym : forall j0 R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  (sep_grant_acc fs gs j0 O R || sep_band_b fs sp R || sep_shadow_b fs R)%bool = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (DT_LO <= w < DT_HI) /\ ~ (DF_LO <= w < DF_HI).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres Hres : LiaFast.U) => LiaFast.u0).
  intros j0 R Hz Hr H w Hw.
  assert (Hsp0 : 0x7fff80000000 <= uE E sp) by (unfold uE; rewrite <- Hsp; unfold init_sp_ok, sp_window_lo in Hspok; lia).
  assert (Hsp1 : uE E sp <= 0x800000000000) by (unfold uE; rewrite <- Hsp; unfold sp_window_hi in Hsphi; lia).
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - destruct (sep_grant_acc_spec fs gs j0 O R H) as (i' & g' & _ & _ & Hn' & Hs1 & Hc & Hmk'). rewrite Nat.sub_0_r in Hn'.
    pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Hw, Hz, Hr. fold (rsz E R) in *.
    rewrite Forall_forall in Hgsh. destruct (Hgsh g' (nth_error_In _ _ Hn')) as (G1 & G2 & G3 & G4 & G5).
    pose proof (gsz_bounds E fs g' HF) as Gb.
    destruct (contained_sound E fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g')) (gsz_lo fs g') HF Hc ltac:(lia) ltac:(unfold two64 in *; lia)) as [C1 C2].
    assert (Hcov : covered (vm_maps (m_vmmaps model)) w = true).
    { apply (grant_pts_covered E gs model BL Hmaps (proj2 (Forall_forall _ _) Hgsh) i' g' (rg_base R) (rsz E R) Hn' Hmk' C1); [unfold rsz in *; lia | exact Hw]. }
    pose proof (Hmres w Hcov) as Hnr. split; intros Hin; [rewrite (res_pts w ltac:(left; exact Hin)) in Hnr | rewrite (res_pts w ltac:(right; exact Hin)) in Hnr]; discriminate.
  - unfold sep_band_b in H. apply orb_prop in H as [H|H].
    + apply Z.leb_le in H. pose proof (irange_sound E fs (lsub sp (rg_base R)) HF) as Rd. fold (uE E (lsub sp (rg_base R))) in Rd.
      destruct (small_diff E sp (rg_base R) _ _ Rd) as [[Hl He]|[Hl He]]; unfold DT_LO, DT_HI, DF_LO, DF_HI; lia.
    + apply Z.ltb_lt in H. pose proof (irange_sound E fs (lsub (rg_base R) sp) HF) as Rd. fold (uE E (lsub (rg_base R) sp)) in Rd.
      pose proof (uE_range E sp). pose proof (uE_range E (rg_base R)).
      destruct (small_diff E (rg_base R) sp _ _ Rd) as [[Hl He]|[Hl He]]; unfold DT_LO, DT_HI, DF_LO, DF_HI, two64 in *; lia.
  - unfold sep_shadow_b in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.leb_le in H.
    pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb. unfold SH_LO, DT_LO, DT_HI, DF_LO, DF_HI in *. lia.
Qed.

#[using="model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres Hres"] Lemma img_sep_sound : forall j0 R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 -> img_sep_b fs gs j0 sp R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (DT_LO <= w < DT_HI) /\ ~ (DF_LO <= w < DF_HI).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hgsh Hsp Hsphi Hspok Hmres Hres : LiaFast.U) => LiaFast.u0).
  intros j0 R Hz Hr H w Hw. unfold img_sep_b in H.
  destruct (is_const (rg_base R)) as [b|] eqn:Hb; destruct (is_const (rg_size R)) as [s0|] eqn:Hs;
    try exact (img_sep_sym j0 R Hz Hr H w Hw).
  destruct (is_const_sound E _ b Hb) as [Hbv Hbr]. destruct (is_const_sound E _ s0 Hs) as [Hsv Hsr].
  assert (HbE : uE E (rg_base R) = b) by (unfold uE; rewrite Hbv; apply fg64'; exact Hbr).
  assert (HsE : rsz E R = s0) by (unfold rsz; rewrite Hsv; apply fg64'; exact Hsr).
  rewrite HbE, HsE in Hw. apply andb_prop in H as [H1 H2]. apply orb_prop in H1, H2.
  unfold DT_LO, DT_HI, DF_LO, DF_HI in *. destruct H1 as [H1|H1]; destruct H2 as [H2|H2]; apply Z.leb_le in H1, H2; lia.
Qed.

(* [comment removed for export] *)
#[using="BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres"] Theorem dep_outside_rgs : forall rgs jD1 jB1 gD1 gB1 D1l B1l,
  Forall (fun R => 0 <= rsz E R /\ uE E (rg_base R) + rsz E R <= two64) rgs ->
  nth_error gs jD1 = Some gD1 -> fst (fst gD1) = D1l -> snd (fst gD1) = lconst 1048576 ->
  nth_error gs jB1 = Some gB1 -> fst (fst gB1) = B1l -> snd (fst gB1) = lconst 8388608 ->
  is_mark gD1 = false -> is_mark gB1 = false ->          (* [comment removed for export] *)
  forallb (dep_sep_b fs gs (vm_reserved (m_vmmaps model)) jD1 jB1 sp D1l B1l) rgs = true ->
  forall x, 0 <= x < two64 -> downed (uE E D1l) (uE E B1l) x -> outside E rgs (Z_to_bv 64 x).
Proof. LiaFast.lf_pins (fun (BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi Hspok Hmres Hres : LiaFast.U) => LiaFast.u0).
  intros rgs jD1 jB1 gD1 gB1 D1l B1l Hsz Hj1 Hb1 Hs1' Hj2 Hb2 Hs2' Hm1 Hm2 Hck x Hx Hdw. unfold outside. rewrite Forall_forall in Hsz |- *.
  assert (Hs1 : gsz E gD1 = 1048576) by (unfold gsz, uE; rewrite Hs1', lden_lconst; apply u_small64; unfold two64; lia).
  assert (Hs2 : gsz E gB1 = 8388608) by (unfold gsz, uE; rewrite Hs2', lden_lconst; apply u_small64; unfold two64; lia).
  rewrite forallb_forall in Hck. intros R HR. specialize (Hck R HR). destruct (Hsz R HR) as [Hz Hr].
  unfold dep_sep_b in Hck. apply andb_prop in Hck as [Hck H3]. apply andb_prop in Hck as [H1 H2].
  rewrite u_small64 by exact Hx.
  destruct (Z_lt_le_dec x (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) x) as [Y|Y]; [right; exact Y|]. exfalso.
  assert (Hw : uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R) by (unfold uE; lia).
  destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]].
  - exact (proj1 (img_sep_sound jD1 R Hz Hr H1 x Hw) D).
  - exact (proj2 (img_sep_sound jD1 R Hz Hr H1 x Hw) D).
  - apply orb_prop in H2 as [H2|H2].
    + apply (sep_app2_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jD1 gD1 D1l 1048576 R Hj1 Hm1) in Hw; [exact (Hw D) | rewrite Hb1; lia | rewrite Hb1, Hs1; lia | unfold two64; lia | exact Hz | exact Hr | exact H2].
    + apply (sep_res_sound E gs model BL Hmaps Hgsh Hmres jD1 gD1 D1l 1048576 R Hj1 Hm1) in Hw; [exact (Hw D) | rewrite Hb1; lia | rewrite Hb1, Hs1; lia | exact H2].
  - apply orb_prop in H3 as [H3|H3].
    + apply (sep_app2_sound E fs gs model sp BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi jB1 gB1 B1l 8388608 R Hj2 Hm2) in Hw; [exact (Hw D) | rewrite Hb2; lia | rewrite Hb2, Hs2; lia | unfold two64; lia | exact Hz | exact Hr | exact H3].
    + apply (sep_res_sound E gs model BL Hmaps Hgsh Hmres jB1 gB1 B1l 8388608 R Hj2 Hm2) in Hw; [exact (Hw D) | rewrite Hb2; lia | rewrite Hb2, Hs2; lia | exact H3].
Qed.
End DepSep.
(* [comment removed for export] *)
End AcDepSep.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CLS : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30].
Definition PRI_LEN : nat := 71.             (* [comment removed for export] *)
Definition PG_SIZE : Z := 0x2000011000.     (* [comment removed for export] *)
Definition TG_SIZE : Z := 0x1000.           (* [comment removed for export] *)

Definition p_nth (a : ast) (k : nat) : lin := nth k (a_pri a) lc0.
Definition p_sb (a : ast) : lin := p_nth a 0.
Definition p_sh (a : ast) : lin := p_nth a 1.
Definition p_ca (a : ast) : lin := p_nth a 2.
Definition p_pg (a : ast) : lin := p_nth a 3.
Definition p_tg (a : ast) : lin := p_nth a 4.
Definition cidx (c : Z) : nat := Z.to_nat (c - 1).
Definition p_j (a : ast) (c : Z) : lin := p_nth a (5 + 2 * cidx c).
Definition p_z (a : ast) (c : Z) : lin := p_nth a (6 + 2 * cidx c).
(* [comment removed for export] *)
Definition p_qj (a : ast) : lin := p_nth a 65.
Definition p_qn (a : ast) : lin := p_nth a 66.
Definition p_qb (a : ast) : lin := p_nth a 67.
(* [comment removed for export] *)
Definition p_gn (a : ast) : lin := p_nth a 68.
Definition p_gl (a : ast) : lin := p_nth a 69.
Definition p_gb (a : ast) : lin := p_nth a 70.
Definition GQ_LO : Z := 930696.
Definition GQ_HI : Z := 930736.
(* [comment removed for export] *)
Definition l_cb (a : ast) : lin := laddc (p_ca a) (-128).
Definition CB_SIZE : Z := 2720.

(* [comment removed for export] *)
Definition zs_of (z : lin) : lin := match ldiv8 z with Some l => l | None => lc0 end.
Definition l_rb (a : ast) (c : Z) : lin := laddc (p_sb a) (4294967296 * c).
Definition l_fa (a : ast) (c : Z) : lin := laddc (p_sb a) (4294967296 * c + 3758096384).
Definition l_shu (a : ast) (c : Z) : lin := laddc (p_sh a) (536870912 * c).
Definition l_shf (a : ast) (c : Z) : lin := laddc (p_sh a) (536870912 * c + 469762048).
Definition l_rip (a : ast) : lin := laddc (p_sb a) 137438953472.
Definition cls_own (a : ast) (c : Z) : list (lin * lin) :=
  [(l_rb a c, p_z a c); (l_fa a c, p_z a c); (l_shu a c, lconst 32768); (l_shf a c, lconst 32768)].
(* [comment removed for export] *)
Definition pri_own (a : ast) : list (lin * lin) :=
  (l_cb a, lconst CB_SIZE) :: (l_rip a, lconst 4096) :: (lconst 930696, lconst 40) :: List.flat_map (cls_own a) CLS.

(* [comment removed for export] *)
Definition zn (pz : list Z) (k : nat) : Z := nth k pz 0.
Definition z_sb (pz : list Z) : Z := zn pz 0.
Definition z_sh (pz : list Z) : Z := zn pz 1.
Definition z_ca (pz : list Z) : Z := zn pz 2.
Definition z_pg (pz : list Z) : Z := zn pz 3.
Definition z_tg (pz : list Z) : Z := zn pz 4.
Definition z_j (pz : list Z) (c : Z) : Z := zn pz (5 + 2 * cidx c).
Definition z_z (pz : list Z) (c : Z) : Z := zn pz (6 + 2 * cidx c).
Definition z_qj (pz : list Z) : Z := zn pz 65.
Definition z_qn (pz : list Z) : Z := zn pz 66.
Definition z_qb (pz : list Z) : Z := zn pz 67.
Definition z_gn (pz : list Z) : Z := zn pz 68.
Definition z_gl (pz : list Z) : Z := zn pz 69.
Definition z_gb (pz : list Z) : Z := zn pz 70.
(* [comment removed for export] *)
Definition q_inv (m0 : word -> option byte) (QC SB qj qn qb : Z) : Prop :=
  0 <= qb < 2^62 /\ rd m0 (QC + 24) 8 qb /\
  ((qn = 0 /\ qb = 0 /\ rd m0 QC 8 0) \/
   (1 <= qn <= 1021 /\ 0 <= qj < 32 /\ rd m0 QC 8 1 /\ rd m0 (QC + 8) 8 (SB + 103079215104 + 8192 * qj) /\
    rd m0 (QC + 16) 8 (SB + 103079215104 + 8192 * qj) /\
    rd m0 (SB + 103079215104 + 8192 * qj + 8) 8 qb /\ rd m0 (SB + 103079215104 + 8192 * qj + 16) 8 qn /\
    wr m0 (SB + 103079215104 + 8192 * qj) 8192)).
(* [comment removed for export] *)
Definition gq_inv_o (m0 : word -> option byte) (SB gn gl gb : Z) : Prop :=
  0 <= gn < 2^32 /\ 0 <= gb < 2^62 /\
  rd m0 930696 4 0 /\ wr m0 930696 4 /\ rd m0 930704 8 gn /\ rd m0 930728 8 gb /\ wr m0 930704 32 /\
  (exists gf, 0 <= gf < 2^64 /\ rd m0 930712 8 gf) /\
  ((gn = 0 /\ exists g0, 0 <= g0 < 2^64 /\ rd m0 930720 8 g0) \/
   (1 <= gn /\ 0 <= gl < 32 /\ rd m0 930720 8 (SB + 103079215104 + 8192 * gl) /\ wr m0 (SB + 103079215104 + 8192 * gl) 8)).
Definition cls_inv (m0 : word -> option byte) (CA SB SH c j z : Z) : Prop :=
  (j = 0 /\ z = 0 /\ VIRG_C m0 CA SB c /\ SHW_C m0 SH c) \/
  (1 <= j /\ z = 262144 /\ j + mc_tbl c / 2 <= 262144 / sz_tbl c /\
   INV_Co m0 CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) j /\ POP_C m0 SB SH c (sz_tbl c) j).
Record INV_Az (pz : list Z) (m0 : word -> option byte) : Prop := {
  iz_len : List.length pz = PRI_LEN ;
  iz_sb : 17594333495296 <= z_sb pz /\ z_sb pz mod 4096 = 0 ;
  iz_sh : z_sh pz = z_sb pz / 8 + 2147450880 ;
  iz_ca : ((4304 <= z_ca pz /\ z_ca pz + 3888 <= 65536) \/ 6537424 <= z_ca pz) /\ z_ca pz mod 16 = 0 /\ z_ca pz + 3888 <= 2^47 ;
  iz_pg : z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + PG_SIZE /\ z_pg pz + PG_SIZE <= 2^47 ;
  iz_tg : z_ca pz = z_tg pz + 208 ;
  iz_nsh : 17594333495296 <= z_pg pz /\ (z_tg pz + 4096 <= 2147446784 \/ 17594333495296 <= z_tg pz) ;   (* [comment removed for export] *)
  iz_st : STATS m0 (z_ca pz) ;
  iz_wc : wr m0 (z_ca pz - 128) 2720 ;
  iz_q : q_inv m0 (z_ca pz - 128) (z_sb pz) (z_qj pz) (z_qn pz) (z_qb pz) /\ (1 <= z_qn pz -> z_qj pz < z_j pz 24) ;
  iz_gq : gq_inv_o m0 (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) /\ (1 <= z_gn pz -> z_gl pz < z_j pz 24) ;
  iz_cls : forall c, In c CLS -> cls_inv m0 (z_ca pz) (z_sb pz) (z_sh pz) c (z_j pz c) (z_z pz c)
}.
(* [comment removed for export] *)
Definition pri_foot_z (pz : list Z) (x : Z) : Prop :=
  z_ca pz - 128 <= x < z_ca pz + 2592 \/
  z_sb pz + 137438953472 <= x < z_sb pz + 137438953472 + 4096 \/
  930696 <= x < 930736 \/
  exists c, In c CLS /\
    (z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + z_z pz c \/
     z_sb pz + 4294967296 * c + 3758096384 <= x < z_sb pz + 4294967296 * c + 3758096384 + z_z pz c \/
     z_sh pz + 536870912 * c <= x < z_sh pz + 536870912 * c + 32768 \/
     z_sh pz + 536870912 * c + 469762048 <= x < z_sh pz + 536870912 * c + 469762048 + 32768).

(* [comment removed for export] *)
Definition FPmax (pz : list Z) (x : Z) : Prop :=
  z_pg pz <= x < z_pg pz + PG_SIZE \/ z_ca pz - 128 <= x < z_ca pz + 2592 \/ z_sh pz <= x < z_sh pz + 17179869184 \/ 930696 <= x < 930736.
Definition pden (E : valu) (a : ast) : list Z := List.map (uE E) (a_pri a).
Definition INV_A (E : valu) (a : ast) (m0 : word -> option byte) : Prop := INV_Az (pden E a) m0.
Definition pri_foot (E : valu) (a : ast) (x : Z) : Prop := pri_foot_z (pden E a) x.

Lemma uE_lc0 : forall E, uE E lc0 = 0.
Proof. intros E. reflexivity. Qed.
Lemma uE_laddc_z : forall E l c, 0 <= uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. intros E l c H. unfold uE in *. rewrite lden_laddc. apply u_small64. exact H. Qed.
Lemma zn_pden : forall E a k, zn (pden E a) k = uE E (p_nth a k).
Proof. intros E a k. unfold zn, pden, p_nth. rewrite <- (uE_lc0 E). apply map_nth. Qed.

Lemma in_cls_rng : forall c, In c CLS -> 1 <= c <= 30.
Proof. intros c H. unfold CLS in H. cbn [In] in H. repeat (destruct H as [<-|H]; [lia|]). destruct H. Qed.
Lemma in_cls_24 : In 24 CLS.
Proof. unfold CLS. cbn [In]. do 23 right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cls_tbl : forall c, In c CLS ->
  32 <= sz_tbl c <= 65536 /\ sz_tbl c = 8 * (sz_tbl c / 8) /\ 4 <= sz_tbl c / 8 <= 8192 /\
  4 <= 262144 / sz_tbl c <= 8192 /\ 262144 / sz_tbl c * sz_tbl c <= 262144 /\ 1 <= mc_tbl c / 2 <= 8.
Proof.
  intros c H. unfold CLS in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [vm_compute; repeat split; first [discriminate | reflexivity]|]). destruct H.
Qed.
Lemma sz_tbl_24 : sz_tbl 24 = 8192.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ext_sem (pz : list Z) (b z : Z) : Prop :=
  (exists c, In c CLS /\ z_sb pz + 4294967296 * c <= b /\ b + z <= z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c /\ b mod 8 = 0) /\
  (* [comment removed for export] *)
  (1 <= z_qn pz -> b + z <= z_sb pz + 103079215104 + 8192 * z_qj pz \/ z_sb pz + 103079215104 + 8192 * z_qj pz + 8192 <= b) /\
  (* [comment removed for export] *)
  (1 <= z_gn pz -> b + z <= z_sb pz + 103079215104 + 8192 * z_gl pz \/ z_sb pz + 103079215104 + 8192 * z_gl pz + 8192 <= b).
Lemma ext_sem_mono : forall pz pz' b z, z_sb pz' = z_sb pz -> (forall c, In c CLS -> z_j pz c <= z_j pz' c) ->
  z_qn pz' = z_qn pz -> z_qj pz' = z_qj pz -> z_gn pz' = z_gn pz -> z_gl pz' = z_gl pz -> ext_sem pz b z -> ext_sem pz' b z.
Proof.
  intros pz pz' b z Hsb Hj Hqn Hqj Hgn Hgl ((c & Hc & H1 & H2 & H3) & HB & HG). split; [|split].
  - exists c. split; [exact Hc|]. rewrite Hsb. split; [exact H1|]. split; [|exact H3].
    pose proof (Hj c Hc) as Hjc. destruct (cls_tbl c Hc) as (Hsz & _). nia.
  - rewrite Hsb, Hqn, Hqj. exact HB.
  - rewrite Hsb, Hgn, Hgl. exact HG.
Qed.
Lemma STATS_frame : forall m m' CA, 0 <= CA -> CA + 4096 <= 2^63 -> (forall x, CA + 2560 <= x < CA + 2592 -> m' (wa x) = m (wa x)) -> STATS m CA -> STATS m' CA.
Proof.
  intros m m' CA H1 H2 HF ((st & Hst & Rst) & (st2 & Hst2 & Rst2) & Wst). split; [|split].
  - exists st. split; [exact Hst|]. apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; lia | exact Rst].
  - exists st2. split; [exact Hst2|]. apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; lia | exact Rst2].
  - apply (wr_frame m); [lia | lia | intros x Hx; apply HF; lia | exact Wst].
Qed.
Lemma gq_inv_o_frame : forall (m0 m0' : word -> option byte) SB gn gl gb, 0 <= SB -> SB + 137438953472 <= 2^63 ->
  (forall x, 930696 <= x < 930736 \/ (1 <= gn /\ SB + 103079215104 + 8192 * gl <= x < SB + 103079215104 + 8192 * gl + 8) -> m0' (wa x) = m0 (wa x)) ->
  gq_inv_o m0 SB gn gl gb -> gq_inv_o m0' SB gn gl gb.
Proof.
  intros m0 m0' SB gn gl gb H1 H2 HF (G1 & G2 & R1 & W1 & R2 & R3 & W2 & (gf & Hgf & R4) & G3).
  split; [exact G1|]. split; [exact G2|]. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R1].
  - apply (wr_frame m0); [lia | lia | intros x Hx; apply HF; left; lia | exact W1].
  - apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R2].
  - apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R3].
  - apply (wr_frame m0); [lia | lia | intros x Hx; apply HF; left; lia | exact W2].
  - exists gf. split; [exact Hgf|]. apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R4].
  - destruct G3 as [(G0 & g0 & Hg0 & R5)|(Gn & Gl & R5 & W5)]; [left | right].
    + split; [exact G0|]. exists g0. split; [exact Hg0|]. apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R5].
    + split; [exact Gn|]. split; [exact Gl|]. split.
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R5].
      * apply (wr_frame m0); [lia | lia | intros x Hx; apply HF; right; split; [exact Gn | lia] | exact W5].
Qed.
Lemma INV_Az_frame : forall pz m0 m0', (forall x, pri_foot_z pz x -> m0' (wa x) = m0 (wa x)) -> INV_Az pz m0 -> INV_Az pz m0'.
Proof.
  intros pz m0 m0' HF [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  assert (B : 0 <= z_ca pz /\ z_ca pz + 4096 <= 2^63 /\ 0 <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= 2^63) by (unfold PG_SIZE in Hpg; lia).
  constructor; try assumption.
  - apply (STATS_frame m0); [lia | lia | | exact Hst]. intros x Hx. apply HF. left. lia.
  - apply (wr_frame m0); [lia | lia | | exact Hwc]. intros x Hx. apply HF. left. lia.
  - destruct Hq as [(Hqb & Rqb & Hq) Hqj]. split; [|exact Hqj]. split; [exact Hqb|]. split.
    { apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact Rqb]. }
    destruct Hq as [(Q0 & Qb0 & R0)|(Q1 & Q2 & R1 & R1b & R2 & R3 & R4 & W1)]; [left | right].
    + split; [exact Q0|]. split; [exact Qb0|]. apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R0].
    + assert (Z24 : z_z pz 24 = 262144).
      { destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [specialize (Hqj ltac:(lia)); lia | exact Z1]. }
      assert (HB : forall x, z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192 -> m0' (wa x) = m0 (wa x)).
      { intros x Hx. apply HF. right. right. right. exists 24. split; [exact in_cls_24|]. left. rewrite Z24. lia. }
      split; [exact Q1|]. split; [exact Q2|]. split; [|split; [|split; [|split; [|split]]]].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R1].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R1b].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; left; lia | exact R2].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HB; lia | exact R3].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HB; lia | exact R4].
      * apply (wr_frame m0); [lia | lia | intros x Hx; apply HB; lia | exact W1].
  - destruct Hgq as [Hg Hgl]. split; [|exact Hgl]. apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(lia) ltac:(lia)); [|exact Hg].
    intros x [Hx|(Hg1 & Hx)]; [apply HF; right; right; left; exact Hx|].
    assert (Z24 : z_z pz 24 = 262144).
    { destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [specialize (Hgl Hg1); destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); lia | exact Z1]. }
    destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [lia|].
    apply HF. right. right. right. exists 24. split; [exact in_cls_24|]. left. rewrite Z24. lia.
  - intros c Hc. pose proof (in_cls_rng c Hc) as Hcr. destruct (cls_tbl c Hc) as (Hsz & Hs8 & Hs8r & Hnw & Hnm & Hmc).
    destruct (Hcls c Hc) as [(J0 & Z0 & HV & HSW)|(J1 & Z1 & Jb & HI & HP)]; [left | right].
    + split; [exact J0|]. split; [exact Z0|]. split.
      * apply (VIRG_C_frame m0); [lia | lia | lia | lia | lia | | exact HV].
        intros x Hx. apply HF. unfold foot_V in Hx. destruct Hx as [Hx|Hx]; [left; lia | right; left; lia].
      * destruct HSW as [W1 W2]. split.
        -- apply (wr_frame m0); [lia | lia | | exact W1]. intros x Hx. apply HF. right. right. right. exists c. split; [exact Hc|]. right. right. left. lia.
        -- apply (wr_frame m0); [lia | lia | | exact W2]. intros x Hx. apply HF. right. right. right. exists c. split; [exact Hc|]. right. right. right. lia.
    + split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
      * apply (INV_Co_frame m0); [lia | lia | lia | lia | | exact HI].
        intros x Hx. apply HF. unfold foot_Co in Hx. destruct Hx as [Hx|[Hx|Hx]]; [left; lia | right; left; lia |].
        right. right. right. exists c. split; [exact Hc|]. right. left. rewrite Z1. lia.
      * apply (POP_C_frame m0); [| nia | exact HP].
        intros x Hx. apply HF. right. right. right. exists c. split; [exact Hc|]. unfold RBX, SHX in Hx.
        assert (0 <= sz_tbl c * z_j pz c) by (apply Z.mul_nonneg_nonneg; lia).
        assert (0 <= sz_tbl c / 8 * z_j pz c) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]).
        destruct Hx as [Hx|Hx]; [left; rewrite Z1; lia | right; right; left; lia].
Qed.
(* [comment removed for export] *)
