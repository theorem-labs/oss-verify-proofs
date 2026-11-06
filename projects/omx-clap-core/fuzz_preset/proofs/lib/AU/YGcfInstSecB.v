(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstSeccgif.v onto omx-clap-core/fuzz_preset's
   asan-ubsan image B' (#102 pin fuzz_preset.asan-ubsan d663f82d7f48, unstripped twin sha256 c90d4fa54d43); module
   paths changed; every image address is this unit's named value (Reusable/YF0m.v TFIB_* / Tfib_const /
   Tfib_owned_static, Reusable/YF0x.v, AU/AGjm.v DZONE, AU/CfImgB.v, AU/AGif0cgif.v, AU/AGif4cgif.v, AU/AGif5.v), and
   no image address is typed in this file. *)
(* The secondary Allocate interfaces of the generic cf instance layer (lib/Reusable/YGcfInstSec.v: ifaceSw_cf, ifaceSE_cf)
   at preset's image B' (AImg_cgif, AGImg_cgif, AImgS_cgif of lib/AU; CfImg_B, CfParams_preset), every image row of
   YGcfInstSec.v's Section b discharged here at a symbol table with TfibSyms (Reusable/YF0m.v), and the two interfaces
   closed at preset's record B := Reusable/YD2l.TfibB with the instance object IOK := (fun i => i = as_inst TfibB).
   - Cited, not restated: the instance cells (CfInstHitImgB.INST_CELLS_B, stated as YGcfInstHit.INST_CELLS_t, the
     same body as YGcfInstSec.INST_CELLS_t), the record's depot hash (CfInstHitImgB.dhash_TfibB_B), the errbuf row
     (CfInstImgB.ERRB_SEP_B), the image cover (YGcfInstF1WB.IMG_COVER_B), the depot contract
     (AFemBx.depot_spec_x_B), the secondary walk's const-cell zone and pad bytes (AGif5.const_cells_CZS / padbI /
     CZS_cgif / CZS_range), the read-write window (AGif5.rw_view, YFff.rw_unhidden), StackDepotPut's footprint
     (AGif5.footprint_DZ), the printf cells' row (CfIalApartPreset.pf_cells_apart_B), the errno rows (ErrnoApartAB,
     ErrnoApartSAB; errno's segment row PresetImg_errnoseg.errno_seg_B; errno's owned-static row at the record,
     PresetImg_errnonst.errno_nstatic_B, a Section hypothesis of the closing section below) and the symbol record
     (YD2l.TfibB_syms).
   - Proved here (no B' file in the tree states them for every B with TfibSyms): the secondary walk's const-cell
     rows, the symbol areas' apartness, the depot zone's rows over AGjm.DZONE, the const / junk table rows and PF_SEP.
   rule 24: no function proved (image rows: closed facts over B''s generated tables, symbol table and class fields). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif2 AllocG AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM03 YG0h YF0p YFff YImgTop YImgCellsB YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoGS ErrnoApart ErrnoApartS CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfErrbSep YGcfImgRows YGcfInstDepot YGcfInstErrno.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG08cf YGcfAbudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YGcfRmodel YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstHit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGif5 AGjm AGis AGhy AFemBx ErrnoApartAB ErrnoApartSAB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfInstImgB CfInstHitImgB YGcfInstF1WB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_errnoseg PresetImg_errnonst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
(* stdpp, through the LPS modules, shadows several list names; the list lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
(* ErrnoGS / ErrnoApartS's Require hazard (their headers): restore lia's euclidean division after the Requires. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Ltac zl := YM03.lf_lia_orig.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Closed checks over B''s tables (Reusable/YF0m.v).                                                                *)

(* No absolute or shadow const cell is in [inst + 408, inst + 416) (the top by_size_log words a request below 2 ^ 30
   can select), none is the out-of-memory byte. *)
Definition abs_ok (c : acell) : bool :=
  match c_at c with
  | ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
      ((e <=? TFIB_INST + 408) || (TFIB_INST + 416 <=? a)) && ((e <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a))
  | _ => false
  end.
Lemma abs_oks : forallb abs_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_dec_B : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. zl. Qed.

Section c.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The symbol table at the image classes.                                                                           *)
Lemma SYM_TSD_B : as_tsd B = im_tsd. Proof. exact (ts_tsd B TS). Qed.
Lemma SYM_OOM_B : as_oom_byte B = im_oom. Proof. exact (ts_oom B TS). Qed.
Lemma SYM_ERRNO_B : as_errno B = im_errno. Proof. exact (ts_errno B TS). Qed.
Lemma INST_AG_B : ag_inst_ok (as_inst B).
Proof.
change (AGif0cgif.inst_ok (as_inst B)). rewrite (ts_inst B TS). unfold AGif0cgif.inst_ok, TFIB_INST.
split; [zl | split; [zl | reflexivity]].
Qed.
Lemma SHB_EQ_B : ImgBaseAGS.SHBv = SHADOW_OFF. Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Where the owned extents are: off the image window and off the shadow band (lo_app).                             *)
Lemma own_off_img : forall ly, layout_ok ly -> YF0x.img_cover ly ->
  forall e a, In e [(ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] ->
  fst e <= a < fst e + snd e -> ~ (YF0x.TFIB_IMG_LO <= a < YF0x.TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros ly LY [I1 I2] e a He Ha.
assert (EO : In e (owned_extents ly)) by (unfold owned_extents; cbn in He |- *; tauto).
pose proof (YGcfInstSec.owned_not_img ly e a LY EO ltac:(unfold in_zr; exact Ha)) as NI.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e EO) as A.
unfold in_zr, in_app, kLowShadowBeg, kHighMemBeg, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in *. cbn [fst snd] in *. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The const cells (Reusable/YF0m.v Tfib_const = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow).           *)
Lemma const_no_bsl_oom : forall ly c k, layout_ok ly -> YF0x.img_cover ly -> ly_tsd ly = TFIB_TSD -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ (TFIB_INST + 408 <= aeval B ly (c_at c) + k < TFIB_INST + 416) /\ aeval B ly (c_at c) + k <> TFIB_OOM.
Proof.
intros ly c k LY IMGC HTSD Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
pose proof (fun a => own_off_img ly LY IMGC (ly_T ly, kThreadObjSize) a ltac:(cbn; tauto)) as OT.
pose proof (fun a => own_off_img ly LY IMGC (ly_C ly, 256) a ltac:(cbn; tauto)) as OC.
pose proof (fun a => own_off_img ly LY IMGC (ly_D ly, 4096) a ltac:(cbn; tauto)) as OD.
cbn [fst snd] in OT, OC, OD.
apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin];
      [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
       match goal with |- ~ (_ <= ?x < _) /\ _ =>
         first [ pose proof (OT x ltac:(unfold kThreadObjSize; zl)) as [OX _]
               | pose proof (OC x ltac:(zl)) as [OX _] | pose proof (OD x ltac:(zl)) as [OX _] | idtac ] end;
       unfold TFIB_TP, TFIB_INST, TFIB_TSD, TFIB_OOM, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, o_space, o_rinfo, o_sec_chunks in *;
       split; zl |]
  | False => destruct Hin
  end.
- clear OT OC OD. pose proof (proj1 (forallb_forall _ _) abs_oks c Hin) as Hc. unfold abs_ok in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval]. cbv zeta in Hc.
  rewrite Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in Hc.
  unfold TFIB_INST, TFIB_OOM in *. split; zl.
Qed.

(* The const bytes miss the words the secondary walk writes: a pad byte of the mutex, or in AGif4.CZS
   (AGif5.const_cells_CZS). *)
Lemma const_byte_B : forall ly c k, layout_ok ly -> YF0x.img_cover ly -> ly_tsd ly = TFIB_TSD -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  let a := aeval B ly (c_at c) + k in
  ~ (ly_Q ly <= a < ly_Q ly + kPtrArrayResv) /\ ~ (ly_T ly + 2768 <= a < ly_T ly + kThreadObjSize) /\
  ~ (TFIB_INST + o_sec_reserved <= a < TFIB_INST + o_sec_sorted + 1) /\ ~ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) /\
  ~ (TFIB_INST + 296 <= a < TFIB_INST + 416) /\ ~ (TFIB_INST + o_sec_mutex <= a < TFIB_INST + o_sec_mutex + 1) /\
  ~ (TFIB_INST + o_comb_stats <= a < TFIB_INST + o_comb_stats + 40) /\ a <> TFIB_OOM.
Proof.
intros ly c k LY IMGC HTSD Hin Hk. cbv zeta.
pose proof (AGif5.const_cells_CZS B TS ly HTSD c k Hin Hk) as X.
pose proof (const_no_bsl_oom ly c k LY IMGC HTSD Hin Hk) as [N1 N2].
set (a := aeval B ly (c_at c) + k) in *.
pose proof (own_off_img ly LY IMGC (ly_Q ly, kPtrArrayResv) a ltac:(cbn; tauto)) as OQ.
pose proof (own_off_img ly LY IMGC (ly_T ly, kThreadObjSize) a ltac:(cbn; tauto)) as OT.
cbn [fst snd] in OQ, OT.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQT.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQC.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQD.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DTC.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DTD.
unfold zdisjoint in DQT, DQC, DQD, DTC, DTD. cbn [fst snd] in DQT, DQC, DQD, DTC, DTD.
pose proof (own_off_img ly LY IMGC (ly_C ly, 256) a ltac:(cbn; tauto)) as OC.
pose proof (own_off_img ly LY IMGC (ly_D ly, 4096) a ltac:(cbn; tauto)) as OD.
cbn [fst snd] in OC, OD.
destruct (AGif5.padbI c).
- unfold TFIB_INST, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats,
    kHighMemBeg in *. zl.
- rewrite AGif5.CZS_cgif in X. unfold AGif5.CZSc in X.
  unfold TFIB_INST, TFIB_TSD, TFIB_OOM, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex,
    o_comb_stats, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
Qed.

(* CONST_APART (YGcfInstSec.v Section b). *)
Lemma CONST_APART_B : forall ly c k, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ YGcfInstSec.gwj B ly (aeval B ly (c_at c) + k).
Proof.
intros ly c k LY IMGC HTSD Hin Hk. rewrite (ts_tsd B TS) in HTSD.
pose proof (const_byte_B ly c k LY IMGC HTSD Hin Hk) as X. cbv zeta in X.
unfold YGcfInstSec.gwj. rewrite (ts_inst B TS). zl.
Qed.

(* CONST_NOT_JUNK (YGcfInstSec.v Section b). *)
Lemma CONST_NOT_JUNK_B : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> im_img_cover ly ->
  ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < cf_malloc_max ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ YGcfInstSec.snull_junk B ly regs0 n (aeval B ly (c_at c) + k).
Proof.
intros ly regs0 n c k LY IMGC HTSD Hinst Hn Hin Hk. rewrite (ts_tsd B TS) in HTSD.
pose proof (const_byte_B ly c k LY IMGC HTSD Hin Hk) as X. cbv zeta in X.
pose proof YG08cf.cf_malloc_max_bound as CB.
pose proof (YGcfInstSec.bsl_bounds regs0 n ltac:(zl)) as BS. rewrite Hinst, (ts_inst B TS) in BS.
unfold YGcfInstSec.snull_junk. rewrite (ts_inst B TS), (ts_oom B TS).
unfold o_sec_sorted, o_sec_stats, o_comb_stats, o_sec_reserved, o_sec_mutex in *. unfold kThreadObjSize in X. zl.
Qed.

(* CONST_KEEP_S (YGcfInstSec.v Section b): the pad bytes from the instance cells, the rest kept as CZS bytes. *)
Lemma CONST_KEEP_S_B : forall ly (H : word -> bool) (mem0 mem : word -> option byte),
  layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem0)) (as_const B ly) ->
  (forall x : word, ims_dzone ly (bv_unsigned x) \/ AGif4.CZS ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview im_segs H mem (as_inst B + o_sec_mutex + k) = Some 0) ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly).
Proof.
intros ly H mem0 mem LY IMG HTSD CF KEEP PAD.
destruct (CfInstHitImgB.INST_CELLS_B B TS ly H mem0 LY HTSD CF) as (_ & _ & _ & _ & _ & _ & _ & C8).
rewrite (ts_tsd B TS) in HTSD. pose proof (ts_inst B TS) as EIN.
apply Forall_forall. intros c Hc.
apply (YGcfInstSec.cell_holds_agree_g B ly (aview im_segs H mem0)); [| exact (proj1 (Forall_forall _ _) CF c Hc)].
intros k Hk. pose proof (AGif5.const_cells_CZS B TS ly HTSD c k Hc Hk) as X.
set (a := aeval B ly (c_at c) + k) in *.
destruct (AGif5.padbI c).
- rewrite EIN in C8, PAD.
  assert (E1 : a = TFIB_INST + o_sec_mutex + (a - (TFIB_INST + o_sec_mutex))) by zl.
  rewrite E1, (PAD (a - (TFIB_INST + o_sec_mutex)) ltac:(zl)).
  assert (E2 : TFIB_INST + o_sec_mutex + (a - (TFIB_INST + o_sec_mutex)) =
               TFIB_INST + o_sec_mutex + 1 + Z.of_nat (Z.to_nat (a - (TFIB_INST + o_sec_mutex + 1)))) by (rewrite Z2Nat.id; zl).
  rewrite E2, (YGcfInstSec.vm_aview_g _ _ _ _ _ _ (Z.to_nat (a - (TFIB_INST + o_sec_mutex + 1))) C8 ltac:(zl)), YGcfInstSec.le_byte_zero.
  reflexivity.
- apply YGcfInstSec.aview_same_g. apply KEEP. right. rewrite EIN.
  assert (U : bv_unsigned (Z_to_bv 64 a) = a) by exact (YG0h.w64_unsigned a (AGif5.CZS_range ly LY a X)).
  rewrite U. exact X.
Qed.

(* AREAS_DISJ (YGcfInstSec.v Section b): the first six areas at TfibSyms' addresses. *)
Lemma AREAS_DISJ_B : pairwise zdisjoint (firstn 6 (asyms_areas B)).
Proof.
unfold asyms_areas. cbn [firstn].
rewrite (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS), (ts_oom B TS).
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM.
cbn [pairwise]. repeat split; repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; zl|]); apply Forall_nil.
Qed.

(* HD (YGcfInstSec.v Section b): the released depot contract at B' (AU/AFemB.v tfib_depot_ok, through AFemBx);
   ims_depot (Reusable/YFl0.v) and AU/AFl0B.v's A_StackDepotPut are both B''s StackDepotPut entry. *)
Lemma HD_B : (forall t, as_dhash B t = YF0p.tfib_dhash t) -> CLdepot.depot_spec_x im_segs ims_depot im_tp im_img_cover B.
Proof. intros HDH. exact (AFemBx.depot_spec_x_B B TS HDH). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Visibility of image bytes: B''s read-write window (AGif5.rw_view, YFff.rw_unhidden).                            *)
Lemma COMB_VIS_B : forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_inst B TS) in Ha. unfold TFIB_INST, o_comb_stats in Ha.
exact (AGif5.rw_view H mem a ltac:(zl)).
Qed.

Lemma ERRNO_VIS_B : forall (H : word -> bool) (mem : word -> option byte) a,
  as_errno B <= a < as_errno B + 4 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_errno B TS) in Ha. unfold TFIB_ERRNO in Ha.
exact (AGif5.rw_view H mem a ltac:(zl)).
Qed.

Lemma DEP_UNHID_B : forall (W : world im_segs) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. rewrite (ts_depot B TS), (ts_store B TS) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
exact (YFff.rw_unhidden W a ltac:(unfold YImgCellsB.B_SEG1_PAGE_HI, YImgTop.IMG_TOP_B; zl)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot zone AGjm.DZONE (AImgS_cgif's ims_dzone).                                                              *)

(* DEP_FP: what StackDepotPut writes is in the zone (AGif5.footprint_DZ). *)
Lemma DEP_FP_B : YGcfInstDepot.dep_fp_img B ims_dzone.
Proof. intros ly a _ _ _ FP. exact (AGif5.footprint_DZ B TS ly a FP). Qed.

(* DZ_LOC: the zone's image part is in the image window and above the instance object, the internal allocator and
   its flag. *)
Lemma DZ_LOC_B : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> ims_dzone ly a ->
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (in_zr a (ly_img ly) /\ ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
   ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2)).
Proof.
intros ly a _ IMG _ Hd. change (YF0x.img_cover ly) in IMG. change (AGjm.DZONE ly a) in Hd. destruct IMG as [I1 I2].
unfold AGjm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]]; [|left; exact Hd|right; left; exact Hd].
right; right. rewrite (ts_inst B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold in_zr, TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in *.
split; [zl | split; [zl | split; zl]].
Qed.

(* DZ_DEC: the zone is three integer ranges. *)
Lemma DZ_DEC_B : forall ly a, ims_dzone ly a \/ ~ ims_dzone ly a.
Proof.
intros ly a. change (AGjm.DZONE ly a \/ ~ AGjm.DZONE ly a). unfold AGjm.DZONE.
match goal with |- ((?l1 <= a < ?h1) \/ (?l2 <= a < ?h2) \/ (?l3 <= a < ?h3)) \/ _ =>
  destruct (zr_dec_B l1 h1 a); [left; left; assumption|];
  destruct (zr_dec_B l2 h2 a); [left; right; left; assumption|];
  destruct (zr_dec_B l3 h3 a); [left; right; right; assumption|]
end.
right. tauto.
Qed.

(* DZ_OWN: an image byte of the zone is in the owned static entry that covers the zone's image part (found by value
   over Tfib_owned_static); the node and store blocks (static extents 4 and 5) are apart from the image window
   (extent 9, lo_disj). *)
Lemma DZ_OWN_B : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a -> in_zr a (ly_img ly) -> Exists (in_zr a) (as_owned_static B).
Proof.
intros ly a LY _ _ Hd Hi. change (AGjm.DZONE ly a) in Hd. unfold AGjm.DZONE in Hd.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 4 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 5 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB.
unfold zdisjoint, in_zr in DNB, DSB, Hi. cbn [fst snd] in DNB, DSB.
rewrite (ts_owned B TS). apply Exists_exists.
destruct Hd as [Hd|[Hd|Hd]]; [|exfalso; zl|exfalso; zl].
match type of Hd with ?lo <= _ < ?hi =>
  assert (E : existsb (fun r => (fst r <=? lo) && (hi <=? fst r + snd r)) Tfib_owned_static = true)
    by (clear; vm_compute; reflexivity)
end.
apply existsb_exists in E as (r & Hr & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
exists r. split; [exact Hr | unfold in_zr; zl].
Qed.

(* PF_SEP: Printf's two cells are below the store, not the out-of-memory byte (CfIalApartPreset.pf_cells_apart_B),
   and inside the image window, which the node and store blocks miss. *)
Lemma PF_SEP_B : YGcfInstSec.PF_SEP_t B.
Proof.
intros ly a LY IMG _ Ha. change (YF0x.img_cover ly) in IMG. destruct IMG as [I1 I2].
destruct (CfIalApartPreset.pf_cells_apart_B B TS a Ha) as (A1 & A2 & _).
split; [exact A2|]. change (~ AGjm.DZONE ly a). unfold AGjm.DZONE. rewrite (ts_store B TS) in A1. unfold TFIB_STORE in A1.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 4 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 5 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB.
unfold zdisjoint in DNB, DSB. cbn [fst snd] in DNB, DSB.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_B] in Ha.
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in *. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Geometry facts at AImgS_cgif's fields.                                                                           *)
Lemma ZONE3_B : forall ly x sz, im_img_cover ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) ->
  ims_zone3 x sz.
Proof. intros ly x sz IMG Hsz A D. exact (YF0x.zone3_intro ly x sz IMG Hsz A D). Qed.

Lemma WFRAME_SP_B : forall W ly regs0 mem0 tr, ims_wframe W ly regs0 mem0 tr ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Proof.
intros W ly regs0 mem0 tr H. change (AGif0cgif.wframe W ly regs0 mem0 tr) in H. destruct H as ((H1 & _ & H3 & _) & _).
unfold ImgBaseAGS.AFSTACK. unfold AGhy.AFSTACK in H1. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The const and junk tables.                                                                                       *)
Lemma CONST_LY_B : forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros ly1 ly2. rewrite !(ts_const B TS). reflexivity. Qed.

Lemma CONST_LT_B : forall ly nn, Forall (cell_lt nn) (as_const B ly).
Proof.
intros ly nn. rewrite (ts_const B TS ly). clear. unfold Tfib_const, Tfib_const_sym, Tfib_const_abs, Tfib_const_shadow. cbn [app].
repeat (apply Forall_cons; [exact (conj I I)|]). apply Forall_nil.
Qed.

Lemma JUNK_LY_B : forall ly1 ly2, as_junk B ly1 = as_junk B ly2.
Proof. intros ly1 ly2. exact (ts_junk_ly B TS ly2 ly1). Qed.

Lemma JUNK_LT_B : forall ly nn, Forall (fun r => asec_lt nn (fst r)) (as_junk B ly).
Proof. intros ly nn. apply Forall_forall. intros r Hr. destruct (ts_junk B TS ly r Hr) as (zz & -> & _). exact I. Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The closing theorems: YGcfInstSec's two interfaces at B''s image classes, at any symbol table with TfibSyms and   *)
(* the record's depot hash, then at preset's record TfibB.                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section close.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.
(* errno's owned-static row: PresetImg_errnonst.errno_nstatic_B states it at the record YD2l.TfibB only. *)
Hypothesis ERR_NST : YGcfInstErrno.errno_nstatic_t B.

Local Ltac rows :=
  first [ exact TS | exact IOK_inst | exact YGcfInstF1WB.IMG_COVER_B
  | exact (PresetImg_errnoseg.errno_seg_B B TS) | exact ERR_NST
  | exact (CfInstImgB.ERRB_SEP_B B TS) | exact (PF_SEP_B B TS)
  | exact (CfInstHitImgB.INST_CELLS_B B TS) | exact (CONST_KEEP_S_B B TS) | exact (CONST_APART_B B TS)
  | exact (CONST_NOT_JUNK_B B TS) | exact (AREAS_DISJ_B B TS) | exact (HD_B B TS HDH)
  | exact (SYM_TSD_B B TS) | exact (SYM_OOM_B B TS) | exact (SYM_ERRNO_B B TS) | exact (INST_AG_B B TS)
  | exact SHB_EQ_B | exact (COMB_VIS_B B TS) | exact (ERRNO_VIS_B B TS) | exact (DEP_UNHID_B B TS)
  | exact ZONE3_B | exact WFRAME_SP_B | exact (DEP_FP_B B TS) | exact (DZ_LOC_B B TS) | exact DZ_DEC_B
  | exact (DZ_OWN_B B TS) | exact (CONST_LY_B B TS) | exact (CONST_LT_B B TS) | exact (JUNK_LY_B B TS)
  | exact (JUNK_LT_B B TS)
  | exact ErrnoApartAB.errno_in_img_cgif | exact ErrnoApartAB.errno_unhidden_cgif
  | exact ErrnoApartAB.errno_apart_inst_ag_cgif | exact ErrnoApartSAB.errno_apart_dzone_s_cgif
  | exact ErrnoApartSAB.errno_apart_shadow_s_cgif | exact ErrnoApartSAB.errno_apart_zone3_s_cgif ].

(* AIfaceSw at NMAXW = cf_malloc_max, NOBW = cf_nob = 2 ^ 29 (CfParams_preset) and ROOMW = 2 ^ 30 <= CF_HEAD. *)
Theorem ifaceSw_B : forall Hp, AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30).
Proof.
intros Hp.
assert (G : AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max cf_nob (2 ^ 30)).
{ eapply YGcfInstSec.ifaceSw_cf; [rows ..|].
  unfold YGcfAbudget.CF_HEAD. apply Z.leb_le. vm_compute. reflexivity. }
exact G.
Qed.

Theorem ifaceSE_B : forall Hp, ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp.
assert (G : ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow).
{ eapply YGcfInstSec.ifaceSE_cf; rows. }
exact G.
Qed.
End close.

(* ---- At preset's record B := Reusable/YD2l.TfibB and IOK := (fun i => i = as_inst TfibB): the symbol record is
   YD2l.TfibB_syms, the depot hash CfInstHitImgB.dhash_TfibB_B (YD2l.v's as_dhash := tfib_dhash), and the instance
   object below. ---- *)
Lemma IOK_inst_TfibB_B : IOK_ok YD2l.TfibB (fun i => i = as_inst YD2l.TfibB).
Proof. intros i H. exact H. Qed.

Theorem ifaceSw_TfibB_B : forall Hp, AGif4.AIfaceSw YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
  (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
  cf_malloc_max LIVE_MAX qtight (dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30).
Proof.
intros Hp. eapply (ifaceSw_B YD2l.TfibB (fun i => i = as_inst YD2l.TfibB));
  first [ exact YD2l.TfibB_syms | exact IOK_inst_TfibB_B | exact CfInstHitImgB.dhash_TfibB_B
        | exact PresetImg_errnonst.errno_nstatic_B ].
Qed.

Theorem ifaceSE_TfibB_B : forall Hp, ErrnoGS.AIfaceSE YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
  (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
  cf_malloc_max LIVE_MAX qtight (dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp. eapply (ifaceSE_B YD2l.TfibB (fun i => i = as_inst YD2l.TfibB));
  first [ exact YD2l.TfibB_syms | exact IOK_inst_TfibB_B | exact CfInstHitImgB.dhash_TfibB_B
        | exact PresetImg_errnonst.errno_nstatic_B ].
Qed.

End a.
