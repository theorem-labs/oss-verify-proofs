(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstSeccgif.v onto omx-clap-core/fuzz_preset's
   asan image A' (#102 pin fuzz_preset.asan 1be0f53d96cb, unstripped twin sha256 bff8519bbe3e); module paths changed;
   every image address is this unit's named value (A/AF0m.v TFIB_* / Tfib_const / Tfib_owned_static, A/AF0x.v,
   A/AGjm.v DZONE, A/CfImgA.v, A/AGImgA.v, A/AGImgSA.v), and no image address is typed in this file. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/YGcfInstSecA.v, with its module paths changed. *)
(* Modified by Theorem Labs: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstSeccgif.v onto omx-clap-core/fuzz_preset's
   asan image A' (#102 pin fuzz_preset.asan 1be0f53d96cb, unstripped twin sha256 bff8519bbe3e); module paths changed;
   every image address is this unit's named value (A/AF0m.v TFIB_* / Tfib_const / Tfib_owned_static, A/AF0x.v,
   A/AGjm.v DZONE, A/CfImgA.v, A/AGImgA.v, A/AGImgSA.v), and no image address is typed in this file. *)
(* The secondary Allocate interfaces of the generic cf instance layer (lib/Reusable/YGcfInstSec.v: ifaceSw_cf, ifaceSE_cf)
   at preset's image A' (AImg_A, AGImg_A, AImgS_A; CfImg_A, CfParams_preset), every image row of YGcfInstSec.v's
   Section b discharged here at a symbol table with TfibSyms, and the two interfaces closed at preset's record
   B := A/AD2l.TfibB with the instance object IOK := (fun i => i = as_inst TfibB).
   - Cited, not restated: the instance cells (CfInstHitImgA.INST_CELLS_A), the image cover (ADIfaceA.img_cover_A),
     the depot contract (YGcfInstF1WA.depot_spec_a_A) and its footprint (YGcfInstF1WA.dep_fp_a_A), errno's segment
     and owned-static rows (YGcfInstF1WA.errno_seg_A / errno_nstatic_A), the errbuf row (CfInstImgA.ERRB_SEP_A), the
     depot zone's owned part and its apartness (CfInstImgA.dzone_owned_ag_A / dzone_apart_ag_A), the printf cells'
     row (CfIalApartPreset.pf_cells_apart_A), the instance window (ADIfaceA.inst_ok_TFIB_INST_A), the constant cells'
     zone (AGix.const_cells_zone / CZONE_range) and the errno rows (ErrnoApartA, ErrnoApartSA).
   - Proved here: the secondary walk's const-cell rows (CONST_KEEP_S / CONST_APART / CONST_NOT_JUNK, over a closed
     check of Tfib_const_abs / Tfib_const_shadow against the instance words the walk writes), the symbol areas'
     apartness, the visibility rows (AB13.tfib_rw_rom, AFff.rw_unhidden), the depot zone's rows over AGjm.DZONE, the
     const / junk table rows and PF_SEP.
   rule 24: no function proved (image rows: closed facts over A''s generated tables, symbol table and class fields). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif2 AllocG AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM03 YG0h YF0p ErrnoGS ErrnoApart ErrnoApartS CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfErrbSep YGcfImgRows YGcfInstDepot YGcfInstErrno.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG08cf YGcfAbudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YGcfRmodel YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstHit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB13 AFff AGjm AGis AGhy AGix AD2l ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfInstImgA CfInstHitImgA CfIalApartPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ErrnoApartA ErrnoApartSA YGcfInstF1WA.
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
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Closed checks over A''s absolute and shadow constant cells (A/AF0m.v Tfib_const_abs / Tfib_const_shadow).        *)

(* None is in [inst + 408, inst + 416) (the top by_size_log words a request below 2 ^ 30 can select), none is the
   out-of-memory byte. *)
Definition abs_ok (c : acell) : bool :=
  match c_at c with
  | ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
      ((e <=? TFIB_INST + 408) || (TFIB_INST + 416 <=? a)) && ((e <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a))
  | _ => false
  end.
Lemma abs_oks : forallb abs_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

(* The mutex's three pad bytes [inst + o_sec_mutex + 1, + 4). *)
Definition padbA (c : acell) : bool :=
  match c_at c with
  | ANum a => (TFIB_INST + o_sec_mutex + 1 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? TFIB_INST + o_sec_mutex + 4)
  | _ => false
  end.
(* Each is a pad-byte cell or misses the five instance windows AGif4.CZS leaves out (the secondary counters and the
   sorted byte, the stats, the by_size_log words, the mutex word and the combined stats). *)
Definition win_ok (c : acell) : bool :=
  match c_at c with
  | ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
      padbA c ||
      (((e <=? TFIB_INST + o_sec_reserved) || (TFIB_INST + o_sec_sorted + 1 <=? a)) &&
       ((e <=? TFIB_INST + o_sec_stats) || (TFIB_INST + o_sec_stats + 32 <=? a)) &&
       ((e <=? TFIB_INST + 296) || (TFIB_INST + 408 <=? a)) &&
       ((e <=? TFIB_INST + o_sec_mutex) || (TFIB_INST + o_sec_mutex + 4 <=? a)) &&
       ((e <=? TFIB_INST + o_comb_stats) || (TFIB_INST + o_comb_stats + 40 <=? a)))
  | _ => false
  end.
Lemma win_oks : forallb win_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

(* A byte of a segment's read-only content is visible in every view (A/AGimW.v:291 aview_rw_some's script). *)
Lemma view_of_rom_A : forall (H : word -> bool) (mem : word -> option byte) a,
  seg_rom tfibsegs (Z_to_bv 64 a) <> None -> aview tfibsegs H mem a <> None.
Proof.
intros H mem a X. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); cbn; [discriminate|].
destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.

Lemma zr_dec_A : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. zl. Qed.

(* AGif4.CZS at A' from AGImgA.CZONE and the five instance windows.  AImgS_A's ims_img_end / ims_shb / ims_csh_end
   are CZONE's image end and shadow window and AImg_A's im_tsd is TFIB_TSD, so each CZONE disjunct is the CZS
   disjunct by conversion; the image part is split at the five windows. *)
Lemma CZS_A_intro : forall ly a, AGImgA.CZONE ly a ->
  ~ (TFIB_INST + o_sec_reserved <= a < TFIB_INST + o_sec_sorted + 1) ->
  ~ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) -> ~ (TFIB_INST + 296 <= a < TFIB_INST + 408) ->
  ~ (TFIB_INST + o_sec_mutex <= a < TFIB_INST + o_sec_mutex + 4) ->
  ~ (TFIB_INST + o_comb_stats <= a < TFIB_INST + o_comb_stats + 40) -> AGif4.CZS ly TFIB_INST a.
Proof.
intros ly a CZ N1 N2 N3 N4 N5. unfold AGif4.CZS. unfold AGImgA.CZONE in CZ.
destruct CZ as [C|[C|[C|[C|[C|C]]]]].
- left.
  destruct (Z_lt_le_dec a (TFIB_INST + o_sec_reserved)) as [L1|G1]; [left; split; [exact (proj1 C) | exact L1]|].
  destruct (Z_lt_le_dec a (TFIB_INST + o_sec_stats)) as [L2|G2]; [right; left; zl|].
  destruct (Z_lt_le_dec a (TFIB_INST + 296)) as [L3|G3]; [do 2 right; left; zl|].
  destruct (Z_lt_le_dec a (TFIB_INST + o_sec_mutex)) as [L4|G4]; [do 3 right; left; zl|].
  destruct (Z_lt_le_dec a (TFIB_INST + o_comb_stats)) as [L5|G5]; [do 4 right; left; zl|].
  do 5 right. split; [zl | exact (proj2 C)].
- right; left; exact C.
- do 2 right; left; exact C.
- do 3 right; left; exact C.
- do 4 right; left; exact C.
- do 5 right; exact C.
Qed.

(* AImgS_A's image end and AImg_A's TSD slot as A''s names; the shadow window [ims_shb, ims_csh_end) inside the
   shadow band [kLowShadowBeg, kHighMemBeg) (each closed by computation). *)
Lemma ims_img_end_A : ims_img_end = AF0x.TFIB_IMG_END. Proof. reflexivity. Qed.
Lemma im_tsd_A : im_tsd = TFIB_TSD. Proof. reflexivity. Qed.
Lemma ims_shadow_A : kLowShadowBeg <= ims_shb /\ ims_csh_end <= kHighMemBeg.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Section c.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The symbol table at the image classes.                                                                           *)
Lemma SYM_TSD_A : as_tsd B = im_tsd. Proof. exact (ts_tsd B TS). Qed.
Lemma SYM_OOM_A : as_oom_byte B = im_oom. Proof. exact (ts_oom B TS). Qed.
Lemma SYM_ERRNO_A : as_errno B = im_errno. Proof. exact (ts_errno B TS). Qed.
Lemma INST_AG_A : ag_inst_ok (as_inst B).
Proof. change (AGImgA.inst_ok (as_inst B)). rewrite (ts_inst B TS). exact ADIfaceA.inst_ok_TFIB_INST_A. Qed.
Lemma SHB_EQ_A : ImgBaseAGS.SHBv = SHADOW_OFF. Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Where the owned extents are: off the image window and off the shadow band (lo_app).                             *)
Lemma own_off_img : forall ly, layout_ok ly -> AF0x.img_cover ly ->
  forall e a, In e [(ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] ->
  fst e <= a < fst e + snd e -> ~ (AF0x.TFIB_IMG_LO <= a < AF0x.TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros ly LY [I1 I2] e a He Ha.
assert (EO : In e (owned_extents ly)) by (unfold owned_extents; cbn in He |- *; tauto).
pose proof (YGcfInstSec.owned_not_img ly e a LY EO ltac:(unfold in_zr; exact Ha)) as NI.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e EO) as A.
unfold in_zr, in_app, kLowShadowBeg, kHighMemBeg, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *. cbn [fst snd] in *. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The const cells (A/AF0m.v Tfib_const = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow).                  *)
Lemma const_no_bsl_oom : forall ly c k, layout_ok ly -> AF0x.img_cover ly -> ly_tsd ly = TFIB_TSD -> In c (as_const B ly) ->
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
       unfold TFIB_TP, TFIB_INST, TFIB_TSD, TFIB_OOM, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, o_space, o_rinfo, o_sec_chunks in *;
       split; zl |]
  | False => destruct Hin
  end.
- clear OT OC OD. pose proof (proj1 (forallb_forall _ _) abs_oks c Hin) as Hc. unfold abs_ok in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval]. cbv zeta in Hc.
  rewrite Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in Hc.
  unfold TFIB_INST, TFIB_OOM in *. split; zl.
Qed.

(* Where a const byte is: a pad byte of the mutex, or in AGif4.CZS (A''s AGju.const_cells_CZ, stated as AU/AGif5.v's
   const_cells_CZS). *)
Lemma const_cells_CZS_A : forall ly, layout_ok ly -> AF0x.img_cover ly -> ly_tsd ly = TFIB_TSD ->
  forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  if padbA c then TFIB_INST + o_sec_mutex + 1 <= aeval B ly (c_at c) + k < TFIB_INST + o_sec_mutex + 4
  else AGif4.CZS ly TFIB_INST (aeval B ly (c_at c) + k).
Proof.
intros ly LY IMG HTSD c k Hin Hk.
pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hin Hk) as CZ.
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
apply in_app_iff in Hin as [Hin|Hin].
- (* the symbol cells: each in one CZS disjunct (the thread / context / TSD / D cells, the instance cells below the
     counters, the thread-pointer cells above the combined stats), as AU/AGif5.v's const_cells_CZS picks them *)
  clear CZ. unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin];
      [cbn [padbA c_at c_w aeval aoff z8 z4 z1 c8 c4 c1]; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
       unfold AGif4.CZS; rewrite ims_img_end_A, im_tsd_A;
       unfold TFIB_TP, TFIB_INST, TFIB_TSD, AF0x.TFIB_IMG_END, o_space, o_rinfo, o_sec_chunks, o_sec_reserved,
         o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, kStackSpan in *;
       first [ do 2 right; left; zl | do 3 right; left; zl | do 4 right; left; zl | do 5 right; zl
             | left; left; zl | left; do 5 right; zl ] |]
  | False => destruct Hin
  end.
- (* the absolute and shadow cells: CZONE (AGix.const_cells_zone) less the five windows (win_oks) *)
  pose proof (proj1 (forallb_forall _ _) win_oks c Hin) as Hc. unfold win_ok in Hc. unfold padbA in Hc |- *.
  destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval] in CZ |- *. cbv beta iota zeta in Hc |- *.
  destruct ((TFIB_INST + o_sec_mutex + 1 <=? z) && (z + Z.max 1 (Z.of_nat (c_w c)) <=? TFIB_INST + o_sec_mutex + 4))
    eqn:P.
  + apply andb_prop in P as [P1 P2]. apply Z.leb_le in P1, P2. zl.
  + cbn [orb] in Hc. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in Hc.
    apply CZS_A_intro; [exact CZ | zl ..].
Qed.

(* The const bytes miss the words the secondary walk writes (AGif5.const_cells_CZS's consumers, cgif's script). *)
Lemma const_byte_A : forall ly c k, layout_ok ly -> AF0x.img_cover ly -> ly_tsd ly = TFIB_TSD -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  let a := aeval B ly (c_at c) + k in
  ~ (ly_Q ly <= a < ly_Q ly + kPtrArrayResv) /\ ~ (ly_T ly + 2768 <= a < ly_T ly + kThreadObjSize) /\
  ~ (TFIB_INST + o_sec_reserved <= a < TFIB_INST + o_sec_sorted + 1) /\ ~ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) /\
  ~ (TFIB_INST + 296 <= a < TFIB_INST + 416) /\ ~ (TFIB_INST + o_sec_mutex <= a < TFIB_INST + o_sec_mutex + 1) /\
  ~ (TFIB_INST + o_comb_stats <= a < TFIB_INST + o_comb_stats + 40) /\ a <> TFIB_OOM.
Proof.
intros ly c k LY IMGC HTSD Hin Hk. cbv zeta.
pose proof (const_cells_CZS_A ly LY IMGC HTSD c k Hin Hk) as X.
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
destruct (padbA c).
- unfold TFIB_INST, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats,
    kHighMemBeg in *. zl.
- pose proof ims_shadow_A as [SH1 SH2].
  unfold AGif4.CZS in X. rewrite ims_img_end_A, im_tsd_A in X.
  unfold TFIB_INST, TFIB_TSD, TFIB_OOM, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex,
    o_comb_stats, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv in *. zl.
Qed.

(* CONST_APART (YGcfInstSec.v Section b). *)
Lemma CONST_APART_A : forall ly c k, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ YGcfInstSec.gwj B ly (aeval B ly (c_at c) + k).
Proof.
intros ly c k LY IMGC HTSD Hin Hk. rewrite (ts_tsd B TS) in HTSD.
pose proof (const_byte_A ly c k LY IMGC HTSD Hin Hk) as X. cbv zeta in X.
unfold YGcfInstSec.gwj. rewrite (ts_inst B TS). zl.
Qed.

(* CONST_NOT_JUNK (YGcfInstSec.v Section b). *)
Lemma CONST_NOT_JUNK_A : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> im_img_cover ly ->
  ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < cf_malloc_max ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ YGcfInstSec.snull_junk B ly regs0 n (aeval B ly (c_at c) + k).
Proof.
intros ly regs0 n c k LY IMGC HTSD Hinst Hn Hin Hk. rewrite (ts_tsd B TS) in HTSD.
pose proof (const_byte_A ly c k LY IMGC HTSD Hin Hk) as X. cbv zeta in X.
pose proof YG08cf.cf_malloc_max_bound as CB.
pose proof (YGcfInstSec.bsl_bounds regs0 n ltac:(zl)) as BS. rewrite Hinst, (ts_inst B TS) in BS.
unfold YGcfInstSec.snull_junk. rewrite (ts_inst B TS), (ts_oom B TS).
unfold o_sec_sorted, o_sec_stats, o_comb_stats, o_sec_reserved, o_sec_mutex in *. unfold kThreadObjSize in X. zl.
Qed.

(* CONST_KEEP_S (YGcfInstSec.v Section b): the pad bytes from the instance cells, the rest kept as CZS bytes. *)
Lemma CONST_KEEP_S_A : forall ly (H : word -> bool) (mem0 mem : word -> option byte),
  layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem0)) (as_const B ly) ->
  (forall x : word, ims_dzone ly (bv_unsigned x) \/ AGif4.CZS ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview im_segs H mem (as_inst B + o_sec_mutex + k) = Some 0) ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly).
Proof.
intros ly H mem0 mem LY IMG HTSD CF KEEP PAD.
destruct (CfInstHitImgA.INST_CELLS_A B TS ly H mem0 LY HTSD CF) as (_ & _ & _ & _ & _ & _ & _ & C8).
rewrite (ts_tsd B TS) in HTSD. change (AF0x.img_cover ly) in IMG. pose proof (ts_inst B TS) as EIN.
apply Forall_forall. intros c Hc.
apply (YGcfInstSec.cell_holds_agree_g B ly (aview im_segs H mem0)); [| exact (proj1 (Forall_forall _ _) CF c Hc)].
intros k Hk. pose proof (const_cells_CZS_A ly LY IMG HTSD c k Hc Hk) as X.
pose proof (AGix.CZONE_range B ly TS LY IMG HTSD _ (AGix.const_cells_zone B ly TS LY IMG HTSD c k Hc Hk)) as RG.
set (a := aeval B ly (c_at c) + k) in *.
destruct (padbA c).
- rewrite EIN in C8, PAD.
  assert (E1 : a = TFIB_INST + o_sec_mutex + (a - (TFIB_INST + o_sec_mutex))) by zl.
  rewrite E1, (PAD (a - (TFIB_INST + o_sec_mutex)) ltac:(zl)).
  assert (E2 : TFIB_INST + o_sec_mutex + (a - (TFIB_INST + o_sec_mutex)) =
               TFIB_INST + o_sec_mutex + 1 + Z.of_nat (Z.to_nat (a - (TFIB_INST + o_sec_mutex + 1)))) by (rewrite Z2Nat.id; zl).
  rewrite E2, (YGcfInstSec.vm_aview_g _ _ _ _ _ _ (Z.to_nat (a - (TFIB_INST + o_sec_mutex + 1))) C8 ltac:(zl)), YGcfInstSec.le_byte_zero.
  reflexivity.
- apply YGcfInstSec.aview_same_g. apply KEEP. right. rewrite EIN.
  assert (U : bv_unsigned (Z_to_bv 64 a) = a) by exact (YG0h.w64_unsigned a RG).
  rewrite U. exact X.
Qed.

(* AREAS_DISJ (YGcfInstSec.v Section b): the first six areas at TfibSyms' addresses. *)
Lemma AREAS_DISJ_A : pairwise zdisjoint (firstn 6 (asyms_areas B)).
Proof.
unfold asyms_areas. cbn [firstn].
rewrite (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS), (ts_oom B TS).
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM.
cbn [pairwise]. repeat split; repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; zl|]); apply Forall_nil.
Qed.

(* HD (YGcfInstSec.v Section b): the released depot contract at A' (A/AFem.v tfib_depot_ok, through YGcfInstF1WA);
   ims_depot and ag_depot_put are both AFl0.A_StackDepotPut. *)
Lemma HD_A : (forall t, as_dhash B t = YF0p.tfib_dhash t) -> CLdepot.depot_spec_x im_segs ims_depot im_tp im_img_cover B.
Proof. intros HDH. exact (YGcfInstF1WA.depot_spec_a_A B TS HDH). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Visibility of image bytes.                                                                                       *)

(* COMB_VIS: the combined allocator's stats words are segment bytes (AB13.tfib_rw_rom). *)
Lemma COMB_VIS_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_inst B TS) in Ha. change im_segs with tfibsegs.
apply view_of_rom_A. apply AB13.tfib_rw_rom. unfold TFIB_INST, o_comb_stats in Ha. zl.
Qed.

(* ERRNO_VIS: errno's four bytes are segment bytes (YGcfInstF1WA.errno_seg_A). *)
Lemma ERRNO_VIS_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_errno B <= a < as_errno B + 4 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. change im_segs with tfibsegs.
apply view_of_rom_A. exact (YGcfInstF1WA.errno_seg_A B TS a Ha).
Qed.

(* DEP_UNHID: the depot's table and its store lie in A''s read-write window (AFff.rw_unhidden). *)
Lemma DEP_UNHID_A : forall (W : world im_segs) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. rewrite (ts_depot B TS), (ts_store B TS) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
exact (AFff.rw_unhidden W a ltac:(zl)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot zone AGjm.DZONE (AImgS_A's ims_dzone; the same three ranges as AGis.DZONE, AGImg_A's ag_dzone).        *)
Lemma dz_ag_A : forall ly a, ims_dzone ly a -> ag_dzone ly a.
Proof. intros ly a Hd. change (AGjm.DZONE ly a) in Hd. change (AGis.DZONE ly a). unfold AGjm.DZONE in Hd. exact Hd. Qed.

(* DEP_FP: StackDepotPut's footprint is in the depot zone (YGcfInstF1WA.dep_fp_a_A over ag_dzone). *)
Lemma DEP_FP_A : YGcfInstDepot.dep_fp_img B ims_dzone.
Proof.
intros ly a LY IMG TSD FP. pose proof (YGcfInstF1WA.dep_fp_a_A B TS ly a LY IMG TSD FP) as X.
change (AGis.DZONE ly a) in X. change (AGjm.DZONE ly a). unfold AGis.DZONE in X. exact X.
Qed.

(* DZ_LOC: the zone's image part is in the image window and apart from the instance object, the internal allocator
   and its flag (CfInstImgA.dzone_apart_ag_A). *)
Lemma DZ_LOC_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> ims_dzone ly a ->
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (in_zr a (ly_img ly) /\ ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
   ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2)).
Proof.
intros ly a LY IMG _ Hd. pose proof (CfInstImgA.dzone_apart_ag_A B TS ly a LY IMG (dz_ag_A ly a Hd)) as AP.
change (AF0x.img_cover ly) in IMG. change (AGjm.DZONE ly a) in Hd. destruct IMG as [I1 I2].
unfold AGjm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]]; [|left; exact Hd|right; left; exact Hd].
right; right. split; [|exact AP]. unfold in_zr, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *. zl.
Qed.

(* DZ_DEC: the zone is three integer ranges. *)
Lemma DZ_DEC_A : forall ly a, ims_dzone ly a \/ ~ ims_dzone ly a.
Proof.
intros ly a. change (AGjm.DZONE ly a \/ ~ AGjm.DZONE ly a). unfold AGjm.DZONE.
match goal with |- ((?l1 <= a < ?h1) \/ (?l2 <= a < ?h2) \/ (?l3 <= a < ?h3)) \/ _ =>
  destruct (zr_dec_A l1 h1 a); [left; left; assumption|];
  destruct (zr_dec_A l2 h2 a); [left; right; left; assumption|];
  destruct (zr_dec_A l3 h3 a); [left; right; right; assumption|]
end.
right. tauto.
Qed.

(* DZ_OWN: an image byte of the zone is owned static data (CfInstImgA.dzone_owned_ag_A); the node and store blocks
   (static extents 4 and 5) are apart from the image window (extent 9, lo_disj). *)
Lemma DZ_OWN_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a -> in_zr a (ly_img ly) -> Exists (in_zr a) (as_owned_static B).
Proof.
intros ly a LY _ _ Hd Hi.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 4 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 5 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB.
unfold zdisjoint, in_zr in DNB, DSB, Hi. cbn [fst snd] in DNB, DSB.
destruct (CfInstImgA.dzone_owned_ag_A B TS ly a (dz_ag_A ly a Hd)) as [X|[X|X]]; [exact X | exfalso; zl | exfalso; zl].
Qed.

(* PF_SEP: Printf's two cells are below the store, not the out-of-memory byte (CfIalApartPreset.pf_cells_apart_A),
   and inside the image window, which the node and store blocks miss (static extents 4 and 5 against 9). *)
Lemma PF_SEP_A : YGcfInstSec.PF_SEP_t B.
Proof.
intros ly a LY IMG _ Ha. change (AF0x.img_cover ly) in IMG. destruct IMG as [I1 I2].
destruct (CfIalApartPreset.pf_cells_apart_A B TS a Ha) as (A1 & A2 & _).
split; [exact A2|]. change (~ AGjm.DZONE ly a). unfold AGjm.DZONE. rewrite (ts_store B TS) in A1. unfold TFIB_STORE in A1.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 4 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 5 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB.
unfold zdisjoint in DNB, DSB. cbn [fst snd] in DNB, DSB.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha.
unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in *. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Geometry facts at AImgS_A's fields.                                                                              *)
Lemma ZONE3_A : forall ly x sz, im_img_cover ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) ->
  ims_zone3 x sz.
Proof. intros ly x sz IMG Hsz A D. exact (AF0x.zone3_intro ly x sz IMG Hsz A D). Qed.

Lemma WFRAME_SP_A : forall W ly regs0 mem0 tr, ims_wframe W ly regs0 mem0 tr ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Proof.
intros W ly regs0 mem0 tr H. change (AGImgA.wframe W ly regs0 mem0 tr) in H. destruct H as ((H1 & _ & H3 & _) & _).
unfold ImgBaseAGS.AFSTACK. unfold AGhy.AFSTACK in H1. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The const and junk tables.                                                                                       *)
Lemma CONST_LY_A : forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros ly1 ly2. rewrite !(ts_const B TS). reflexivity. Qed.

Lemma CONST_LT_A : forall ly nn, Forall (cell_lt nn) (as_const B ly).
Proof.
intros ly nn. rewrite (ts_const B TS ly). clear. unfold Tfib_const, Tfib_const_sym, Tfib_const_abs, Tfib_const_shadow. cbn [app].
repeat (apply Forall_cons; [exact (conj I I)|]). apply Forall_nil.
Qed.

Lemma JUNK_LY_A : forall ly1 ly2, as_junk B ly1 = as_junk B ly2.
Proof. intros ly1 ly2. exact (ts_junk_ly B TS ly2 ly1). Qed.

Lemma JUNK_LT_A : forall ly nn, Forall (fun r => asec_lt nn (fst r)) (as_junk B ly).
Proof. intros ly nn. apply Forall_forall. intros r Hr. destruct (ts_junk B TS ly r Hr) as (zz & -> & _). exact I. Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The closing theorems: YGcfInstSec's two interfaces at A''s image classes, at any symbol table with TfibSyms and   *)
(* the record's depot hash, then at preset's record TfibB.                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section close.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.

Local Ltac rows :=
  first [ exact TS | exact IOK_inst | exact ADIfaceA.img_cover_A
  | exact (YGcfInstF1WA.errno_seg_A B TS) | exact (YGcfInstF1WA.errno_nstatic_A B TS)
  | exact (CfInstImgA.ERRB_SEP_A B TS) | exact (PF_SEP_A B TS)
  | exact (CfInstHitImgA.INST_CELLS_A B TS) | exact (CONST_KEEP_S_A B TS) | exact (CONST_APART_A B TS)
  | exact (CONST_NOT_JUNK_A B TS) | exact (AREAS_DISJ_A B TS) | exact (HD_A B TS HDH)
  | exact (SYM_TSD_A B TS) | exact (SYM_OOM_A B TS) | exact (SYM_ERRNO_A B TS) | exact (INST_AG_A B TS)
  | exact SHB_EQ_A | exact (COMB_VIS_A B TS) | exact (ERRNO_VIS_A B TS) | exact (DEP_UNHID_A B TS)
  | exact ZONE3_A | exact WFRAME_SP_A | exact (DEP_FP_A B TS) | exact (DZ_LOC_A B TS) | exact DZ_DEC_A
  | exact (DZ_OWN_A B TS) | exact (CONST_LY_A B TS) | exact (CONST_LT_A B TS) | exact (JUNK_LY_A B TS)
  | exact (JUNK_LT_A B TS)
  | exact ErrnoApartA.errno_in_img_cgif | exact ErrnoApartA.errno_unhidden_cgif
  | exact ErrnoApartA.errno_apart_inst_ag_cgif | exact ErrnoApartSA.errno_apart_dzone_s_cgif
  | exact ErrnoApartSA.errno_apart_shadow_s_cgif | exact ErrnoApartSA.errno_apart_zone3_s_cgif ].

(* AIfaceSw at NMAXW = cf_malloc_max, NOBW = cf_nob = 2 ^ 29 (CfParams_preset) and ROOMW = 2 ^ 30 <= CF_HEAD. *)
Theorem ifaceSw_A : forall Hp, AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30).
Proof.
intros Hp.
assert (G : AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max cf_nob (2 ^ 30)).
{ eapply YGcfInstSec.ifaceSw_cf; [rows ..|].
  unfold YGcfAbudget.CF_HEAD. apply Z.leb_le. vm_compute. reflexivity. }
exact G.
Qed.

Theorem ifaceSE_A : forall Hp, ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOXm_cf B) (YGcfRmodel.rpre_cfr B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp.
assert (G : ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow).
{ eapply YGcfInstSec.ifaceSE_cf; rows. }
exact G.
Qed.
End close.

(* ---- At preset's record B := A/AD2l.TfibB and IOK := (fun i => i = as_inst TfibB): the symbol record is
   AD2l.TfibB_syms, the depot hash CfInstHitImgA.dhash_TfibB_A, and the instance object below. ---- *)
Lemma IOK_inst_TfibB_A : IOK_ok AD2l.TfibB (fun i => i = as_inst AD2l.TfibB).
Proof. intros i H. exact H. Qed.

Theorem ifaceSw_TfibB_A : forall Hp, AGif4.AIfaceSw AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
  (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
  cf_malloc_max LIVE_MAX qtight (dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30).
Proof.
exact (ifaceSw_A AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) AD2l.TfibB_syms IOK_inst_TfibB_A
  CfInstHitImgA.dhash_TfibB_A).
Qed.

Theorem ifaceSE_TfibB_A : forall Hp, ErrnoGS.AIfaceSE AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
  (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
  cf_malloc_max LIVE_MAX qtight (dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
exact (ifaceSE_A AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) AD2l.TfibB_syms IOK_inst_TfibB_A
  CfInstHitImgA.dhash_TfibB_A).
Qed.

End a.
