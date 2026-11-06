(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RT_strncmp.v's runtime contract rt_strncmp restated over a generic
   allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of lib/Rt/RTx.v
   (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout, rtl_const_cells).
   RT_strncmp.v is not edited; its helper lemmas are used by Import. The statement is W_sites_x.v's
   astrncmp_realizes_x; the proof of rt_strncmp_x is RT_strncmp.v's with AR -> ARx (am_layout of proj1 HAR ->
   rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_const (through RT_kit.walk_cells, :286), al_frame / al_stack (through RT_post.aentry_post_of_walk, :361) and
   the ARm field am_layout (:281 and RT_post.v:249), the layout law here; a Theorem Labs lane's three-law note
   (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   The original's named premise FrRtCells (RT_kit.v:226) is not needed over ARx: the walk reads only conjuncts 1-10
   of fr_rt_rest (through RT_kit.walk_cells, RT_kit.v:207), all const rows. So rt_strncmp_x_walk takes the walk's
   cells RT_kit_cells_x.FrWalkCells_x, and the twin rt_strncmp_x derives them from rt_laws + FrShadowSyms +
   TfibSyms (RT_kit_cells_x.walk_cells_x_of_syms): no cell premise.
   At the end: rt_strncmp_of_x, whose statement is byte for byte RT_strncmp.v's rt_strncmp, from rt_strncmp_x_walk
   at cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR, the cells from FrRtCells by walk_cells_x_of_cells);
   and rt_strncmp_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf). rt_strncmp_cf's
   premises are AR_laws_cf frsegs B, FrShadowSyms B and TfibSyms B; at the cf top (B := TfibB) each is a closed
   theorem: AR_laws_ok_cf (Reusable/YG0lawscf.v), RT_kit.fr_shadow_of_palib of W_palib_fr.palib_tfib TfibB
   TfibB_syms, and AD2l.TfibB_syms. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strncmp_x.v at commit 6b4f6082575, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.IcptSpec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FRbz_bridge RT_kit RT_post YE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YF0m.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit_cells_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_strncmp.
Open Scope Z_scope.
(* the libraries Required above (FCiface -> YF0v; the cf files) set Zify's euclidean-division flag to false
   globally (e.g. Reusable/Q/YW06_cf.v:26); the original's lia steps need it on, as in the original's own build *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module CFN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Module NCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Module DCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module WSX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.W_sites_x.
Module AFM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YF0m.
Module KC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit_cells_x.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- THE SITE CONTRACT over ARx, from the walk's cells ---- *)
Theorem rt_strncmp_x_walk : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> KC.FrWalkCells_x ARx ->
  WSX.astrncmp_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strncmp).
Proof.
  intros B ARx LAWS WALK ly S hps W regs mem md x y n kx ky Hpre (Hslo2 & Hpres2) Hx Hy Hn Hn63 Hn40 Hx0 Hy0
    Hfb1 Hfb2 Hxe Hye Hin1 Hin2 (Ham1 & Hra1 & Hhull1) (Ham2 & Hra2 & Hhull2) Hrom (Ham8x & Ham8y).
  change (@pa_segs _ fr_prog_listing PB_fr) with tfibsegs in *.
  pose proof LAWS as LAWS'. change frsegs with tfibsegs in LAWS'.
  change (fr_sigma WS_strncmp) with 0x421f4.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (RTX.rtl_layout _ _ _ LAWS ly S hps W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (WALK ly S hps W mem md HAR) as (M2S & _ & _ & _ & ICS & _ & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 y) by (rewrite <- RP.getr_nz by reflexivity; exact Hy).
  assert (Ha2 : reg_get regs 12 = Z_to_bv 64 n) by (rewrite <- RP.getr_nz by reflexivity; exact Hn).
  destruct Hfb1 as (Kx & Bx & Lx). destruct Hfb2 as (Ky & By & Ly).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (L1 := Z.min n (kx + 1)) in *. set (L2 := Z.min n (ky + 1)) in *.
  set (b1 := K.mk_slack mR x (Z.to_nat L1)). set (b2 := K.mk_slack mR y (Z.to_nat L2)).
  assert (LB1 : Z.of_nat (length b1) = L1) by (unfold b1; rewrite K.length_mk_slack; lia).
  assert (LB2 : Z.of_nat (length b2) = L2) by (unfold b2; rewrite K.length_mk_slack; lia).
  assert (V1 : forall a, x <= a < x + Z.of_nat (Z.to_nat L1) -> aview tfibsegs H mem a <> None)
    by (intros a Ha; apply (proj1 (Hin1 a ltac:(lia)))).
  assert (V2 : forall a, y <= a < y + Z.of_nat (Z.to_nat L2) -> aview tfibsegs H mem a <> None)
    by (intros a Ha; apply (proj1 (Hin2 a ltac:(lia)))).
  assert (R1 : forall j z, nth_error b1 j = Some z -> aview tfibsegs H mem (x + Z.of_nat j) = Some (bv_unsigned z))
    by (intros j z Hj; exact (mk_view H mem x _ j z V1 Hj)).
  assert (R2 : forall j z, nth_error b2 j = Some z -> aview tfibsegs H mem (y + Z.of_nat j) = Some (bv_unsigned z))
    by (intros j z Hj; exact (mk_view H mem y _ j z V2 Hj)).
  destruct (strncmp_fn (aview tfibsegs H mem) x y n kx ky b1 b2 ltac:(lia) Kx Bx Lx Ky By Ly LB1 LB2 R1 R2)
    as (OK & RES).
  set (sz := SCS.strncmp_sz n b1 b2) in *.
  assert (SZ : (0 < n -> 1 <= sz) /\ sz <= L1 /\ sz <= L2 /\ sz <= n).
  { destruct OK as (O1 & O2). unfold sz, SCS.strncmp_sz, SCS.strncmp_idx in *. lia. }
  apply (FSB.srr_of_evt K.Hwx_fr W 0x421f4 regs mem md
    (RP.walk_at (SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr (SCS.strncmp_res n b1 b2) lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421f4) fp_csr mR)).
    apply RP.bz_transport; [exact RO|].
    apply (bz_strncmp regs fp_regs fp_csr _ x y n b1 b2 lo).
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + lia.
    + lia.
    + lia.
    + intros NP.
      assert (Hamr1 : (0 <= x /\ x + L1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                      (0x10007fff8000 <= x /\ x + L1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
        by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham1, Ham8x; lia).
      assert (Hamr2 : (0 <= y /\ y + L2 <= 0x7fff7fff /\ y + 8 <= 0x7fff7fff) \/
                      (0x10007fff8000 <= y /\ y + L2 <= 0x7fffffffffff /\ y + 8 <= 0x7fffffffffff))
        by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham2, Ham8y; lia).
      assert (Hfr1 : x + L1 - 1 < sp - 8192 \/ sp <= x).
      { apply (K.off_window sp (2 * ESTACK) x L1); [lia | lia |]. intros a Ha. exact (proj2 (Hin1 a Ha)). }
      assert (Hfr2 : y + L2 - 1 < sp - 8192 \/ sp <= y).
      { apply (K.off_window sp (2 * ESTACK) y L2); [lia | lia |]. intros a Ha. exact (proj2 (Hin2 a Ha)). }
      split; [|split; [|split; [exact OK|split; [|split; [|split; [|split; [|split]]]]]]].
      * refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x b1 RO _ _); [rewrite LB1; unfold TASK_SIZE; lia |].
        apply K.bytes_at_mk; [lia | lia | exact V1].
      * refine (NM.bytes_at_normalize_cj_low I0.rsegs mR y b2 RO _ _); [rewrite LB2; unfold TASK_SIZE; lia |].
        apply K.bytes_at_mk; [lia | lia | exact V2].
      * lia.
      * lia.
      * rewrite Esp. lia.
      * rewrite Esp. lia.
      * apply RP.chk_norm; [lia | lia | lia | lia | | | ].
        -- unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
        -- apply (ra_mono _ _ _ L1); [exact Hra1 | lia].
        -- apply (hull_mono _ _ L1); [lia | exact (Hhull1 ltac:(lia))].
      * apply RP.chk_norm; [lia | lia | lia | lia | | | ].
        -- unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
        -- apply (ra_mono _ _ _ L2); [exact Hra2 | lia].
        -- apply (hull_mono _ _ L2); [lia | exact (Hhull2 ltac:(lia))].
    + exact M2S.
    + exact ICS.
    + apply RP.bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    apply (RP.aentry_post_of_walk_x B ARx LAWS (2 * ESTACK) 2256 [] (fun _ => False) _ (SCS.strncmp_res n b1 b2)
      ly S hps W regs mem md ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
    + exact Hpre.
    + exact Hslo2.
    + exact RO.
    + lia.
    + intros a Ha. inversion Ha.
    + intros a [].
    + intros a [].
    + exact Hrel.
    + exact Hsame.
    + exact Heqv.
    + rewrite app_nil_r. exact MU.
    + exact ST'.
    + exact Hsbm.
    + intros regs'' mem'' Hr _. rewrite Hr.
      pose proof (res_range n b1 b2) as Rr.
      destruct (Z.eq_dec (SCS.strncmp_res n b1 b2) 0) as [E0|N0].
      * rewrite E0. split; [intros _; exact (proj1 RES E0) | intros _; reflexivity].
      * split.
        -- intros E. exfalso. apply N0. apply (f_equal bv_unsigned) in E. unfold w64 in E.
           rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
           rewrite Z.mod_0_l in E by lia.
           destruct (Z.eq_dec (SCS.strncmp_res n b1 b2) (-1)) as [Em|Nm].
           ++ rewrite Em in E. cbn in E. discriminate E.
           ++ assert (E1 : SCS.strncmp_res n b1 b2 = 1) by lia. rewrite E1 in E. cbn in E. discriminate E.
        -- intros A. exfalso. apply N0. exact (proj2 RES A).
Qed.

(* ---- THE TWIN: no cell premise (the cells from the const-cells law and TfibSyms) ---- *)
Theorem rt_strncmp_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrncmp_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strncmp).
Proof.
  intros B ARx LAWS TL TB. exact (rt_strncmp_x_walk B ARx LAWS (KC.walk_cells_x_of_syms B ARx LAWS TL TB)).
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT_strncmp.v's rt_strncmp, byte for byte ---- *)
Corollary rt_strncmp_of_x : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrncmp_realizes (PI := PB_fr) B (fr_sigma WS_strncmp).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md.
  exact (rt_strncmp_x_walk B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS)
    (KC.walk_cells_x_of_cells B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) TL (K.FrRtCells_x_AR B CELLS))
    ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_strncmp_cf : forall B, DCF.AR_laws_cf frsegs B -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrncmp_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_strncmp).
Proof.
  intros B L TL TB.
  exact (rt_strncmp_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L) TL TB).
Qed.
End cf.

End core.
