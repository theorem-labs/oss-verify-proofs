(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RT_strcmp.v's runtime contract rt_strcmp restated over a generic
   allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of lib/Rt/RTx.v
   (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout, rtl_const_cells).
   RT_strcmp.v is not edited; its helper lemmas are used by Import. The statement is W_sites_x.v's
   astrcmp_realizes_x; the proof of rt_strcmp_x is RT_strcmp.v's with AR -> ARx (am_layout of proj1 HAR ->
   rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_const (through RT_kit.walk_cells, :259), al_frame / al_stack (through RT_post.aentry_post_of_walk, :356) and
   the ARm field am_layout (:254 and RT_post.v:249), the layout law here; a Theorem Labs lane's three-law note
   (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   The original's named premise FrRtCells (RT_kit.v:226) is not needed over ARx: the walk reads only conjuncts 1-10
   of fr_rt_rest (through RT_kit.walk_cells, RT_kit.v:207), all const rows. So rt_strcmp_x_walk takes the walk's
   cells RT_kit_cells_x.FrWalkCells_x, and the twin rt_strcmp_x derives them from rt_laws + FrShadowSyms +
   TfibSyms (RT_kit_cells_x.walk_cells_x_of_syms): no cell premise.
   At the end: rt_strcmp_of_x, whose statement is byte for byte RT_strcmp.v's rt_strcmp, from rt_strcmp_x_walk at
   cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR, the cells from FrRtCells by walk_cells_x_of_cells); and
   rt_strcmp_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf). rt_strcmp_cf's premises
   are AR_laws_cf frsegs B, FrShadowSyms B and TfibSyms B; at the cf top (B := TfibB) each is a closed theorem:
   AR_laws_ok_cf (Reusable/YG0lawscf.v), RT_kit.fr_shadow_of_palib of W_palib_fr.palib_tfib TfibB TfibB_syms, and
   AD2l.TfibB_syms. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strcmp_x.v at commit 6b4f6082575, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRsl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmp.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YB1v W_syms W_listing W_kit W_tbl W_place W_img W_contract W_sites.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_strcmp.
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
Theorem rt_strcmp_x_walk : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> KC.FrWalkCells_x ARx ->
  WSX.astrcmp_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strcmp).
Proof.
  intros B ARx LAWS WALK ly St hps W regs mem md x y kx ky Hpre (Hslo2 & Hpres2) Hx Hy Hx0 Hy0 Hkx0 Hky0 Hxk Hyk Hk40
    Hfbx Hfby Hainx Hainy (Hamrx & Hrax & Hhullx) (Hamry & Hray & Hhully) Hrom (Ham8x & Ham8y).
  change (@pa_segs _ fr_prog_listing PB_fr) with frsegs in *.
  change (fr_sigma WS_strcmp) with 0x421f0.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (RTX.rtl_layout _ _ _ LAWS ly St hps W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (WALK ly St hps W mem md HAR) as (M2S & _ & _ & _ & ICS & FLAG & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 y) by (rewrite <- RP.getr_nz by reflexivity; exact Hy).
  assert (Hamx' : (0 <= x /\ x + kx + 1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= x /\ x + kx + 1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamrx, Ham8x; lia).
  assert (Hamy' : (0 <= y /\ y + ky + 1 <= 0x7fff7fff /\ y + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= y /\ y + ky + 1 <= 0x7fffffffffff /\ y + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamry, Ham8y; lia).
  assert (Hfx : x + kx < spZ regs - 8192 \/ spZ regs <= x).
  { assert (Hw : forall a, x <= a < x + (kx + 1) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; exact (proj2 (Hainx a Ha))).
    destruct (K.off_window (spZ regs) (2 * ESTACK) x (kx + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  assert (Hfy : y + ky < spZ regs - 8192 \/ spZ regs <= y).
  { assert (Hw : forall a, y <= a < y + (ky + 1) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) by (intros a Ha; exact (proj2 (Hainy a Ha))).
    destruct (K.off_window (spZ regs) (2 * ESTACK) y (ky + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  destruct (cstr_list W mem x kx Hx0 Hkx0 ltac:(lia) Hfbx) as (ELx & NZ1 & BYX & BX).
  destruct (cstr_list W mem y ky Hy0 Hky0 ltac:(lia) Hfby) as (ELy & NZ2 & BYY & BY).
  pose proof (cstr_eq_iff W mem x y kx ky Hkx0 Hky0 BX BY) as EQV.
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (sx := K.mk_slack mR x (Z.to_nat kx)) in *. set (sy := K.mk_slack mR y (Z.to_nat ky)) in *.
  assert (Lsx : length sx = Z.to_nat kx) by (unfold sx; apply K.length_mk_slack).
  assert (Lsy : length sy = Z.to_nat ky) by (unfold sy; apply K.length_mk_slack).
  destruct (strcmp_facts sx sy NZ1 NZ2) as (KL & KR & HP & HB & HE).
  set (k := strcmp_k sx sy) in *.
  set (cx := nth k (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) in *.
  set (cy := nth k (sy ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) in *.
  set (ls := firstn (S k) (sx ++ [Z_to_bv 8 0])).
  set (rs := firstn (S k) (sy ++ [Z_to_bv 8 0])).
  assert (LL : length ls = S k) by (unfold ls; apply firstn_length_le; rewrite length_app; cbn [length]; lia).
  assert (LR : length rs = S k) by (unfold rs; apply firstn_length_le; rewrite length_app; cbn [length]; lia).
  assert (EX : nth_error ls k = Some cx).
  { unfold ls. rewrite nth_error_firstn_lt by lia. apply nth_error_nth'. rewrite length_app; cbn; lia. }
  assert (EY : nth_error rs k = Some cy).
  { unfold rs. rewrite nth_error_firstn_lt by lia. apply nth_error_nth'. rewrite length_app; cbn; lia. }
  assert (HPc : BS.sc_pre ls rs k).
  { intros j Hj. destruct (HP j Hj) as (z & E1 & E2 & NZ). exists z. unfold ls, rs.
    rewrite !nth_error_firstn_lt by lia. auto. }
  (* the prefixes the interceptor reads, on the walk's memory *)
  assert (PREF : forall p kp (s : list byte), length s = Z.to_nat kp -> (k <= Z.to_nat kp)%nat -> 0 <= kp ->
    BM.bytes_at BI.asegs mR p (s ++ [Z_to_bv 8 0]) -> p + kp + 1 <= TASK_SIZE ->
    BM.bytes_at BI.asegs (NM.normalize_cj I0.rsegs mR) p (firstn (S k) (s ++ [Z_to_bv 8 0]))).
  { intros p kp s Ls Hk Hkp BYS Hp. apply (NM.bytes_at_normalize_cj_low I0.rsegs mR p _ RO).
    - rewrite firstn_length_le by (rewrite length_app; cbn; lia). lia.
    - assert (E : s ++ [Z_to_bv 8 0] = firstn (S k) (s ++ [Z_to_bv 8 0]) ++ skipn (S k) (s ++ [Z_to_bv 8 0]))
        by (rewrite firstn_skipn; reflexivity).
      rewrite E in BYS. exact (proj1 (proj1 (BM.bytes_at_app BI.asegs _ _ _ _) BYS)). }
  set (r := BS.cmpx (bv_unsigned cx) (bv_unsigned cy)).
  assert (Hr : r = -1 \/ r = 0 \/ r = 1)
    by (unfold r; rewrite cmpx_sgn; destruct (Z.sgn_spec (bv_unsigned cx - bv_unsigned cy)) as [[_ ->]|[[_ ->]|[_ ->]]]; lia).
  assert (Hr0 : r = 0 <-> sx = sy).
  { unfold r. rewrite cmpx_sgn. split.
    - intros E. apply HE. apply Z.sgn_null_iff in E. lia.
    - intros E. apply Z.sgn_null_iff. apply HE in E. lia. }
  apply (FSB.srr_of_evt K.Hwx_fr W 0x421f0 regs mem md
    (RP.walk_at (BSC.istrcmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
       r lo (NM.normalize_cj I0.rsegs mR)) mR)).
  - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421f0) fp_csr mR)).
    apply RP.bz_transport; [exact RO|].
    apply (bz_strcmp regs fp_regs fp_csr _ x y ls rs k cx cy lo).
    + exact Ha0.
    + exact Ha1.
    + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
    + rewrite Esp. unfold lo. lia.
    + unfold BR.kHighShadowEnd, lo. lia.
    + rewrite Esp. lia.
    + apply (PREF x kx sx Lsx ltac:(lia) Hkx0); [rewrite <- ELx; exact BYX | unfold TASK_SIZE; lia].
    + apply (PREF y ky sy Lsy ltac:(lia) Hky0); [rewrite <- ELy; exact BYY | unfold TASK_SIZE; lia].
    + exact LL.
    + exact LR.
    + exact HPc.
    + exact EX.
    + exact EY.
    + exact HB.
    + lia.
    + lia.
    + rewrite Esp. lia.
    + rewrite Esp. lia.
    + apply RP.chk_norm; [lia | lia | lia | lia | | |].
      * unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      * apply (range_addressable_sub _ _ _ (kx + 1)); [lia | exact Hrax].
      * apply (hull_sub _ _ (kx + 1)); [lia | lia | exact (Hhullx ltac:(lia))].
    + apply RP.chk_norm; [lia | lia | lia | lia | | |].
      * unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      * apply (range_addressable_sub _ _ _ (ky + 1)); [lia | exact Hray].
      * apply (hull_sub _ _ (ky + 1)); [lia | lia | exact (Hhully ltac:(lia))].
    + exact M2S.
    + exact ICS.
    + exact FLAG.
    + apply RP.bz_mem_inv_normalize.
  - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
    subst s0. rewrite Esp in MU, ST'.
    refine (RP.aentry_post_of_walk_x B ARx LAWS (2 * ESTACK) 2272 [] (fun _ => False) _ r ly St hps W regs mem md
      ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre Hslo2 RO ltac:(lia) _ _ _ Hrel Hsame Heqv _ ST' Hsbm _).
    + intros a Ha. inversion Ha.
    + intros a [].
    + intros a [].
    + cbn [app]. exact MU.
    + intros regs'' mem'' Hreg _. rewrite Hreg. rewrite <- EQV, <- Hr0. clearbody r. unfold w64.
      destruct Hr as [-> | [-> | ->]]; split; intros E; try reflexivity; try discriminate E;
        apply (f_equal bv_unsigned) in E; rewrite !Z_to_bv_unsigned in E; vm_compute in E; discriminate E.
Qed.

(* ---- THE TWIN: no cell premise (the cells from the const-cells law and TfibSyms) ---- *)
Theorem rt_strcmp_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrcmp_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strcmp).
Proof.
  intros B ARx LAWS TL TB. exact (rt_strcmp_x_walk B ARx LAWS (KC.walk_cells_x_of_syms B ARx LAWS TL TB)).
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT_strcmp.v's rt_strcmp, byte for byte ---- *)
Corollary rt_strcmp_of_x : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrcmp_realizes (PI := PB_fr) B (fr_sigma WS_strcmp).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md.
  exact (rt_strcmp_x_walk B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS)
    (KC.walk_cells_x_of_cells B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) TL (K.FrRtCells_x_AR B CELLS))
    ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_strcmp_cf : forall B, DCF.AR_laws_cf frsegs B -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrcmp_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_strcmp).
Proof.
  intros B L TL TB.
  exact (rt_strcmp_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L) TL TB).
Qed.
End cf.

End core.
