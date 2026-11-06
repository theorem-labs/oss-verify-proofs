(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RT_strrchr.v's runtime contract rt_strrchr restated over a generic
   allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of lib/Rt/RTx.v
   (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout, rtl_const_cells).
   RT_strrchr.v is not edited; its helper lemmas are used by Import. The statement is W_sites_x.v's
   astrrchr_realizes_x; the proof of rt_strrchr_x is RT_strrchr.v's with AR -> ARx (am_layout of proj1 HAR ->
   rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_const (through RT_kit.walk_cells, :204; RT_kit.walk_rest :206 uses FrRtCells only), al_frame / al_stack
   (through RT_post.aentry_post_of_walk, :272) and the ARm field am_layout (:199 and RT_post.v:249), the layout law
   here; the three-law note (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count the ARm fields, hence the record's rtl_layout
   and rtl_const_cells.
   The original's named premise FrRtCells (RT_kit.v:226) becomes RT_kit.FrRtCells_x over ARx in rt_strrchr_x_cells
   (the walk reads conjuncts 1-10 through RT_kit.walk_cells_x and 13-14 through RT_kit.walk_rest_x). The twin
   rt_strrchr_x has no cell premise: all 14 conjuncts come from rt_laws + TfibSyms (the const-cells law,
   RT_kit_cells_x.FrRtCells_x_of_syms), the cell 0x9fc90 (REAL(strrchr) = 0x9740c; the walk loads it and jumps to
   it) included: it is the generated AF0m's row at index 405 of Tfib_const_abs (AF0m.v sha256 007c9a7eb8b9; internal record).
   At the end: rt_strrchr_of_x, whose statement is byte for byte RT_strrchr.v's rt_strrchr, from rt_strrchr_x_cells
   at cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR); and rt_strrchr_cf, the twin at ARx := ARcf with the
   laws from AR_laws_cf (RTx.rt_laws_cf). rt_strrchr_cf's premises are AR_laws_cf frsegs B, FrShadowSyms B and
   TfibSyms B; at the cf top (B := TfibB) each is a closed theorem: AR_laws_ok_cf (Reusable/YG0lawscf.v),
   RT_kit.fr_shadow_of_palib of W_palib_fr.palib_tfib TfibB TfibB_syms, and AD2l.TfibB_syms. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strrchr_x.v at commit 6b4f6082575, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (5 numerals; per-numeral report). *)
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
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strrchr.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_strrchr.
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

(* ---- THE SITE CONTRACT over ARx, from RT_kit's wide cell premise ---- *)
Theorem rt_strrchr_x_cells : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> K.FrShadowSyms B -> K.FrRtCells_x B ARx ->
  WSX.astrrchr_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strrchr).
Proof.
  intros B ARx LAWS TL CELLS ly S hps W regs mem md x c k Hpre (Hslo2 & Hpres2) Hx Hc Hc256 Hx0 Hk0 Hxk Hk40
    Hfb Hin Htail Hrom (Ham1 & Hra & Hhull) Ham8.
  change (@pa_segs _ fr_prog_listing PB_fr) with tfibsegs in *.
  pose proof LAWS as LAWS'. change frsegs with tfibsegs in LAWS'.
  change (fr_sigma WS_strrchr) with 0x421fc.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (RTX.rtl_layout _ _ _ LAWS ly S hps W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (K.walk_cells_x B ARx LAWS TL CELLS ly S hps W mem md HAR) as (M2S & ICN & _ & ICL & _ & _ & _).
  assert (ISR : SR.icells_srr (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem))).
  { pose proof (K.walk_rest_x B ARx CELLS ly S hps W mem md HAR) as REST. unfold K.fr_rt_rest in REST.
    repeat match type of REST with _ /\ (_ /\ _) => destruct REST as [_ REST] end.
    destruct REST as [C1 C2]. split; [exact C1 | exact C2]. }
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 c) by (rewrite <- RP.getr_nz by reflexivity; exact Hc).
  assert (Hamr : (0 <= x /\ x + (k + 1) <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                 (0x10007fff8000 <= x /\ x + (k + 1) <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham1, Ham8; lia).
  destruct (str_buf W mem x k Hx0 Hk0 ltac:(lia) Hfb Htail) as (BUF & NZ & Hs).
  pose proof Hfb as (Hkn & Hbef & Hlast).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (str := K.mk_slack mR x (Z.to_nat k)) in *.
  set (slack := K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))) in *.
  assert (Lstr : Z.of_nat (length str) = k) by (unfold str; rewrite K.length_mk_slack; lia).
  assert (Lsl : Z.of_nat (length slack) = 7 - (x + k) mod 8) by (unfold slack; rewrite K.length_mk_slack; exact Hs).
  pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm8.
  assert (Hfr : x + k < sp - 8192 \/ sp <= x).
  { assert (Hw : forall a, x <= a < x + (k + 1) -> ~ (sp - 2 * ESTACK <= a < sp)) by (intros a Ha; exact (proj2 (Hin a Ha))).
    destruct (K.off_window sp (2 * ESTACK) x (k + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  (* the k + 1 bytes the walk's answer is about, each as the donor's reader sees it *)
  assert (RB : forall i z, nth_error (str ++ [Z_to_bv 8 0]) i = Some z ->
                 aview tfibsegs H mem (x + Z.of_nat i) = Some (bv_unsigned z)).
  { intros i z Hi.
    destruct (Nat.lt_ge_cases i (length str)) as [Li|Li].
    - rewrite nth_error_app1 in Hi by exact Li.
      assert (Li' : (i < Z.to_nat k)%nat) by (unfold str in Li; rewrite K.length_mk_slack in Li; exact Li).
      unfold str in Hi. rewrite K.nth_mk_slack in Hi by exact Li'. injection Hi as <-.
      destruct (Hbef (Z.of_nat i) ltac:(lia)) as (v & Hv & _).
      destruct (K.byte_at_view H mem _ v Hv) as (Eb & Rv). fold mR in Eb. rewrite Eb, Hv.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
    - rewrite nth_error_app2 in Hi by exact Li.
      destruct (i - length str)%nat as [|q] eqn:Eq; [|destruct q; discriminate Hi].
      cbn in Hi. injection Hi as <-.
      replace (x + Z.of_nat i) with (x + k) by lia. rewrite (Hlast ltac:(lia)). reflexivity. }
  assert (LB : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = k + 1) by (rewrite length_app; cbn [length]; lia).
  assert (ELB : length (str ++ [Z_to_bv 8 0]) = Datatypes.S (length str)) by (rewrite length_app; cbn [length]; lia).
  destruct (rchr_fn (aview tfibsegs H mem) x c k (str ++ [Z_to_bv 8 0]) Hk0 LB RB) as [(NONE & E0)|(i & Hi & Vi & AFT & Ei)];
    rewrite ELB in *.
  all: apply (FSB.srr_of_evt K.Hwx_fr W 0x421fc regs mem md
    (RP.walk_at (SR.istrrchr_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr (SR.rchr_res x c (str ++ [Z_to_bv 8 0]) (Datatypes.S (length str))) lo
                  (NM.normalize_cj I0.rsegs mR)) mR)).
  all: try (refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421fc) fp_csr mR));
    apply RP.bz_transport; [exact RO|];
    apply (bz_strrchr regs fp_regs fp_csr _ x c str slack lo);
    [ exact Ha0 | exact Ha1 | exact Hc256
    | rewrite Esp; apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |];
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2]
    | rewrite Esp; unfold lo; lia
    | unfold BR.kHighShadowEnd, lo; lia
    | rewrite Esp; lia
    | lia
    | rewrite Lstr; lia
    | rewrite Lstr; lia
    | refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ BUF);
      rewrite length_app; cbn [length]; unfold TASK_SIZE; lia
    | exact NZ
    | rewrite Lstr, Lsl; Z.div_mod_to_equations; lia
    | rewrite Esp, Lstr, Lsl; lia
    | rewrite Lstr; apply RP.chk_norm; [lia | lia | lia | lia | | exact Hra | exact (Hhull ltac:(lia))];
      unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd; lia
    | exact M2S | exact ICN | exact ICL | exact ISR | apply RP.bz_mem_inv_normalize ]).
  all: intros ms' model' (cc & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _;
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST');
    subst s0; rewrite Esp in MU, ST';
    apply (RP.aentry_post_of_walk_x B ARx LAWS (2 * ESTACK) 4400 [] (fun _ => False) _
      (SR.rchr_res x c (str ++ [Z_to_bv 8 0]) (Datatypes.S (length str)))
      ly S hps W regs mem md ms' model' cc m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
    [ exact Hpre | exact Hslo2 | exact RO | lia | intros a Ha; inversion Ha | intros a [] | intros a []
    | exact Hrel | exact Hsame | exact Heqv | rewrite app_nil_r; exact MU | exact ST' | exact Hsbm |].
  - intros regs'' mem'' Hr _. rewrite Hr, E0. left. split; [exact NONE | reflexivity].
  - intros regs'' mem'' Hr _. rewrite Hr, Ei. right. exists i. split; [exact Hi|]. split; [exact Vi|].
    split; [exact AFT | reflexivity].
Qed.

(* ---- THE TWIN: no cell premise (the cells from the const-cells law and TfibSyms) ---- *)
Theorem rt_strrchr_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrrchr_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strrchr).
Proof.
  intros B ARx LAWS TL TB. exact (rt_strrchr_x_cells B ARx LAWS TL (KC.FrRtCells_x_of_syms B ARx LAWS TB)).
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT_strrchr.v's rt_strrchr, byte for byte ---- *)
Corollary rt_strrchr_of_x : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrrchr_realizes (PI := PB_fr) B (fr_sigma WS_strrchr).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md.
  exact (rt_strrchr_x_cells B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) TL (K.FrRtCells_x_AR B CELLS)
    ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_strrchr_cf : forall B, DCF.AR_laws_cf frsegs B -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WSX.astrrchr_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_strrchr).
Proof.
  intros B L TL TB.
  exact (rt_strrchr_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L) TL TB).
Qed.
End cf.

End core.
