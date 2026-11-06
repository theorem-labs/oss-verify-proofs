(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract astrlen_realizes (lib/A/W_contract.v) proved for
   fuzz_reply.asan's strlen interceptor, entered at the trampoline __wrap_strlen 0x4218c. *)
(* Modified by Theorem Labs, 2026-10-29: from lib/A/RT_strlen.v, as the module RT_strlen_x: cut to the proof of rt_strlen (the helper lemmas are used by Import) and restated over a generic allocator invariant ARx under lib/Rt/RTx.v's rt_laws (rt_strlen_x_walk, rt_strlen_x; the cell premise FrRtCells replaced by RT_kit_cells_x's FrWalkCells_x, which rt_strlen_x derives from rt_laws, FrShadowSyms and TfibSyms); the corollaries rt_strlen_of_x (rt_strlen's statement, unchanged) and rt_strlen_cf added. *)
(* lib/A/RT_strlen.v's runtime contract rt_strlen restated over a generic
   allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of lib/Rt/RTx.v
   (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout, rtl_const_cells).
   RT_strlen.v is not edited; its helper lemmas are used by Import. The statement is W_contract_x.v:173's
   astrlen_realizes_x; the proof of rt_strlen_x is RT_strlen.v's with AR -> ARx (am_layout of proj1 HAR ->
   rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_const (through RT_kit.walk_cells, :176), al_frame / al_stack (through RT_post.aentry_post_of_walk, :227) and
   the ARm field am_layout (:171 and RT_post.v:249), the layout law here; a Theorem Labs lane's three-law note
   (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   The original's named premise FrRtCells (RT_kit.v:230) is not needed over ARx: the walk reads only conjuncts 1-10
   of fr_rt_rest (through RT_kit.walk_cells, RT_kit.v:211), all const rows. So rt_strlen_x_walk takes the walk's
   cells RT_kit_cells_x.FrWalkCells_x, and the twin rt_strlen_x derives them from rt_laws + FrShadowSyms +
   TfibSyms (RT_kit_cells_x.walk_cells_x_of_syms): no cell premise.
   At the end: rt_strlen_of_x, whose statement is byte for byte RT_strlen.v's rt_strlen, from rt_strlen_x_walk at
   cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR, the cells from FrRtCells by walk_cells_x_of_cells); and
   rt_strlen_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf). rt_strlen_cf's premises
   are AR_laws_cf frsegs B, FrShadowSyms B and TfibSyms B; at the cf top (B := TfibB) each is a closed theorem:
   AR_laws_ok_cf (Reusable/YG0lawscf.v), RT_kit.fr_shadow_of_palib of W_palib_fr.palib_tfib TfibB TfibB_syms, and
   AD2l.TfibB_syms. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRsl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
AB1v W_syms W_listing W_kit W_tbl W_place W_img W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FRbz_bridge RT_kit RT_post AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_contract_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AF0m.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit_cells_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_strlen.
Open Scope Z_scope.
(* the libraries Required above (FCiface -> YF0v; the cf files) set Zify's euclidean-division flag to false
   globally (e.g. Reusable/Q/YW06_cf.v:26); the original's lia steps need it on, as in the original's own build *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module CFN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Module NCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Module DCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module WSX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.
Module WCX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_contract_x.
Module AFM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.AF0m.
Module KC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_kit_cells_x.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- THE SITE CONTRACT over ARx, from the walk's cells ---- *)
Theorem rt_strlen_x_walk : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> KC.FrWalkCells_x ARx ->
  WCX.astrlen_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strlen).
Proof.
  intros B ARx LAWS WALK ly S hps W regs mem md x k Hpre Hslo2 Hpres2 Hx Hx0 Hk0 Hk32 Hxk Hfb Hsrc Hband Hamr Ham8
    Hra Hhull Htail Hrom.
  change (@pa_segs _ fr_prog_listing PB_fr) with frsegs in *.
  change (fr_sigma WS_strlen) with 0x4218c.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (RTX.rtl_layout _ _ _ LAWS ly S hps W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (WALK ly S hps W mem md HAR) as (M2S & ICN & _ & ICL & _ & _ & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Hamr' : (0 <= x /\ x + k + 1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= x /\ x + k + 1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr, Ham8; lia).
  destruct (str_buf W mem x k Hx0 Hk0 ltac:(lia) Hfb Htail) as (BUF & NZ & Hs).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (str := K.mk_slack mR x (Z.to_nat k)) in *.
  set (slack := K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))) in *.
  assert (Lstr : Z.of_nat (length str) = k) by (unfold str; rewrite K.length_mk_slack; lia).
  assert (Lsl : Z.of_nat (length slack) = 7 - (x + k) mod 8) by (unfold slack; rewrite K.length_mk_slack; exact Hs).
  pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm8.
  assert (Hfr : x + k < sp - 8192 \/ sp <= x).
  { assert (Hw : forall a, x <= a < x + (k + 1) -> ~ (sp - 2 * ESTACK <= a < sp)) by (intros a Ha; apply Hband; lia).
    destruct (K.off_window sp (2 * ESTACK) x (k + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  eapply SRr_mono.
  { apply (FSB.srr_of_evt K.Hwx_fr W 0x4218c regs mem md
      (RP.walk_at (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
         (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
         (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
         (Z.of_nat (length str)) lo (NM.normalize_cj I0.rsegs mR)) mR)
      (WSX.aentry_post_x (PI := PB_fr) ARx (2 * ESTACK) ly S hps W regs mem md (fun _ => False)
         (fun regs' _ => YK11.getr regs' 10 = w64 k))).
    - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x4218c) fp_csr mR)).
      apply RP.bz_transport; [exact RO|].
      apply (bz_strlen regs fp_regs fp_csr _ x str slack lo).
      + exact Ha0.
      + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
        apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
      + rewrite Esp. unfold lo. lia.
      + unfold BR.kHighShadowEnd, lo. lia.
      + rewrite Esp. lia.
      + lia.
      + rewrite Lstr. lia.
      + rewrite Lstr. lia.
      + refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ BUF).
        rewrite length_app. cbn [length]. unfold TASK_SIZE. lia.
      + exact NZ.
      + rewrite Lstr, Lsl. Z.div_mod_to_equations. lia.
      + rewrite Esp, Lstr, Lsl. lia.
      + rewrite Lstr. apply RP.chk_norm; [lia | lia | lia | lia | | exact Hra | exact Hhull].
        unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      + exact M2S.
      + exact ICN.
      + exact ICL.
      + apply RP.bz_mem_inv_normalize.
    - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
      destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
      subst s0. rewrite Esp in MU, ST'.
      refine (RP.aentry_post_of_walk_x B ARx LAWS (2 * ESTACK) 2224 [] (fun _ => False) _ (Z.of_nat (length str)) ly S hps W regs mem md
        ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre Hslo2 RO ltac:(lia) _ _ _ Hrel Hsame Heqv _ ST' Hsbm _).
      + intros a Ha. inversion Ha.
      + intros a [].
      + intros a [].
      + cbn [app]. exact MU.
      + intros regs'' mem'' Hr _. rewrite Hr, Lstr. reflexivity. }
  cbv beta. intros W' c' _ (EW & regs' & mem' & md' & Ec & HAR' & Hpre' & Hsbm' & Hres & Hfr' & Hp').
  split; [exact EW|]. exists regs', mem', md'.
  split; [exact Ec|]. split; [exact HAR'|]. split; [exact Hpre'|]. split; [exact Hsbm'|]. split; [exact Hres|].
  split; [intros a Ha Hn; apply Hfr'; [exact Ha | intros [] | exact Hn] | exact Hp'].
Qed.

(* ---- THE TWIN: no cell premise (the cells from the const-cells law and TfibSyms) ---- *)
Theorem rt_strlen_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WCX.astrlen_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_strlen).
Proof.
  intros B ARx LAWS TL TB. exact (rt_strlen_x_walk B ARx LAWS (KC.walk_cells_x_of_syms B ARx LAWS TL TB)).
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT_strlen.v's rt_strlen, byte for byte ---- *)
Corollary rt_strlen_of_x : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrlen_realizes (PI := PB_fr) B (fr_sigma WS_strlen).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md.
  exact (rt_strlen_x_walk B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS)
    (KC.walk_cells_x_of_cells B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) TL (K.FrRtCells_x_AR B CELLS))
    ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_strlen_cf : forall B, DCF.AR_laws_cf frsegs B -> K.FrShadowSyms B -> AFM.TfibSyms B ->
  WCX.astrlen_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_strlen).
Proof.
  intros B L TL TB.
  exact (rt_strlen_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L) TL TB).
Qed.
End cf.

End core.
