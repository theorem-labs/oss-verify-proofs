(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The source half of ubsan_agrees at lim_source = ShippedBudgets.lim_source = 2^34: PmXasanBaseW.xsrc_half on the
   2^34 copies of the XLIM layer, closed with the plain library (TopGlueXW.Lay0, PMX.pm_staticsx) and
   PHI0U = phi_lim (2^34). L0, KPM, BOV, K0 and B0 of PmHeapInst6_s34 have the bodies of PmHeapInst6's, so the
   released proof's layout facts over PmHeapInst6.L0 are used by conversion. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim HeapIface HeapIfaceX L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs PmLibSpecsX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF KillFree VmLimitFrame Spec BigintSpec LibIface LibIfaceFp LibIfaceFpW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HalfOk SpecG PmTopSpecsXW Pm6DrvLibL Pm6DrvG.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PmLayoutInst Pm6DrvD MmapSim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.MB Require ModelBounds.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require TopGlueXW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmInteg Require PmLibInstXW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require PmHeapInst6_s34 PmHeapClosed6_s34.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmInteg Require AssemblyFullXW_s34.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmPhiX_s34 PmXubsanStmt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXsrcHalf16.
Abbreviation IMG_xsrc :=
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Definition PHI0U : list byte -> Prop := PmXubsanStmt.PmXubsanStmt.PHI0U.
Abbreviation Lay0F := (fun sp : word => TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp)).

Lemma cfg0_eq : PmPhiX_s34.PmPhiX16.cfg0 = PmXubsanStmt.PmXubsanStmt.cfgU.  Proof. reflexivity. Qed.
Lemma lim16_le : ShippedBudgets.lim_source <= 2 ^ 34.
Proof. unfold ShippedBudgets.lim_source. rewrite MmapSim.source_alloc_limit_val. lia. Qed.

(* The plain library at 2^34 (PmLibInstXW.lib_spec0w / lib_iface0w on the 2^34 heap instance). *)
Theorem lib_spec16 :
  forall sp, valid_sp sp -> @PMXW.lib_specxw TopGlueXW.TopGlueXW.cfg0P (PmHeapInst6_s34.L0 (bv_unsigned sp)) (PmHeapInst6_s34.HI0 (bv_unsigned sp))
                             PML.STRTOD_SCR_V PMES.WD_SCR_X PHI0U (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp)).
Proof.
  intros sp Hsp.
  exact (@AssemblyFullXW_s34.ASMFXW16.lib_ok_xw_full TopGlueXW.TopGlueXW.cfg0P (PmHeapInst6_s34.L0 (bv_unsigned sp)) (PmHeapInst6_s34.HI0 (bv_unsigned sp))
           (PmHeapClosed6_s34.HI0_ok_closed (bv_unsigned sp) PmPhiX_s34.PmPhiX16.cfg0 eq_refl)
           (PmLayoutInst.pm0_layout_L0 (bv_unsigned sp) (PmLibInstXW.PmLibInstXW.valid_sp_img sp Hsp)) PmLibInstXW.PmLibInstXW.fpm0
           (PmHeapInst6_s34.HI0_malloc_x (bv_unsigned sp) PmPhiX_s34.PmPhiX16.cfg0 eq_refl (fun R => @ModelBounds.model_bounds_proof R))
           (PmHeapInst6_s34.hi0_live_fit_src (bv_unsigned sp))
           (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp))).
Qed.

Lemma Lay0_ifacew16 : forall (PHI : list byte -> Prop) sptop,
  @PMXW.lib_specxw TopGlueXW.TopGlueXW.cfg0P (PmHeapInst6_s34.L0 sptop) (PmHeapInst6_s34.HI0 sptop) PML.STRTOD_SCR_V PMES.WD_SCR_X PHI (TopGlueXW.TopGlueXW.Lay0 sptop) ->
  lib_iface_ok_fpw (TopGlueXW.TopGlueXW.Lay0 sptop) PmPhiX_s34.PmPhiX16.cfg0 (PmHeapInst6_s34.HI0 sptop) PMX.pm_staticsx PHI.
Proof.
  intros PHI sptop LIB. constructor.
  - exact (LIB (TopGlueXW.TopGlueXW.Lay0_pm sptop)).
  - exact (TopGlueXW.TopGlueXW.pm_statics_init sptop).
  - exact (TopGlueXW.TopGlueXW.pm_statics_frame sptop).
Qed.

Theorem lib_iface16 : forall sp, valid_sp sp ->
  lib_iface_ok_fpw (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp)) PmPhiX_s34.PmPhiX16.cfg0 (PmHeapInst6_s34.HI0 (bv_unsigned sp)) PMX.pm_staticsx PHI0U.
Proof. intros sp Hsp. exact (Lay0_ifacew16 PHI0U (bv_unsigned sp) (lib_spec16 sp Hsp)). Qed.

Lemma DLL16 : forall sp, valid_sp sp -> Pm6DrvLibL.drv_lib_layout (Lay0F sp) (PmHeapInst6_s34.L0 (bv_unsigned sp)).
Proof. intros sp _. exact (TopGlueXW.TopGlueXW.Lay0_drv (bv_unsigned sp)). Qed.
Lemma LX16 : forall sp : word, valid_sp sp -> Pm6DrvLibL.lib_exit_ok PMX.pm_staticsx.
Proof. intros sp _. exact TopGlueXW.TopGlueXW.pm_exit_ok. Qed.
Lemma BUD16 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Pm6DrvG.cred (PmHeapInst6_s34.L0 (bv_unsigned sp))
    (PmHeapInst6_s34.KPM + 4 * fst (ll_credit (Lay0F sp) n)) (n + PmHeapInst6_s34.BOV + 4 * snd (ll_credit (Lay0F sp) n)) 0
    (debit (PmHeapInst6_s34.L0 (bv_unsigned sp)) (PmHeapInst6_s34.K0, PmHeapInst6_s34.B0) 65536).
Proof. exact TopGlueXW.TopGlueXW.Lay0_budget. Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* A plain run that is not refused at 2^34 yields PHI0U for the payload (PmXasanBaseW.phi_of_premise at 2^34). *)
Lemma phi_of_premise16 : forall sp brk mb rnd inp,
  valid_entry IMG_xsrc (mkEntry sp brk mb rnd) inp -> valid_input_abort inp ->
  ~ run_scfg_budget_refused PmPhiX_s34.PmPhiX16.cfg0 IMG_xsrc ShippedBudgets.lim_source (mkEntry sp brk mb rnd) inp ->
  forall a0 path data, in_argv inp = [a0; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
    fs_lookup (in_fs inp) path = Some data -> SpecG.hdr_okD data -> PHI0U (Pm6DrvD.payload data).
Proof.
  intros sp brk mb rnd inp Hen Hvalid Hwb a0 path data Hargv Hlen Hne Hnd Hlk Hhdr.
  exact (PmPhiX_s34.PmPhiX16.phi_xsrc_at Lay0F (fun _ => PMX.pm_staticsx) PHI0U DLL16 lib_iface16 LX16 BUD16
           ShippedBudgets.lim_source sp brk mb rnd inp a0 path data lim16_le Hen Hvalid Hwb Hargv Hlen Hne Hnd Hlk Hhdr).
Qed.

(* The source half at ShippedBudgets.lim_source. *)
Theorem xsrc_half16 : forall en_s inp,
  valid_entry IMG_xsrc en_s inp -> valid_input_abort inp ->
  ~ run_scfg_budget_refused PmPhiX_s34.PmPhiX16.cfg0 IMG_xsrc ShippedBudgets.lim_source en_s inp ->
  half_ok PmPhiX_s34.PmPhiX16.cfg0 IMG_xsrc ShippedBudgets.lim_source en_s inp (spec (in_argv inp) (in_fs inp)).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hwb.
  apply half_ok_of_srealizes.
  - apply (srz_conseq _ _ _ (specG (fun d => PHI0U (Pm6DrvD.payload d)) (in_argv inp) (in_fs inp))).
    + exact (PmPhiX_s34.PmPhiX16.srealizes_specG_init Lay0F (fun _ => PMX.pm_staticsx) PHI0U DLL16 lib_iface16 LX16 BUD16
               ShippedBudgets.lim_source sp brk mb rnd inp lim16_le Hen Hvalid).
    + apply specG_eq. intros a0 path data Hargv Hlen Hne Hnd Hlk Hhdr.
      exact (phi_of_premise16 sp brk mb rnd inp Hen Hvalid Hwb a0 path data Hargv Hlen Hne Hnd Hlk Hhdr).
  - apply Safe_init_within_budget. exact Hwb.
  - apply kill_free_spec.
Qed.
End FPX_1.
End PmXsrcHalf16.
