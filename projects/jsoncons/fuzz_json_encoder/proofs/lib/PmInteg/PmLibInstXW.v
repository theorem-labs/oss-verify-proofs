(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim HeapIface HeapIfaceX L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmEncSpecs PmLibSpecsX FrmInv Pm6FrmInv PmLayoutInst.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import LibIfaceFpW PmTopSpecsXW PmPhiX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require PmHeapInst6 PmHeapClosed6.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.MB Require ModelBounds.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require TopGlueXW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmInteg Require AssemblyFullXW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLibInstXW.
Definition PHI0 : list byte -> Prop := PMXW.phi_lim (2 ^ 31).

Lemma fpm0 : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Proof. intros fx fx' R pc M R' pc' M' H. exact (FrmInv.msteps_fp_ok PML.RSEGS Pm6FrmInv.text_safe fx fx' R _ M _ R' _ M' _ H). Qed.
Lemma valid_sp_img : forall sp, valid_sp sp -> 0xfb000 <= bv_unsigned sp.
Proof. intros sp (H & _). assert (X : (0xfb000 <=? sp_window_lo) = true) by reflexivity. apply Z.leb_le in X. lia. Qed.

(* [comment removed for export] *)
Theorem lib_spec0w :
  forall sp, valid_sp sp -> @PMXW.lib_specxw TopGlueXW.TopGlueXW.cfg0P (PmHeapInst6.L0 (bv_unsigned sp)) (PmHeapInst6.HI0 (bv_unsigned sp)) PML.STRTOD_SCR_V PMES.WD_SCR_X PHI0
                             (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp)).
Proof.
  intros sp Hsp.
  exact (@AssemblyFullXW.ASMFXW.lib_ok_xw_full TopGlueXW.TopGlueXW.cfg0P (PmHeapInst6.L0 (bv_unsigned sp)) (PmHeapInst6.HI0 (bv_unsigned sp))
           (PmHeapClosed6.HI0_ok_closed (bv_unsigned sp) PmPhiX.cfg0 eq_refl) (PmLayoutInst.pm0_layout_L0 (bv_unsigned sp) (valid_sp_img sp Hsp)) fpm0
           (PmHeapInst6.HI0_malloc_x (bv_unsigned sp) PmPhiX.cfg0 eq_refl (fun R => @ModelBounds.model_bounds_proof R))
           (PmHeapInst6.hi0_live_fit_src (bv_unsigned sp))
           (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp))).
Qed.

(* [comment removed for export] *)
Theorem lib_iface0w : forall sp, valid_sp sp ->
  lib_iface_ok_fpw (TopGlueXW.TopGlueXW.Lay0 (bv_unsigned sp)) PmPhiX.cfg0 (PmHeapInst6.HI0 (bv_unsigned sp)) PMX.pm_staticsx PHI0.
Proof. intros sp Hsp. exact (TopGlueXW.TopGlueXW.Lay0_ifacew PHI0 (bv_unsigned sp) (lib_spec0w sp Hsp)). Qed.
End PmLibInstXW.
