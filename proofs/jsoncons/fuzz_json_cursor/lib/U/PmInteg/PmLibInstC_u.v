(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u PmLayoutInst_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require PmFinal_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u PmHeapClosed10_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require TopGlueC_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmInteg Require AssemblyFullC_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLibInstC.
Lemma fpm0 : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Proof. intros fx fx' R pc M R' pc' M' H. exact (FrmInv.msteps_fp_ok PML.RSEGS Pm10FrmInv.text_safe fx fx' R _ M _ R' _ M' _ H). Qed.
Lemma valid_sp_img : forall sp, valid_sp sp -> 0xf8000 <= bv_unsigned sp.
Proof. intros sp (H & _). assert (X : (0xf8000 <=? sp_window_lo) = true) by reflexivity. apply Z.leb_le in X. lia. Qed.
Lemma scr_ok : PML.STRTOD_SCR_V <= 54208. Proof. unfold PML.STRTOD_SCR_V. lia. Qed.

Theorem lib_spec0 :
  forall sp, valid_sp sp -> @PMCS.lib_spec_c TopGlueC_u.TopGlueC.cfg0P (PmHeapInst10_u.L0 (bv_unsigned sp)) (PmHeapInst10_u.HI0 (bv_unsigned sp)) PML.STRTOD_SCR_V (TopGlueC_u.TopGlueC.Lay0 (bv_unsigned sp)).
Proof.
  intros sp Hsp.
  exact (@AssemblyFullC_u.ASMFC.lib_ok_c_full TopGlueC_u.TopGlueC.cfg0P (PmHeapInst10_u.L0 (bv_unsigned sp)) (PmHeapInst10_u.HI0 (bv_unsigned sp))
           (PmHeapClosed10_u.HI0_ok_closed (bv_unsigned sp) PmFinal_u.cfg0 eq_refl) (PmLayoutInst_u.pm0_layout_L0 (bv_unsigned sp) (valid_sp_img sp Hsp)) fpm0 (TopGlueC_u.TopGlueC.Lay0 (bv_unsigned sp))).
Qed.
End PmLibInstC.
