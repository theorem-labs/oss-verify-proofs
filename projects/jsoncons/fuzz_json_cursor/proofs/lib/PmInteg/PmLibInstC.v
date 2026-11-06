(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmLayout PmCurSpecs FrmInv Pm10FrmInv PmLayoutInst.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmFinal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require PmHeapInst10 PmHeapClosed10.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmTop Require TopGlueC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmInteg Require AssemblyFullC.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmLibInstC.
Lemma fpm0 : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Proof. intros fx fx' R pc M R' pc' M' H. exact (FrmInv.msteps_fp_ok PML.RSEGS Pm10FrmInv.text_safe fx fx' R _ M _ R' _ M' _ H). Qed.
Lemma valid_sp_img : forall sp, valid_sp sp -> 0xf6000 <= bv_unsigned sp.
Proof. intros sp (H & _). assert (X : (0xf6000 <=? sp_window_lo) = true) by reflexivity. apply Z.leb_le in X. lia. Qed.
Lemma scr_ok : PML.STRTOD_SCR_V <= 54224. Proof. unfold PML.STRTOD_SCR_V. lia. Qed.

Theorem lib_spec0 :
  forall sp, valid_sp sp -> @PMCS.lib_spec_c TopGlueC.TopGlueC.cfg0P (PmHeapInst10.L0 (bv_unsigned sp)) (PmHeapInst10.HI0 (bv_unsigned sp)) PML.STRTOD_SCR_V (TopGlueC.TopGlueC.Lay0 (bv_unsigned sp)).
Proof.
  intros sp Hsp.
  exact (@AssemblyFullC.ASMFC.lib_ok_c_full TopGlueC.TopGlueC.cfg0P (PmHeapInst10.L0 (bv_unsigned sp)) (PmHeapInst10.HI0 (bv_unsigned sp))
           (PmHeapClosed10.HI0_ok_closed (bv_unsigned sp) PmFinal.cfg0 eq_refl) (PmLayoutInst.pm0_layout_L0 (bv_unsigned sp) (valid_sp_img sp Hsp)) fpm0 (TopGlueC.TopGlueC.Lay0 (bv_unsigned sp))).
Qed.
End PmLibInstC.
