(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "app"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "FUEL_r2"; "cutpcs_r2"; "cuts_r2"; "exits_r2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA"; "check_cutA'"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import FastChkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CC : ltac2:(tb__ "0|0|
S8S0FT;") := ltac2:(tb__ "0|0|
ScS3S4S5S9S1S8S6S7A3A5").

Lemma chk_Pre : CC Pre_r2 = true.  Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ks : CC Ks = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ka : CC Ka = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kr : CC Kr = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_K_rf : CC K_rf = true.   Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kf : CC Kf = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kfan : CC Kfan = true.   Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Km : CC Km = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ki : CC Ki = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kc : CC Kc = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kcm : CC Kcm = true.     Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kg : CC Kg = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kgb : CC Kgb = true.     Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kgbm : CC Kgbm = true.   Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kx : CC Kx = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma check_r2 : ltac2:(tb__ "0|0|
SaS0SbS3S4S5S9S6S7A6S2A3").
Proof.
  rewrite <- check_cfgA'_eq. unfold check_cfgA'.
  change (forallb_lazy CC [Pre_r2; Ks; Ka; Kr; K_rf; Kf; Kfan; Km; Ki; Kc; Kcm; Kg; Kgb; Kgbm; Kx] = true).
  apply forallb_lazy_cons_true; [exact chk_Pre|].
  apply forallb_lazy_cons_true; [exact chk_Ks|].
  apply forallb_lazy_cons_true; [exact chk_Ka|].
  apply forallb_lazy_cons_true; [exact chk_Kr|].
  apply forallb_lazy_cons_true; [exact chk_K_rf|].
  apply forallb_lazy_cons_true; [exact chk_Kf|].
  apply forallb_lazy_cons_true; [exact chk_Kfan|].
  apply forallb_lazy_cons_true; [exact chk_Km|].
  apply forallb_lazy_cons_true; [exact chk_Ki|].
  apply forallb_lazy_cons_true; [exact chk_Kc|].
  apply forallb_lazy_cons_true; [exact chk_Kcm|].
  apply forallb_lazy_cons_true; [exact chk_Kg|].
  apply forallb_lazy_cons_true; [exact chk_Kgb|].
  apply forallb_lazy_cons_true; [exact chk_Kgbm|].
  apply forallb_lazy_cons_true; [exact chk_Kx|].
  reflexivity.
Qed.
