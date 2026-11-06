(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Abbreviation SEGS := Plain.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_1f5c0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 76164)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_1f5f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128496) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 76424)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f5f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128504) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 90568)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f600_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128512) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 92688)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f608_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f638_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 198936)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f640_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128576) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 330864)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f648_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 330856)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f650_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128592) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 128456)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f658_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 128448)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_1f660_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 330840)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_20890_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 133264) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
Lemma img_1f5e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 128488) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_20880_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 133248) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_50a00_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_50a10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330256) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_50a18_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330264) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_50c60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330848) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_50c88_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330888) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_50ca0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 330912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End WithFP1.
