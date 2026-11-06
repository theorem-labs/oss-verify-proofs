(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
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
Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Lemma img_200b8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131256) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 76260)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_200e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131304) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 76520)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_200f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131312) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 93380)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_200f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131320) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 95500)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20100_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20130_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131376) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 201736)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20138_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131384) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 333664)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20140_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131392) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 333656)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20148_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131400) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131264)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20150_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 131256)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_20158_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 333640)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_21380_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 136064) 1%nat = Some ([Z_to_bv 8 0]).
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
Lemma img_200e0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 131296) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_21378_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 136056) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma img_514f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_51500_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333056) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_51508_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333064) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_51750_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_51778_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_51790_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 333712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
End WithFP1.
