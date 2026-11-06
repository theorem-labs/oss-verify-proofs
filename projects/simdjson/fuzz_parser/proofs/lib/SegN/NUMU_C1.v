(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Module MMVU_cert.
Import NUMU_D.MMVU_defs.
(* [comment removed for export] *)

Lemma mmvu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) MMVU MMVU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End MMVU_cert.

Module LADU_cert.
Import NUMU_D.LADU_defs.
(* [comment removed for export] *)

Lemma ladu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) LADU LADU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End LADU_cert.

Module LMU_cert.
Import NUMU_D.LADU_sum.
Import NUMU_D.LMU_defs.
(* [comment removed for export] *)

Lemma lmu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) LMU LMU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End LMU_cert.

Module P5U_cert.
Import NUMU_D.LMU_sum.
Import NUMU_D.P5U_defs.
(* [comment removed for export] *)

Lemma p5u_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) P5U P5U_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End P5U_cert.

Module SHLU_cert.
Import NUMU_D.MMVU_sum.
Import NUMU_D.SHLU_defs.
(* [comment removed for export] *)

Lemma shlu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) SHLU SHLU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SHLU_cert.

Module NDCU_cert.
Import NUMU_D.P5U_sum.
Import NUMU_D.SHLU_sum.
Import NUMU_D.NDCU_defs.
(* [comment removed for export] *)

Lemma ndcu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) NDCU NDCU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End NDCU_cert.

Module MMVUN_cert.
Import NUMU_D.MMVUN_defs.
(* [comment removed for export] *)

Lemma mmvun_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) MMVUN MMVUN_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End MMVUN_cert.

Module LADUN_cert.
Import NUMU_D.LADUN_defs.
(* [comment removed for export] *)

Lemma ladun_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) LADUN LADUN_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End LADUN_cert.

Module LMUN_cert.
Import NUMU_D.LADUN_sum.
Import NUMU_D.LMUN_defs.
(* [comment removed for export] *)

Lemma lmun_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) LMUN LMUN_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End LMUN_cert.

Module P5UN_cert.
Import NUMU_D.LMUN_sum.
Import NUMU_D.P5UN_defs.
(* [comment removed for export] *)

Lemma p5un_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) P5UN P5UN_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End P5UN_cert.

Module SHLUN_cert.
Import NUMU_D.MMVUN_sum.
Import NUMU_D.SHLUN_defs.
(* [comment removed for export] *)

Lemma shlun_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) SHLUN SHLUN_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SHLUN_cert.

Module HI64U_cert.
Import NUMU_D.HI64U_defs.
(* [comment removed for export] *)

Lemma hi64u_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) HI64U HI64U_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End HI64U_cert.

Module PDCU_cert.
Import NUMU_D.P5UN_sum.
Import NUMU_D.SHLUN_sum.
Import NUMU_D.HI64U_sum.
Import NUMU_D.PDCU_defs.
(* [comment removed for export] *)

Lemma pdcu_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) PDCU PDCU_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PDCU_cert.
