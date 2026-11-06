(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMP_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Module MMV_cert.
Import NUMP_D.MMV_defs.
(* [comment removed for export] *)

Lemma mmv_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) MMV MMV_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End MMV_cert.

Module LM_cert.
Import NUMP_D.LM_defs.
(* [comment removed for export] *)

Lemma lm_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) LM LM_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End LM_cert.

Module P5_cert.
Import NUMP_D.LM_sum.
Import NUMP_D.P5_defs.
(* [comment removed for export] *)

Lemma p5_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) P5 P5_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End P5_cert.

Module NDC_cert.
Import NUMP_D.P5_sum.
Import NUMP_D.MMV_sum.
Import NUMP_D.NDC_defs.
(* [comment removed for export] *)

Lemma ndc_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) NDC NDC_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End NDC_cert.

Module PDC_cert.
Import NUMP_D.P5_sum.
Import NUMP_D.MMV_sum.
Import NUMP_D.PDC_defs.
(* [comment removed for export] *)

Lemma pdc_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PDC PDC_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PDC_cert.

Module PM_cert.
Import NUMP_D.PM_defs.
(* [comment removed for export] *)

Lemma pm_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PM PM_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PM_cert.

Module PWF_cert.
Import NUMP_D.SLOW_sum.
Import NUMP_D.PWF_defs.
(* [comment removed for export] *)

Lemma pwf_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PWF PWF_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PWF_cert.

Module SFP_cert.
Import NUMP_D.PWF_sum.
Import NUMP_D.SFP_defs.
(* [comment removed for export] *)

Lemma sfp_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) SFP SFP_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SFP_cert.

Module SFPC_cert.
Import NUMP_D.PWF_sum.
Import NUMP_D.SFPC_defs.
(* [comment removed for export] *)

Lemma sfpc_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) SFPC SFPC_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SFPC_cert.

Module PFF_cert.
Import NUMP_D.PWF_sum.
Import NUMP_D.PFF_defs.
(* [comment removed for export] *)

Lemma pff_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PFF PFF_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PFF_cert.

Module PFFC_cert.
Import NUMP_D.PWF_sum.
Import NUMP_D.PFFC_defs.
(* [comment removed for export] *)

Lemma pffc_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PFFC PFFC_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PFFC_cert.
