(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Module PMUN_cert.
Import NUMU_D.PMUN_defs.
(* [comment removed for export] *)

Lemma pmun_cert : SP.pcheck SG SNU.snu_gfp (NRC.nrc_ok SG) PMUN PMUN_IT 3000 true ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PMUN_cert.

Module PWFU_cert.
Import NUMU_D.SLOWU_sum.
Import NUMU_D.PWFU_defs.
(* [comment removed for export] *)

Lemma pwfu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PWFU PWFU_IT 3000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PWFU_cert.

Module SFPU_cert.
Import NUMU_D.PWFU_sum.
Import NUMU_D.SFPU_defs.
(* [comment removed for export] *)

Lemma sfpu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) SFPU SFPU_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SFPU_cert.

Module SFPCU_cert.
Import NUMU_D.PWFU_sum.
Import NUMU_D.SFPCU_defs.
(* [comment removed for export] *)

Lemma sfpcu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) SFPCU SFPCU_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SFPCU_cert.

Module PFFU_cert.
Import NUMU_D.PWFU_sum.
Import NUMU_D.PFFU_defs.
(* [comment removed for export] *)

Lemma pffu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PFFU PFFU_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PFFU_cert.

Module PFFCU_cert.
Import NUMU_D.PWFU_sum.
Import NUMU_D.PFFCU_defs.
(* [comment removed for export] *)

Lemma pffcu_cert : SP.pcheck SG (fun _ _ => []) (fun _ => false) PFFCU PFFCU_IT 2000 false ([]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End PFFCU_cert.
