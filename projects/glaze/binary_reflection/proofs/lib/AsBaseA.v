(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import TopProof4 AsDrvRootA AsWalkRowsA AsAllocMSbFin2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem A_root_closed : TopProof4.A_root.
Proof.
  exact (AsDrvRootA.A_root_holds
           (AsWalkRowsA.WALK_all_A
              (fun RC hv BF BT => @AsAllocMSbFin2.H_SEC_S RC hv BF BT)
              (fun RC hv BF BT => @AsAllocMSbFin2.H_SEC_DR RC hv BF BT))).
Qed.

(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Theorem A_root_f_closed : TopHalts.A_root_f.
Proof.
  exact (AsDrvRootA.A_root_f_gen
           (AsWalkRowsA.WALK_all_A
              (fun RC hv BF BT => @AsAllocMSbFin2.H_SEC_S RC hv BF BT)
              (fun RC hv BF BT => @AsAllocMSbFin2.H_SEC_DR RC hv BF BT))
           _ StoreOk.RunLim.LMIN_le_source).
Qed.
