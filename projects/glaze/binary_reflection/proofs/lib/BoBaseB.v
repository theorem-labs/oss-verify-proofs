(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import TopProof4 BoDrvRootA BoWalkClosedB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem B_root_closed : TopProof4.B_root.
Proof. exact (BoDrvRootA.B_root_holds BoWalkClosedB.WALK_all_B_closed). Qed.

(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Theorem B_root_f_closed : TopHalts.B_root_f.
Proof. exact (BoDrvRootA.B_root_f_gen BoWalkClosedB.WALK_all_B_closed _ StoreOk.RunLim.LMIN_le_source). Qed.
