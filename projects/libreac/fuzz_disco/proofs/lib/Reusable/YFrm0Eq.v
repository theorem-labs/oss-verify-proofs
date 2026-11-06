(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for fuzz_disco (both images). *)
(* The core's frm0 guard (lib/Reusable/YFrm0.v) and the program walks' frm0 (lib/Lib/FP.v) are one definition.
   Required only by the walk side: it loads lib/Lib/FP.v, whose imports redefine Zify.zify_pre_hook globally, so no
   core file Requires it. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFrm0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
Lemma frm0_same : YFrm0.frm0 = lib.Lib.FP.frm0.
Proof. reflexivity. Qed.
Lemma frm0_iff : forall c, YFrm0.frm0 c <-> lib.Lib.FP.frm0 c.
Proof. intros c. reflexivity. Qed.
