(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK05 YA0l YG00 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00 YB0z YF90 YF93.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YF1n.
Section a.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem afree_realizes_closed : forall B, TraSyms B -> (forall t, as_dhash B t = tra_dhash t) -> afree_realizes trasegs B.
Proof. first [ exact (YF1n.afree_realizes_closed (imgk := YF00.K_tra)) | solve [ eapply (YF1n.afree_realizes_closed (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YF1n.afree_realizes_closed (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End a.
