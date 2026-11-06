(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import M4Pure.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnDev.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxFFB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyIfOk AsanTopG TopBothF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem harn_cons_closed : Forall (con_ok AsanUbsan.M.loaded_segments) M4HB.HarnDev.CONS.
Proof.
  unfold M4HB.HarnDev.CONS. apply Forall_cons; [exact KxFFB.fcd_b_closed |]. apply Forall_cons; [exact KxFFB.fcf_b_closed |].
  apply Forall_cons; [exact OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.fci_ok | apply Forall_nil].
Qed.

Lemma harn_hyps_closed : FXDB.AsanBodyIfOk.harn_hyps FXDB.TopBothF.DCFG.
Proof. unfold FXDB.AsanBodyIfOk.harn_hyps. exact harn_cons_closed. Qed.
Definition Hleaves := FXDB.AsanTopG.hleaves FXDB.TopBothF.DCFG eq_refl eq_refl harn_hyps_closed.
Theorem base_both : ltac:(let t := type of (FXDB.TopBothF.base_both_from Hleaves) in exact t).
Proof. exact (FXDB.TopBothF.base_both_from Hleaves). Qed.
