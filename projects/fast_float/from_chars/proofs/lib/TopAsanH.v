(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import M4Pure.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require M4AHarn HarnDev.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxFFA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanBodyIfOk AsanTopG TopAsanF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem harn_cons_closed : Forall (con_ok Asan.M.loaded_segments) HarnDev.CONS.
Proof.
  pose proof KxFFA.M4A_cons_closed as H. unfold M4AHarn.M4A_CONS in H.
  apply Forall_cons_iff in H as [Hd H]. apply Forall_cons_iff in H as [Hi H]. apply Forall_cons_iff in H as [Hf _].
  unfold HarnDev.CONS. apply Forall_cons; [exact Hd |]. apply Forall_cons; [exact Hf |]. apply Forall_cons; [exact Hi | apply Forall_nil].
Qed.

(* [comment removed for export] *)
Lemma harn_hyps_closed : FXD.AsanBodyIfOk.harn_hyps FXD.TopAsanF.DCFG.
Proof. unfold FXD.AsanBodyIfOk.harn_hyps. exact harn_cons_closed. Qed.
Definition Hleaves := FXD.AsanTopG.hleaves FXD.TopAsanF.DCFG eq_refl eq_refl harn_hyps_closed.
Theorem base_asan : ltac:(let t := type of (FXD.TopAsanF.base_asan_from Hleaves) in exact t).
Proof. exact (FXD.TopAsanF.base_asan_from Hleaves). Qed.
