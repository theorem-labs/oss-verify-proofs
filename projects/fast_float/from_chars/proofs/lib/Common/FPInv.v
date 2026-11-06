(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fcsr_frm (fc : bv 32) : Z := Z.land (Z.shiftr (bv_unsigned fc) 5) 7.

(* [comment removed for export] *)
Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.

Lemma frm0_iff : forall fc, frm0 fc <-> fcsr_frm fc = 0%Z.
Proof. intros fc. unfold frm0, fcsr_frm. tauto. Qed.

(* [comment removed for export] *)
Lemma frm0_fx0 : frm0 (@fp_csr fx0).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition fp_ok (fx : FPState) : Prop := frm0 (@fp_csr fx).

Lemma fp_ok_fx0 : fp_ok fx0.
Proof. exact frm0_fx0. Qed.
