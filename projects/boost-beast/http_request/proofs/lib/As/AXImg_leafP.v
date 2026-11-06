(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AXRep AXPRep AXRep_leafP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma img_tchar_ok : img_tchar_hyp.
Proof. intros m AC. apply (ACONST_img_accessible m AL_TAB_IS_TOKEN_CHAR 256 AC). vm_compute. reflexivity. Qed.
Lemma img_qd_ok : img_qd_hyp.
Proof. intros m AC. apply (ACONST_img_accessible m AL_TAB_IS_QDCHAR 256 AC). vm_compute. reflexivity. Qed.
Lemma img_qp_ok : img_qp_hyp.
Proof. intros m AC. apply (ACONST_img_accessible m AL_TAB_IS_QPCHAR 256 AC). vm_compute. reflexivity. Qed.
End HCW.
