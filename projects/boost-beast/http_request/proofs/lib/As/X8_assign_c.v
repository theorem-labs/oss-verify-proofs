(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AXRep AXRep2 X8_assign.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma IMG_VT_closed : forall m, ACONST m -> accessible m (AVP_HTTP_ECAT + 48) 8.
Proof. intros m AC. apply (ACONST_img_accessible m _ _ AC). vm_compute. reflexivity. Qed.

Lemma IMG_CAT_closed : forall m, ACONST m -> accessible m (AG_HTTP_CAT + 16) 36.
Proof. intros m AC. apply (ACONST_img_accessible m _ _ AC). vm_compute. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma aassignA_closed : asan_memset_stmt -> aassignA_stmt.
Proof. intros MS. exact (aassignA_spec MS IMG_VT_closed IMG_CAT_closed). Qed.

Lemma aassignB_closed : asan_memset_stmt -> aassignB_stmt.
Proof. intros MS. exact (aassignB_spec MS IMG_VT_closed IMG_CAT_closed). Qed.

End HCW.
