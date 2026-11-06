(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition nb_ok (L : dsv) : Prop := 0 <= sv_nblock L <= 900000.

(* [comment removed for export] *)
Definition dinv_H14 (L : dsv) (d : dst) : Prop := nb_ok L.
Definition dinv_HEND (L : dsv) (d : dst) : Prop := nb_ok L.
Definition dinv_HBCRC (L : dsv) (d : dst) : Prop := nb_ok L /\ 0 <= d_sbcrc d < 2^32.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition op_ok (d : dst) : Prop := hdr_ok d.
Definition dinv_HMAP (L : dsv) (d : dst) : Prop :=
  nb_ok L /\ op_ok d /\ 0 <= sv_i L < 16 /\
  (forall k, 0 <= k < sv_i L -> 0 <= zget (d_inUse16 d) k <= 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma d_origPtr_set_origPtr : forall d x, d_origPtr (d_set_origPtr d x) = x.
Proof. intros []; reflexivity. Qed.
Lemma d_bs100k_set_origPtr : forall d x, d_bs100k (d_set_origPtr d x) = d_bs100k d.
Proof. intros []; reflexivity. Qed.
Lemma edge_27 : forall F v L d s,
  dgo F (gb_after 27 v L d s) =
  if Z.lor (Z.shiftl (d_origPtr d) 8) v <? 0
  then DRet BZ_DATA_ERROR L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s
  else if 10 + 100000 * d_bs100k d <? Z.lor (Z.shiftl (d_origPtr d) 8) v
  then DRet BZ_DATA_ERROR L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s
  else drun F 28 (sv_set_i L 0) (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s.
Proof.
  intros F v L d s. rewrite gb_after_27. cbv zeta. rewrite d_origPtr_set_origPtr, d_bs100k_set_origPtr.
  rewrite !dgo_if, !dgo_DRet, dgo_DGo. reflexivity.
Qed.
