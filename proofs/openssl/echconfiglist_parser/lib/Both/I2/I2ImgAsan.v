(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Export ASegs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState FxMem FxRel FxImage I2Image.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition IMX : fimage := odflt [] (mk_fimage asegs).
Definition IM : fimage := im_ro IMX.

(* [comment removed for export] *)
Lemma IMX_isSome : match mk_fimage asegs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma IMX_eq : mk_fimage asegs = Some IMX.
Proof.
  unfold IMX. pose proof IMX_isSome as H.
  destruct (mk_fimage asegs) as [im|]; [reflexivity | discriminate H].
Qed.

Lemma IMX_ok : image_ok asegs IMX.
Proof. exact (mk_fimage_ok asegs IMX IMX_eq). Qed.

Lemma IMX_wr_ok : image_wr_ok IMX.
Proof. exact (mk_fimage_wr_ok asegs IMX IMX_eq). Qed.
