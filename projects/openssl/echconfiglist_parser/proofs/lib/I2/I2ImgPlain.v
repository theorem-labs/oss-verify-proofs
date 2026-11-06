(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Export RSegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState FxMem FxRel FxImage I2Image.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition IMX : fimage := odflt [] (mk_fimage rsegs).
Definition IM : fimage := im_ro IMX.

(* [comment removed for export] *)
Lemma IMX_isSome : match mk_fimage rsegs with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma IMX_eq : mk_fimage rsegs = Some IMX.
Proof.
  unfold IMX. pose proof IMX_isSome as H.
  destruct (mk_fimage rsegs) as [im|]; [reflexivity | discriminate H].
Qed.

Lemma IMX_ok : image_ok rsegs IMX.
Proof. exact (mk_fimage_ok rsegs IMX IMX_eq). Qed.

Lemma IMX_wr_ok : image_wr_ok IMX.
Proof. exact (mk_fimage_wr_ok rsegs IMX IMX_eq). Qed.
