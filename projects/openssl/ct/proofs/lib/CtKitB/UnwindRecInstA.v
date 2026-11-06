(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import RT_iface RT_unwind_kit SiteChk RT_unwind_rec.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import UnwindA EdgesA EdgesInstA UnwindRecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ASN1_COLLECT_E : Z := 0x2462d4.
Definition ASN1_COLLECT_REC_RA : Z := 0x2463f0.     (* [comment removed for export] *)
Definition ASN1_COLLECT_DEPTH : nat := 6.
Definition I2O_SCT_LIST_E : Z := 0x34af40.
Definition I2O_SCT_LIST_REC_RA : Z := 0x34b2a8.    (* [comment removed for export] *)
Definition I2O_SCT_LIST_DEPTH : nat := 6.

Lemma asn1_collect_rec_closed : rec_closedb ASN1_COLLECT_E ASN1_COLLECT_REC_RA ASN1_COLLECT_DEPTH = true.
Proof. vm_compute. reflexivity. Qed.

#[export] Instance UR_asn1_collect_B : @UnwindRec UK_A ASN1_COLLECT_E ASN1_COLLECT_REC_RA ASN1_COLLECT_DEPTH :=
  {| uk_ctxJ := site_ctxJ ASN1_COLLECT_E ASN1_COLLECT_DEPTH;
     uk_ctxJ_enter := site_ctxJ_enter ASN1_COLLECT_E ASN1_COLLECT_DEPTH;
     uk_ctxJ_rec := site_ctxJ_rec ASN1_COLLECT_E ASN1_COLLECT_DEPTH;
     uk_ctxJ_call := site_ctxJ_call ASN1_COLLECT_E ASN1_COLLECT_REC_RA ASN1_COLLECT_DEPTH asn1_collect_rec_closed;
     uk_ctxJ_leaf := site_ctxJ_leaf ASN1_COLLECT_E ASN1_COLLECT_REC_RA ASN1_COLLECT_DEPTH asn1_collect_rec_closed |}.

Lemma i2o_sct_list_rec_closed : rec_closedb I2O_SCT_LIST_E I2O_SCT_LIST_REC_RA I2O_SCT_LIST_DEPTH = true.
Proof. vm_compute. reflexivity. Qed.

#[export] Instance UR_i2o_SCT_LIST_A : @UnwindRec UK_A I2O_SCT_LIST_E I2O_SCT_LIST_REC_RA I2O_SCT_LIST_DEPTH :=
  {| uk_ctxJ := site_ctxJ I2O_SCT_LIST_E I2O_SCT_LIST_DEPTH;
     uk_ctxJ_enter := site_ctxJ_enter I2O_SCT_LIST_E I2O_SCT_LIST_DEPTH;
     uk_ctxJ_rec := site_ctxJ_rec I2O_SCT_LIST_E I2O_SCT_LIST_DEPTH;
     uk_ctxJ_call := site_ctxJ_call I2O_SCT_LIST_E I2O_SCT_LIST_REC_RA I2O_SCT_LIST_DEPTH i2o_sct_list_rec_closed;
     uk_ctxJ_leaf := site_ctxJ_leaf I2O_SCT_LIST_E I2O_SCT_LIST_REC_RA I2O_SCT_LIST_DEPTH i2o_sct_list_rec_closed |}.

(* [comment removed for export] *)
Example uk_ctxJ_example (X0 : list Z) :
  uk_ctx ASN1_COLLECT_E X0 -> uk_ctx 0x1f8bdc (0x2464cc :: repeat ASN1_COLLECT_REC_RA 2 ++ X0).
Proof.
  intros H. apply (uk_ctxJ_call 2%nat X0 0x2464cc 0x1f8bdc E_asn1_collect_2464a8); [unfold ASN1_COLLECT_REC_RA; lia|].
  apply uk_ctxJ_rec; [| unfold ASN1_COLLECT_DEPTH; lia]. apply uk_ctxJ_rec; [| unfold ASN1_COLLECT_DEPTH; lia].
  apply uk_ctxJ_enter. exact H.
Qed.

(* [comment removed for export] *)
Example uk_ctxJ_i2o_example (ras : list Z) :
  uk_ctx 0x34b748 ras -> uk_ctxJ (f:=I2O_SCT_LIST_E) 1%nat (0x34b850 :: ras).
Proof.
  intros H. apply uk_ctxJ_rec; [| unfold I2O_SCT_LIST_DEPTH; lia]. apply uk_ctxJ_enter. exact (uk_ctx_call _ _ _ _ E_i2d_SCT_LIST_34b82c H).
Qed.

