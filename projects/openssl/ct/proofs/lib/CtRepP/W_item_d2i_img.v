(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import ApPrim.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs ApRep W_item_d2i_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

Lemma ro_cells_recast : forall m A cs cs',
  ro_cells ctpsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctpsegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

(* [comment removed for export] *)
Definition ITEM_OCTET : Z := 0x28d070.
Definition ITEM_INTEGER : Z := 0x28d0a8.
Definition ITEM_ENUM : Z := 0x28d0e0.
Definition ITEM_ANY : Z := 0x28d1c0.
Definition item_of (utype : Z) : Z :=
  if utype =? V_ASN1_OCTET_STRING then ITEM_OCTET else if utype =? V_ASN1_INTEGER then ITEM_INTEGER else ITEM_ENUM.

(* [comment removed for export] *)
Definition item_cells (m : mem) (it u : Z) : Prop :=
  ro_cells ctpsegs m it [C1 (Z_to_bv 8 0)]
  /\ ro_cells ctpsegs m (it + 8) [C4 (Z_to_bv 64 u)]
  /\ ro_cells ctpsegs m (it + 8) [C8 (Z_to_bv 64 u)]
  /\ ro_cells ctpsegs m (it + 16) [C8 (Z_to_bv 64 0)]
  /\ ro_cells ctpsegs m (it + 32) [C8 (Z_to_bv 64 0)].

Local Ltac img_cell A n c :=
  let bs := eval vm_compute in (match image_bytes ctpsegs A n with Some bs => bs | None => [] end) in
  lazymatch goal with |- ro_cells _ ?mm _ _ =>
  apply (ro_cells_recast mm A [CB n bs] [c]);
  [ apply (ap_img_ro_cells mm A n bs); [assumption| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ] end.

Lemma item_cells_octet : forall m, ap_img m -> item_cells m ITEM_OCTET V_ASN1_OCTET_STRING.
Proof.
  intros m HI. unfold item_cells, ITEM_OCTET, V_ASN1_OCTET_STRING. split; [| split; [| split; [| split]]].
  - img_cell 2674800 1%nat (C1 (Z_to_bv 8 0)).
  - img_cell 2674808 4%nat (C4 (Z_to_bv 64 4)).
  - img_cell 2674808 8%nat (C8 (Z_to_bv 64 4)).
  - img_cell 2674816 8%nat (C8 (Z_to_bv 64 0)).
  - img_cell 2674832 8%nat (C8 (Z_to_bv 64 0)).
Qed.

Lemma item_cells_integer : forall m, ap_img m -> item_cells m ITEM_INTEGER V_ASN1_INTEGER.
Proof.
  intros m HI. unfold item_cells, ITEM_INTEGER, V_ASN1_INTEGER. split; [| split; [| split; [| split]]].
  - img_cell 2674856 1%nat (C1 (Z_to_bv 8 0)).
  - img_cell 2674864 4%nat (C4 (Z_to_bv 64 2)).
  - img_cell 2674864 8%nat (C8 (Z_to_bv 64 2)).
  - img_cell 2674872 8%nat (C8 (Z_to_bv 64 0)).
  - img_cell 2674888 8%nat (C8 (Z_to_bv 64 0)).
Qed.

Lemma item_cells_enum : forall m, ap_img m -> item_cells m ITEM_ENUM V_ASN1_ENUMERATED.
Proof.
  intros m HI. unfold item_cells, ITEM_ENUM, V_ASN1_ENUMERATED. split; [| split; [| split; [| split]]].
  - img_cell 2674912 1%nat (C1 (Z_to_bv 8 0)).
  - img_cell 2674920 4%nat (C4 (Z_to_bv 64 10)).
  - img_cell 2674920 8%nat (C8 (Z_to_bv 64 10)).
  - img_cell 2674928 8%nat (C8 (Z_to_bv 64 0)).
  - img_cell 2674944 8%nat (C8 (Z_to_bv 64 0)).
Qed.

Lemma item_cells_of : forall m e utype, ap_img m -> d2i_entry e utype -> item_cells m (item_of utype) utype.
Proof.
  intros m e utype HI [[_ ->]|[[_ ->]|[_ ->]]]; unfold item_of; cbn.
  - apply item_cells_octet; exact HI.
  - apply item_cells_integer; exact HI.
  - apply item_cells_enum; exact HI.
Qed.

(* [comment removed for export] *)
Lemma item_cells_any : forall m, ap_img m ->
  ro_cells ctpsegs m ITEM_ANY [C1 (Z_to_bv 8 0)] /\ ro_cells ctpsegs m (ITEM_ANY + 8) [C4 (Z_to_bv 64 (2^32 - 4))]
  /\ ro_cells ctpsegs m (ITEM_ANY + 16) [C8 (Z_to_bv 64 0)] /\ ro_cells ctpsegs m (ITEM_ANY + 32) [C8 (Z_to_bv 64 0)].
Proof.
  intros m HI. unfold ITEM_ANY. split; [| split; [| split]].
  - img_cell 2675136 1%nat (C1 (Z_to_bv 8 0)).
  - img_cell 2675144 4%nat (C4 (Z_to_bv 64 (2^32 - 4))).
  - img_cell 2675152 8%nat (C8 (Z_to_bv 64 0)).
  - img_cell 2675168 8%nat (C8 (Z_to_bv 64 0)).
Qed.

(* [comment removed for export] *)
Local Ltac rom_cell4 A v :=
  intros m MI;
  let bs := eval vm_compute in (match image_bytes ctpsegs A 4 with Some bs => bs | None => [] end) in
  apply (ro_cells_recast m A [CB 4 bs] [C4 (Z_to_bv 64 v)]);
  [ apply (ro_cells_image ctpsegs m A bs MI); [vm_compute; reflexivity| lia| cbn; lia]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ].

(* [comment removed for export] *)
Lemma jt_embed_d2i : forall m, mem_inv ctpsegs m -> ro_cells ctpsegs m 267692 [C4 (Z_to_bv 64 801668)]. Proof. rom_cell4 267692 801668. Qed.
(* [comment removed for export] *)
Lemma jt_ex_prim_int : forall m, mem_inv ctpsegs m -> ro_cells ctpsegs m 267724 [C4 (Z_to_bv 64 805564)]. Proof. rom_cell4 267724 805564. Qed.
Lemma jt_ex_prim_oct : forall m, mem_inv ctpsegs m -> ro_cells ctpsegs m 267732 [C4 (Z_to_bv 64 805856)]. Proof. rom_cell4 267732 805856. Qed.
Lemma jt_ex_prim_enum : forall m, mem_inv ctpsegs m -> ro_cells ctpsegs m 267756 [C4 (Z_to_bv 64 805564)]. Proof. rom_cell4 267756 805564. Qed.
(* [comment removed for export] *)
Lemma jt_embed_free : forall m, mem_inv ctpsegs m -> ro_cells ctpsegs m 268016 [C4 (Z_to_bv 64 809200)]. Proof. rom_cell4 268016 809200. Qed.

(* [comment removed for export] *)
Definition jt_prim_entry (utype : Z) : Z := if utype =? V_ASN1_OCTET_STRING then 805856 else 805564.
Lemma jt_ex_prim_of : forall m e utype, mem_inv ctpsegs m -> d2i_entry e utype ->
  ro_cells ctpsegs m (267720 + 4 * (utype - 1)) [C4 (Z_to_bv 64 (jt_prim_entry utype))].
Proof.
  intros m e utype MI [[_ ->]|[[_ ->]|[_ ->]]]; unfold jt_prim_entry; cbn -[Z_to_bv ro_cells ctpsegs].
  - apply jt_ex_prim_oct; exact MI.
  - apply jt_ex_prim_int; exact MI.
  - apply jt_ex_prim_enum; exact MI.
Qed.

End WithCeiling0.
