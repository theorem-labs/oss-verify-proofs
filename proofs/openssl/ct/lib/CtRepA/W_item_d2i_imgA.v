(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout GDesc RT_iface RT_client_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_item_d2i_stmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITEM_OCTET_A : Z := 0x547620.
Definition ITEM_INTEGER_A : Z := 0x547680.
Definition ITEM_ENUM_A : Z := 0x5476e0.
Definition ITEM_ANY_A : Z := 0x547860.
Definition item_ofA (utype : Z) : Z :=
  if utype =? V_ASN1_OCTET_STRING then ITEM_OCTET_A else if utype =? V_ASN1_INTEGER then ITEM_INTEGER_A else ITEM_ENUM_A.

(* [comment removed for export] *)
Definition item_cellsA (m : mem) (it u : Z) : Prop :=
  ro_cells ctasegs m it [C1 (Z_to_bv 8 0)]
  /\ ro_cells ctasegs m (it + 8) [C4 (Z_to_bv 64 u)]
  /\ ro_cells ctasegs m (it + 8) [C8 (Z_to_bv 64 u)]
  /\ ro_cells ctasegs m (it + 16) [C8 (Z_to_bv 64 0)]
  /\ ro_cells ctasegs m (it + 32) [C8 (Z_to_bv 64 0)]
  /\ acc ctasegs m it 56.

(* [comment removed for export] *)
Lemma ro_cells_recastA : forall m A cs cs',
  ro_cells ctasegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctasegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Ltac ulit := unfold ITEM_OCTET_A, ITEM_INTEGER_A, ITEM_ENUM_A, ITEM_ANY_A, RELRO_LO, RELRO_HI.
Local Ltac relro_cell A c :=
  lazymatch goal with |- ro_cells _ ?mm _ _ =>
    apply (relro_ro_cells mm A [c]); [assumption| cbn; auto| ulit; lia| ulit; cbn; lia| vm_compute; reflexivity] end.

Local Ltac item_tac IT u g :=
  intros Σ OW LB m H; pose proof (af_relro RT AF Σ m (AH_art _ _ _ _ H)) as R; unfold item_cellsA, IT;
  split; [| split; [| split; [| split; [| split]]]];
  [ relro_cell IT (C1 (Z_to_bv 8 0))
  | relro_cell (IT + 8) (C4 (Z_to_bv 64 u))
  | relro_cell (IT + 8) (C8 (Z_to_bv 64 u))
  | relro_cell (IT + 16) (C8 (Z_to_bv 64 0))
  | relro_cell (IT + 32) (C8 (Z_to_bv 64 0))
  | eapply (af_lib_acc_lit RT AF Σ m g); [exact (AH_art _ _ _ _ H)| vm_compute; reflexivity| ulit; cbn; lia| ulit; cbn; lia] ].

Lemma item_cellsA_octet : forall Σ OW LB m, AHEAP Σ OW LB m -> item_cellsA m ITEM_OCTET_A V_ASN1_OCTET_STRING.
Proof. item_tac ITEM_OCTET_A 4 (0x547620, 56, 96). Qed.
Lemma item_cellsA_integer : forall Σ OW LB m, AHEAP Σ OW LB m -> item_cellsA m ITEM_INTEGER_A V_ASN1_INTEGER.
Proof. item_tac ITEM_INTEGER_A 2 (0x547680, 56, 96). Qed.
Lemma item_cellsA_enum : forall Σ OW LB m, AHEAP Σ OW LB m -> item_cellsA m ITEM_ENUM_A V_ASN1_ENUMERATED.
Proof. item_tac ITEM_ENUM_A 10 (0x5476e0, 56, 96). Qed.
(* [comment removed for export] *)
Lemma item_cellsA_any : forall Σ OW LB m, AHEAP Σ OW LB m -> item_cellsA m ITEM_ANY_A (2^64 - 4).
Proof. item_tac ITEM_ANY_A (2^64 - 4) (0x547860, 56, 96). Qed.

Lemma item_cellsA_of : forall Σ OW LB m e utype, AHEAP Σ OW LB m -> d2i_entryA e utype -> item_cellsA m (item_ofA utype) utype.
Proof.
  intros Σ OW LB m e utype H [_ ->]; unfold item_ofA; cbn. eapply item_cellsA_octet; exact H.   (* [comment removed for export] *)
Qed.

Lemma item_ofA_range : forall utype, 0x547620 <= item_ofA utype /\ item_ofA utype + 56 <= 0x547720.
Proof. intros utype. unfold item_ofA, ITEM_OCTET_A, ITEM_INTEGER_A, ITEM_ENUM_A. destruct (utype =? _); [lia|]. destruct (utype =? _); lia. Qed.

End WithRT.

(* [comment removed for export] *)
Local Ltac rom_cell4 A v :=
  intros m MI;
  let bs := eval vm_compute in (match image_bytes ctasegs A 4 with Some bs => bs | None => [] end) in
  apply (ro_cells_recastA m A [CB 4 bs] [C4 (Z_to_bv 64 v)]);
  [ apply (ro_cells_image ctasegs m A bs MI); [vm_compute; reflexivity| lia| cbn; lia]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ].

(* [comment removed for export] *)
Lemma jt_embed_d2iA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m 0x729f8 [C4 (Z_to_bv 64 1891992)]. Proof. rom_cell4 0x729f8 1891992. Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma jt_ex_prim_intA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m 0x72a18 [C4 (Z_to_bv 64 1897752)]. Proof. rom_cell4 0x72a18 1897752. Qed.   (* [comment removed for export] *)
Lemma jt_ex_prim_octA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m 0x72a20 [C4 (Z_to_bv 64 1898084)]. Proof. rom_cell4 0x72a20 1898084. Qed.   (* [comment removed for export] *)
Lemma jt_ex_prim_enumA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m 0x72a38 [C4 (Z_to_bv 64 1897752)]. Proof. rom_cell4 0x72a38 1897752. Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma jt_embed_freeA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m 0x72e18 [C4 (Z_to_bv 64 1904572)]. Proof. rom_cell4 0x72e18 1904572. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition jt_prim_entryA (utype : Z) : Z := if utype =? V_ASN1_OCTET_STRING then 1898084 else 1897752.   (* [comment removed for export] *)
Lemma jt_ex_prim_ofA : forall m e utype, mem_inv ctasegs m -> d2i_entryA e utype ->
  ro_cells ctasegs m (0x72a14 + 4 * (utype - 1)) [C4 (Z_to_bv 64 (jt_prim_entryA utype))].
Proof.
  intros m e utype MI [_ ->]; unfold jt_prim_entryA; cbn -[Z_to_bv ro_cells ctasegs]. apply jt_ex_prim_octA; exact MI.   (* [comment removed for export] *)
Qed.

Lemma utype_casesA : forall e utype, d2i_entryA e utype -> utype = 4 \/ utype = 2 \/ utype = 10.
Proof. intros e utype [_ ->]; unfold V_ASN1_OCTET_STRING; lia. Qed.   (* [comment removed for export] *)
