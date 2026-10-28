(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Frame Cells Step.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Prog ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApObjRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation AOBJ_DYN_FLAGS := CtRepP.ApObjRep.AOBJ_DYN_FLAGS.
Notation static_obj_ok := CtRepP.ApObjRep.static_obj_ok.
Definition A_NID_OBJS_VA : Z := 0x534500.   (* [comment removed for export] *)
Definition A_OBJ_OBJS_VA : Z := 0x6f780.     (* [comment removed for export] *)

Definition obj_rep (m : mem) (OW : list block) (o : aobj bptr) (oadr : Z) : Prop :=
  match o with
  | ONone => oadr = 0
  | OStatic nid lnlen => oadr = A_NID_OBJS_VA + 40 * nid /\ 0 < nid < NUM_NID /\ static_obj_ok nid lnlen
  | ODyn blk data alloc content =>
      oadr = badr OW blk /\ In (blk, oadr, ASN1_OBJECT_SIZE) OW /\ In (data, badr OW data, alloc) OW /\ blk <> data /\
      0 < zlength content <= Z.min alloc 67108863 /\ Forall (fun c => 0 <= c < 256) content /\
      rw_cells ctasegs m oadr (asn1_object_cells 0 0 0 (zlength content) (badr OW data) AOBJ_DYN_FLAGS) /\
      (exists junk, rw_cells ctasegs m (badr OW data)
                      [CB (Z.to_nat (zlength content)) (map (Z_to_bv 8) content); CB (Z.to_nat (alloc - zlength content)) junk])
  end.

(* [comment removed for export] *)
Lemma obj_rep_null : forall m OW o, obj_rep m OW o 0 -> o = ONone \/ exists blk data alloc content, o = ODyn blk data alloc content /\ badr OW blk = 0.
Proof.
  intros m OW [|nid lnlen|blk data alloc content] H; [left; reflexivity| | right].
  - cbn in H. unfold A_NID_OBJS_VA, NUM_NID in H. lia.
  - cbn in H. exists blk, data, alloc, content. split; [reflexivity| symmetry; exact (proj1 H)].
Qed.
