(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Frame Cells Step.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Prog ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AOBJ_DYN_FLAGS : Z := 9.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_NID_OBJS_VA : Z := 0x2c3888.   (* [comment removed for export] *)
Definition P_OBJ_OBJS_VA : Z := 0x40044.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition static_obj_ok (nid lnlen : Z) : Prop :=
  exists i content, 0 <= i < NUM_OBJ /\ tab_entry i = (nid, content, lnlen) /\ content <> [].   (* [comment removed for export] *)

Definition obj_rep (m : mem) (OW : list block) (o : aobj bptr) (oadr : Z) : Prop :=
  match o with
  | ONone => oadr = 0
  | OStatic nid lnlen => oadr = P_NID_OBJS_VA + 40 * nid /\ 0 < nid < NUM_NID /\ static_obj_ok nid lnlen
  | ODyn blk data alloc content =>
      oadr = badr OW blk /\ In (blk, oadr, ASN1_OBJECT_SIZE) OW /\ In (data, badr OW data, alloc) OW /\ blk <> data /\
      0 < zlength content <= Z.min alloc 2147483647 /\ Forall (fun c => 0 <= c < 256) content /\
      rw_cells ctusegs m oadr (asn1_object_cells 0 0 0 (zlength content) (badr OW data) AOBJ_DYN_FLAGS) /\
      (exists junk, rw_cells ctusegs m (badr OW data)
                      [CB (Z.to_nat (zlength content)) (map (Z_to_bv 8) content); CB (Z.to_nat (alloc - zlength content)) junk])
  end.

(* [comment removed for export] *)
Lemma obj_rep_null : forall m OW o, obj_rep m OW o 0 -> o = ONone \/ exists blk data alloc content, o = ODyn blk data alloc content /\ badr OW blk = 0.
Proof.
  intros m OW [|nid lnlen|blk data alloc content] H; [left; reflexivity| | right].
  - cbn in H. unfold P_NID_OBJS_VA, NUM_NID in H. lia.
  - cbn in H. exists blk, data, alloc, content. split; [reflexivity| symmetry; exact (proj1 H)].
Qed.
