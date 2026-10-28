(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep ARepQ ARepQP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Record qrconc := mkQR {
  qr_loc : list qbatchc;              (* [comment removed for export] *)
  qr_glob : list qbatchc;             (* [comment removed for export] *)
  qr_ia : bool;                       (* [comment removed for export] *)
  qr_tmp : list (abatch * qbatchc);   (* [comment removed for export] *)
  qr_pendb : list Z;                  (* [comment removed for export] *)
  qr_pend : list (achunk * Z);        (* [comment removed for export] *)
  qr_qpend : list (Z * Z)             (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition qr_entries (st : astate) (R : qrconc) : list (achunk * Z) :=
  qentries (a_qloc st) (qr_loc R) ++ qentries (a_qglob st) (qr_glob R)
  ++ qentries (map fst (qr_tmp R)) (map snd (qr_tmp R)) ++ qr_pend R.
Definition qr_bslots (R : qrconc) : list Z :=
  map qb_slot (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) ++ qr_pendb R.

Definition qcoupled_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) : Prop :=
  let es := qr_entries st R in let bslots := qr_bslots R in
     length (qr_loc R) = length (a_qloc st) /\ length (qr_glob R) = length (a_qglob st)
  /\ Forall (qentry_ok X) es
  /\ List.NoDup (qprim_ids es ++ qr_qpend R) /\ List.NoDup bslots
  /\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
  /\ (forall c k, In (c, k) (qprim_ids es ++ qr_qpend R) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
  /\ Forall (fun k => 0 <= k) bslots.

(* [comment removed for export] *)
Definition qnum_tmp (bs : list abatch) : Prop := Forall (fun b => Q_BATCH_BYTES <= b_size b) bs.

(* [comment removed for export] *)
Definition aquar_mutex (m : amem) (mc mr : Z) : Prop :=
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 mc); C1 (Z_to_bv 8 mr); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aquar_consts (m : amem) : Prop :=
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qr_of_q (Q : qconc) : qrconc := mkQR (q_loc Q) (q_glob Q) (q_ia Q) [] [] [] (q_pend Q).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
