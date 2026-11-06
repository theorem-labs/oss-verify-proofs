(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ARep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Export AQConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition abatch_addr (L : alayout) (k : Z) : Z := aslot_addr L K_BATCH_CLASS k.
Definition qhdr (L : alayout) (ch : achunk) (k : Z) : Z :=
match ch with
| CPrim c n => aslot_addr L c k + rz_size n - 16
| CSec mb ms n => mb + PG + rz_size n - 16
end.
Record qbatchc := mkQB {
qb_slot : Z;
qb_ks : list Z
}.
Record qconc := mkQConc {
q_loc : list qbatchc;
q_glob : list qbatchc;
q_ia : bool;
q_pend : list (Z * Z)
}.
Fixpoint qhdrs (L : alayout) (chs : list achunk) (ks : list Z) : list Z :=
match chs, ks with
| ch :: chs', k :: ks' => qhdrs L chs' ks' ++ [qhdr L ch k]
| _, _ => []
end.
Definition qaddrs (L : alayout) (qs : list qbatchc) : list Z := map (fun q => abatch_addr L (qb_slot q)) qs.
Definition qfirst (L : alayout) (qs : list qbatchc) : Z := hd 0 (qaddrs L qs).
Definition qlast (L : alayout) (qs : list qbatchc) : Z := List.last (qaddrs L qs) 0.
Definition abatch_cells (L : alayout) (m : amem) (b : abatch) (q : qbatchc) (nx : Z) : Prop :=
let B := abatch_addr L (qb_slot q) in
rw_cells asegs m B [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
/\ u64arr asegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
/\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
/\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
/\ 0 <= b_count b <= Q_BATCH.
Fixpoint abatches_to (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) (nxt : Z) : Prop :=
match bs, qs with
| [], [] => True
| b :: bs', q :: qs' => abatch_cells L m b q (hd nxt (qaddrs L qs')) /\ abatches_to L m bs' qs' nxt
| _, _ => False
end.
Definition abatches (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) : Prop := abatches_to L m bs qs 0.
Definition aqcache (L : alayout) (m : amem) (C : Z) (bs : list abatch) (qs : list qbatchc) (bytes : Z) : Prop :=
rw_cells asegs m C [C8 (Z_to_bv 64 (Z.of_nat (length bs))); C8 (Z_to_bv 64 (qfirst L qs));
C8 (Z_to_bv 64 (qlast L qs)); C8 (Z_to_bv 64 bytes)]
/\ abatches L m bs qs.
Definition aquar_glob_const (m : amem) : Prop :=
rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)]
/\ rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aintal (ia : bool) (m : amem) : Prop :=
rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE)
/\ (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))).
Fixpoint qentries (bs : list abatch) (qs : list qbatchc) : list (achunk * Z) :=
match bs, qs with
| b :: bs', q :: qs' => combine (b_chunks b) (qb_ks q) ++ qentries bs' qs'
| _, _ => []
end.
Definition qentry_ok (X : aconc) (e : achunk * Z) : Prop :=
match fst e with
| CPrim c n => exists b1 ctx, In (mkXBusy c (snd e) n BQuar b1 ctx) (x_busy X)
| CSec _ _ _ => True
end.
Definition qprim_ids (es : list (achunk * Z)) : list (Z * Z) :=
flat_map (fun e => match fst e with CPrim c _ => [(c, snd e)] | CSec _ _ _ => [] end) es.
Definition qcoupled (L : alayout) (st : astate) (X : aconc) (Q : qconc) : Prop :=
let es := qentries (a_qloc st) (q_loc Q) ++ qentries (a_qglob st) (q_glob Q) in
let bslots := map qb_slot (q_loc Q ++ q_glob Q) in
length (q_loc Q) = length (a_qloc st) /\ length (q_glob Q) = length (a_qglob st)
/\ Forall (qentry_ok X) es
/\ List.NoDup (qprim_ids es ++ q_pend Q) /\ List.NoDup bslots
/\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
/\ (forall c k, In (c, k) (qprim_ids es ++ q_pend Q) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
/\ Forall (fun k => 0 <= k) bslots.
Definition qnum (st : astate) : Prop :=
a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
/\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st)
/\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX.
Definition AQUAR_at (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) : Prop :=
aquar_glob_const m
/\ aqcache L m (aq_tcache L) (a_qloc st) (q_loc Q) (a_qloc_bytes st)
/\ aqcache L m AQ_GCACHE (a_qglob st) (q_glob Q) (a_qglob_bytes st)
/\ aintal (q_ia Q) m
/\ qcoupled L st X Q
/\ qnum st.
Definition AQUAR (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
exists Q, AQUAR_at L st X Q m.
Definition qconc0 : qconc := mkQConc [] [] false [].
End CANSEC1.
