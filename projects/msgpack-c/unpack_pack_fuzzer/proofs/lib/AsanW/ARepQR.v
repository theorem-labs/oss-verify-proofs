(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ARep ARepQ ARepQP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Record qrconc := mkQR {
  qr_loc : list qbatchc;
  qr_glob : list qbatchc;
  qr_ia : bool;
  qr_tmp : list (abatch * qbatchc);
  qr_pendb : list Z;
  qr_pend : list (achunk * Z);
  qr_qpend : list (Z * Z)
}.

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

Definition qnum_tmp (bs : list abatch) : Prop := Forall (fun b => Q_BATCH_BYTES <= b_size b) bs.

Definition aquar_mutex (m : amem) (mc mr : Z) : Prop :=
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 mc); C1 (Z_to_bv 8 mr); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aquar_consts (m : amem) : Prop :=
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)].

Definition AQUAR_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) (TMP mc mr : Z) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ aqcache L m TMP (map fst (qr_tmp R)) (map snd (qr_tmp R)) (batches_bytes (map fst (qr_tmp R)))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnum st /\ qnum_tmp (map fst (qr_tmp R)).

Definition qr_of_q (Q : qconc) : qrconc := mkQR (q_loc Q) (q_glob Q) (q_ia Q) [] [] [] (q_pend Q).

Lemma qentries_nil : qentries [] [] = []. Proof. reflexivity. Qed.

Lemma AQUAR_rec_of_at : forall L st X Q TMP m,
  AQUAR_at L st X Q m ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  AQUAR_rec L st X (qr_of_q Q) TMP 0 0 m.
Proof.
  intros L st X Q TMP m ([QK MX] & TC & GL & IA & CP & NUM) TMPC.
  unfold AQUAR_rec, qr_of_q. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
  split; [exact QK|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|].
  split. { split; [| exact I]. cbn [length batches_bytes fold_right qfirst qlast qaddrs map hd List.last]. exact TMPC. }
  split; [exact IA|].
  split.
  { destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled_rec, qr_entries, qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
    rewrite !app_nil_r.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN]. }
  split; [exact NUM| constructor].
Qed.

Lemma AQUAR_at_of_rec : forall L st X R TMP m,
  AQUAR_rec L st X R TMP 0 0 m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R TMP m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split; [| exact NUM].
  destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
  unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
  unfold qcoupled. cbv zeta.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB ARep.TwinB ARepQ.TwinB ARepQP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Record qrconc := mkQR {
  qr_loc : list qbatchc;
  qr_glob : list qbatchc;
  qr_ia : bool;
  qr_tmp : list (abatch * qbatchc);
  qr_pendb : list Z;
  qr_pend : list (achunk * Z);
  qr_qpend : list (Z * Z)
}.

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

Definition qnum_tmp (bs : list abatch) : Prop := Forall (fun b => Q_BATCH_BYTES <= b_size b) bs.

Definition aquar_mutex (m : amem) (mc mr : Z) : Prop :=
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 mc); C1 (Z_to_bv 8 mr); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition aquar_consts (m : amem) : Prop :=
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)].

Definition AQUAR_rec (L : alayout) (st : astate) (X : aconc) (R : qrconc) (TMP mc mr : Z) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ aqcache L m TMP (map fst (qr_tmp R)) (map snd (qr_tmp R)) (batches_bytes (map fst (qr_tmp R)))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnum st /\ qnum_tmp (map fst (qr_tmp R)).

Definition qr_of_q (Q : qconc) : qrconc := mkQR (q_loc Q) (q_glob Q) (q_ia Q) [] [] [] (q_pend Q).

Lemma qentries_nil : qentries [] [] = []. Proof. reflexivity. Qed.

Lemma AQUAR_rec_of_at : forall L st X Q TMP m,
  AQUAR_at L st X Q m ->
  rw_cells bsegs m TMP [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  AQUAR_rec L st X (qr_of_q Q) TMP 0 0 m.
Proof.
  intros L st X Q TMP m ([QK MX] & TC & GL & IA & CP & NUM) TMPC.
  unfold AQUAR_rec, qr_of_q. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
  split; [exact QK|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|].
  split. { split; [| exact I]. cbn [length batches_bytes fold_right qfirst qlast qaddrs map hd List.last]. exact TMPC. }
  split; [exact IA|].
  split.
  { destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled_rec, qr_entries, qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb qr_pend qr_qpend map fst snd qentries].
    rewrite !app_nil_r.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN]. }
  split; [exact NUM| constructor].
Qed.

Lemma AQUAR_at_of_rec : forall L st X R TMP m,
  AQUAR_rec L st X R TMP 0 0 m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R TMP m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split; [| exact NUM].
  destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
  unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
  unfold qcoupled. cbv zeta.
  split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
  split; [exact BS|]. split; [exact PS| exact NN].
Qed.
End CANSEC1.
End TwinB.
