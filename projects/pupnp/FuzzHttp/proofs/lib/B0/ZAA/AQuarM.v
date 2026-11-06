(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim APrimLem LJ APrimSpec APrimSpec2 APrimQ ASec AQuar F_sec_C F_quar_E.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Fixpoint sc_index (l : list schunk) (sc : schunk) : nat :=
  match l with [] => 0%nat | x :: r => if sc_beg x =? sc_beg sc then 0%nat else Datatypes.S (sc_index r sc) end.

Section M.
Context {HC : HasCeiling}.
Variable AL : alayout.

Definition pstate := (prim * asec)%type.

Definition recycle1 (X : pstate) (ch : qchunk) : pstate :=
  match qc_kind ch with
  | QPrim c v => (cache_dealloc (fst X) c v, snd X)
  | QSec sc => (fst X, sec_dealloc (snd X) (sc_index (se_chunks (snd X)) sc))
  end.
Definition t_recycle1 (X : pstate) (ch : qchunk) : itree nodeL (exc unit) :=
  match qc_kind ch with
  | QPrim c v => t_cdealloc AL c (get_cls (fst X) c)
  | QSec sc => sec_dealloc_tree sc
  end.
Definition H_cdealloc (P : prim) (c : Z) (H : word -> bool) : word -> bool :=
  let k := get_cls P c in if p_cnt k =? max_count c then H_efa AL c k (p_nf k + max_count c / 2) H else H.
Definition H_recycle1 (X : pstate) (ch : qchunk) (H : word -> bool) : word -> bool :=
  match qc_kind ch with
  | QPrim c v => H_cdealloc (fst X) c H
  | QSec sc => sec_dealloc_H sc H
  end.

Fixpoint recycle_chunks (X : pstate) (chs : list qchunk) : pstate :=
  match chs with [] => X | ch :: r => recycle_chunks (recycle1 X ch) r end.
Fixpoint t_recycle_chunks (X : pstate) (chs : list qchunk) : itree nodeL (exc unit) :=
  match chs with [] => Ret (Ok tt) | ch :: r => ebind (t_recycle1 X ch) (fun _ => t_recycle_chunks (recycle1 X ch) r) end.
Fixpoint H_recycle_chunks (X : pstate) (chs : list qchunk) (H : word -> bool) : word -> bool :=
  match chs with [] => H | ch :: r => H_recycle_chunks (recycle1 X ch) r (H_recycle1 X ch H) end.

Definition recycle_batch (X : pstate) (b : qbatch) : pstate :=
  let X1 := recycle_chunks X (qb_chunks b) in (cache_dealloc (fst X1) K_BCLASS (qb_v b), snd X1).
Definition t_recycle_batch (X : pstate) (b : qbatch) : itree nodeL (exc unit) :=
  ebind (t_recycle_chunks X (qb_chunks b))
        (fun _ => t_cdealloc AL K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS)).
Definition H_recycle_batch (X : pstate) (b : qbatch) (H : word -> bool) : word -> bool :=
  H_cdealloc (fst (recycle_chunks X (qb_chunks b))) K_BCLASS (H_recycle_chunks X (qb_chunks b) H).

Fixpoint dorecycle (X : pstate) (bs : list qbatch) : pstate :=
  match bs with [] => X | b :: r => dorecycle (recycle_batch X b) r end.
Fixpoint t_dorecycle (X : pstate) (bs : list qbatch) : itree nodeL (exc unit) :=
  match bs with [] => Ret (Ok tt) | b :: r => ebind (t_recycle_batch X b) (fun _ => t_dorecycle (recycle_batch X b) r) end.
Fixpoint H_dorecycle (X : pstate) (bs : list qbatch) (H : word -> bool) : word -> bool :=
  match bs with [] => H | b :: r => H_dorecycle (recycle_batch X b) r (H_recycle_batch X b H) end.

Definition q_drain (X : pstate) (Q : aquar) : pstate * aquar :=
  let '(Q1, todo) := q_drain_sel Q in (dorecycle X todo, Q1).
Definition t_drain (X : pstate) (Q : aquar) : itree nodeL (exc unit) := t_dorecycle X (snd (q_drain_sel Q)).
Definition H_drain (X : pstate) (Q : aquar) (H : word -> bool) : word -> bool := H_dorecycle X (snd (q_drain_sel Q)) H.

Definition q_put_enq (P : prim) (Q : aquar) (ch : qchunk) : prim * aquar :=
  (fst (enq_prim P (q_loc Q)), mkAQ (q_enq (q_loc Q) ch (snd (enq_prim P (q_loc Q)))) (q_glob Q)).
Definition put_drains (P : prim) (Q : aquar) (ch : qchunk) : bool := Q_CACHE <? qbytes (q_loc (snd (q_put_enq P Q ch))).
Definition q_put (X : pstate) (Q : aquar) (ch : qchunk) : pstate * aquar :=
  let '(P1, Q1) := q_put_enq (fst X) Q ch in
  if put_drains (fst X) Q ch then q_drain (P1, snd X) Q1 else ((P1, snd X), Q1).
Definition t_put (X : pstate) (Q : aquar) (ch : qchunk) : itree nodeL (exc unit) :=
  ebind (t_enq AL (fst X) (q_loc Q))
        (fun _ => if put_drains (fst X) Q ch then t_drain (fst (q_put_enq (fst X) Q ch), snd X) (snd (q_put_enq (fst X) Q ch)) else Ret (Ok tt)).
Definition H_put (X : pstate) (Q : aquar) (ch : qchunk) (H : word -> bool) : word -> bool :=
  let H1 := H_enq AL (fst X) (q_loc Q) H in
  if put_drains (fst X) Q ch then H_drain (fst (q_put_enq (fst X) Q ch), snd X) (snd (q_put_enq (fst X) Q ch)) H1 else H1.
End M.
