(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import CellsX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RMalloc_iface_stmt HeapSR_iface XRep XPRep XF_rep XM_rep XP_req_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record pst := mkPST {
  ps_c : pcore ; ps_S : list Z ; ps_L : list Z ; ps_ns : NS ; ps_ls : LS ; ps_em : gmap Z elt ;
  ps_h : hdrv ; ps_u : Z ; ps_es : list mbe ; ps_insz : Z ; ps_g : bool ; ps_rdi : byte ;
  ps_LBn : list block ; ps_st : PState ; ps_errv : word }.

(* [comment removed for export] *)
Definition KB : Z := 22.

(* [comment removed for export] *)
Definition body_res (es : list mbe) (insz r : Z) : Z :=
  3 * (insz + r) + 512 - mb_cap es + 31 * (KB - Z.of_nat (length es)).

(* [comment removed for export] *)
Definition new_body_off (LB0 : list block) (SP : Z) (es0 es : list mbe) : Prop :=
  forall x s, In (x, s) es -> In (x, s) es0 \/ (forall a k, rclient_range LB0 SP a k -> 0 <= k -> a + k <= x \/ x + 24 + s <= a).

(* [comment removed for export] *)
Definition http_fail (E' : ecv) : Prop := ec_cat E' = G_HTTP_CAT /\ ec_failed E' = true /\ ec_ok E' /\ 2 <= ec_flags E' /\ 1 <= ec_val E' <= 28.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition SvOwnP (LB : list block) (ptr len : Z) : Prop := (len = 0 /\ ptr = 0) \/ (1 <= len /\ exists p, In (p, ptr, len) LB).
Definition HdrOwnP (LB : list block) (h : hdrv) : Prop :=
  SvOwnP LB (hv_mp h) (hv_ml h) /\ SvOwnP LB (hv_tp h) (hv_tl h) /\ 0 <= hv_ml h < 2^64 /\ 0 <= hv_tl h < 2^64.
Definition HdrDisjP (em : gmap Z elt) (h : hdrv) : Prop :=
  (1 <= hv_ml h -> em !! (hv_mp h) = None) /\ (1 <= hv_tl h -> em !! (hv_tp h) = None) /\ (1 <= hv_ml h -> 1 <= hv_tl h -> hv_mp h <> hv_tp h).
Definition BodyDisjP (em : gmap Z elt) (h : hdrv) (es : list mbe) : Prop :=
  forall x s, In (x, s) es -> em !! x = None /\ (1 <= hv_ml h -> x <> hv_mp h) /\ (1 <= hv_tl h -> x <> hv_tp h).

(* [comment removed for export] *)
Definition hdr_disj (L : list Z) (es : list mbe) (h : hdrv) : Prop :=
  (hv_tl h <> 0 -> forall e, e ∈ L -> e + 48 <= hv_tp h \/ hv_tp h + hv_tl h <= e)
  /\ (hv_ml h <> 0 -> forall e, e ∈ L -> e + 48 <= hv_mp h \/ hv_mp h + hv_ml h <= e)
  /\ (hv_tl h <> 0 -> forall x s, In (x, s) es -> x + 24 + s <= hv_tp h \/ hv_tp h + hv_tl h <= x)
  /\ (hv_ml h <> 0 -> forall x s, In (x, s) es -> x + 24 + s <= hv_mp h \/ hv_mp h + hv_ml h <= x)
  /\ (hv_ml h <> 0 -> hv_tl h <> 0 -> hv_mp h + hv_ml h <= hv_tp h \/ hv_tp h + hv_tl h <= hv_mp h).

(* [comment removed for export] *)
Definition blk_fresh (LB0 : list block) (SP : Z) (A n : Z) : Prop :=
  forall a k, rclient_range LB0 SP a k -> 0 <= k -> a + k <= A \/ A + n <= a.

(* [comment removed for export] *)
Definition hdr_new (LB0 : list block) (SP : Z) (h0 h : hdrv) : Prop :=
  h = h0 \/ (hdr_empty h0 /\ (hv_tl h <> 0 -> blk_fresh LB0 SP (hv_tp h) (hv_tl h)) /\ (hv_ml h <> 0 -> blk_fresh LB0 SP (hv_mp h) (hv_ml h))).

(* [comment removed for export] *)
Definition svownedP (ptr len : Z) (b : block) : Prop := 1 <= len /\ blk_addr b = ptr /\ blk_size b = len.
Definition mbownedP (es : list mbe) (b : block) : Prop := exists s, In (blk_addr b, s) es /\ blk_size b = mb_block_size s.
Definition lbn_ownedP (L : list Z) (h : hdrv) (es : list mbe) (LBn : list block) : Prop :=
  forall b, In b LBn -> (blk_addr b ∈ L /\ 1 <= blk_size b) \/ svownedP (hv_mp h) (hv_ml h) b \/ svownedP (hv_tp h) (hv_tl h) b \/ mbownedP es b.
End HCW.
