(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Seal PkOps PkUSwap.
Import ListNotations.
Import HeapOp PK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkUAdd.
Section Add.
Variables (ws uw : list window).
Hypothesis PU : forall x, In x uw -> exists q, pku_val x = Some q.

Lemma add_in_ws : forall a, in_ws (ws ++ uw) a <-> in_ws ws a.
Proof.
  intros a. unfold in_ws, in_ivs. rewrite !Exists_exists. split; intros (iv & Hiv & Ha); apply in_map_iff in Hiv as (x & <- & Hx).
  - apply in_app_iff in Hx as [Hx|Hx]; [exists (w_iv x); split; [apply in_map; exact Hx| exact Ha]|].
    exfalso. destruct (PU x Hx) as [q PV]. exact (PkUSwap.no_byte x q a PV Ha).
  - exists (w_iv x). split; [apply in_map; apply in_app_iff; left; exact Hx| exact Ha].
Qed.

Lemma add_keep : forall LB, wins_keep LB ws (ws ++ uw).
Proof.
  intros LB. split; [| split].
  - intros x T. split; intros H; [| apply in_app_iff; left; exact H].
    apply in_app_iff in H as [H|H]; [exact H|]. exfalso. destruct (PU x H) as [q PV]. exact (PkUSwap.not_tied x q PV T).
  - intros x Hx NX _ _. exfalso. apply NX. apply in_app_iff. left. exact Hx.
  - intros x Hx NX KB. exfalso. apply in_app_iff in Hx as [Hx|Hx]; [exact (NX Hx)|].
    destruct (PU x Hx) as [q PV]. destruct (pku_val_kind x q PV) as [K _]. unfold K_BLOCK in KB. lia.
Qed.

Lemma add_wf : forall segs IMGX (A : alloc_world segs IMGX) LB ceil, ceil <= Mem.two62Z -> windows_wf ws LB ceil -> windows_wf (ws ++ uw) LB ceil.
Proof.
  intros segs IMGX A LB ceil HC WF. unfold windows_wf in *. apply Forall_app. split; [exact WF|]. apply Forall_forall. intros x Hx.
  destruct (PU x Hx) as [q PV]. destruct (pku_val_kind x q PV) as [K L0]. pose proof (PkUSwap.pku_val_lo x q PV) as LO. unfold PKU_BASE, PKU_ST, PKU_SPAN in LO.
  unfold window_wf. rewrite L0. unfold Mem.two62Z in HC. unfold W64.W64.two64 || unfold W64.two64.
  split; [lia|]. split; [lia|]. split; [lia|]. left. split; [exact K| lia].
Qed.

Lemma add_wins_pk : forall g, wins_pk g ws -> wins_pk g (ws ++ uw).
Proof.
  intros g Wk. unfold wins_pk in *. apply Forall_app. split; [exact Wk|]. apply Forall_forall. intros x Hx NS.
  exfalso. apply NS. destruct (PU x Hx) as [q PV]. destruct (pku_val_kind x q PV) as [K _]. unfold K_STACK. exact K.
Qed.

Lemma add_ghost : forall g, ghost_pk g ws -> ghost_pk g (ws ++ uw).
Proof.
  intros g [SE EP]. split.
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros x Hx K9. apply in_app_iff in Hx as [Hx|Hx]; [exact Hx|].
    exfalso. destruct (PU x Hx) as [q PV]. destruct (pku_val_kind x q PV) as [K _]. unfold Seal.K_TWIN in K9. lia.
  - intros VB. destruct (EP VB) as (x & Hx & EW & LEN). exists x. split; [apply in_app_iff; left; exact Hx| split; [exact EW| exact LEN]].
Qed.

Lemma add_cost : forall u g ls, (forall x, In x ws -> pku_val x = None) ->
  (forall x fr v, In x uw -> pku_val x = Some (fr, v) -> np (k_tree g) ls fr (a_cf u =? 0) <= v) -> cost_pk u g ls (ws ++ uw).
Proof.
  intros u g ls NO LE x fr v Hx PX. apply in_app_iff in Hx as [Hx|Hx]; [rewrite (NO x Hx) in PX; discriminate| exact (LE x fr v Hx PX)].
Qed.
End Add.
End PkUAdd.
