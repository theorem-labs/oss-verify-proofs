(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Seal PkOps.
Import ListNotations.
Import HeapOp PK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkUSwap.

Lemma pku_val_lo : forall w p, pku_val w = Some p -> PKU_BASE <= w_lo w < PKU_BASE + PKU_ST + PKU_SPAN.
Proof.
  intros w p H. unfold pku_val in H. destruct ((w_kind w =? 0) && (w_len w =? 0)); [| discriminate].
  destruct ((PKU_BASE <=? w_lo w) && (w_lo w <? PKU_BASE + PKU_SPAN)) eqn:A.
  - apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. unfold PKU_ST. lia.
  - destruct ((PKU_BASE + PKU_ST <=? w_lo w) && (w_lo w <? PKU_BASE + PKU_ST + PKU_SPAN)) eqn:B; [| discriminate].
    apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. unfold PKU_ST in *. lia.
Qed.

Section Swap.
Variables (pre post : list window) (w w' : window) (p p' : bool * Z).
Hypothesis PV : pku_val w = Some p.
Hypothesis PV' : pku_val w' = Some p'.
Let ws := pre ++ w :: post.
Let ws' := pre ++ w' :: post.

Lemma in_swap : forall x, In x ws' -> x = w' \/ In x ws.
Proof. intros x H. unfold ws, ws' in *. apply in_app_iff in H as [H|[<-|H]]; [right; apply in_app_iff; left; exact H| left; reflexivity| right; apply in_app_iff; right; right; exact H]. Qed.
Lemma in_swap_rev : forall x, In x ws -> x = w \/ In x ws'.
Proof. intros x H. unfold ws, ws' in *. apply in_app_iff in H as [H|[<-|H]]; [right; apply in_app_iff; left; exact H| left; reflexivity| right; apply in_app_iff; right; right; exact H]. Qed.
Lemma in_new : In w' ws'. Proof. unfold ws'. apply in_app_iff. right. left. reflexivity. Qed.

Lemma swap_length : length ws' = length ws.
Proof. unfold ws, ws'. rewrite !length_app. reflexivity. Qed.

Lemma no_byte : forall x q a, pku_val x = Some q -> ~ in_iv (w_iv x) a.
Proof. intros x q a H. destruct (pku_val_kind x q H) as [_ L0]. unfold in_iv, w_iv. cbn [fst snd]. lia. Qed.

Lemma swap_in_ws : forall a, in_ws ws' a <-> in_ws ws a.
Proof.
  intros a. unfold in_ws, in_ivs. rewrite !Exists_exists. split; intros (iv & Hiv & Ha); apply in_map_iff in Hiv as (x & <- & Hx).
  - destruct (in_swap x Hx) as [->|Hx']; [exfalso; exact (no_byte w' p' a PV' Ha)|]. exists (w_iv x). split; [apply in_map; exact Hx'| exact Ha].
  - destruct (in_swap_rev x Hx) as [->|Hx']; [exfalso; exact (no_byte w p a PV Ha)|]. exists (w_iv x). split; [apply in_map; exact Hx'| exact Ha].
Qed.

Lemma swap_wf : forall segs IMGX (A : alloc_world segs IMGX) LB ceil, ceil <= Mem.two62Z -> windows_wf ws LB ceil -> windows_wf ws' LB ceil.
Proof.
  intros segs IMGX A LB ceil HC WF. unfold windows_wf in *. apply Forall_forall. intros x Hx.
  destruct (in_swap x Hx) as [->|Hx']; [| exact (proj1 (Forall_forall _ _) WF x Hx')].
  destruct (pku_val_kind w' p' PV') as [K L0]. pose proof (pku_val_lo w' p' PV') as LO. unfold PKU_BASE, PKU_ST, PKU_SPAN in LO.
  unfold window_wf. rewrite L0. unfold Mem.two62Z in HC. unfold W64.W64.two64 || unfold W64.two64.
  split; [lia|]. split; [lia|]. split; [lia|]. left. split; [exact K| lia].
Qed.

Lemma not_tied : forall x q, pku_val x = Some q -> ~ aw_tied x.
Proof.
  intros x q H [[_ LO]|G]; destruct (pku_val_kind x q H) as [K _]; pose proof (pku_val_lo x q H) as B.
  - unfold AW_BAND, PKU_BASE in *. lia.
  - unfold K_GHOST in G. lia.
Qed.

Lemma swap_keep : forall LB, wins_keep LB ws ws'.
Proof.
  intros LB. split; [| split].
  - intros x T. split; intros H.
    + destruct (in_swap x H) as [->|H']; [exfalso; exact (not_tied w' p' PV' T)| exact H'].
    + destruct (in_swap_rev x H) as [->|H']; [exfalso; exact (not_tied w p PV T)| exact H'].
  - intros x Hx NX HK _. exfalso. destruct (in_swap_rev x Hx) as [->|H']; [| exact (NX H')].
    destruct (pku_val_kind w p PV) as [K _]. unfold heap_kind, K_BLOCK in HK. lia.
  - intros x Hx NX KB. exfalso. destruct (in_swap x Hx) as [->|H']; [| exact (NX H')].
    destruct (pku_val_kind w' p' PV') as [K _]. unfold K_BLOCK in KB. lia.
Qed.

Lemma swap_wins_pk : forall g, wins_pk g ws -> wins_pk g ws'.
Proof.
  intros g Wk. unfold wins_pk in *. apply Forall_forall. intros x Hx NS.
  destruct (in_swap x Hx) as [->|Hx']; [| exact (proj1 (Forall_forall _ _) Wk x Hx' NS)].
  exfalso. apply NS. destruct (pku_val_kind w' p' PV') as [K _]. unfold K_STACK. exact K.
Qed.

Lemma swap_ghost : forall g, ghost_pk g ws -> ghost_pk g ws'.
Proof.
  intros g [SE EP]. split.
  - apply (Seal.seal_ok_ws ws); [exact SE|]. intros x Hx K9. destruct (in_swap x Hx) as [->|Hx']; [| exact Hx'].
    exfalso. destruct (pku_val_kind w' p' PV') as [K _]. unfold Seal.K_TWIN in K9. lia.
  - intros VB. destruct (EP VB) as (x & Hx & EW & LEN). exists x. split; [| split; [exact EW| exact LEN]].
    destruct (in_swap_rev x Hx) as [->|Hx']; [| exact Hx']. exfalso. destruct (pku_val_kind w p PV) as [_ L0]. lia.
Qed.

Lemma swap_cost : forall u g ls, (forall x, In x (pre ++ post) -> pku_val x = None) ->
  np (k_tree g) ls (fst p') (a_cf u =? 0) <= snd p' -> cost_pk u g ls ws'.
Proof.
  intros u g ls NO LE x fr v Hx PX. unfold ws' in Hx. apply in_app_iff in Hx as [Hx|[<-|Hx]].
  - rewrite (NO x ltac:(apply in_app_iff; left; exact Hx)) in PX. discriminate.
  - rewrite PV' in PX. injection PX as EP. subst p'. exact LE.
  - rewrite (NO x ltac:(apply in_app_iff; right; exact Hx)) in PX. discriminate.
Qed.

Lemma old_cost : forall u g ls, cost_pk u g ls ws -> np (k_tree g) ls (fst p) (a_cf u =? 0) <= snd p.
Proof. intros u g ls C. destruct p as [fr v]. apply (C w fr v); [unfold ws; apply in_app_iff; right; left; reflexivity| exact PV]. Qed.

End Swap.

Lemma cost_none : forall u g ls ws, (forall x, In x ws -> pku_val x = None) -> cost_pk u g ls ws.
Proof. intros u g ls ws NO x fr v Hx PX. rewrite (NO x Hx) in PX. discriminate. Qed.

End PkUSwap.
