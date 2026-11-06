(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the count of secondary requests of a plain-model trace (nsec_tr) and its bridge from the
   allocator meter's tr_cost. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfNsec.v, with its module paths changed; 1 line of the source is left out. *)
(* KF-COUNT: the one definition of the secondary count of a request trace, shared by the per-trace count files
   (ReplyKfTr.v, ReplyKfTrRr.v, ReplyKfTrRig.v, ReplyKfTrSm.v).  proves no function (kind: segment lemma).
   - nsec_tr tr: the number of RMalloc n and RRealloc _ n _ events of tr with 64512 < n (a secondary request: ReplyCnt.v
     Psec, n >= 64,513).  Frees count 0.
   - tr_cost_sec: at a meter whose mo_malloc n is (if 64512 <? n then 1 else 0) and whose mo_free is 0 (the KF meter
     MT_sec), W_contract.tr_cost is nsec_tr.
   - nsec_tr_app, nsec_tr_cons, nsec_tr_nil, nsec_tr_nonneg: the fold's algebra. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract.
Import ListNotations.
Open Scope Z_scope.

Definition nsec_tr {P : Type} (tr : list (RelayRunT.rev P)) : Z :=
  fold_right (fun ev acc =>
    match ev with
    | RelayRunT.RMalloc n => (if 64512 <? n then 1 else 0)
    | RelayRunT.RFree _ _ => 0
    | RelayRunT.RRealloc _ n _ => (if 64512 <? n then 1 else 0)
    end + acc) 0 tr.

Lemma nsec_tr_nil : forall (P : Type), nsec_tr (@nil (RelayRunT.rev P)) = 0.
Proof. reflexivity. Qed.

Lemma nsec_tr_cons : forall (P : Type) (ev : RelayRunT.rev P) (r : list (RelayRunT.rev P)),
  nsec_tr (ev :: r) =
  match ev with
  | RelayRunT.RMalloc n => (if 64512 <? n then 1 else 0)
  | RelayRunT.RFree _ _ => 0
  | RelayRunT.RRealloc _ n _ => (if 64512 <? n then 1 else 0)
  end + nsec_tr r.
Proof. reflexivity. Qed.

Lemma nsec_tr_app : forall (P : Type) (a b : list (RelayRunT.rev P)), nsec_tr (a ++ b) = nsec_tr a + nsec_tr b.
Proof.
  intros P a b. induction a as [|ev a IH]; [reflexivity|].
  rewrite <- app_comm_cons, !nsec_tr_cons, IH. lia.
Qed.

Lemma nsec_tr_nonneg : forall (P : Type) (tr : list (RelayRunT.rev P)), 0 <= nsec_tr tr.
Proof.
  intros P tr. induction tr as [|[n|k a|k n a] r IH]; [rewrite nsec_tr_nil; lia| | |]; rewrite nsec_tr_cons;
    try (destruct (64512 <? n)); lia.
Qed.

Lemma tr_cost_sec : forall (MT : ameter_ops) (P : Type) (tr : list (RelayRunT.rev P)),
  (forall n, mo_malloc MT n = if 64512 <? n then 1 else 0) -> mo_free MT = 0 ->
  W_contract.tr_cost MT tr = nsec_tr tr.
Proof.
  intros MT P tr HM HF. induction tr as [|[n|k a|k n a] r IH]; [reflexivity| | |];
    unfold W_contract.tr_cost in *; rewrite nsec_tr_cons, <- IH; cbn [fold_right]; rewrite ?HM, HF; lia.
Qed.
