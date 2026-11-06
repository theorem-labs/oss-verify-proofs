(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR.
Local Set Keyed Unification.

Import ListNotations.
Local Open Scope Z_scope.

Definition q_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.

Definition q_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => q_link st0 g head
| None => q_single st0 h g
end.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma data_of_eq r r' :
data_of r = data_of r' <->
(m_mem r = m_mem r' /\ m_avail r = m_avail r' /\ m_freed r = m_freed r' /\ m_last_idx r = m_last_idx r'
/\ m_freeable r = m_freeable r' /\ m_sizeclass r = m_sizeclass r' /\ m_maplen r = m_maplen r').
Proof.
destruct r, r'; unfold data_of; cbn; split.
- intros H. inversion H. repeat split; reflexivity.
- intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.

Lemma get_stride_data r r' : data_of r = data_of r' -> get_stride r = get_stride r'.
Proof. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.

Section LINKED.
Variable st : mstate.

End LINKED.

Record lists_ok (st : mstate) (LS : lhead -> list aptr) : Prop := mkLO {
lo_head : forall h, get_head st h = head_of (LS h);
lo_dll : forall h, dll st (LS h);
lo_nodup : forall h, NoDup (LS h);
lo_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
lo_link : forall m, ((exists h, In m (LS h)) <-> m_next (MR st m) <> None)
/\ (m_next (MR st m) = None -> m_prev (MR st m) = None)
}.

#[export] Instance lhead_eq_dec : EqDecision lhead.
Proof. intros [a|] [b|]; try (right; discriminate); try (left; reflexivity).
destruct (decide (a = b)) as [->|NE]; [left; reflexivity| right; congruence]. Defined.

Definition fupd (LS : lhead -> list aptr) (h : lhead) (l : list aptr) : lhead -> list aptr :=
fun h' => if decide (h' = h) then l else LS h'.

Section FACTS.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.

End FACTS.

Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Section DEQUEUE.
Variables (h : lhead) (m : aptr) (st : mstate).
Let mr := MR st m.
Let st' := dequeue h m st.

Let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end.
Let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end.
Let st3 := if negb (optr_eqb (m_next mr) (Some m))
then (if optr_eqb (get_head st2 h) (Some m) then set_head h (m_next mr) st2 else st2)
else set_head h None st.

End DEQUEUE.

Section QUEUE.
Variables (h : lhead) (g : aptr) (st : mstate).
Let st' := queue_st h g st.

End QUEUE.

Section EVOL.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.

End EVOL.
