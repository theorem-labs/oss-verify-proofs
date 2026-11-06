(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Fixpoint SA_ConjL (l : list Prop) : Prop :=
  match l with nil => True | cons c l' => match l' with nil => c | cons _ _ => c /\ SA_ConjL l' end end.
Fixpoint SA_ImpL (l : list Prop) (G : Prop) : Prop :=
  match l with nil => G | cons c l' => c -> SA_ImpL l' G end.
Lemma SA_impL_gen : forall (l : list Prop) (G : Prop), (SA_ConjL l -> G) -> SA_ImpL l G.
Proof.
  induction l as [|c l IH]; intros G H; cbn [SA_ImpL].
  - exact (H Logic.I).
  - intros pc. destruct l as [|c' l'].
    + exact (H pc).
    + apply IH. intros Hl. apply H. exact (conj pc Hl).
Qed.
Lemma SA_conjL_intro : forall (l : list Prop), SA_ImpL l (SA_ConjL l).
Proof. intros l. apply SA_impL_gen. exact (fun H => H). Qed.
Ltac sa_list G := lazymatch G with
  | ?A /\ ?B => let l := sa_list B in constr:(@cons Prop A l)
  | _ => constr:(@cons Prop G (@nil Prop)) end.
Ltac sa_refine t l := lazymatch l with
  | nil => refine t
  | cons _ ?l' => sa_refine uconstr:(t _) l' end.
Ltac split_all :=
  lazymatch goal with
  | |- _ /\ _ => (lazymatch goal with |- ?G => let l := sa_list G in sa_refine uconstr:(SA_conjL_intro l) l end); split_all
  | |- _ => idtac
  end.
Ltac rsplit := repeat first [ progress split_all | split ].
