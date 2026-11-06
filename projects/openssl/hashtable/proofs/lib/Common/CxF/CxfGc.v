(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFG.
Import AX2. Import APC.
Section G.
Variable nx0 : nat.
Fixpoint expr_vars_tF (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => if Nat.ltb n nx0 then acc else pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_tF x (expr_vars_tF y acc)
  | EExt _ _ _ x => expr_vars_tF x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_tF (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_tF PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_tF (a_base a) (expr_vars_tF v acc)
                                      | KZero a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KBlob a n _ => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KWr a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KFill a n _ => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | KUnk a n => expr_vars_tF (a_base a) (expr_vars_tF n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_tF (am_base m) (expr_vars_tF (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_tF (fst p) (expr_vars_tF (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_tF (fst p) (expr_vars_tF (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_tF l (expr_vars_tF o acc) | _ => acc end in
  expr_vars_tF (a_brk cs) acc.
Definition cs_gcF (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_tF cs in
  set_kn cs (List.filter (kn_gc_entry_t nx0 spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition hi_agree (t' t : ptree unit) : Prop := forall v, (nx0 <= v)%nat -> in_live_t t' v = in_live_t t v.
Lemma hi_agree_expr : forall e t' t, hi_agree t' t -> hi_agree (expr_vars_tF e t') (expr_vars_t e t).
Proof.
  induction e; intros t' t H; cbn [expr_vars_tF expr_vars_t]; try exact H; auto.
  intros v Hv. unfold in_live_t. destruct (Nat.ltb_spec n nx0) as [Hlt|Hge].
  - rewrite pt_gso by (intros HK; apply vkey_inj in HK; lia). apply H. exact Hv.
  - destruct (Nat.eq_dec v n) as [->|NE]; [rewrite !pt_gss; reflexivity|].
    rewrite !pt_gso by (intros HK; apply NE; apply vkey_inj; exact HK). apply H. exact Hv.
Qed.
Lemma hi_agree_fold : forall (X : Type) (f g : X -> ptree unit -> ptree unit) (l : list X) t' t,
  (forall a t' t, hi_agree t' t -> hi_agree (f a t') (g a t)) ->
  hi_agree t' t -> hi_agree (fold_right f t' l) (fold_right g t l).
Proof. intros X f g l t' t Hfg H. induction l as [|a r IH]; [exact H|]. cbn [fold_right]. apply Hfg. exact IH. Qed.
Lemma live_vars_hi_agree : forall cs, hi_agree (live_vars_tF cs) (live_vars_t cs).
Proof.
  intros cs. unfold live_vars_tF, live_vars_t.
  apply hi_agree_expr.
  assert (A0 : hi_agree PTLeaf PTLeaf) by (intros v _; reflexivity).
  match goal with |- hi_agree (match a_fd cs with _ => _ end) _ =>
    assert (A5 : forall t' t, hi_agree t' t ->
      hi_agree (match a_fd cs with FdFile _ l o => expr_vars_tF l (expr_vars_tF o t') | _ => t' end)
               (match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o t) | _ => t end))
      by (intros t' t H; destruct (a_fd cs); repeat apply hi_agree_expr; exact H);
    apply A5 end.
  apply hi_agree_fold; [intros; repeat apply hi_agree_expr; assumption|].
  apply hi_agree_fold; [intros; repeat apply hi_agree_expr; assumption|].
  apply hi_agree_fold; [intros; repeat apply hi_agree_expr; assumption|].
  apply hi_agree_fold; [intros a t' t H; destruct a as [[] ? ?|[] ?|[] ? ?| | | |[] ?| |[] ? ?|[] ?]; repeat apply hi_agree_expr; assumption|].
  apply hi_agree_fold; [intros; repeat apply hi_agree_expr; assumption|].
  exact A0.
Qed.
Lemma all_live_hi_agree : forall t' t e, hi_agree t' t -> expr_all_live_t nx0 t' e = expr_all_live_t nx0 t e.
Proof.
  intros t' t e H. induction e; cbn [expr_all_live_t]; try reflexivity.
  - destruct (Nat.ltb_spec n nx0); [reflexivity|]. apply H. assumption.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - exact IHe.
Qed.
Lemma gc_entry_hi_agree : forall spb spk t' t K, hi_agree t' t -> kn_gc_entry_t nx0 spb spk t' K = kn_gc_entry_t nx0 spb spk t K.
Proof.
  intros spb spk t' t K H. destruct K; cbn [kn_gc_entry_t]; try reflexivity; rewrite ?(all_live_hi_agree t' t) by exact H; reflexivity.
Qed.
Lemma cs_gcF_eq : forall cs, cs_gcF cs = cs_gc nx0 cs.
Proof.
  intros cs. unfold cs_gcF, cs_gc. destruct (split_lit (reg cs 2)) as [spb spk]. f_equal.
  apply List.filter_ext. intros K. apply gc_entry_hi_agree. apply live_vars_hi_agree.
Qed.
End G.
End CXFG.
