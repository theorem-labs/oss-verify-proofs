(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import CAP. Import CXS.

Section Glue.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Lemma cs_ok_sinv : forall (SINV SINV' : env -> (word -> option byte) -> Prop) E cs R FULL model,
  (SINV E FULL -> SINV' E FULL) ->
  cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model -> cs_ok SEGS A LIMIT SINV' argH ISP FS0 E cs R FULL model.
Proof. intros SINV SINV' E cs R FULL model H HC. destruct HC. constructor; try assumption. apply H. assumption. Qed.

(* [comment removed for export] *)
Fixpoint apply_sig (E : env) (s : list (nat * expr)) : env :=
  match s with
  | [] => E
  | (J, e) :: r => apply_sig (upd E J (edenot E e)) r
  end.

Definition sig_holds (E : env) (s : list (nat * expr)) : Prop :=
  Forall (fun p => ev E (fst p) = edenot E (snd p)) s.

(* [comment removed for export] *)
Fixpoint sig_ok (vb : nat) (s : list (nat * expr)) : bool :=
  match s with
  | [] => true
  | (J, e) :: r => (Nat.leb vb J && negb (existsb (fun p => Nat.eqb (fst p) J) r) && CAP.expr_vars_lt vb e && sig_ok vb r)%bool
  end.

Lemma apply_sig_agree : forall vb s E, (forall p, In p s -> (vb <= fst p)%nat) -> env_agree vb E (apply_sig E s).
Proof.
  intros vb s. induction s as [|[J e] r IH]; intros E H; cbn [apply_sig]; [apply env_agree_refl|].
  eapply env_agree_trans; [|apply IH; intros p Hp; apply H; right; exact Hp].
  eapply env_agree_le; [apply upd_agree | apply (H (J, e)); left; reflexivity].
Qed.

Lemma apply_sig_other : forall s E J, existsb (fun p => Nat.eqb (fst p) J) s = false -> ev (apply_sig E s) J = ev E J.
Proof.
  induction s as [|[J' e'] r IH]; intros E J H; cbn [apply_sig]; [reflexivity|].
  cbn [existsb fst] in H. apply orb_false_iff in H as [H1 H2]. rewrite IH by exact H2.
  cbn [upd ev]. apply Nat.eqb_neq in H1. destruct (Nat.eqb_spec J J'); [congruence | reflexivity].
Qed.

Lemma sig_ok_dom : forall vb s, sig_ok vb s = true -> forall p, In p s -> (vb <= fst p)%nat.
Proof.
  intros vb s. induction s as [|[J e] r IH]; intros H p Hp; [destruct Hp|].
  cbn [sig_ok] in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct Hp as [<-|Hp]; [apply Nat.leb_le; exact H1 | exact (IH H4 p Hp)].
Qed.

Lemma apply_sig_holds : forall vb s E, sig_ok vb s = true -> sig_holds (apply_sig E s) s.
Proof.
  intros vb s. induction s as [|[J e] r IH]; intros E H; [constructor|].
  pose proof H as H0. cbn [sig_ok] in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.leb_le in H1. apply negb_true_iff in H2.
  assert (Hag : env_agree vb E (apply_sig E ((J, e) :: r))) by (apply apply_sig_agree; exact (sig_ok_dom vb _ H0)).
  constructor.
  - cbn [fst snd apply_sig]. rewrite (apply_sig_other r _ J H2). rewrite upd_at.
    change (apply_sig (upd E J (edenot E e)) r) with (apply_sig E ((J, e) :: r)).
    apply (edenot_agree' vb E _ e Hag H3).
  - cbn [apply_sig]. exact (IH _ H4).
Qed.

Section WithSinv.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[local] Notation cs_ok := (cs_ok SEGS A LIMIT SINV argH ISP FS0).

(* [comment removed for export] *)
Lemma cs_ok_apply_sig : forall s ch E R FULL model,
  (forall p, In p s -> (nx0 <= fst p)%nat) -> s_log (a_ss ch) = [] ->
  cs_ok E (inst_list ch s) R FULL model -> cs_ok (apply_sig E s) ch R FULL model.
Proof.
  induction s as [|[J e] r IH]; intros ch E R FULL model Hnx Hlog HC; cbn [apply_sig]; [exact HC|].
  cbn [inst_list] in HC.
  assert (HJ : (nx0 <= J)%nat) by (apply (Hnx (J, e)); left; reflexivity).
  apply (proj1 (cs_ok_inst SEGS A nx0 LIMIT NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E J e (inst_list ch r) R FULL model HJ (inst_list_log ch r Hlog))) in HC.
  apply IH; [intros p Hp; apply Hnx; right; exact Hp | exact Hlog | exact HC].
Qed.
End WithSinv.

(* [comment removed for export] *)
Lemma cs_ok_inst_list_same : forall (SINV : env -> (word -> option byte) -> Prop) s ch E R FULL model,
  sig_holds E s -> s_log (a_ss ch) = [] ->
  CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E ch R FULL model -> CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (inst_list ch s) R FULL model.
Proof.
  intros SINV s. induction s as [|[J e] r IH]; intros ch E R FULL model Hs Hlog HC; cbn [inst_list]; [exact HC|].
  inversion Hs as [|p l Hp Hr]; subst. cbn [fst snd] in Hp.
  apply cs_ok_inst_same; [symmetry; exact Hp | exact (inst_list_log ch r Hlog) | exact (IH ch E R FULL model Hr Hlog HC)].
Qed.

(* [comment removed for export] *)
Definition pure_fact (K : kentry) : bool := match K with KRange _ _ _ | KAlign _ _ => true | _ => false end.
Definition pure_holds (E : env) (K : kentry) : Prop :=
  match K with
  | KRange e lo hi => lo <= bv_unsigned (edenot E e) /\ bv_unsigned (edenot E e) <= hi
  | KAlign e m => 0 < m /\ bv_unsigned (edenot E e) mod m = 0
  | _ => False
  end.
Lemma cs_ok_add_pure : forall (SINV : env -> (word -> option byte) -> Prop) E cs R FULL model facts,
  CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model -> Forall (pure_holds E) facts ->
  CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (add_kn cs facts) R FULL model.
Proof.
  intros SINV E cs R FULL model facts HC HF. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_app. split; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  apply Forall_forall. intros K HK. pose proof (proj1 (Forall_forall _ _) HF K HK) as H.
  destruct K; cbn [pure_holds] in H; try contradiction; cbn [kentry_ok]; exact H.
Qed.


(* [comment removed for export] *)
Lemma cs_ok_unadd : forall (SINV : env -> (word -> option byte) -> Prop) E cs R FULL model facts,
  s_log (a_ss cs) = [] ->
  CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (add_kn cs facts) R FULL model -> CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model.
Proof.
  intros SINV E cs R FULL model facts Hlog HC.
  assert (HM : Mr A argH E (add_kn cs facts) model FULL = Mr A argH E cs model FULL).
  { unfold Mr. rewrite (hid_ext A argH E cs (add_kn cs facts) model eq_refl). reflexivity. }
  destruct HC.
  constructor; cbn [add_kn set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know] in *;
    try assumption.
  rewrite HM in co_know0. unfold know_ok in *. exact (proj2 (proj1 (Forall_app _ _ _) co_know0)).
Qed.

Lemma pure_holds_of_know : forall E M facts, forallb pure_fact facts = true -> know_ok SEGS E M facts -> Forall (pure_holds E) facts.
Proof.
  intros E M facts Hp HK. apply Forall_forall. intros K HKin.
  pose proof (proj1 (forallb_forall _ _) Hp K HKin) as Hpk. pose proof (proj1 (Forall_forall _ _) HK K HKin) as H.
  destruct K; cbn [pure_fact] in Hpk; try discriminate; cbn [kentry_ok] in H; cbn [pure_holds]; exact H.
Qed.
Lemma know_of_pure_holds : forall E M facts, Forall (pure_holds E) facts -> know_ok SEGS E M facts.
Proof.
  intros E M facts H. apply Forall_forall. intros K HKin. pose proof (proj1 (Forall_forall _ _) H K HKin) as HK.
  destruct K; cbn [pure_holds] in HK; try contradiction; cbn [kentry_ok]; exact HK.
Qed.
Lemma add_kn_facts_hold : forall (SINV : env -> (word -> option byte) -> Prop) E cs R FULL model facts,
  forallb pure_fact facts = true ->
  CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (add_kn cs facts) R FULL model -> Forall (pure_holds E) facts.
Proof.
  intros SINV E cs R FULL model facts Hp HC. eapply pure_holds_of_know; [exact Hp|].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. unfold add_kn, set_kn in HK. cbn [kn with_ss a_ss mk_ss s_know] in HK.
  exact (proj1 (proj1 (Forall_app _ _ _) HK)).
Qed.

End Glue.
