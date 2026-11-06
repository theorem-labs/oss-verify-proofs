(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxState AxEntryRel AxSys.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition ts_occ (v : int) (ts : terms) : bool := existsb (fun p => (fst p =? v)%uint63) ts.

Definition xb_occ (v : int) (b : xb) : bool := match b with BF ts _ _ => ts_occ v ts | _ => false end.

Definition xv_occ (v : int) (x : xv) : bool :=
  match x with
  | XS ts _ => ts_occ v ts
  | XB l => existsb (xb_occ v) l
  | _ => false
  end.

Definition cell_occ (v : int) (c : cell) : bool := match c with CB l => existsb (xb_occ v) l | CW _ => false end.

(* [comment removed for export] *)
Definition inone {A : Type} (f : A -> bool) (t : itrie A) : bool := iall (fun a => negb (f a)) t.

Lemma inone_iget {A : Type} (f : A -> bool) (d : nat) (t : itrie A) (k : int) (a : A) :
  inone f t = true -> iget d t k = Some a -> f a = false.
Proof. intros H Hg. apply negb_true_iff. exact (iall_iget _ d t k a H Hg). Qed.

Definition region_occ (v : int) (R : region) : bool :=
  ts_occ v (rg_ts R) || negb (inone (cell_occ v) (rg_cells R)).

Definition fact_occ (v : int) (fc : fact) : bool := ts_occ v (snd (fc_f fc)).

Definition store_occ (v : int) (s : store) : bool :=
  (if (v <? 65536)%uint63 then match iget bdepth (st_box s) v with Some _ => true | None => false end else false)
  || existsb (fact_occ v) (st_facts s).

Definition rsv_occ (v : int) (r : rsv) : bool := match r with RSome x => xv_occ v x | _ => false end.

Definition piece_occ (v : int) (p : piece) : bool := match p with PB b => xb_occ v b | PS _ => false end.

Definition ent_occ (v : int) (e : aent) : bool := ts_occ v (snd (ae_base e)).

Definition model_occ (v : int) (am : amodel) : bool :=
  afd_occ v (am_fd am) || existsb (ent_occ v) (am_maps am) || ts_occ v (snd (am_brk0 am)) || ts_occ v (snd (am_brk am))
  || ts_occ v (snd (am_atop am)) || (match am_tid am with Some t => xv_occ v t | None => false end)
  || existsb (fun x => ent_occ v (fst (fst x)) || ts_occ v (snd (snd (fst x)))) (am_exp am)
  || existsb (piece_occ v) (am_out am).

Definition state_occ (v : int) (A : astate amodel) : bool :=
  entry_var v || negb (inone (xv_occ v) (a_regs A)) || rsv_occ v (a_resv A) || existsb (region_occ v) (a_mem A)
  || store_occ v (a_facts A) || model_occ v (a_model A).

Lemma occ_entry (v : int) (A : astate amodel) : state_occ v A = false -> entry_var v = false.
Proof. unfold state_occ. intros H. do 5 (apply orb_false_iff in H as [H _]). exact H. Qed.

Lemma state_occ_parts (v : int) (A : astate amodel) : state_occ v A = false ->
  entry_var v = false /\ inone (xv_occ v) (a_regs A) = true /\ rsv_occ v (a_resv A) = false
  /\ existsb (region_occ v) (a_mem A) = false /\ store_occ v (a_facts A) = false /\ model_occ v (a_model A) = false.
Proof.
  unfold state_occ. intros H. apply orb_false_iff in H as [H H6]. apply orb_false_iff in H as [H H5].
  apply orb_false_iff in H as [H H4]. apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H1 H2].
  apply negb_false_iff in H2. repeat split; assumption.
Qed.

Lemma model_occ_parts (v : int) (am : amodel) : model_occ v am = false ->
  afd_occ v (am_fd am) = false /\ existsb (ent_occ v) (am_maps am) = false /\ ts_occ v (snd (am_brk0 am)) = false
  /\ ts_occ v (snd (am_brk am)) = false /\ ts_occ v (snd (am_atop am)) = false
  /\ (match am_tid am with Some t => xv_occ v t | None => false end) = false
  /\ existsb (fun x => ent_occ v (fst (fst x)) || ts_occ v (snd (snd (fst x)))) (am_exp am) = false
  /\ existsb (piece_occ v) (am_out am) = false.
Proof.
  unfold model_occ. intros H. apply orb_false_iff in H as [H H8]. apply orb_false_iff in H as [H H7].
  apply orb_false_iff in H as [H H6]. apply orb_false_iff in H as [H H5]. apply orb_false_iff in H as [H H4].
  apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H1 H2]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma teval_agree (v : int) (ρ ρ' : valuation) : (forall x, x <> v -> ρ' x = ρ x) -> forall ts, ts_occ v ts = false -> teval ρ' ts = teval ρ ts.
Proof.
  intros Hag. induction ts as [|[x k] r IH]; [reflexivity|]. unfold ts_occ. cbn [existsb fst teval]. intros H.
  apply orb_false_iff in H as [H1 H2]. rewrite (IH H2). rewrite Hag; [reflexivity|].
  intros ->. rewrite Uint63.eqb_refl in H1. discriminate H1.
Qed.

Lemma leval_agree (v : int) (ρ ρ' : valuation) : (forall x, x <> v -> ρ' x = ρ x) -> forall f : lin, ts_occ v (snd f) = false -> leval ρ' f = leval ρ f.
Proof. intros Hag f H. unfold leval. rewrite (teval_agree v ρ ρ' Hag _ H). reflexivity. Qed.

Lemma smod_agree (v : int) (ρ ρ' : valuation) (ts : terms) (o : w64) :
  (forall x, x <> v -> ρ' x = ρ x) -> ts_occ v ts = false -> smod ρ' ts o = smod ρ ts o.
Proof. intros Hag H. unfold smod. rewrite (teval_agree v ρ ρ' Hag _ H). reflexivity. Qed.

Lemma xb_z_agree (v : int) (ρ ρ' : valuation) (b : xb) (z : Z) :
  (forall x, x <> v -> ρ' x = ρ x) -> xb_occ v b = false -> xb_z ρ b z -> xb_z ρ' b z.
Proof.
  intros Hag Ho H. destruct b as [c| |ts o i]; cbn [xb_z xb_occ] in *; try exact H.
  rewrite (smod_agree v ρ ρ' ts o Hag Ho). exact H.
Qed.

Lemma xv_val_agree (v : int) (ρ ρ' : valuation) (x : xv) (w : bv 64) :
  (forall y, y <> v -> ρ' y = ρ y) -> xv_occ v x = false -> xv_val ρ x w -> xv_val ρ' x w.
Proof.
  intros Hag Ho H. destruct x as [c|ts o|lo hi|m c|l|]; cbn [xv_val xv_occ] in *; try exact H.
  - rewrite (smod_agree v ρ ρ' ts o Hag Ho). exact H.
  - destruct H as [Hl Hb]. split; [exact Hl|]. intros i Hi. apply (xb_z_agree v ρ ρ'); [exact Hag | | exact (Hb i Hi)].
    destruct (existsb (xb_occ v) l) eqn:E; [discriminate|].
    destruct (xb_occ v (nth i l BT)) eqn:E2; [|reflexivity].
    exfalso. assert (X : existsb (xb_occ v) l = true) by (apply existsb_exists; exists (nth i l BT); split; [apply nth_In; lia | exact E2]).
    rewrite X in E. discriminate.
Qed.
