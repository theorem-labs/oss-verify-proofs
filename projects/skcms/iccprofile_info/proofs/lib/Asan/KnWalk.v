(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC.
Unset Lia Cache.

Section Walk.
Variable eqb : kentry -> kentry -> bool.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_from (K : kentry) (cur : list kentry) : option (list kentry) :=
  match cur with
  | [] => None
  | X :: r => if eqb X K then Some r else find_from K r
  end.

Lemma find_from_hit : forall K cur r, find_from K cur = Some r ->
  existsb (fun X => eqb X K) cur = true /\ (forall Y, In Y r -> In Y cur).
Proof.
  intros K cur; induction cur as [|X cur IH]; intros r H; cbn [find_from] in H; [discriminate|].
  destruct (eqb X K) eqn:E.
  - injection H as <-. cbn. rewrite E. split; [reflexivity|]. intros Y HY; right; exact HY.
  - destruct (IH r H) as [H1 H2]. cbn. rewrite E, H1. split; [reflexivity|]. intros Y HY; right; apply H2, HY.
Qed.

Lemma existsb_incl : forall (f : kentry -> bool) (a b : list kentry), (forall Y, In Y a -> In Y b) ->
  existsb f a = true -> existsb f b = true.
Proof.
  intros f a b Hi Ha. apply existsb_exists in Ha as [x [Hx Hf]]. apply existsb_exists. exists x. split; [apply Hi, Hx | exact Hf].
Qed.

(* [comment removed for export] *)
Fixpoint incl_walk (f : kentry -> bool) (cur : list kentry) (tk : list kentry) : bool :=
  match tk with
  | [] => true
  | K :: tk' => match find_from K cur with
                | Some cur' => incl_walk f cur' tk'
                | None => if f K then incl_walk f cur tk' else false
                end
  end.

Lemma incl_walk_eq : forall (k : list kentry) (f : kentry -> bool),
  (forall K, existsb (fun X => eqb X K) k = true -> f K = true) ->
  forall tk cur, (forall Y, In Y cur -> In Y k) -> incl_walk f cur tk = forallb f tk.
Proof.
  intros k f Hf tk; induction tk as [|K tk IH]; intros cur Hc; cbn [incl_walk forallb]; [reflexivity|].
  destruct (find_from K cur) as [cur'|] eqn:E.
  - destruct (find_from_hit K cur cur' E) as [H1 H2]. rewrite (Hf K (existsb_incl _ cur k Hc H1)). cbn [andb].
    apply IH. intros Y HY; apply Hc, H2, HY.
  - destruct (f K); cbn [andb]; [apply IH, Hc | reflexivity].
Qed.

(* [comment removed for export] *)
Fixpoint meet_walk (k cur : list kentry) (ka : list kentry) : list kentry :=
  match ka with
  | [] => []
  | K :: ka' => match find_from K cur with
                | Some cur' => K :: meet_walk k cur' ka'
                | None => if existsb (fun X => eqb X K) k then K :: meet_walk k cur ka' else meet_walk k cur ka'
                end
  end.

Lemma meet_walk_eq : forall k ka cur, (forall Y, In Y cur -> In Y k) ->
  meet_walk k cur ka = List.filter (fun K => existsb (fun X => eqb X K) k) ka.
Proof.
  intros k ka; induction ka as [|K ka IH]; intros cur Hc; cbn [meet_walk List.filter]; [reflexivity|].
  destruct (find_from K cur) as [cur'|] eqn:E.
  - destruct (find_from_hit K cur cur' E) as [H1 H2]. rewrite (existsb_incl _ cur k Hc H1). f_equal. apply IH. intros Y HY; apply Hc, H2, HY.
  - destruct (existsb (fun X => eqb X K) k); [f_equal|]; apply IH, Hc.
Qed.
End Walk.

Section Fast.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
Definition kn_incl_hF (k tk : list kentry) : bool := incl_walk kentry_eqb (kn_incl1_h A k) k tk.
Lemma kn_incl_hF_eq : forall k tk, kn_incl_hF k tk = kn_incl_h A k tk.
Proof.
  intros. unfold kn_incl_hF, kn_incl_h. apply (incl_walk_eq kentry_eqb k).
  - intros K H. unfold kn_incl1_h. rewrite H. reflexivity.
  - intros Y HY; exact HY.
Qed.

(* [comment removed for export] *)
Definition kn_incl_exF (k tk : list kentry) : bool :=
  incl_walk (fun X K => kentry_eqb K X) (fun K => existsb (kentry_eqb K) k) k tk.
Lemma kn_incl_exF_eq : forall k tk, kn_incl_exF k tk = forallb (fun K => existsb (kentry_eqb K) k) tk.
Proof.
  intros. unfold kn_incl_exF. apply (incl_walk_eq (fun X K => kentry_eqb K X) k).
  - intros K H. exact H.
  - intros Y HY; exact HY.
Qed.

Definition entailsF (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_exF (kn cs) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Lemma entailsF_eq : forall cs ch, entailsF cs ch = entails cs ch.
Proof. intros. unfold entailsF, entails. rewrite kn_incl_exF_eq. reflexivity. Qed.

Definition entails_hF (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_hF (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Lemma entails_hF_eq : forall lo hi cs ch, entails_hF lo hi cs ch = entails_h A lo hi cs ch.
Proof. intros. unfold entails_hF, entails_h. rewrite kn_incl_hF_eq. reflexivity. Qed.

Definition node_diamond_joinF (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := meet_walk kentry_eqb (kn cb) (kn cb) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_hF v0 hi ca csJ && entails_hF v0 hi cb csJ)%bool
  then Some csJ else None.
Lemma node_diamond_joinF_eq : forall nx joinpc rs ca cb,
  node_diamond_joinF nx joinpc rs ca cb = node_diamond_join A nx0 nx joinpc rs ca cb.
Proof.
  intros. unfold node_diamond_joinF, node_diamond_join. rewrite !entails_hF_eq.
  rewrite (meet_walk_eq kentry_eqb (kn cb) (kn ca) (kn cb) (fun Y HY => HY)). reflexivity.
Qed.
End Fast.

(* [comment removed for export] *)
From Stdlib Require Import FunctionalExtensionality.
Lemma entailsF_fun : entailsF = entails.
Proof. apply functional_extensionality; intros cs. apply functional_extensionality; intros ch. apply entailsF_eq. Qed.
Lemma entails_hF_fun : forall A, entails_hF A = entails_h A.
Proof.
  intros A. apply functional_extensionality; intros lo. apply functional_extensionality; intros hi.
  apply functional_extensionality; intros cs. apply functional_extensionality; intros ch. apply entails_hF_eq.
Qed.
Lemma node_diamond_joinF_fun : forall A nx0, node_diamond_joinF A nx0 = node_diamond_join A nx0.
Proof.
  intros A nx0. apply functional_extensionality; intros nx. apply functional_extensionality; intros jp.
  apply functional_extensionality; intros rs. apply functional_extensionality; intros ca.
  apply functional_extensionality; intros cb. apply node_diamond_joinF_eq.
Qed.
