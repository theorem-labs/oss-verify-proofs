(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module APWS.
Import AX2. Import AX2S. Import AP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition updl (E : env) (sg : sbind) : env :=
  Env (fun n => match sg_get sg n with Some e => edenot E e | None => ev E n end) (eb E).

Lemma esubsts_denot : forall E sg x, edenot E (esubsts sg x) = edenot (updl E sg) x.
Proof.
  intros E sg x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [esubsts edenot]; try reflexivity.
  - cbn [updl ev]. destruct (sg_get sg n); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma sg_get_in : forall sg n e, sg_get sg n = Some e -> In (n, e) sg.
Proof.
  induction sg as [|[v x] rest IH]; intros n e H; cbn [sg_get] in H; [discriminate|].
  destruct (Nat.eqb_spec v n); [injection H as <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.

Lemma updl_agree : forall lo E sg, sg_dom_ge lo sg = true -> env_agree lo E (updl E sg).
Proof.
  intros lo E sg H. split; [|reflexivity]. intros n Hn. cbn [updl ev].
  destruct (sg_get sg n) as [e|] eqn:Hg; [|reflexivity].
  apply sg_get_in in Hg. unfold sg_dom_ge in H. apply forallb_forall with (x := (n, e)) in H; [|exact Hg].
  cbn [fst] in H. apply Nat.leb_le in H. lia.
Qed.

Lemma sg_dom_in_ge : forall lo hi sg, sg_dom_in lo hi sg = true -> sg_dom_ge lo sg = true.
Proof.
  intros lo hi sg H. unfold sg_dom_in, sg_dom_ge in *. apply forallb_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) H p Hp) as X. apply andb_prop in X as [X _]. exact X.
Qed.

Lemma estart_asubsts : forall E sg a, estart E (asubsts sg a) = estart (updl E sg) a.
Proof. intros E sg [b o]. unfold asubsts, estart. cbn [a_base a_off]. rewrite esubsts_denot. reflexivity. Qed.
Lemma adenot_asubsts : forall E sg a, adenot E (asubsts sg a) = adenot (updl E sg) a.
Proof. intros E sg [b o]. unfold asubsts, adenot. cbn [a_base a_off]. rewrite esubsts_denot. reflexivity. Qed.

Lemma kentry_ok_ksubsts : forall segs E sg M K,
  kentry_ok segs E M (ksubsts sg K) <-> kentry_ok segs (updl E sg) M K.
Proof.
  intros segs E sg M K. set (E' := updl E sg).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubsts kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubsts, ?adenot_asubsts, ?esubsts_denot; fold E'; tauto.
Qed.

Lemma know_ok_ksubsts : forall segs E sg M k,
  know_ok segs E M (map (ksubsts sg) k) <-> know_ok segs (updl E sg) M k.
Proof.
  intros segs E sg M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ksubsts segs E sg M K); assumption.
Qed.

Lemma regs_ok_insts : forall E sg sr R,
  regs_ok E (map (esubsts sg) sr) R <-> regs_ok (updl E sg) sr R.
Proof.
  intros E sg sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubsts sg) sr) (ELit 0))
                     = edenot (updl E sg) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (esubsts sg (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubsts_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma elim1_test1_sound : forall segs E M kn c ts (test : Z -> Z -> bool) f t,
  know_ok segs E M kn -> sfact_ok E f -> elim1_test1 kn c ts test f t = true ->
  exists lo hi, test lo hi = true /\ (lo <= c + tden E ts <= hi)%Z.
Proof.
  intros segs E M kn c ts test [fts [flo fhi]] [kF x] Hkn Hf H. unfold elim1_test1 in H.
  destruct (Z.eqb (coeff_of_e x ts) 0 || Z.eqb kF 0 || negb (Z.eqb (coeff_of_e x ts mod kF) 0))%bool; [discriminate|].
  set (lam := (coeff_of_e x ts / kF)%Z) in *.
  apply (lin_test_sound segs E M kn) in H as (a & b & Ht & Hb); [|exact Hkn].
  rewrite sub_fact_sound in Hb. unfold sfact_ok in Hf. cbn [fst snd] in Hf.
  destruct (Z.leb_spec 0 lam).
  - exists (a + lam * flo)%Z, (b + lam * fhi)%Z. split; [exact Ht | nia].
  - exists (a + lam * fhi)%Z, (b + lam * flo)%Z. split; [exact Ht | nia].
Qed.

Lemma lin_test_elim1_sound : forall segs E M kn c ts test,
  know_ok segs E M kn -> lin_test_elim1 kn c ts test = true ->
  exists lo hi, test lo hi = true /\ (lo <= c + tden E ts <= hi)%Z.
Proof.
  intros segs E M kn c ts test Hkn H. unfold lin_test_elim1 in H.
  apply existsb_exists in H as [f [Hf H]]. apply existsb_exists in H as [t [Ht H]].
  pose proof (proj1 (Forall_forall _ _) (sum_facts_sound segs E M kn kn Hkn Hkn) f Hf) as Hfok.
  eapply elim1_test1_sound; [exact Hkn | exact Hfok | exact H].
Qed.

Lemma krange_lin_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> krange_lin kn e lo hi = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi Hkn H. unfold krange_lin in H.
  apply andb_prop in H as [H Hu]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [H0 Hh].
  apply Z.leb_le in H0. apply Z.ltb_lt in Hh.
  destruct (lin_of e) as [c ts] eqn:Hle. cbn [fst snd] in Hl, Hu.
  assert (Hl' : exists a b, Z.leb lo a = true /\ (a <= c + tden E ts <= b)%Z).
  { match type of Hl with (if ?t then _ else _) = _ => destruct t eqn:Hp end.
    - apply (lin_test_sound segs E M kn) in Hp as (a & b & Hta & Hba); [|exact Hkn]. exists a, b. split; assumption.
    - apply (lin_test_elim1_sound segs E M kn) in Hl as (a & b & Hta & Hba); [|exact Hkn]. exists a, b. split; assumption. }
  assert (Hu' : exists a b, Z.leb b hi = true /\ (a <= c + tden E ts <= b)%Z).
  { match type of Hu with (if ?t then _ else _) = _ => destruct t eqn:Hp end.
    - apply (lin_test_sound segs E M kn) in Hp as (a & b & Hta & Hba); [|exact Hkn]. exists a, b. split; assumption.
    - apply (lin_test_elim1_sound segs E M kn) in Hu as (a & b & Hta & Hba); [|exact Hkn]. exists a, b. split; assumption. }
  clear Hl Hu. destruct Hl' as (a & b & Hta & Hba). destruct Hu' as (a' & b' & Htb & Hbb).
  apply Z.leb_le in Hta. apply Z.leb_le in Htb.
  pose proof (lin_of_sound E e) as [q Hq]. rewrite Hle in Hq. unfold lden in Hq. cbn [fst snd] in Hq.
  unfold AX2S.uE in Hq. unfold two64 in Hh.
  pose proof (u64_range (edenot E e)) as Hr.
  assert (q = 0) by nia. subst q. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kentry_eqb_eq' : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.

Lemma find_win_in : forall w k K k', find_win w k K = Some k' -> In K k /\ (forall X, In X k' -> In X k).
Proof.
  induction w as [|w IH]; intros [|X k] K k' H; cbn [find_win] in H; try discriminate.
  destruct (kentry_eqb X K) eqn:He.
  - injection H as <-. apply kentry_eqb_eq' in He. subst. split; [left; reflexivity | intros Y HY; right; exact HY].
  - destruct (IH k K k' H) as [H1 H2]. split; [right; exact H1 | intros Y HY; right; apply H2; exact HY].
Qed.

Lemma subseq_left_in : forall tk k0 k acc K,
  (forall X, In X k -> In X k0) -> (In K tk \/ In K acc) -> In K (subseq_left k tk acc) \/ In K k0.
Proof.
  induction tk as [|T tk IH]; intros k0 k acc K Hsub Hin; cbn [subseq_left].
  - destruct Hin as [[]|H]; left; exact H.
  - destruct (find_win 16 k T) as [k'|] eqn:Hf.
    + destruct (find_win_in _ _ _ _ Hf) as [H1 H2].
      destruct Hin as [[HT|Hin]|Hin]; [right; apply Hsub; rewrite <- HT; exact H1| |];
        apply (IH k0 k' acc K ltac:(intros X HX; apply Hsub; apply H2; exact HX)); tauto.
    + apply (IH k0 k (T :: acc) K Hsub). cbn [In]. destruct Hin as [[HT|Hin]|Hin]; tauto.
Qed.

(* [comment removed for export] *)
Lemma kn_incl_s_cases : forall A k tk, kn_incl_s A k tk = true ->
  forall K, In K tk -> In K k \/ kn_incl1_s A k K = true.
Proof.
  intros A k tk H K Hin. unfold kn_incl_s in H.
  destruct (subseq_left_in tk k k [] K ltac:(intros X HX; exact HX) (or_introl Hin)) as [Hl|Hk].
  - right. exact (proj1 (forallb_forall _ _) H K Hl).
  - left. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_snext_eq : forall s, is_snext s = true -> s = SNext.
Proof. intros s H. destruct s; try discriminate. reflexivity. Qed.

End APWS.
