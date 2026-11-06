(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums AsanNodesLib AsanNodesLibSound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HKIT.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).
#[local] Notation inr := LBNS.inr (only parsing).

Section Kit.
Variable SEGS : list Segment.
#[local] Notation cell := (LBNS.cell SEGS) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).

Lemma u_eaddz : forall E e z, bv_unsigned (edenot E (eaddz e z)) = (bv_unsigned (edenot E e) + z) mod 2 ^ 64.
Proof.
  intros E e z. unfold eaddz. rewrite mkAlu_denot, u_add64, edenot_lit, LBNS.u_Zbv_mod.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma kwr_wr_ok : forall E M k b off n, know_ok SEGS E M k -> kwritable_x k k b off (ELit n) = true -> 0 < n < 2 ^ 63 ->
  estart E (SA b off) < 2 ^ 63 ->
  wr_ok M (estart E (SA b off)) n /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M k b off n HK Hw Hn Hlt.
  assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  destruct (kwritable_x_sound SEGS E M k k b off (ELit n) HK HK Hw) as (Wst & Wlo & Whi). rewrite El in *.
  split; [|split; assumption].
  intros x m Hx Hxm.
  apply (store_ok_sub SEGS M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) (LBNS.W x) m).
  - rewrite u64_lit by lia. lia.
  - apply Wst. lia.
  - rewrite u64_lit by lia. rewrite LBNS.u_W by lia. lia.
  - rewrite u64_lit by lia. rewrite LBNS.u_W by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hrange : Type := (expr * Z * Z)%type.
Fixpoint havs (k : list kentry) (rs : list hrange) : list kentry :=
  match rs with
  | [] => k
  | (b, o, n) :: rest => havs (kn_havoc k b o (ELit n)) rest
  end.
Definition in_rs (E : env) (rs : list hrange) (x : word) : bool :=
  existsb (fun r : hrange => let '(b, o, n) := r in LBNS.inrb (estart E (SA b o)) n x) rs.

Lemma havs_mix : forall E (M M' : word -> option byte) rs k (P : word -> bool),
  Forall (fun r : hrange => 0 <= snd r < 2 ^ 64) rs -> mem_grows M M' ->
  know_ok SEGS E (LBNS.mixm P M M') k ->
  know_ok SEGS E (LBNS.mixm (fun x => (P x || in_rs E rs x)%bool) M M') (havs k rs).
Proof.
  intros E M M' rs. induction rs as [|[[b o] n] rest IH]; intros k P Hn Hg HK.
  - assert (EQ : P = (fun x : word => (P x || in_rs E [] x)%bool)).
    { apply functional_extensionality. intros x. cbn [in_rs existsb]. rewrite orb_false_r. reflexivity. }
    exact (eq_ind _ (fun P0 => know_ok SEGS E (LBNS.mixm P0 M M') k) HK _ EQ).
  - apply Forall_cons_iff in Hn as [Hn1 Hn]. cbn [snd] in Hn1. cbn [havs].
    assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
    set (P1 := fun x => (P x || LBNS.inrb (estart E (SA b o)) n x)%bool).
    assert (K1 : know_ok SEGS E (LBNS.mixm P1 M M') (kn_havoc k b o (ELit n))).
    { apply (w_know_ok_havoc SEGS E (LBNS.mixm P M M') (LBNS.mixm P1 M M') k b o (ELit n) HK).
      - intros x Hx. rewrite El in Hx. unfold LBNS.mixm, P1.
        destruct (LBNS.inrb (estart E (SA b o)) n x) eqn:Hb; [|rewrite orb_false_r; reflexivity].
        exfalso. apply LBNS.inrb_inr in Hb. unfold LBNS.inr in Hb. lia.
      - apply LBNS.mixm_grows2; [exact Hg|]. intros x Hx. unfold P1. rewrite Hx. reflexivity. }
    specialize (IH _ P1 Hn Hg K1).
    assert (EQ : (fun x : word => (P1 x || in_rs E rest x)%bool) = (fun x : word => (P x || in_rs E ((b, o, n) :: rest) x)%bool)).
    { apply functional_extensionality. intros x. unfold P1. cbn [in_rs existsb]. rewrite orb_assoc. reflexivity. }
    exact (eq_ind _ (fun P0 => know_ok SEGS E (LBNS.mixm P0 M M') (havs (kn_havoc k b o (ELit n)) rest)) IH _ EQ).
Qed.

(* [comment removed for export] *)
Lemma havs_sound : forall E (M M' : word -> option byte) rs k,
  Forall (fun r : hrange => 0 <= snd r < 2 ^ 64) rs -> mem_grows M M' -> know_ok SEGS E M k ->
  (forall x, in_rs E rs x = false -> M' x = M x) ->
  know_ok SEGS E M' (havs k rs).
Proof.
  intros E M M' rs k Hn Hg HK Hout.
  pose proof (havs_mix E M M' rs k (fun _ => false) Hn Hg HK) as X.
  assert (EQ : LBNS.mixm (fun x : word => (false || in_rs E rs x)%bool) M M' = M').
  { apply functional_extensionality. intros x. unfold LBNS.mixm. cbn [orb].
    destruct (in_rs E rs x) eqn:Hb; [reflexivity | symmetry; exact (Hout x Hb)]. }
  exact (eq_ind _ (fun M0 => know_ok SEGS E M0 (havs k rs)) X _ EQ).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_eq_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> W a = W b.
Proof. intros a b H. apply bv_eq. unfold LBNS.W. rewrite !LBNS.u_Zbv_mod. exact H. Qed.

Lemma w_eaddz : forall E e z, edenot E (eaddz e z) = W (bv_unsigned (edenot E e) + z).
Proof. intros. apply bv_eq. rewrite u_eaddz. unfold LBNS.W. rewrite LBNS.u_Zbv_mod. reflexivity. Qed.

Lemma w_eadd : forall E a b, edenot E (eadd a b) = W (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)).
Proof. intros. apply bv_eq. rewrite LBNS.u_eadd. unfold LBNS.W. rewrite LBNS.u_Zbv_mod. reflexivity. Qed.

Lemma u_mulk : forall E c e, 0 <= c < 2 ^ 64 ->
  bv_unsigned (edenot E (EMd M_MUL (ELit c) e)) = (c * bv_unsigned (edenot E e)) mod 2 ^ 64.
Proof. intros E c e Hc. cbn [edenot]. rewrite u_mul64. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma w_lin2 : forall E e kx c ez kz, bv_unsigned (edenot E e) = ez -> bv_unsigned (edenot E kx) = kz ->
  0 <= c < 2 ^ 64 -> 0 <= c * kz < 2 ^ 64 ->
  edenot E (eadd e (EMd M_MUL (ELit c) kx)) = W (ez + c * kz).
Proof.
  intros E e kx c ez kz He Hk Hc Hck. rewrite w_eadd. apply W_eq_mod. rewrite u_mulk by lia. rewrite He, Hk.
  rewrite (Z.mod_small (c * kz)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sr_upds (sr : list expr) (ups : list (nat * expr)) : list expr :=
  fold_left (fun acc p => sr_upd acc (fst p) (snd p)) ups sr.

Lemma regs_ok_upds : forall E' (R' : bvmap 5 word) ups sr0,
  (forall i e, In (i, e) ups -> edenot E' e = getr R' (Z_to_bv 5 (Z.of_nat i))) ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) (map fst ups) -> getr R' r = edenot E' (nth (ridx r) sr0 (ELit 0))) ->
  regs_ok E' (sr_upds sr0 ups) R'.
Proof.
  intros E' R' ups. induction ups as [|[i e] rest IH]; intros sr0 Hu Hb.
  - apply regs_ok_pointwise. intros r Hr. apply Hb; [exact Hr | intros []].
  - unfold sr_upds. cbn [fold_left fst snd]. apply IH.
    + intros j e' Hin. apply (Hu j e'). right. exact Hin.
    + intros r Hr Hn. rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) i) as [Ei|Ne].
      * rewrite (Hu i e (or_introl eq_refl)). rewrite <- Ei. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
      * apply Hb; [exact Hr|]. cbn [map fst In]. intros [X|X]; [apply Ne; symmetry; exact X | exact (Hn X)].
Qed.

(* [comment removed for export] *)
Lemma kword_intro : forall E (M : word -> option byte) b o (w : nat) ve z v,
  (w <= 8)%nat -> estart E (SA b o) = z -> 0 <= z -> z + Z.of_nat w <= 2 ^ 64 -> z < 2 ^ 64 ->
  cell M z w v -> edenot E ve = v -> kentry_ok SEGS E M (KWord (SA b o) w ve).
Proof.
  intros E M b o w ve z v Hw Hz H0 H1 H2 Hc Hv. cbn [kentry_ok]. split; [exact Hw|].
  assert (F : flat E (SA b o) (Z.of_nat w)) by (unfold flat; rewrite Hz; lia).
  split; [exact F|].
  assert (Ea : adenot E (SA b o) = W z).
  { apply bv_eq. rewrite (flat_u E _ _ F). rewrite Hz. unfold LBNS.W. rewrite u64_lit by lia. reflexivity. }
  rewrite Ea, Hv. exact Hc.
Qed.



(* [comment removed for export] *)
Lemma in_rs_false : forall E rs x, in_rs E rs x = false ->
  Forall (fun r : hrange => ~ inr x (estart E (SA (fst (fst r)) (snd (fst r)))) (snd r)) rs.
Proof.
  intros E rs x. induction rs as [|[[b o] n] rest IH]; intros H; [constructor|].
  cbn [in_rs existsb] in H. apply orb_false_iff in H as [H1 H2]. constructor; [|exact (IH H2)].
  cbn [fst snd]. intros X. apply LBNS.inrb_inr in X. congruence.
Qed.

(* [comment removed for export] *)
Lemma estart_shift : forall E b o d, estart E (SA b (o + d)) = estart E (SA b o) + d.
Proof. intros. unfold estart. cbn [a_base a_off]. lia. Qed.

Lemma havs_app : forall l1 l2 k, havs k (l1 ++ l2) = havs (havs k l1) l2.
Proof. induction l1 as [|[[b o] n] rest IH]; intros l2 k; cbn [havs app]; [reflexivity | apply IH]. Qed.

Lemma in_rs_app : forall E l1 l2 x, in_rs E (l1 ++ l2) x = (in_rs E l1 x || in_rs E l2 x)%bool.
Proof. intros. unfold in_rs. apply existsb_app. Qed.

Lemma incl_dec : forall l1 l2 : list nat, forallb (fun n => existsb (Nat.eqb n) l2) l1 = true -> forall n, In n l1 -> In n l2.
Proof.
  intros l1 l2 H n Hn. rewrite forallb_forall in H. specialize (H n Hn). apply existsb_exists in H as (m & Hm & E0).
  apply Nat.eqb_eq in E0. subst m. exact Hm.
Qed.

End Kit.
End HKIT.
