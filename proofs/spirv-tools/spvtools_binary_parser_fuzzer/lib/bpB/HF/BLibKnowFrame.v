(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BStoreOk BAllocSim BMmapSim BMemSplit BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (b : expr) (k n : Z) : bool :=
  if expr_eqb b ub then (Z.leb (k + n) uk || Z.leb (uk + un) k)%bool
  else ranges_apart allkn ub uk un b k n.

Lemma apart_b_sound : forall segs E M allkn ub uk un b k n,
  know_ok segs E M allkn -> apart_b allkn ub uk un b k n = true ->
  ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
  intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
  destruct (expr_eqb b ub) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - eapply ranges_apart_sound; [exact HK | exact H].
Qed.

Definition kn_frame1 (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : list kentry :=
  match K with
  | KWord (SA b k) w _ => if apart_b allkn ub uk un b k (Z.of_nat w) then [K] else []
  | KZero (SA b k) (ELit l) =>
      if (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool then
        if apart_b allkn ub uk un b k l then [K]
        else if expr_eqb b ub then
          (if Z.ltb k uk then [KZero (SA b k) (ELit (Z.min l (uk - k)))] else [])
          ++ (if Z.ltb (uk + un) (k + l) then [KZero (SA b (Z.max k (uk + un))) (ELit (k + l - Z.max k (uk + un)))] else [])
        else []
      else []
  | KZero _ _ => []
  | KBlob (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
  | KBlob _ _ _ => []
  | KImg lo hi => if (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b allkn ub uk un (ELit 0) lo (hi - lo))%bool then [K] else []
  | KAlign _ _ => [K]
  | KRange _ _ _ => [K]
  | KDisj _ _ _ _ => [K]
  | KWr _ _ => [K]
  end.

Definition kn_frame (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  flat_map (kn_frame1 kn ub uk un) kn.

Lemma edenot_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros. reflexivity. Qed.

Lemma know_ok_frame : forall segs E M M' kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un ->
  (forall x : word,
     (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (kn_frame kn ub uk un).
Proof.
  intros segs E M M' kn ub uk un HK Hfl OUT GR.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_frame1] in Hb.
  -
    destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
  -
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
    apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. pose proof Hf as Hf0. destruct Hf as (G1 & G2 & G3 & G4).
    destruct (apart_b kn ub uk un b k l) eqn:Hap.
    + destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia.
    + destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
      apply expr_eqb_eq in Heq. subst b.
      unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
        intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
      * destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
        intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
        replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
          with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
        apply Hz. lia.
  -
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  -
    destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
    pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
    rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
  -   destruct Hb as [<-|[]]. exact HKK.
  -   destruct Hb as [<-|[]]. exact HKK.
  -
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
  -   destruct Hb as [<-|[]]. exact HKK.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
