(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive
  LibKnowFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition lit_in (lo hi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (ELit z) a) w _ => (Z.eqb z 0 && Z.leb lo a && Z.leb (a + Z.of_nat w) hi)%bool
  | _ => false
  end.

Definition log_outside (lo hi : Z) (log : list sentry) : list sentry := List.filter (fun e => negb (lit_in lo hi e)) log.

Definition carry_skip (lo hi : Z) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let '(kn1, scs, hs) := carry (log_outside lo hi log) kn hints in
  (kn_frame kn1 (ELit 0) lo (hi - lo), scs, hs).

Lemma wbytes_same_at : forall bs (m1 m2 : word -> option byte) (a x : word),
  m1 x = m2 x -> wbytes m1 a bs x = wbytes m2 a bs x.
Proof.
  induction bs as [|b rest IH]; intros m1 m2 a x H; [exact H|].
  cbn [wbytes]. apply IH. cbv beta. destruct (bv_eqb x a); [reflexivity | exact H].
Qed.

Lemma wbytes_grows_mono : forall bs (m1 m2 : word -> option byte) (a : word),
  mem_grows m1 m2 -> mem_grows (wbytes m1 a bs) (wbytes m2 a bs).
Proof.
  induction bs as [|b rest IH]; intros m1 m2 a H; [exact H|].
  cbn [wbytes]. apply IH. intros y Hy. cbv beta in Hy |- *. destruct (bv_eqb y a); [discriminate | exact (H y Hy)].
Qed.

Lemma log_outside_flat : forall E lo hi log, log_flat E log -> log_flat E (log_outside lo hi log).
Proof.
  intros E lo hi log. induction log as [|[a w v] rest IH]; intro H; [cbn; trivial|].
  cbn [log_flat] in H. destruct H as (Hw & Hf & Hr). unfold log_outside in *. cbn [List.filter].
  destruct (negb (lit_in lo hi (SE a w v))); [cbn [log_flat]; split; [exact Hw | split; [exact Hf | exact (IH Hr)]] | exact (IH Hr)].
Qed.

Lemma log_outside_agree : forall E base lo hi log, (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z -> log_flat E log ->
  forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z ->
  mem_denot E base log x = mem_denot E base (log_outside lo hi log) x.
Proof.
  intros E base lo hi log Hlo Hhi. induction log as [|[a w v] rest IH]; intros Hlf x Hx; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hf & Hr). unfold log_outside in *. cbn [List.filter mem_denot].
  destruct (lit_in lo hi (SE a w v)) eqn:Hin; cbn [negb].
  - rewrite <- (IH Hr x Hx). destruct a as [ab ak]. cbn [lit_in] in Hin.
    destruct ab as [z| | | | | | |]; try discriminate Hin.
    apply andb_prop in Hin as [Hin H3]. apply andb_prop in Hin as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst z.
    pose proof (flat_u E _ _ Hf) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu. rewrite edenot_lit0 in Hu.
    destruct Hf as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4. rewrite edenot_lit0 in F1, F2, F4.
    destruct Hx as [Hx|Hx].
    + apply wbytes_below; rewrite ?length_N_to_le_bytes, Hu; lia.
    + apply wbytes_above; rewrite ?length_N_to_le_bytes, Hu; lia.
  - cbn [mem_denot]. apply wbytes_same_at. exact (IH Hr x Hx).
Qed.

Lemma log_outside_grows : forall E base lo hi log,
  mem_grows (mem_denot E base (log_outside lo hi log)) (mem_denot E base log).
Proof.
  intros E base lo hi log. induction log as [|[a w v] rest IH]; [apply mem_grows_refl|].
  unfold log_outside in *. cbn [List.filter mem_denot].
  destruct (lit_in lo hi (SE a w v)); cbn [negb].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
  - cbn [mem_denot]. apply wbytes_grows_mono. exact IH.
Qed.

Lemma carry_skip_sound : forall segs E (anybase : word -> option byte) base lo hi log kn hints kn' scs hs',
  carry_skip lo hi log kn hints = (kn', scs, hs') ->
  (0 <= lo)%Z -> (lo <= hi)%Z -> (lo < 2 ^ 64)%Z -> (hi <= 2 ^ 64)%Z ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs anybase E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof.
  intros segs E anyb base lo hi log kn hints kn' scs hs' Hc Hlo Hlh Hlo64 Hhi Hlf Hkn Hscs.
  unfold carry_skip in Hc. destruct (carry (log_outside lo hi log) kn hints) as [[kn1 scs1] hs1] eqn:Hca.
  injection Hc as <- <- <-.
  pose proof (carry_sound segs E anyb base _ kn hints kn1 scs1 hs1 Hca (log_outside_flat E lo hi log Hlf) Hkn Hscs) as HK1.
  apply (know_ok_frame segs E (mem_denot E base (log_outside lo hi log)) (mem_denot E base log) kn1 (ELit 0) lo (hi - lo) HK1).
  - unfold flat, estart. cbn [a_base a_off]. rewrite edenot_lit0. lia.
  - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite edenot_lit0 in Hx.
    apply log_outside_agree; [exact Hlo | exact Hhi | exact Hlf | lia].
  - apply log_outside_grows.
Qed.
