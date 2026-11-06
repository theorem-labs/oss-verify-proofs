(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec StoreOk MmapSim SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit SymDriveX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint vb_lookup (vb : list (nat * Z)) (i : nat) : option Z :=
  match vb with
  | [] => None
  | (j, n) :: rest => if Nat.eqb i j then Some n else vb_lookup rest i
  end.

Definition vb_ok (E : env) (spi : nat) (vb : list (nat * Z)) : Prop :=
  Forall (fun p => (bv_unsigned (ev E (fst p)) + snd p <= bv_unsigned (ev E spi))%Z) vb.

Lemma vb_lookup_sound : forall E spi vb i n,
  vb_ok E spi vb -> vb_lookup vb i = Some n ->
  (bv_unsigned (ev E i) + n <= bv_unsigned (ev E spi))%Z.
Proof.
  intros E spi vb i n Hvb. induction vb as [|[j m] rest IH]; intros H; [discriminate|].
  apply Forall_cons_iff in Hvb as [H1 H2]. cbn [vb_lookup] in H.
  destruct (Nat.eqb_spec i j).
  - injection H as <-. subst j. exact H1.
  - apply IH; assumption.
Qed.

Definition entry_below_vb (vb : list (nat * Z)) (spi : nat) (ihi : Z) (e : sentry) : bool :=
  entry_below_b spi ihi e ||
  match e with
  | SE (SA (EVar i) k) w _ =>
      match vb_lookup vb i with
      | Some n => Z.leb 0 k && Z.leb (k + Z.of_nat w) n
      | None => false
      end
  | _ => false
  end.

Definition log_below_vb (vb : list (nat * Z)) (spi : nat) (ihi : Z) (log : list sentry) : bool :=
  forallb (entry_below_vb vb spi ihi) log.

Lemma entry_below_vb_sound : forall E spi vb ihi b k w v (x : word),
  vb_ok E spi vb ->
  entry_below_vb vb spi ihi (SE (SA b k) w v) = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
Proof.
  intros E spi vb ihi b k w v x Hvb He Hsp Hx1 Hx2.
  unfold entry_below_vb in He. apply orb_prop in He as [He|He].
  - eapply entry_below_sound; eassumption.
  - destruct b as [z|i| | | | | |]; try discriminate.
    destruct (vb_lookup vb i) as [n|] eqn:Hr; [|discriminate].
    apply andb_prop in He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (vb_lookup_sound E spi vb i n Hvb Hr) as Hb.
    unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x). pose proof (u64_range (ev E i)).
    rewrite u_small by lia. lia.
Qed.

Lemma mem_denot_above_vb : forall E M vb log spi ihi (x : word),
  vb_ok E spi vb ->
  log_below_vb vb spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M vb log spi ihi x Hvb Hb Hsp Hx1 Hx2.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_below_vb forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  pose proof (entry_below_vb_sound E spi vb ihi b k w v x Hvb He Hsp Hx1 Hx2) as Hbnd.
  pose proof (u64_range x) as Hxr.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. lia.
  - rewrite length_N_to_le_bytes. right. lia.
Qed.

Lemma rdn_mem_denot_above_vb : forall segs E M vb log spi ihi (a : word) n,
  vb_ok E spi vb ->
  log_below_vb vb spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned a)%Z -> (ihi <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros segs E M vb log spi ihi a n Hvb Hb Hsp H1 H2 Hnw.
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_above_vb E M vb log spi ihi); try assumption; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma vb_ok_nil : forall E spi, vb_ok E spi [].
Proof. intros. constructor. Qed.

Lemma vb_ok_cons : forall E spi i n vb,
  (bv_unsigned (ev E i) + n <= bv_unsigned (ev E spi))%Z -> vb_ok E spi vb -> vb_ok E spi ((i, n) :: vb).
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma vb_ok_app : forall vals extra ebs spi vb,
  (spi < length vals)%nat ->
  Forall (fun p => (fst p < length vals)%nat) vb ->
  vb_ok (Env (vals_ev vals) ebs) spi vb -> vb_ok (Env (vals_ev (vals ++ extra)) ebs) spi vb.
Proof.
  intros vals extra ebs spi vb Hspi Hlt H. unfold vb_ok in *.
  induction vb as [|[i n] rest IH]; [constructor|].
  apply Forall_cons_iff in H as [H1 H2]. apply Forall_cons_iff in Hlt as [L1 L2].
  constructor; [| apply IH; assumption]. cbn [fst snd ev] in *.
  rewrite !vals_ev_app_l by assumption. exact H1.
Qed.
