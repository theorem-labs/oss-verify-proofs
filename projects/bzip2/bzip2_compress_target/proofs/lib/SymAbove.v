(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec StoreOk MmapSim SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit SymDriveX.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX.
Import ListNotations.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Above.
  Variable segs : list Segment.

  Fixpoint krange_of (kn : list kentry) (i : nat) : option (Z * Z) :=
    match kn with
    | [] => None
    | KRange (EVar j) lo hi :: rest => if Nat.eqb i j then Some (lo, hi) else krange_of rest i
    | _ :: rest => krange_of rest i
    end.

  Lemma krange_of_sound : forall E M kn i lo hi,
    know_ok segs E M kn -> krange_of kn i = Some (lo, hi) ->
    (lo <= bv_unsigned (ev E i) <= hi)%Z.
  Proof.
    intros E M kn i lo hi HK. induction kn as [|K rest IH]; intros H; [discriminate|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    cbn [krange_of] in H.
    destruct K as [| | | | |e lo' hi'| |]; try (apply IH; assumption).
    destruct e as [|j| | | | | |]; try (apply IH; assumption).
    destruct (Nat.eqb_spec i j).
    - injection H as <- <-. subst j. cbn [kentry_ok edenot] in HK1. exact HK1.
    - apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Fixpoint kbelow_of (kn : list kentry) (i spi : nat) : option Z :=
    match kn with
    | [] => None
    | KDisj (SA (EVar j) Z0) n (SA (EVar s) o) m :: rest =>
        if (Nat.eqb i j && Nat.eqb spi s && Z.leb (- (2 ^ 40)) o && Z.leb o 0 && Z.leb (2 ^ 64) m)%bool
        then Some n else kbelow_of rest i spi
    | _ :: rest => kbelow_of rest i spi
    end.

  Lemma kbelow_of_sound : forall E M kn i spi n,
    know_ok segs E M kn -> kbelow_of kn i spi = Some n ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E i) + n <= bv_unsigned (ev E spi))%Z.
  Proof.
    intros E M kn i spi n HK. induction kn as [|K rest IH]; intros H Hsp; [discriminate|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    cbn [kbelow_of] in H.
    destruct K as [| | | | | | |a1 n1 a2 n2]; try (apply IH; assumption).
    destruct a1 as [b1 o1]. destruct b1 as [|j| | | | | |]; try (apply IH; assumption).
    destruct o1; try (apply IH; assumption).
    destruct a2 as [b2 o]. destruct b2 as [|s| | | | | |]; try (apply IH; assumption).
    destruct (Nat.eqb i j && Nat.eqb spi s && Z.leb (- (2 ^ 40)) o && Z.leb o 0 && Z.leb (2 ^ 64) n2)%bool eqn:Hc;
      [|apply IH; assumption].
    injection H as <-.
    repeat (apply andb_prop in Hc as [Hc ?H1]).
    apply Nat.eqb_eq in Hc. apply Nat.eqb_eq in H3. apply Z.leb_le in H2. apply Z.leb_le in H0. apply Z.leb_le in H1.
    subst j s. cbn [kentry_ok] in HK1. unfold estart in HK1. cbn [a_base a_off edenot] in HK1.
    pose proof (u64_range (ev E i)). lia.
  Qed.

  Definition entry_below_kb (kn : list kentry) (spi : nat) (ihi ceil : Z) (e : sentry) : bool :=
    entry_below_b spi ihi e ||
    match e with
    | SE (SA (EVar i) k) w _ =>
        match krange_of kn i with
        | Some (lo, hi) => Z.leb 0 (lo + k) && Z.leb (hi + k + Z.of_nat w) ceil
        | None => false
        end
        || match kbelow_of kn i spi with
           | Some n => Z.leb 0 k && Z.leb (k + Z.of_nat w) n
           | None => false
           end
    | _ => false
    end.

  Definition log_below_kb (kn : list kentry) (spi : nat) (ihi ceil : Z) (log : list sentry) : bool :=
    forallb (entry_below_kb kn spi ihi ceil) log.

  Lemma entry_below_kb_sound : forall E M0 kn spi ihi ceil b k w v (x : word),
    know_ok segs E M0 kn ->
    entry_below_kb kn spi ihi ceil (SE (SA b k) w v) = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
  Proof.
    intros E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3.
    unfold entry_below_kb in He. apply orb_prop in He as [He|He].
    - eapply entry_below_sound; eassumption.
    - destruct b as [z|i| | | | | |]; try discriminate.
      apply orb_prop in He as [He|He].
      + destruct (krange_of kn i) as [[lo hi]|] eqn:Hr; [|discriminate].
        apply andb_prop in He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        pose proof (krange_of_sound E M0 kn i lo hi HK Hr) as Hb.
        unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x).
        rewrite u_small by lia. lia.
      + destruct (kbelow_of kn i spi) as [n|] eqn:Hr; [|discriminate].
        apply andb_prop in He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        pose proof (kbelow_of_sound E M0 kn i spi n HK Hr Hsp) as Hb.
        unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x). pose proof (u64_range (ev E i)).
        pose proof (u64_range (ev E spi)).
        rewrite u_small by lia. lia.
  Qed.

  Lemma mem_denot_above_kb : forall E M0 M kn log spi ihi ceil (x : word),
    know_ok segs E M0 kn ->
    log_below_kb kn spi ihi ceil log = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    mem_denot E M log x = M x.
  Proof.
    intros E M0 M kn log spi ihi ceil x HK Hb Hc Hsp Hx1 Hx2 Hx3.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_below_kb forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    pose proof (entry_below_kb_sound E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3) as Hbnd.
    pose proof (u64_range x) as Hxr.
    cbn [mem_denot]. rewrite wbytes_outside.
    - apply IH. exact Hrest.
    - rewrite length_N_to_le_bytes. lia.
    - rewrite length_N_to_le_bytes. right. lia.
  Qed.
End Above.

(* [comment removed for export] *)
Definition above_eq (sp0 : word) (mem0 M : word -> option byte) : Prop :=
  forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

Lemma above_eq_step : forall sp0 mem0 M M',
  (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) ->
  above_eq sp0 mem0 M -> above_eq sp0 mem0 M'.
Proof. intros sp0 mem0 M M' H HA a Ha. rewrite (H a Ha). apply HA, Ha. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac pins := repeat match goal with P : vals_ev _ _ = _ |- _ => rewrite P end.
