(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec StoreOk MmapSim SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit SymDriveX SymAbove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AboveD.
  Variable segs : list Segment.

  Definition BELOW48 : Z := 281474976710656.

  (* [comment removed for export] *)
  Fixpoint kdisj_sp_of (kn : list kentry) (spi i : nat) : option Z :=
    match kn with
    | [] => None
    | KDisj (SA (EVar s) o) m (SA (EVar j) 0) n :: rest =>
        if (Nat.eqb s spi && Z.eqb o (-8388608) && Z.eqb m BELOW48 && Nat.eqb j i)%bool then Some n
        else kdisj_sp_of rest spi i
    | _ :: rest => kdisj_sp_of rest spi i
    end.

  Lemma kdisj_sp_of_sound : forall E M kn spi i n,
    know_ok segs E M kn -> kdisj_sp_of kn spi i = Some n ->
    (bv_unsigned (ev E spi) + -8388608 + BELOW48 <= bv_unsigned (ev E i) + 0
     \/ bv_unsigned (ev E i) + 0 + n <= bv_unsigned (ev E spi) + -8388608)%Z.
  Proof.
    intros E M kn spi i n HK. induction kn as [|K rest IH]; intros H; [discriminate|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    cbn [kdisj_sp_of] in H.
    destruct K as [| | | | | | |a1 m a2 n2]; try (apply IH; assumption).
    destruct a1 as [b1 o]. destruct b1 as [|s| | | | | |]; try (apply IH; assumption).
    destruct a2 as [b2 o2]. destruct b2 as [|j| | | | | |]; try (apply IH; assumption).
    destruct (Z.eq_dec o2 0) as [Eo2|Ne].
    2:{ destruct o2; try (apply IH; assumption); exfalso; apply Ne; reflexivity. }
    subst o2.
    destruct (Nat.eqb s spi && Z.eqb o (-8388608) && Z.eqb m BELOW48 && Nat.eqb j i)%bool eqn:Hc.
    - injection H as <-. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. apply Nat.eqb_eq in H4. subst s o m j.
      cbn [kentry_ok] in HK1. unfold estart in HK1. cbn [a_base a_off edenot] in HK1. exact HK1.
    - apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition CEIL40 : Z := 1099511627776.

  Definition entry_below_kd (kn : list kentry) (spi : nat) (ihi : Z) (e : sentry) : bool :=
    entry_below_kb kn spi ihi CEIL40 e ||
    match e with
    | SE (SA (EVar i) k) w _ =>
        match krange_of kn i, kdisj_sp_of kn spi i with
        | Some (lo, hi), Some n => Z.leb 0 (lo + k) && Z.leb 0 k && Z.leb (k + Z.of_nat w) n && Z.ltb (hi + n) BELOW48
        | _, _ => false
        end
    | _ => false
    end.

  Definition log_below_kd (kn : list kentry) (spi : nat) (ihi : Z) (log : list sentry) : bool :=
    forallb (entry_below_kd kn spi ihi) log.

  Lemma entry_below_kd_sound : forall E M0 kn spi ihi b k w v (x : word),
    know_ok segs E M0 kn ->
    entry_below_kd kn spi ihi (SE (SA b k) w v) = true ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
    (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
  Proof.
    intros E M0 kn spi ihi b k w v x HK He Hsp Hx1 Hx2.
    unfold entry_below_kd in He. apply orb_prop in He as [He|He].
    - eapply (entry_below_kb_sound segs E M0 kn spi ihi CEIL40 b k w v x); try eassumption; unfold CEIL40; lia.
    - destruct b as [z|i| | | | | |]; try discriminate.
      destruct (krange_of kn i) as [[lo hi]|] eqn:Hr; [|discriminate].
      destruct (kdisj_sp_of kn spi i) as [n|] eqn:Hd; [|discriminate].
      apply andb_prop in He as [He H4]. apply andb_prop in He as [He H3]. apply andb_prop in He as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
      pose proof (krange_of_sound segs E M0 kn i lo hi HK Hr) as Hb.
      pose proof (kdisj_sp_of_sound E M0 kn spi i n HK Hd) as Hdj. unfold BELOW48 in *.
      unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x). pose proof (u64_range (ev E spi)).
      rewrite u_small by lia. lia.
  Qed.

  Lemma mem_denot_above_kd : forall E M0 M kn log spi ihi (x : word),
    know_ok segs E M0 kn ->
    log_below_kd kn spi ihi log = true ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
    mem_denot E M log x = M x.
  Proof.
    intros E M0 M kn log spi ihi x HK Hb Hsp Hx1 Hx2.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_below_kd forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    pose proof (entry_below_kd_sound E M0 kn spi ihi b k w v x HK He Hsp Hx1 Hx2) as Hbnd.
    pose proof (u64_range x) as Hxr.
    cbn [mem_denot]. rewrite wbytes_outside.
    - apply IH. exact Hrest.
    - rewrite length_N_to_le_bytes. lia.
    - rewrite length_N_to_le_bytes. right. lia.
  Qed.
End AboveD.
