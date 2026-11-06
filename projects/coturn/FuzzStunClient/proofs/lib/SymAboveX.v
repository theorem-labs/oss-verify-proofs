(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk MmapSim SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MemSplit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveX SymAbove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AboveX.
  Variable segs : list Segment.

  Fixpoint kdisj_of (kn : list kentry) (spi i : nat) : option (Z * Z * Z) :=
    match kn with
    | [] => None
    | KDisj (SA (EVar s) d) D (SA (EVar j) 0) n :: rest =>
        if Nat.eqb s spi && Nat.eqb j i then Some (d, D, n) else kdisj_of rest spi i
    | _ :: rest => kdisj_of rest spi i
    end.

  Lemma kdisj_of_sound : forall E M kn spi i d D n,
    know_ok segs E M kn -> kdisj_of kn spi i = Some (d, D, n) ->
    (bv_unsigned (ev E spi) + d + D <= bv_unsigned (ev E i) \/ bv_unsigned (ev E i) + n <= bv_unsigned (ev E spi) + d)%Z.
  Proof.
    intros E M kn spi i d D n HK. induction kn as [|K rest IH]; intros H; [discriminate|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    cbn [kdisj_of] in H.
    destruct K as [| | | | | | |[b1 k1] D1 [b2 k2] n2]; try (apply IH; assumption).
    destruct b1 as [|s| | | | | |]; try (apply IH; assumption).
    destruct b2 as [|j| | | | | |]; try (apply IH; assumption).
    destruct k2 as [|p|p]; try (apply IH; assumption).
    destruct (Nat.eqb_spec s spi); destruct (Nat.eqb_spec j i); cbn [andb] in H; try (apply IH; assumption).
    injection H as <- <- <-. subst s j. cbn [kentry_ok] in HK1. unfold estart in HK1. cbn [a_base a_off edenot] in HK1. lia.
  Qed.

  Definition entry_below_kbx (kn : list kentry) (spi : nat) (ihi ceil : Z) (e : sentry) : bool :=
    entry_below_kb kn spi ihi ceil e ||
    match e with
    | SE (SA (EVar i) k) w _ =>
        match kdisj_of kn spi i, krange_of kn i with
        | Some (d, D, n), Some (lo, hi) =>
            Z.ltb 0 n && Z.leb 0 k && Z.leb (k + Z.of_nat w) n && Z.leb d 0 && Z.leb (2 ^ 31) (d + D)
            && Z.leb 0 lo && Z.leb (hi + n) (2 ^ 47)
        | _, _ => false
        end
    | _ => false
    end.

  Definition log_below_kbx (kn : list kentry) (spi : nat) (ihi ceil : Z) (log : list sentry) : bool :=
    forallb (entry_below_kbx kn spi ihi ceil) log.

  Lemma entry_below_kbx_sound : forall E M0 kn spi ihi ceil b k w v (x : word),
    know_ok segs E M0 kn ->
    entry_below_kbx kn spi ihi ceil (SE (SA b k) w v) = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 47 - 2 ^ 31 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
  Proof.
    intros E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3.
    unfold entry_below_kbx in He. apply orb_prop in He as [He|He].
    - eapply entry_below_kb_sound; try eassumption. lia.
    - destruct b as [z|i| | | | | |]; try discriminate.
      destruct (kdisj_of kn spi i) as [[[d D] n]|] eqn:Hd; [|discriminate].
      destruct (krange_of kn i) as [[lo hi]|] eqn:Hr; [|discriminate].
      repeat (apply andb_prop in He as [He ?H]). apply Z.ltb_lt in He.
      repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
      pose proof (krange_of_sound segs E M0 kn i lo hi HK Hr) as Hb.
      pose proof (kdisj_of_sound E M0 kn spi i d D n HK Hd) as Hdj.
      unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x).
      rewrite u_small by lia. lia.
  Qed.

  Lemma mem_denot_above_kbx : forall E M0 M kn log spi ihi ceil (x : word),
    know_ok segs E M0 kn ->
    log_below_kbx kn spi ihi ceil log = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 47 - 2 ^ 31 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    mem_denot E M log x = M x.
  Proof.
    intros E M0 M kn log spi ihi ceil x HK Hb Hc Hsp Hx1 Hx2 Hx3.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_below_kbx forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    pose proof (entry_below_kbx_sound E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3) as Hbnd.
    pose proof (u64_range x) as Hxr.
    cbn [mem_denot]. rewrite wbytes_outside.
    - apply IH. exact Hrest.
    - rewrite length_N_to_le_bytes. lia.
    - rewrite length_N_to_le_bytes. right. lia.
  Qed.
End AboveX.
