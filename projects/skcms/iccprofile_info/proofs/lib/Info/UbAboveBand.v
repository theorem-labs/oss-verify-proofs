(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec StoreOk MmapSim SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit SymDriveX SymAbove.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section Band.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Fixpoint band_of (kn : list kentry) (spi i : nat) : option Z :=
    match kn with
    | [] => None
    | KDisj (SA (EVar s) d) n1 (SA (EVar j) 0) n2 :: rest =>
        if Nat.eqb s spi && Nat.eqb j i && Z.eqb d (-8388608) && Z.eqb n1 0x800000000000
        then Some n2 else band_of rest spi i
    | _ :: rest => band_of rest spi i
    end.

  Lemma band_of_sound : forall E M kn spi i n,
    know_ok segs E M kn -> band_of kn spi i = Some n ->
    (bv_unsigned (ev E spi) - 8388608 + 0x800000000000 <= bv_unsigned (ev E i)
     \/ bv_unsigned (ev E i) + n <= bv_unsigned (ev E spi) - 8388608)%Z.
  Proof.
    intros E M kn spi i n HK. induction kn as [|K rest IH]; intros H; [discriminate|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    cbn [band_of] in H.
    destruct K as [| | | | | | |a1 n1 a2 n2]; try (apply IH; assumption).
    destruct a1 as [b1 d1]. destruct a2 as [b2 d2].
    destruct b1 as [|s| | | | | |]; try (apply IH; assumption).
    destruct b2 as [|j| | | | | |]; try (apply IH; assumption).
    destruct d2 as [|p|p]; try (apply IH; assumption).
    destruct (Nat.eqb s spi && Nat.eqb j i && Z.eqb d1 (-8388608) && Z.eqb n1 0x800000000000) eqn:Hc.
    - injection H as <-. repeat (apply andb_prop in Hc as [Hc ?]).
      apply Nat.eqb_eq in Hc. match goal with H : Nat.eqb j i = true |- _ => apply Nat.eqb_eq in H end.
      repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end. subst.
      cbn [kentry_ok] in HK1. unfold estart in HK1. cbn [a_base a_off edenot] in HK1. lia.
    - apply IH; assumption.
  Qed.

  Definition entry_below_band (kn : list kentry) (spi : nat) (ihi ceil : Z) (e : sentry) : bool :=
    entry_below_kb kn spi ihi ceil e ||
    match e with
    | SE (SA (EVar i) k) w _ =>
        match band_of kn spi i, krange_of kn i with
        | Some n, Some (lo, hi) => Z.leb 0 k && Z.leb (k + Z.of_nat w) n && Z.leb 0 lo && Z.leb hi 0x800000000000
        | _, _ => false
        end
    | _ => false
    end.

  Definition log_below_band (kn : list kentry) (spi : nat) (ihi ceil : Z) (log : list sentry) : bool :=
    forallb (entry_below_band kn spi ihi ceil) log.

  Lemma entry_below_band_sound : forall E M0 kn spi ihi ceil b k w v (x : word),
    know_ok segs E M0 kn ->
    entry_below_band kn spi ihi ceil (SE (SA b k) w v) = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
  Proof.
    intros E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3.
    unfold entry_below_band in He. apply orb_prop in He as [He|He].
    - eapply entry_below_kb_sound; eassumption.
    - destruct b as [z|i| | | | | |]; try discriminate.
      destruct (band_of kn spi i) as [n|] eqn:Hb; [|discriminate].
      destruct (krange_of kn i) as [[lo hi]|] eqn:Hr; [|discriminate].
      repeat (apply andb_prop in He as [He ?]). apply Z.leb_le in He.
      repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end.
      pose proof (krange_of_sound segs E M0 kn i lo hi HK Hr) as Hrg.
      pose proof (band_of_sound E M0 kn spi i n HK Hb) as Hbd.
      unfold adenot, v_addi. cbn [a_base a_off edenot]. pose proof (u64_range x).
      rewrite u_small by lia. lia.
  Qed.

  Lemma mem_denot_above_band : forall E M0 M kn log spi ihi ceil (x : word),
    know_ok segs E M0 kn ->
    log_below_band kn spi ihi ceil log = true ->
    (ceil <= 2 ^ 64)%Z ->
    (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
    (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z -> (ceil <= bv_unsigned x)%Z ->
    mem_denot E M log x = M x.
  Proof.
    intros E M0 M kn log spi ihi ceil x HK Hb Hc Hsp Hx1 Hx2 Hx3.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_below_band forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    pose proof (entry_below_band_sound E M0 kn spi ihi ceil b k w v x HK He Hc Hsp Hx1 Hx2 Hx3) as Hbnd.
    pose proof (u64_range x) as Hxr.
    cbn [mem_denot]. rewrite wbytes_outside.
    - apply IH. exact Hrest.
    - rewrite length_N_to_le_bytes. lia.
    - rewrite length_N_to_le_bytes. right. lia.
  Qed.
End Band.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
