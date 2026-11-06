(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Definition HS_one (HS0 : acs) (h : nat) : option acs := if Nat.eqb h 0 then Some HS0 else None.

Fixpoint hole0_shape (s : shape) : bool :=
  match s with
  | SHole h => Nat.eqb h 0
  | SCase _ _ s1 s2 => hole0_shape s1 && hole0_shape s2
  | _ => false
  end.

Section Chain.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIM : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable fs : Fs.Fs.
  Variable XN : nat -> list expr -> acs -> option acs.
  Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
  Variable XB : nat -> list expr -> acs -> option (acs * acs).
  Variable HOLES : nat -> env -> Fs.Fs -> ShapeAlg.TSet.

  Lemma sd_hole0 : forall s E fs', hole0_shape s = true -> sd HOLES t_nil E fs' s = HOLES 0%nat E fs'.
  Proof.
    induction s as [| | | | e mid s1 IH1 s2 IH2 | h |]; intros E fs' H; cbn [hole0_shape] in H; try discriminate.
    - apply andb_prop in H as [H1 H2]. cbn [sd]. destruct (_ <=? _)%Z; [apply IH1 | apply IH2]; assumption.
    - apply Nat.eqb_eq in H. subst h. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis CHECK_SOUND : forall IT, itab_sound SEGS IT ->
    forall HS, holes_stmt SEGS A LIM HS SINV argH ISP HOLES fs ->
    forall KC FUEL BFUEL p cs s,
      check SEGS IT A NX0 LIM XN XE XB HS KC BFUEL FUEL None cs p = COk s ->
      forall E R FULL model, cs_ok SEGS A LIM SINV argH ISP fs E cs R FULL model ->
        srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).

  Inductive chain : acs -> acs -> Prop :=
  | chain_nil : forall cs, chain cs cs
  | chain_cons : forall IT cs1 cs2 cs3 p s KC BFUEL FUEL,
      itab_sound SEGS IT ->
      check SEGS IT A NX0 LIM XN XE XB (HS_one cs2) KC BFUEL FUEL None cs1 p = COk s ->
      hole0_shape s = true ->
      chain cs2 cs3 -> chain cs1 cs3.

  Theorem chain_holes : forall cs1 cs3, chain cs1 cs3 ->
    holes_stmt SEGS A LIM (HS_one cs3) SINV argH ISP HOLES fs ->
    holes_stmt SEGS A LIM (HS_one cs1) SINV argH ISP HOLES fs.
  Proof.
    intros cs1 cs3 Hch. induction Hch as [cs | IT cs1 cs2 cs3 p s KC BFUEL FUEL HIT Hck Hsh Hch IH]; intros Hlast; [exact Hlast|].
    intros h ch Hh E R FULL model HC. unfold HS_one in Hh.
    destruct (Nat.eqb h 0) eqn:Hh0; [|discriminate]. apply Nat.eqb_eq in Hh0. subst h. injection Hh as <-.
    rewrite <- (sd_hole0 s E (m_fs model) Hsh).
    exact (CHECK_SOUND IT HIT (HS_one cs2) (IH Hlast) KC FUEL BFUEL p cs1 s Hck E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  Corollary chain_realizes : forall cs1 cs3, chain cs1 cs3 ->
    holes_stmt SEGS A LIM (HS_one cs3) SINV argH ISP HOLES fs ->
    forall E R FULL model, cs_ok SEGS A LIM SINV argH ISP fs E cs1 R FULL model ->
      srealizes SEGS (cfg_of SEGS R (pc cs1) FULL model) (HOLES 0%nat E (m_fs model)).
  Proof.
    intros cs1 cs3 Hch Hlast E R FULL model HC.
    exact (chain_holes cs1 cs3 Hch Hlast 0%nat cs1 eq_refl E R FULL model HC).
  Qed.
End Chain.
