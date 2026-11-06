(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step KnownT GapsM EntM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step GapsM.GapsM EntM.EntM.
Open Scope Z_scope.

Module DecPre.

Record dctx : Type := DC { dc_ix : fidx; dc_g : list gapc }.
Definition mk_dc (fs : list fact) : dctx := let IX := mk_ix fs in DC IX (gaps_x IX fs).
Definition dc_ok (fs : list fact) (dc : dctx) : Prop := ix_ok fs (dc_ix dc) /\ dc_g dc = gaps fs.
Lemma mk_dc_ok : forall fs, dc_ok fs (mk_dc fs).
Proof. intros fs. unfold mk_dc, dc_ok. cbn [dc_ix dc_g]. split; [apply mk_ix_ok|]. apply gaps_x_eq. apply mk_ix_ok. Qed.

Section D.
Variable dc : dctx.

Definition decide_ltu_d (fs : list fact) (a b : sv) : option bool := decide_ltu_mx (dc_ix dc) (dc_g dc) fs a b.
Definition decide_eq_d (fs : list fact) (a b : sv) : option bool := decide_eq_mx (dc_ix dc) (dc_g dc) fs a b.
Definition decide_eq0_d (fs : list fact) (v : sv) : option bool :=
  match (match decide_eq0_s fs v with Some r => Some r | None => bnd_eq0_x (dc_ix dc) v end) with
  | Some r => Some r
  | None => decide_eq_d fs v (VL wzero)
  end.

Definition known_leu_d (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu_d fs b a).
Definition known_ltu_d (fs : list fact) (a b : sv) : bool := dec_true (decide_ltu_d fs a b).

Definition decide_ltu_td (fs : list fact) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_ltu (rel_facts vs fs) a b with
  | Some r => Some r
  | None => match decide_ltu (rel_facts (close_vs fs vs vs) fs) a b with
            | Some r => Some r
            | None => decide_ltu_d fs a b
            end
  end.
Definition decide_eq_td (fs : list fact) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_eq (rel_facts vs fs) a b with
  | Some r => Some r
  | None => match decide_eq (rel_facts (close_vs fs vs vs) fs) a b with
            | Some r => Some r
            | None => decide_eq_d fs a b
            end
  end.
Definition decide_eq0_td (fs : list fact) (v : sv) : option bool :=
  let vs := sv_vs v [] in
  match decide_eq0 (rel_facts vs fs) v with
  | Some r => Some r
  | None => match decide_eq0 (rel_facts (close_vs fs vs vs) fs) v with
            | Some r => Some r
            | None => decide_eq0_d fs v
            end
  end.
Definition known_ltu_td (fs : list fact) (a b : sv) : bool := dec_true (decide_ltu_td fs a b).
Definition known_leu_td (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu_td fs b a).
Definition known_eq_td (fs : list fact) (a b : sv) : bool := dec_true (decide_eq_td fs a b).
Definition known_ne_td (fs : list fact) (a b : sv) : bool := dec_false (decide_eq_td fs a b).
Definition known_nz_td (fs : list fact) (v : sv) : bool := dec_false (decide_eq0_td fs v).
Definition known_z_td (fs : list fact) (v : sv) : bool := dec_true (decide_eq0_td fs v).
End D.

Definition decide_ltu_c (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with Some r => Some r | None => bnd_ltu fs a b end.
Definition decide_ltu_fin (dc : dctx) (fs : list fact) (c : option bool) (a b : sv) : option bool :=
  match c with Some r => Some r | None => decide_ltu_Gx (dc_ix dc) (dc_g dc) fs a b end.

Section Eq.
Variable fs : list fact.
Variable dc : dctx.
Hypothesis Hdc : dc_ok fs dc.

Lemma decide_ltu_d_eq : forall a b, decide_ltu_d dc fs a b = decide_ltu fs a b.
Proof.
  intros a b. destruct Hdc as [HIX HG]. unfold decide_ltu_d. rewrite (decide_ltu_mx_eq fs _ HIX), HG. apply decide_ltu_m_eq.
Qed.
Lemma decide_eq_d_eq : forall a b, decide_eq_d dc fs a b = decide_eq fs a b.
Proof.
  intros a b. destruct Hdc as [HIX HG]. unfold decide_eq_d. rewrite (decide_eq_mx_eq fs _ HIX), HG. apply decide_eq_m_eq.
Qed.
Lemma decide_eq0_d_eq : forall v, decide_eq0_d dc fs v = decide_eq0 fs v.
Proof.
  intros v. destruct Hdc as [HIX HG]. unfold decide_eq0_d, decide_eq0, decide_eq0_b.
  rewrite (bnd_eq0_x_eq fs _ HIX). destruct (decide_eq0_s fs v); [reflexivity|]. destruct (bnd_eq0 fs v); [reflexivity|].
  apply decide_eq_d_eq.
Qed.
Lemma known_leu_d_eq : forall a b, known_leu_d dc fs a b = CtrLib.known_leu fs a b.
Proof. intros a b. unfold known_leu_d, CtrLib.known_leu. rewrite decide_ltu_d_eq. reflexivity. Qed.
Lemma decide_ltu_td_eq : forall a b, decide_ltu_td dc fs a b = KnownT.KnownT.decide_ltu_tt fs a b.
Proof. intros a b. unfold decide_ltu_td, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.tiers. rewrite decide_ltu_d_eq. reflexivity. Qed.
Lemma decide_eq_td_eq : forall a b, decide_eq_td dc fs a b = KnownT.KnownT.decide_eq_tt fs a b.
Proof. intros a b. unfold decide_eq_td, KnownT.KnownT.decide_eq_tt, KnownT.KnownT.tiers. rewrite decide_eq_d_eq. reflexivity. Qed.
Lemma decide_eq0_td_eq : forall v, decide_eq0_td dc fs v = KnownT.KnownT.decide_eq0_tt fs v.
Proof. intros v. unfold decide_eq0_td, KnownT.KnownT.decide_eq0_tt, KnownT.KnownT.tiers. rewrite decide_eq0_d_eq. reflexivity. Qed.
Lemma known_ltu_td_eq : forall a b, known_ltu_td dc fs a b = KnownT.KnownT.known_ltu_t fs a b.
Proof. intros. unfold known_ltu_td, KnownT.KnownT.known_ltu_t, KnownT.KnownT.dec_true, dec_true. rewrite decide_ltu_td_eq. reflexivity. Qed.
Lemma known_leu_td_eq : forall a b, known_leu_td dc fs a b = KnownT.KnownT.known_leu_t fs a b.
Proof. intros. unfold known_leu_td, KnownT.KnownT.known_leu_t, KnownT.KnownT.dec_false, dec_false. rewrite decide_ltu_td_eq. reflexivity. Qed.
Lemma known_eq_td_eq : forall a b, known_eq_td dc fs a b = KnownT.KnownT.known_eq_t fs a b.
Proof. intros. unfold known_eq_td, KnownT.KnownT.known_eq_t, KnownT.KnownT.dec_true, dec_true. rewrite decide_eq_td_eq. reflexivity. Qed.
Lemma known_ne_td_eq : forall a b, known_ne_td dc fs a b = KnownT.KnownT.known_ne_t fs a b.
Proof. intros. unfold known_ne_td, KnownT.KnownT.known_ne_t, KnownT.KnownT.dec_false, dec_false. rewrite decide_eq_td_eq. reflexivity. Qed.
Lemma known_nz_td_eq : forall v, known_nz_td dc fs v = KnownT.KnownT.known_nz_t fs v.
Proof. intros. unfold known_nz_td, KnownT.KnownT.known_nz_t, KnownT.KnownT.dec_false, dec_false. rewrite decide_eq0_td_eq. reflexivity. Qed.
Lemma known_z_td_eq : forall v, known_z_td dc fs v = KnownT.KnownT.known_z_t fs v.
Proof. intros. unfold known_z_td, KnownT.KnownT.known_z_t, KnownT.KnownT.dec_true, dec_true. rewrite decide_eq0_td_eq. reflexivity. Qed.
Lemma decide_ltu_fin_eq : forall a b, decide_ltu_fin dc fs (decide_ltu_c fs a b) a b = decide_ltu fs a b.
Proof.
  intros a b. destruct Hdc as [HIX HG]. unfold decide_ltu_fin, decide_ltu_c, decide_ltu.
  destruct (decide_ltu_s fs a b); [reflexivity|]. destruct (bnd_ltu fs a b); [reflexivity|].
  rewrite (decide_ltu_Gx_eq fs _ HIX), HG. reflexivity.
Qed.
End Eq.

End DecPre.
