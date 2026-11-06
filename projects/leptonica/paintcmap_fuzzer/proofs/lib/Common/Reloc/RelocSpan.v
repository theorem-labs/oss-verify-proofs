(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive skind := SK_RO | SK_RELRO | SK_DATA.
Record cspan := mkSpan { sp_blk : positive; sp_kind : skind; sp_lo : Z; sp_hi : Z; sp_al : Z }.

Section Spans.
Context {RL : Reloc} {RD : RelocData RL}.

Definition span_P (s : cspan) : Prop :=
  match sp_kind s with
  | SK_RO => rl_img_lo <= sp_lo s + rl_delta (sp_blk s) /\ sp_hi s + rl_delta (sp_blk s) <= rl_rw_lo
  | SK_RELRO => rl_rw_lo <= sp_lo s + rl_delta (sp_blk s) /\ sp_hi s + rl_delta (sp_blk s) <= rl_data_lo
  | SK_DATA => rl_data_lo <= sp_lo s + rl_delta (sp_blk s) /\ sp_hi s + rl_delta (sp_blk s) <= rl_img_hi
  end /\ rl_delta (sp_blk s) mod sp_al s = 0.

Definition span_okb (s : cspan) : bool :=
  match sp_kind s with
  | SK_RO => (rl_img_lo <=? sp_lo s + rl_delta (sp_blk s)) && (sp_hi s + rl_delta (sp_blk s) <=? rl_rw_lo)
  | SK_RELRO => (rl_rw_lo <=? sp_lo s + rl_delta (sp_blk s)) && (sp_hi s + rl_delta (sp_blk s) <=? rl_data_lo)
  | SK_DATA => (rl_data_lo <=? sp_lo s + rl_delta (sp_blk s)) && (sp_hi s + rl_delta (sp_blk s) <=? rl_img_hi)
  end && (rl_delta (sp_blk s) mod sp_al s =? 0).

Definition spans_check (tbl : list cspan) : bool := forallb span_okb tbl.

Fixpoint span_find (tbl : list cspan) (b : positive) : option cspan :=
  match tbl with
  | [] => None
  | s :: t => if Pos.eqb (sp_blk s) b then Some s else span_find t b
  end.

Lemma span_find_In : forall tbl b s, span_find tbl b = Some s -> In s tbl.
Proof.
  induction tbl as [|x t IH]; intros b s H; cbn [span_find] in H; [discriminate|].
  destruct (Pos.eqb (sp_blk x) b); [inversion H; subst; left; reflexivity | right; eapply IH; exact H].
Qed.

Lemma span_fact : forall tbl, spans_check tbl = true -> forall b s, span_find tbl b = Some s -> span_P s.
Proof.
  intros tbl Hok b s Hf. unfold spans_check in Hok. rewrite forallb_forall in Hok.
  specialize (Hok s (span_find_In _ _ _ Hf)). unfold span_okb in Hok. unfold span_P.
  apply andb_prop in Hok as [H1 H2]. apply Z.eqb_eq in H2. split; [|exact H2].
  destruct (sp_kind s); apply andb_prop in H1 as [Ha Hb]; apply Z.leb_le in Ha; apply Z.leb_le in Hb; auto.
Qed.

(* [comment removed for export] *)
Definition order_okb (tbl : list cspan) (p : positive * positive) : bool :=
  match span_find tbl (fst p), span_find tbl (snd p) with
  | Some s1, Some s2 => sp_hi s1 + rl_delta (fst p) <=? sp_lo s2 + rl_delta (snd p)
  | _, _ => false
  end.
Definition orders_check (tbl : list cspan) (ord : list (positive * positive)) : bool := forallb (order_okb tbl) ord.

Definition skind_eqb (a b : skind) : bool :=
  match a, b with SK_RO, SK_RO | SK_RELRO, SK_RELRO | SK_DATA, SK_DATA => true | _, _ => false end.

Definition pair_inb (ord : list (positive * positive)) (b1 b2 : positive) : bool :=
  existsb (fun p => Pos.eqb (fst p) b1 && Pos.eqb (snd p) b2) ord.

(* [comment removed for export] *)
Definition xblk_apartb (tbl : list cspan) (ord : list (positive * positive)) (b1 b2 : positive) (ca : Z) (n : nat) (cb : Z) (len : nat) : bool :=
  match span_find tbl b1, span_find tbl b2 with
  | Some s1, Some s2 =>
      (sp_lo s1 <=? ca) && (ca + Z.of_nat n <=? sp_hi s1) && (sp_lo s2 <=? cb) && (cb + Z.of_nat len <=? sp_hi s2)
      && (negb (skind_eqb (sp_kind s1) (sp_kind s2)) || pair_inb ord b1 b2 || pair_inb ord b2 b1)
  | _, _ => false
  end.

Definition hull_okb : bool :=
  (2^16 <=? rl_img_lo) && (rl_img_lo <=? rl_rw_lo) && (rl_rw_lo <=? rl_data_lo) && (rl_data_lo <=? rl_img_hi) && (rl_img_hi <=? 2^31)
  && (rl_img_hi mod 8 =? 0).

Lemma hull_fact : hull_okb = true ->
  2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo /\ rl_data_lo <= rl_img_hi /\ rl_img_hi <= 2^31 /\ rl_img_hi mod 8 = 0.
Proof.
  intros H. unfold hull_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.eqb_eq in H6.
  auto 10.
Qed.
Lemma xblk_apart : forall tbl ord, spans_check tbl = true -> orders_check tbl ord = true -> hull_okb = true ->
  forall b1 b2 ca n cb len, xblk_apartb tbl ord b1 b2 ca n cb len = true ->
  0 <= ca + rl_delta b1 /\ ca + rl_delta b1 + Z.of_nat n <= 2^31 /\ 0 <= cb + rl_delta b2 /\ cb + rl_delta b2 + Z.of_nat len <= 2^31 /\
  (ca + rl_delta b1 + Z.of_nat n <= cb + rl_delta b2 \/ cb + rl_delta b2 + Z.of_nat len <= ca + rl_delta b1).
Proof.
  intros tbl ord Hsp Hord Hhull b1 b2 ca n cb len H. unfold xblk_apartb in H.
  destruct (span_find tbl b1) as [s1|] eqn:F1; [|discriminate H]. destruct (span_find tbl b2) as [s2|] eqn:F2; [|discriminate H].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  pose proof (span_fact tbl Hsp b1 s1 F1) as [P1 _]. pose proof (span_fact tbl Hsp b2 s2 F2) as [P2 _].
  assert (B1 : sp_blk s1 = b1).
  { clear -F1. induction tbl as [|x t IH]; cbn [span_find] in F1; [discriminate|]. destruct (Pos.eqb (sp_blk x) b1) eqn:E; [inversion F1; subst; apply Pos.eqb_eq; exact E | exact (IH F1)]. }
  assert (B2 : sp_blk s2 = b2).
  { clear -F2. induction tbl as [|x t IH]; cbn [span_find] in F2; [discriminate|]. destruct (Pos.eqb (sp_blk x) b2) eqn:E; [inversion F2; subst; apply Pos.eqb_eq; exact E | exact (IH F2)]. }
  rewrite B1 in P1. rewrite B2 in P2.
  pose proof (Zle_0_nat n) as Hn0. pose proof (Zle_0_nat len) as Hl0.
  assert (HH : 2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo /\ rl_data_lo <= rl_img_hi /\ rl_img_hi <= 2^31 /\ rl_img_hi mod 8 = 0)
    by (apply hull_fact; exact Hhull).
  destruct HH as (G1 & G2 & G3 & G4 & G5 & _).
  apply Bool.orb_prop in Hk as [Hk|Hk]; [apply Bool.orb_prop in Hk as [Hk|Hk]|].
  - (* [comment removed for export] *)
    destruct (sp_kind s1), (sp_kind s2); cbn [skind_eqb negb] in Hk; try discriminate Hk; lia.
  - (* [comment removed for export] *)
    unfold pair_inb in Hk. apply existsb_exists in Hk as (p & Hin & Hp). apply andb_prop in Hp as [E1 E2].
    apply Pos.eqb_eq in E1. apply Pos.eqb_eq in E2.
    unfold orders_check in Hord. rewrite forallb_forall in Hord. specialize (Hord p Hin). unfold order_okb in Hord.
    rewrite E1, E2, F1, F2 in Hord. apply Z.leb_le in Hord.
    destruct (sp_kind s1), (sp_kind s2); lia.
  - (* [comment removed for export] *)
    unfold pair_inb in Hk. apply existsb_exists in Hk as (p & Hin & Hp). apply andb_prop in Hp as [E1 E2].
    apply Pos.eqb_eq in E1. apply Pos.eqb_eq in E2.
    unfold orders_check in Hord. rewrite forallb_forall in Hord. specialize (Hord p Hin). unfold order_okb in Hord.
    rewrite E1, E2, F2, F1 in Hord. apply Z.leb_le in Hord.
    destruct (sp_kind s1), (sp_kind s2); lia.
Qed.

(* [comment removed for export] *)
Lemma order_fact : forall tbl ord, orders_check tbl ord = true -> forall b1 b2 s1 s2,
  pair_inb ord b1 b2 = true -> span_find tbl b1 = Some s1 -> span_find tbl b2 = Some s2 ->
  sp_hi s1 + rl_delta b1 <= sp_lo s2 + rl_delta b2.
Proof.
  intros tbl ord Hord b1 b2 s1 s2 Hk F1 F2.
  unfold pair_inb in Hk. apply existsb_exists in Hk as (p & Hin & Hp). apply andb_prop in Hp as [E1 E2].
  apply Pos.eqb_eq in E1. apply Pos.eqb_eq in E2.
  unfold orders_check in Hord. rewrite forallb_forall in Hord. specialize (Hord p Hin). unfold order_okb in Hord.
  rewrite E1, E2, F1, F2 in Hord. apply Z.leb_le in Hord. exact Hord.
Qed.

End Spans.
