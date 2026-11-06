(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Step Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
      | None => false
      end
  end.

#[using="Type"] Lemma ro_bytes_b_sound : forall bs A, ro_bytes_b A bs = true -> ro_bytes segs A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
  destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.

#[using="Type"] Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A bs Hinv Hb HA Hl. split.
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
    apply ro_bytes_b_sound. exact Hb.
Qed.

(* [comment removed for export] *)
Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

#[using="Type"] Lemma image_bytes_length : forall n A bs, image_bytes A n = Some bs -> length bs = n.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros A bs H; cbn in H.
  - inversion H. reflexivity.
  - destruct (seg_rom segs (wa A)); [|discriminate]. destruct (image_bytes (A + 1) n) eqn:E; [|discriminate].
    inversion H. cbn. f_equal. eapply IH. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pristine (m : word -> option byte) (lo hi : Z) : Prop :=
  (0 <= lo)%Z /\ (hi <= 2^64)%Z /\ forall i, (lo <= i < hi)%Z -> m (wa i) = None.

#[using="Type"] Lemma image_bytes_nth : forall n A bs i b,
  image_bytes A n = Some bs -> nth_error bs i = Some b -> seg_rom segs (wa (A + Z.of_nat i)) = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros A bs i b H Hn; cbn in H.
  - inversion H; subst. destruct i; discriminate.
  - destruct (seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
    destruct (image_bytes (A + 1) n) as [bs'|] eqn:E; [|discriminate].
    inversion H; subst. destruct i as [|i]; cbn in Hn.
    + inversion Hn; subst. rewrite Z.add_0_r. exact E0.
    + replace (A + Z.of_nat (S i))%Z with (A + 1 + Z.of_nat i)%Z by lia. eapply IH; eassumption.
Qed.

#[using="Type"] Lemma pristine_bytes_at : forall m lo hi A bs,
  pristine m lo hi -> image_bytes A (length bs) = Some bs ->
  (lo <= A)%Z -> (A + Z.of_nat (length bs) <= hi)%Z ->
  bytes_at segs m A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi A bs (Hlo & Hhi & Hp) Himg HA Hl. split; [lia|]. split; [lia|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
  unfold mrd. rewrite Hp by lia. eapply image_bytes_nth; eassumption.
Qed.

#[using="Type"] Lemma ro_cells_pristine : forall m lo hi A bs,
  pristine m lo hi -> image_bytes A (length bs) = Some bs ->
  (lo <= A)%Z -> (A + Z.of_nat (length bs) <= hi)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi A bs Hp Himg HA Hl. split.
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. eapply pristine_bytes_at; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pristine_read : forall m lo hi A n bs,
  pristine m lo hi -> image_bytes A n = Some bs ->
  (lo <= A)%Z -> (A + Z.of_nat n <= hi)%Z ->
  ov_read_bytes segs m (wa A) n = Some bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi A n bs Hp Himg HA Hl.
  pose proof (image_bytes_length _ _ _ Himg) as L. subst n.
  pose proof (pristine_bytes_at m lo hi A bs Hp Himg HA Hl) as B.
  rewrite <- (Z.add_0_r A). change 0%Z with (Z.of_nat 0).
  rewrite (bytes_at_ov_read segs m A bs 0 (length bs) B) by lia. cbn. rewrite firstn_all. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pristine_write_other : forall m lo hi (a : Z) bs,
  pristine m lo hi -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (hi <= a \/ a + Z.of_nat (length bs) <= lo)%Z ->
  pristine (write_to_mem m (wa a) bs) lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi a bs (Hlo & Hhi & Hp) Ha Hl Hd. split; [lia|]. split; [lia|].
  intros i Hi. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a i); destruct (Z.ltb_spec0 i (a + Z.of_nat (length bs))); cbn [andb];
    try (apply Hp; lia). exfalso. lia.
Qed.

#[using="Type"] Lemma pristine_transport : forall W m m' lo hi,
  pristine m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> pristine m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' lo hi (Hlo & Hhi & Hp) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. rewrite Hm. { apply Hp. lia. }
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact Hd| lia].
Qed.

#[using="Type"] Lemma pristine_sub : forall m lo hi lo' hi',
  pristine m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> pristine m lo' hi'.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo hi lo' hi' (A & B & C) H1 H2. split; [lia|]. split; [lia|]. intros i Hi. apply C. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.

#[using="Type"] Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1.
  f_equal; [exact H1| apply IH; exact H2].
Qed.

Fixpoint table_b (A : Z) (w : nat) (cell : Z -> list byte) (vals : list Z) : bool :=
  match vals with
  | [] => true
  | v :: vs =>
      match image_bytes A w with
      | Some bs => bytes_eqb bs (cell v) && table_b (A + Z.of_nat w) w cell vs
      | None => false
      end
  end.

#[using="Type"] Lemma table_b_nth : forall vals A w cell k v,
  table_b A w cell vals = true -> nth_error vals k = Some v ->
  image_bytes (A + Z.of_nat w * Z.of_nat k) w = Some (cell v).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction vals as [|v0 vs IH]; intros A w cell k v H Hk; [destruct k; discriminate|].
  cbn in H. destruct (image_bytes A w) as [bs|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2]. apply bytes_eqb_eq in H1. subst bs.
  destruct k as [|k]; cbn in Hk.
  - inversion Hk; subst. rewrite Z.mul_0_r, Z.add_0_r. exact E.
  - replace (A + Z.of_nat w * Z.of_nat (S k))%Z with (A + Z.of_nat w + Z.of_nat w * Z.of_nat k)%Z by lia.
    eapply IH; eassumption.
Qed.

#[using="Type"] Lemma table_read : forall cell vals A (w : nat) m lo hi,
  table_b A w cell vals = true -> pristine m lo hi ->
  (lo <= A)%Z -> (A + Z.of_nat w * Z.of_nat (length vals) <= hi)%Z ->
  forall i, (0 <= i < Z.of_nat (length vals))%Z ->
  ov_read_bytes segs m (wa (A + Z.of_nat w * i)) w = Some (cell (nth (Z.to_nat i) vals 0%Z)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cell vals A w m lo hi Ht Hp HA Hhi i Hi.
  destruct (nth_error vals (Z.to_nat i)) as [v|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  rewrite (nth_error_nth _ _ _ E).
  pose proof (table_b_nth vals A w cell (Z.to_nat i) v Ht E) as Hb. rewrite Z2Nat.id in Hb by lia.
  eapply pristine_read; [exact Hp | exact Hb | nia | nia ].
Qed.

End WithSegs.

(* [comment removed for export] *)
