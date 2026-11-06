(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition kb_leb (k k' : kb) : bool :=
  match k, k' with
  | KU, _ => true
  | KB z, KB z' => z =? z'
  | KP t o j, KP t' o' j' => (t =? t')%uint63 && w_eqb o o' && (j =? j')
  | _, _ => false
  end.

Lemma kb_leb_ok (rho : valuation) (k k' : kb) (b : byte) : kb_leb k k' = true -> kb_ok rho k' b -> kb_ok rho k b.
Proof.
  destruct k as [z|t o j|], k' as [z'|t' o' j'|]; cbn [kb_leb]; intros H Hk; try discriminate; try exact I.
  - apply Z.eqb_eq in H. subst. exact Hk.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. apply Z.eqb_eq in H3.
    rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2. subst. exact Hk.
Qed.

Section Query.
Variable segs : list Segment.

Fixpoint kb_check (rg : region) (off : Z) (ks : list kb) : bool :=
  match ks with
  | [] => true
  | k :: ks' => kb_leb k (rg_kb segs rg off) && kb_check rg (off + 1) ks'
  end.

Lemma kb_check_sound (rho : valuation) (t : int) (rg : region) (m : word -> option byte) : forall (ks : list kb) (off : Z),
  region_ok segs rho t rg m -> kb_check rg off ks = true -> 0 <= off -> off + Z.of_nat (length ks) <= to_Z (rg_size rg) ->
  exists bs, Forall2 (kb_ok rho) ks bs /\ bytes_at segs m (rbase rho t rg + off) bs
             /\ (rg_wr rg = true -> wr_at segs m (rbase rho t rg + off) (Z.of_nat (length ks))).
Proof.
  intros ks off Hok. pose proof Hok as (B0 & B1 & _ & _ & _ & _ & _ & Hby). unfold two63 in B1.
  revert off. induction ks as [|k ks IH]; intros off Hc H0 Hfit.
  - exists []. split; [constructor|]. split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]|].
    intros _. split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]].
  - cbn [kb_check] in Hc. apply andb_prop in Hc as [Hk Hc]. cbn [length] in Hfit.
    destruct (IH (off + 1) Hc ltac:(lia) ltac:(lia)) as (bs & HF & (_ & _ & Hb) & Hw).
    destruct (Hby off ltac:(lia)) as (b & Eb & Kb & Wb).
    exists (b :: bs). split; [constructor; [exact (kb_leb_ok rho _ _ b Hk Kb) | exact HF]|].
    assert (Hl : length bs = length ks) by (symmetry; exact (Forall2_length HF)).
    split.
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
      * cbn [nth_error]. rewrite Z.add_0_r. exact Eb.
      * cbn [nth_error]. rewrite <- (Hb i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
    + intros Hwr. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; exact (Wb Hwr)|].
      destruct (Hw Hwr) as (_ & _ & Hw'). specialize (Hw' (i - 1) ltac:(lia)). replace (rbase rho t rg + (off + 1) + (i - 1)) with (rbase rho t rg + off + i) in Hw' by lia. exact Hw'.
Qed.

End Query.

Definition kbs_Z (n : nat) (z : Z) : list kb := map (fun j => KB (byteZ z (Z.of_nat j))) (seq 0 n).
Definition kbs_ptr (tag : int) : list kb := map (fun j => KP tag w_zero (Z.of_nat j)) (seq 0 8).
Definition kbs_bytes (zs : list Z) : list kb := map KB zs.
Definition kbs_any (n : nat) : list kb := repeat KU n.

Lemma Forall2_kb_nth (rho : valuation) (f : nat -> kb) : forall (n s : nat) (bs : list byte),
  Forall2 (kb_ok rho) (map f (seq s n)) bs -> length bs = n /\ forall i b, nth_error bs i = Some b -> kb_ok rho (f (s + i)%nat) b.
Proof.
  induction n as [|n IH]; intros s bs H; cbn [seq map] in H; inversion H; subst.
  - split; [reflexivity|]. intros i b Hi. destruct i; discriminate.
  - destruct (IH (S s) _ H4) as [Hl Hn]. split; [cbn; lia|]. intros i b Hi. destruct i as [|i].
    + cbn in Hi. injection Hi as <-. rewrite Nat.add_0_r. assumption.
    + cbn in Hi. replace (s + S i)%nat with (S s + i)%nat by lia. exact (Hn i b Hi).
Qed.

Lemma kbs_Z_bytes (rho : valuation) (n : nat) (z : Z) (bs : list byte) : 0 <= z ->
  Forall2 (kb_ok rho) (kbs_Z n z) bs -> bs = Z_to_le_bytes n z.
Proof.
  intros Hz H. destruct (Forall2_kb_nth rho _ n 0%nat bs H) as [Hl Hn]. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite (nth_Z_to_le_bytes n z i Hz Hi). destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    f_equal. apply byte_of_eq. exact (Hn i b E).
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)); [reflexivity|]. rewrite length_Z_to_le_bytes. lia.
Qed.

Lemma kbs_ptr_bytes (rho : valuation) (tag : int) (bs : list byte) : 0 <= rho tag < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_ptr tag) bs -> bs = le8 (Z_to_bv 64 (rho tag)).
Proof.
  intros Hr H. destruct (Forall2_kb_nth rho _ 8 0%nat bs H) as [Hl Hn].
  assert (Ep : bv_unsigned (pword rho tag w_zero) = rho tag).
  { unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r, Z_to_bv_unsigned. apply bv_wrap_small. exact Hr. }
  unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hr. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
  - rewrite (nth_Z_to_le_bytes 8 (rho tag) i ltac:(lia) Hi). destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    f_equal. apply byte_of_eq. pose proof (Hn i b E) as K. cbn [kb_ok] in K. rewrite Ep in K. exact K.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)); [reflexivity|]. rewrite length_Z_to_le_bytes. lia.
Qed.

Lemma kbs_bytes_bytes (rho : valuation) : forall (zs : list Z) (bs : list byte),
  Forall2 (kb_ok rho) (kbs_bytes zs) bs -> bs = map (Z_to_bv 8) zs.
Proof.
  induction zs as [|z zs IH]; intros bs H; cbn [kbs_bytes map] in H; inversion H; subst; [reflexivity|].
  cbn [map]. f_equal; [|apply IH; assumption]. cbn [kb_ok] in H2. apply bv_eq. rewrite H2, Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. rewrite <- H2. apply bv_unsigned_in_range.
Qed.

Lemma Forall2_app_split {A B : Type} (P : A -> B -> Prop) : forall (l1 l2 : list A) (bs : list B),
  Forall2 P (l1 ++ l2) bs -> exists b1 b2, bs = b1 ++ b2 /\ Forall2 P l1 b1 /\ Forall2 P l2 b2.
Proof. intros l1 l2 bs H. apply Forall2_app_inv_l in H as (b1 & b2 & H1 & H2 & ->). exists b1, b2. auto. Qed.
