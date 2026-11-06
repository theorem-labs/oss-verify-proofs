(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "nat"; "S"; "bool"; "list"; "app"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring.Ring"; "iter"; "live"; "ring_ok"; "chain"; "findex"; "fupd"; "@Corelib.Init.Peano"; "lt"; "le"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "eqb"; "modulo"; "of_nat"; "sub"; "to_nat"; "@Corelib.Init.Nat"; "sub"; "add"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "nth"; "skipn"; "@Stdlib.Lists.List"; "In"; "NoDup"; "@Stdlib.Arith.PeanoNat.Nat"; "modulo"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Ring.
Implicit Types (nx pv : Z -> Z).

Fixpoint iter nx (k : nat) (x : Z) : Z :=
  match k with O => x | S k' => iter nx k' (nx x) end.

Fixpoint chain nx (x : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => x :: chain nx (nx x) k' end.

Lemma nth_map_lt' : forall {A B} (f : A -> B) (l : list A) i (d : A) (d' : B),
  (i < length l)%nat -> nth i (map f l) d' = f (nth i l d).
Proof.
  intros A B f l. induction l as [|x t IH]; intros i d d' Hi; cbn in Hi; [lia|].
  destruct i; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma iter_S : ltac2:(tb__ "0|0|
S0S0F_;S1S0S7S0ScR3S2R2A1R1A3R3ScR3R2R1A3A1A3Fx;Fk;Fnx;").
Proof. intros nx k. induction k as [|k IH]; intros x; cbn; [reflexivity|]. rewrite <- IH. reflexivity. Qed.

Lemma iter_add : ltac2:(tb__ "0|0|
S0S0F_;S1S1S0S7S0ScR4S1dR3R2A2R1A3ScR4R2ScR4R3R1A3A3A3Fx;Fb;Fa;Fnx;").
Proof. intros nx a. induction a as [|a IH]; intros b x; cbn; [reflexivity|]. apply IH. Qed.

Lemma chain_length : ltac2:(tb__ "0|0|
S0S0F_;S0S1S7S1S6S0SfR3R2R1A3A2R1A3Fk;Fx;Fnx;").
Proof. intros nx x k. revert x. induction k; intros; cbn; auto. Qed.

Lemma chain_nth : ltac2:(tb__ "0|0|
S0S0F_;S0S1S1S0S12R2R3A2S7S0S20S0R3SfR6R5R4A3R2A4ScR6R3R5A3A3F_;Fd;Fj;Fk;Fx;Fnx;").
Proof.
  intros nx x k. revert x. induction k as [|k IH]; intros x j d Hj; [lia|].
  destruct j as [|j]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma chain_In : ltac2:(tb__ "0|0|
S0S0F_;S0S1S0SaS22S0R1SfR4R3R2A3A3SbS1S1S8S12R1R3A2S7S0R2ScR5R1R4A3A3A2Lj;A2A2Fy;Fk;Fx;Fnx;").
Proof.
  intros nx x k y. split.
  - intros H. apply In_nth with (d := 0) in H as (j & Hj & <-). rewrite chain_length in Hj.
    exists j. split; [exact Hj|]. apply chain_nth. exact Hj.
  - intros (j & Hj & ->). rewrite <- (chain_nth nx x k j 0 Hj). apply nth_In. rewrite chain_length. exact Hj.
Qed.

Lemma chain_app : ltac2:(tb__ "0|0|
S0S0F_;S0S1S1S7S4S0A1SfR4R3S1dR2R1A2A3S5S0SfR4R3R2A3SfR4ScR4R2R3A3R1A3A3A3Fb;Fa;Fx;Fnx;").
Proof. intros nx x a. revert x. induction a as [|a IH]; intros x b; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma chain_ext : ltac2:(tb__ "0|2|
S0S0F_;M0G0S0S1S1S12S2R1A1R2A2S7S0R5ScR6R2R4A3M1A1R6G1A1A3F_;Fj;S7S4S0A1SfR4R3R2A3SfR5R3R2A3A3F_;Fk;Fx;Fnx';Fnx;").
Proof.
  intros nx nx' x k. revert x. induction k as [|k IH]; intros x H; cbn; [reflexivity|].
  f_equal. destruct k as [|k]; [reflexivity|].
  pose proof (H 0%nat ltac:(lia)) as H0. cbn in H0. rewrite H0. apply IH. intros j Hj.
  specialize (H (S j) ltac:(lia)). cbn in H. exact H.
Qed.

Lemma iter_ext : ltac2:(tb__ "0|2|
S0S0F_;M0G0S0S1S1S12R1R2A2S7S0R5ScR6R2R4A3M1A1R6G1A1A3F_;Fj;S7S0ScR4R2R3A3ScR5R2R3A3A3F_;Fk;Fx;Fnx';Fnx;").
Proof.
  intros nx nx' x k. revert x. induction k as [|k IH]; intros x H; cbn; [reflexivity|].
  pose proof (H 0%nat ltac:(lia)) as H0. cbn in H0. rewrite H0. apply IH. intros j Hj. specialize (H (S j) ltac:(lia)). cbn in H. exact H.
Qed.

Definition ring_ok (n : Z) (R : nat) (cur : Z) nx pv : Prop := ltac2:(tb__ "0|1|
S8S13U1VR;A2S8S23S0SfVnx;Vcur;VR;A3M0A2S8S1eS0S0S8S15Z0R1A2S14R1Vn;A2A2Lx;G0A3S8S7S0ScVnx;VR;Vcur;A3Vcur;A3S1eS0S0S7S0Vpv;Vnx;R1A1A1R1A3Lx;G0A3A2A2A2A2").

Definition live (R : nat) (cur : Z) nx (x : Z) : Prop := ltac2:(tb__ "0|0|
S22S0Vx;SfVnx;Vcur;VR;A3A3").

Lemma iter_mod : ltac2:(tb__ "0|0|
S0S0F_;S1S0S1S7S0ScR4R3R2A3R2A3S12U0R4A2S7S0ScR6R3R4A3ScR6S24R3R5A2R4A3A3F_;F_;Fj;Fcur;FR;Fnx;").
Proof.
  intros nx R cur j Hcyc HR.
  rewrite (Nat.div_mod_eq j R) at 1.
  induction (j / R)%nat as [|q IH].
  - rewrite Nat.mul_0_r, Nat.add_0_l. reflexivity.
  - replace (R * S q + j mod R)%nat with (R + (R * q + j mod R))%nat by lia.
    rewrite iter_add, Hcyc. exact IH.
Qed.

Lemma live_iter : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S1SeR6R5R4R3R2A5SdR6R5R4ScR4R2R5A3A4F_;Fj;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv j (HR & _ & _ & Hcyc & _). unfold live. rewrite chain_In.
  exists (j mod R)%nat. split; [apply Nat.mod_upper_bound; lia|]. apply iter_mod; [exact Hcyc|lia].
Qed.

Lemma live_lt : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5SdR6R5R4R2A4S8S15Z0R3A2S14R3R8A2A2F_;F_;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof. intros n R cur nx pv x (_ & _ & Hb & _) Hx. exact (proj1 (Forall_forall _ _) Hb x Hx). Qed.

Lemma live_cur : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0SeR5R4R3R2R1A5SdR5R4R3R4A4F_;Fpv;Fnx;Fcur;FR;Fn;").
Proof. intros. apply (live_iter n R cur nx pv 0). assumption. Qed.

Lemma live_nx : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5SdR6R5R4R2A4SdR7R6R5R5R3A1A4F_;F_;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv x HR Hx. pose proof Hx as Hx0. unfold live in Hx. rewrite chain_In in Hx.
  destruct Hx as (j & Hj & ->). rewrite <- iter_S. eapply live_iter. exact HR.
Qed.

Lemma pv_nx : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5SdR6R5R4R2A4S7S0R4R5R3A1A1R3A3F_;F_;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof. intros n R cur nx pv x (_ & _ & _ & _ & Hp) Hx. exact (proj1 (Forall_forall _ _) Hp x Hx). Qed.

Lemma live_pv : ltac2:(tb__ "0|2|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5SdR6R5R4R2A4S8SdR7R6R5R4R3A1M1A4S7S0R5G1A1R3A3A2F_;F_;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv x HR Hx. pose proof HR as (HR1 & _ & _ & Hcyc & _).
  unfold live in Hx. rewrite chain_In in Hx. destruct Hx as (j & Hj & ->).
  assert (E : iter nx j cur = nx (iter nx (j + (R - 1)) cur)).
  { rewrite <- iter_S. replace (S (j + (R - 1))) with (R + j)%nat by lia. rewrite iter_add, Hcyc. reflexivity. }
  rewrite E. rewrite (pv_nx n R cur nx pv); [| exact HR | eapply live_iter; exact HR].
  split; [eapply live_iter; exact HR | reflexivity].
Qed.

Lemma pv_cur : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0SeR5R4R3R2R1A5S7S0R2R4A1ScR3S1cR5U1A2R4A3A3F_;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv HR. pose proof HR as (HR1 & _ & _ & Hcyc & _).
  transitivity (pv (nx (iter nx (R - 1) cur))).
  - rewrite <- iter_S. replace (S (R - 1)) with R by lia. rewrite Hcyc. reflexivity.
  - eapply pv_nx; [exact HR|]. eapply live_iter; exact HR.
Qed.

Lemma nx_inj : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0S0SeR7R6R5R4R3A5SdR7R6R5R3A4SdR8R7R6R3A4S7S0R7R5A1R7R4A1A3S7S0R6R5A3F_;F_;F_;F_;Fy;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv x y HR Hx Hy E.
  rewrite <- (pv_nx n R cur nx pv x HR Hx), <- (pv_nx n R cur nx pv y HR Hy), E. reflexivity.
Qed.

Lemma chain_rotate : ltac2:(tb__ "0|1|
S0S0F_;S1S0S1S7S0ScR4R3R2A3R2A3S13R2R4A2S7S4S0A1SfR6ScR6R3R4A3R5A3S5S0S21S0R3SfR6R4R5A3M0A3S1fS0R3G0A3A3A3F_;F_;Fj;Fcur;FR;Fnx;").
Proof.
  intros nx R cur j Hcyc Hj.
  replace (chain nx cur R) with (chain nx cur (j + (R - j))) by (f_equal; lia).
  rewrite chain_app. rewrite skipn_app, firstn_app, chain_length, skipn_all2 by (rewrite chain_length; lia).
  rewrite firstn_all2 by (rewrite chain_length; lia). replace (j - j)%nat with 0%nat by lia. cbn [skipn firstn app].
  rewrite app_nil_r.
  replace R with ((R - j) + j)%nat at 1 by lia. rewrite chain_app. f_equal.
  rewrite <- iter_add. replace (j + (R - j))%nat with R by lia. rewrite Hcyc. reflexivity.
Qed.

Lemma NoDup_app_comm : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  intros A l1 l2 H. apply NoDup_app.
  - apply NoDup_app_remove_l in H. exact H.
  - apply NoDup_app_remove_r in H. exact H.
  - intros a Ha2 Ha1. apply In_split in Ha1 as (u & v & ->).
    rewrite <- app_assoc in H. cbn in H. apply NoDup_remove_2 in H. apply H. apply in_or_app. right. apply in_or_app. right. exact Ha2.
Qed.

Lemma ring_rotate : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5SdR6R5R4R2A4SeR8R7R3R5R4A5F_;F_;Fy;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv y HR Hy. pose proof HR as (HR1 & Hnd & Hb & Hcyc & Hp).
  unfold live in Hy. rewrite chain_In in Hy. destruct Hy as (j & Hj & ->).
  pose proof (chain_rotate nx R cur j Hcyc ltac:(lia)) as ROT.
  assert (SAME : forall x, In x (chain nx (iter nx j cur) R) <-> In x (chain nx cur R)).
  { intros x. rewrite ROT, in_app_iff. rewrite <- (firstn_skipn j (chain nx cur R)) at 3. rewrite in_app_iff. tauto. }
  split; [exact HR1|]. split.
  { rewrite ROT. apply NoDup_app_comm. rewrite firstn_skipn. exact Hnd. }
  split. { apply Forall_forall. intros x Hx. apply SAME in Hx. exact (proj1 (Forall_forall _ _) Hb x Hx). }
  split. { rewrite <- iter_add, Nat.add_comm, iter_add, Hcyc. reflexivity. }
  apply Forall_forall. intros x Hx. apply SAME in Hx. exact (proj1 (Forall_forall _ _) Hp x Hx).
Qed.

Lemma live_rotate : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0S0SeR7R6R5R4R3A5SdR7R6R5R3A4SaSdR8R4R6R3A4SdR8R7R6R3A4A2F_;F_;Fx;Fy;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv y x HR Hy. pose proof HR as (HR1 & Hnd & Hb & Hcyc & Hp).
  unfold live in Hy. rewrite chain_In in Hy. destruct Hy as (j & Hj & ->).
  pose proof (chain_rotate nx R cur j Hcyc ltac:(lia)) as ROT. unfold live.
  rewrite ROT, in_app_iff. rewrite <- (firstn_skipn j (chain nx cur R)) at 3. rewrite in_app_iff. tauto.
Qed.

Lemma ring_full : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S0SeR6R5R4R3R2A5S7S0S19R6A1R7A3S8S15Z0R3A2S14R3R8A2A2SdR8R7R6R4A4F_;F_;F_;Fx;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv x (HR1 & Hnd & Hb & _ & _) HRn Hx. unfold live.
  set (all := map Z.of_nat (seq 0 R)).
  assert (Hincl : incl (chain nx cur R) all).
  { intros y Hy. pose proof (proj1 (Forall_forall _ _) Hb y Hy) as Hy2. cbn beta in Hy2. unfold all.
    apply in_map_iff. exists (Z.to_nat y). split; [lia|]. apply in_seq. lia. }
  assert (Hlen : (length all <= length (chain nx cur R))%nat).
  { unfold all. rewrite length_map, length_seq, chain_length. lia. }
  pose proof (NoDup_length_incl Hnd Hlen Hincl) as Hback.
  apply Hback. unfold all. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Fixpoint findex nx (x y : Z) (k : nat) : nat :=
  match k with
  | O => O
  | S k' => if x =? y then O else S (findex nx (nx x) y k')
  end.

Lemma findex_S : ltac2:(tb__ "0|0|
S0S0F_;S0S0S1S7S1S10R4R3R2S2R1A1A4S3S1L_;S17R3R2A2U0S2S10R4R4R3A1R2R1A4A1X3x2A3Fk;Fy;Fx;Fnx;").
Proof. reflexivity. Qed.

Lemma findex_le_fuel : ltac2:(tb__ "0|0|
S0S0F_;S0S0S1S13S10R4R3R2R1A4R1A2Fk;Fy;Fx;Fnx;").
Proof. intros nx x y k. revert x. induction k as [|k IH]; intros x; cbn; [lia|]. destruct (x =? y); [lia|]. specialize (IH (nx x)). lia. Qed.

Lemma findex_le : ltac2:(tb__ "0|0|
S0S0F_;S0S0S1S1S12R1R2A2S7S0ScR6R2R5A3R4A3S13S10R7R6R5R4A4R3A2F_;F_;Fj;Fk;Fy;Fx;Fnx;").
Proof.
  intros nx x y k. revert x. induction k as [|k IH]; intros x j Hj Hit; [lia|].
  cbn. destruct (Z.eqb_spec x y); [lia|]. destruct j as [|j]; [cbn in Hit; congruence|].
  cbn in Hit. specialize (IH (nx x) j ltac:(lia) Hit). lia.
Qed.

Lemma findex_hit : ltac2:(tb__ "0|0|
S0S0F_;S0S0S1S1S12R1R2A2S7S0ScR6R2R5A3R4A3S7S0ScR7S10R7R6R5R4A4R6A3R5A3F_;F_;Fj;Fk;Fy;Fx;Fnx;").
Proof.
  intros nx x y k. revert x. induction k as [|k IH]; intros x j Hj Hit; [lia|].
  cbn. destruct (Z.eqb_spec x y); [cbn; congruence|]. destruct j as [|j]; [cbn in Hit; congruence|].
  cbn in Hit |- *. eapply IH; [|exact Hit]. lia.
Qed.

Lemma findex_step : ltac2:(tb__ "0|2|
S0S1S0S0S0F_;M0G0S0S0SeR7R6R5R4R3A5SdR7R6R5R3A4SdR8R7R6R3A4S9S7S0R5R4A3A1S8S12S10R8R8R6A1R5RaA4S10R8R6R5RaA4M1A2S12G1RaA2A2F_;F_;F_;F_;Fb;Fa;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv a b HR Ha Hb Hab.
  pose proof (ring_rotate n R cur nx pv a HR Ha) as HRa.
  assert (Hb' : live R a nx b).
  { pose proof HRa as (_ & _ & _ & Hcyca & _). pose proof HR as (_ & _ & _ & Hcyc & _).
    unfold live in Ha, Hb |- *. rewrite chain_In in Ha, Hb. destruct Ha as (i & Hi & ->). destruct Hb as (j & Hj & ->).
    rewrite chain_In. exists ((j + (R - i)) mod R)%nat. split; [apply Nat.mod_upper_bound; lia|].
    rewrite <- (iter_mod nx R (iter nx i cur)); [|exact Hcyca|lia].
    rewrite <- iter_add. replace (i + (j + (R - i)))%nat with (R + j)%nat by lia. rewrite iter_add, Hcyc. reflexivity. }
  unfold live in Hb'. rewrite chain_In in Hb'. destruct Hb' as (j & Hj & Eb).
  destruct j as [|j]; [cbn in Eb; congruence|]. cbn in Eb.
  destruct R as [|R']; [lia|].

  assert (GEN : forall k x, (forall j, (j < k)%nat -> iter nx j x = b -> findex nx x b (S k) = findex nx x b k)).
  { induction k as [|k IH]; intros x j0 Hj0 Hit; [lia|].
    rewrite (findex_S nx x b (S k)), (findex_S nx x b k). destruct (Z.eqb_spec x b); [reflexivity|].
    destruct j0 as [|j0]; [cbn in Hit; congruence|]. cbn in Hit.
    rewrite (IH (nx x) j0 ltac:(lia) Hit). reflexivity. }
  rewrite (GEN R' (nx a) j ltac:(lia) (eq_sym Eb)).
  rewrite (findex_S nx a b R'). destruct (Z.eqb_spec a b); [congruence|].
  pose proof (findex_le nx (nx a) b R' j ltac:(lia) (eq_sym Eb)) as Hle2. lia.
Qed.

Lemma ring_iter_inj : ltac2:(tb__ "0|1|
S0S1S0S0S0F_;M0G0S1S1SeR7R6R5R4R3A5S12R3R7A2S12R3R8A2S7S0ScR7R5R8A3ScR7R4R8A3A3S7S1R6R5A3F_;F_;F_;F_;Fj;Fi;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv i j (_ & Hnd & _) Hi Hj E.
  apply (proj1 (NoDup_nth_error _) Hnd i j); [rewrite chain_length; exact Hi|].
  rewrite !(nth_error_nth' _ 0) by (rewrite chain_length; lia). rewrite !chain_nth by lia. rewrite E. reflexivity.
Qed.

Definition fupd (f : Z -> Z) (a v : Z) : Z -> Z := ltac2:(tb__ "0|0|
S0S3S0L_;S17R1Va;A2Vv;Vf;R1A1X3x2Lx;").

Lemma ring_clip : ltac2:(tb__ "0|2|
S0S1S0S0S0F_;M0G0SeR5R4R3R2R1A5S13U3R5A2R3R5A1S0R5R6A1S0S8SeR9S1cR8U1M1A2R1S11R6R2R1A3S11R5R1R2A3A5S8S0SaSdS1cR9G1A2R2S11R7R3R2A3R1A4S8SdR9R8R7R1A4S9S7S0R1R8A3A1A2A2Fx;S8S9S7S0R2R7A3A1S8S9S7S0R1R7A3A1S8S9S7S0R2R1A3A1S8SdR8R7R6R2A4SdR8R7R6R1A4A2A2A2A2A2A2Tnext;Tprev;F_;F_;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv HR H3. pose proof HR as (HR1 & Hnd & Hb & Hcyc & Hp).
  cbn zeta. set (prev := pv cur). set (next := nx cur).
  set (nx' := fupd nx prev next). set (pv' := fupd pv next prev).
  pose proof (pv_cur n R cur nx pv HR) as Eprev. fold prev in Eprev.
  assert (Hlive_prev : live R cur nx prev) by (rewrite Eprev; eapply live_iter; exact HR).
  assert (Hlive_next : live R cur nx next) by (change next with (iter nx 1 cur); eapply live_iter; exact HR).

  destruct R as [|R']; [lia|]. cbn [chain] in Hnd, Hb, Hp. replace (S R' - 1)%nat with R' by lia.
  assert (Hcur_notin : ~ In cur (chain nx next R')) by (inversion Hnd; assumption).
  assert (Hnd' : NoDup (chain nx next R')) by (inversion Hnd; assumption).

  assert (Eprev' : prev = iter nx (R' - 1) next).
  { rewrite Eprev. replace (S R' - 1)%nat with (S (R' - 1)) by lia. reflexivity. }
  assert (AGREE : forall j, (S j < R')%nat -> nx' (iter nx j next) = nx (iter nx j next)).
  { intros j Hj. unfold nx', fupd. destruct (Z.eqb_spec (iter nx j next) prev) as [E|]; [|reflexivity].
    exfalso. rewrite Eprev' in E.
    pose proof (proj1 (NoDup_nth_error _) Hnd' j (R' - 1)%nat ltac:(rewrite chain_length; lia)) as INJ.
    rewrite !(nth_error_nth' _ 0) in INJ by (rewrite chain_length; lia).
    rewrite !chain_nth in INJ by lia. specialize (INJ ltac:(rewrite E; reflexivity)). lia. }
  assert (CH : chain nx' next R' = chain nx next R') by (apply chain_ext; exact AGREE).
  assert (Ecur : cur = iter nx 0 cur) by reflexivity.
  assert (Enext : next = iter nx 1 cur) by reflexivity.
  assert (NEQpc : prev <> cur).
  { intros E. pose proof (ring_iter_inj n (S R') cur nx pv (S R' - 1) 0 HR ltac:(lia) ltac:(lia)) as X.
    rewrite <- Eprev, <- Ecur in X. specialize (X E). lia. }
  assert (NEQnc : next <> cur).
  { intros E. pose proof (ring_iter_inj n (S R') cur nx pv 1 0 HR ltac:(lia) ltac:(lia)) as X.
    rewrite <- Enext, <- Ecur in X. specialize (X E). lia. }
  assert (NEQpn : prev <> next).
  { intros E. pose proof (ring_iter_inj n (S R') cur nx pv (S R' - 1) 1 HR ltac:(lia) ltac:(lia)) as X.
    rewrite <- Eprev, <- Enext in X. specialize (X E). lia. }
  split.
  - split; [lia|]. rewrite CH. split; [exact Hnd'|]. split; [inversion Hb; assumption|]. split.
    +
      destruct R' as [|R'']; [lia|]. rewrite iter_S.
      rewrite (iter_ext nx nx' next R'') by (intros j Hj; apply AGREE; lia).
      replace R'' with (S R'' - 1)%nat by lia. rewrite <- Eprev'. unfold nx', fupd. rewrite Z.eqb_refl. reflexivity.
    + apply Forall_forall. intros x Hx. unfold nx', pv', fupd.
      destruct (Z.eqb_spec x prev) as [->|Hxp].
      * rewrite Z.eqb_refl. reflexivity.
      * assert (Hnxx : nx x <> next).
        { intros E. apply Hxp. unfold next in E.
          assert (x = cur).
          { eapply nx_inj; [exact HR| | apply (live_cur n (S R') cur nx pv HR) | exact E]. right. exact Hx. }
          exfalso. apply Hcur_notin. congruence. }
        destruct (Z.eqb_spec (nx x) next); [congruence|].
        inversion Hp as [|? ? _ Hp']; subst. exact (proj1 (Forall_forall _ _) Hp' x Hx).
  - split.
    + intros x. unfold live. rewrite CH. cbn [chain]. split.
      * intros Hx. split; [right; exact Hx|]. intros ->. exact (Hcur_notin Hx).
      * intros [[<-|Hx] Hne]; [congruence|exact Hx].
    + repeat split; assumption.
Qed.

Lemma ring_ok_ext : ltac2:(tb__ "0|3|
S0S1S0S0S0F_;M0G0G0G0S0S8S15Z0R1A2M1S14R1R8A2A2S7S0R4R2A1R6R2A1A3M2F_;Fx;S0S8G1S14R1R9A2A2G2F_;Fx;SeR9R8R7R6R5A5SeRaR9R8R5R4A5F_;F_;F_;Fpv2;Fnx2;Fpv;Fnx;Fcur;FR;Fn;").
Proof.
  intros n R cur nx pv nx2 pv2 Hn Hpv HR. pose proof HR as (HR1 & Hnd & Hb & Hcyc & Hp).
  assert (AG : forall j, (j < R)%nat -> nx2 (iter nx j cur) = nx (iter nx j cur)).
  { intros j Hj. apply Hn. eapply live_lt; [exact HR|]. eapply live_iter. exact HR. }
  assert (CH : chain nx2 cur R = chain nx cur R) by (apply chain_ext; intros; apply AG; lia).
  split; [exact HR1|]. rewrite CH. split; [exact Hnd|]. split; [exact Hb|]. split.
  - rewrite (iter_ext nx nx2 cur R AG). exact Hcyc.
  - apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) Hb x Hx) as Bx.
    rewrite (Hn x Bx). rewrite Hpv; [exact (proj1 (Forall_forall _ _) Hp x Hx)|].
    eapply live_lt; [exact HR|]. eapply live_nx; [exact HR|exact Hx].
Qed.

Lemma ring_init : ltac2:(tb__ "0|5|
S0S0S0F_;M0G0S15Z1M1R3A2S0S8S15Z0M2R1A2M3S14R1R5A2A2S7S0R5R2A1M4S18S16R2G1A2R6A2A3F_;Fi;S0S8G3S14R1R6A2A2S7S0G4S18S1aS16R2R7A2G1A2R7A2A3F_;Fi;SeR6S1bR6A1G2R5R4A5F_;F_;F_;Fpv;Fnx;Fn;").
Proof.
  intros n nx pv Hn Hnx Hpv.
  assert (IT : forall j, (j < Z.to_nat n)%nat -> iter nx j 0 = Z.of_nat j).
  { induction j as [|j IH]; intros Hj; [reflexivity|]. rewrite iter_S, IH by lia. rewrite Hnx by lia.
    rewrite Z.mod_small; lia. }
  assert (CH : chain nx 0 (Z.to_nat n) = map Z.of_nat (seq 0 (Z.to_nat n))).
  { apply nth_ext with (d := 0) (d' := 0); [rewrite chain_length, length_map, length_seq; reflexivity|].
    intros j Hj. rewrite chain_length in Hj. rewrite chain_nth by lia. rewrite IT by lia.
    rewrite (nth_map_lt' Z.of_nat (seq 0 (Z.to_nat n)) j 0%nat 0) by (rewrite length_seq; exact Hj). rewrite seq_nth by exact Hj. reflexivity. }
  split; [lia|]. rewrite CH. split.
  { apply NoDup_map_NoDup_ForallPairs.
    - intros a b _ _ E. lia.
    - apply seq_NoDup. }
  split. { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (j & <- & Hj). apply in_seq in Hj. lia. }
  split.
  { destruct (Z.to_nat n) as [|k] eqn:E; [lia|]. rewrite iter_S, IT by lia. rewrite Hnx by lia.
    replace (Z.of_nat k + 1) with n by lia. apply Z.mod_same. lia. }
  apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (j & <- & Hj). apply in_seq in Hj.
  rewrite Hnx by lia.
  destruct (Z.lt_ge_cases (Z.of_nat j + 1) n).
  - rewrite (Z.mod_small (Z.of_nat j + 1) n) by lia. rewrite Hpv by lia.
    replace (Z.of_nat j + 1 + n - 1) with (Z.of_nat j + 1 * n) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (Z.of_nat j + 1) with n by lia. rewrite Z.mod_same by lia. rewrite Hpv by lia.
    replace (0 + n - 1) with (Z.of_nat j) by lia. apply Z.mod_small. lia.
Qed.
End Ring.

