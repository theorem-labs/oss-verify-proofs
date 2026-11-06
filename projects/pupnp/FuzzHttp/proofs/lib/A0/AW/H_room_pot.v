(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HCount.
Import ListNotations.
Open Scope Z_scope.

Definition ramp (a T s : Z) : Z := Z.min (T - a) (Z.max 0 (s - a)).
Definition stepf (T s : Z) : Z := if T <=? s then 1 else 0.
Definition lowf (T s : Z) : Z := if s <=? T then 1 else 0.

Lemma ramp_range : forall a T s, a <= T -> 0 <= ramp a T s <= T - a. Proof. intros. unfold ramp. lia. Qed.
Lemma ramp_top : forall a T s, a <= T -> T <= s -> ramp a T s = T - a. Proof. intros. unfold ramp. lia. Qed.
Lemma ramp_mono : forall a T s s', s <= s' -> ramp a T s <= ramp a T s'. Proof. intros. unfold ramp. lia. Qed.
Lemma ramp_lip : forall a T s s', a <= T -> s <= s' -> ramp a T s' <= ramp a T s + (s' - s). Proof. intros. unfold ramp. lia. Qed.
Lemma ramp_le : forall a T s, a <= T -> ramp a T s <= Z.max 0 (s - a). Proof. intros. unfold ramp. lia. Qed.
Lemma stepf_range : forall T s, 0 <= stepf T s <= 1. Proof. intros. unfold stepf. destruct (T <=? s); lia. Qed.
Lemma stepf_mono : forall T s s', s <= s' -> stepf T s <= stepf T s'.
Proof. intros T s s' H. unfold stepf. destruct (T <=? s) eqn:E1; destruct (T <=? s') eqn:E2; lia. Qed.
Lemma lowf_range : forall T s, 0 <= lowf T s <= 1. Proof. intros. unfold lowf. destruct (s <=? T); lia. Qed.
Lemma lowf_anti : forall T s s', s <= s' -> lowf T s' <= lowf T s.
Proof. intros T s s' H. unfold lowf. destruct (s <=? T) eqn:E1; destruct (s' <=? T) eqn:E2; lia. Qed.

Lemma stepf_cases : forall T s, (stepf T s = 0 /\ s < T) \/ (stepf T s = 1 /\ T <= s).
Proof. intros T s. unfold stepf. destruct (T <=? s) eqn:E; [right; apply Z.leb_le in E; lia| left; apply Z.leb_gt in E; lia]. Qed.
Lemma lowf_cases : forall T s, (lowf T s = 0 /\ T < s) \/ (lowf T s = 1 /\ s <= T).
Proof. intros T s. unfold lowf. destruct (s <=? T) eqn:E; [right; apply Z.leb_le in E; lia| left; apply Z.leb_gt in E; lia]. Qed.

Section W.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation lbrm := (lb_remove (am_K_eqb FI AI)).

Definition psum (f : Z -> Z) (LB : BL) : Z := fold_right (fun b acc => f (blk_size b) + acc) 0 LB.
#[using="Type"] Lemma psum_cons : forall f (b : BLK) LB, psum f (b :: LB) = f (blk_size b) + psum f LB. Proof. reflexivity. Qed.
#[using="Type"] Lemma psum_nonneg : forall f LB, (forall s, 0 <= f s) -> 0 <= psum f LB.
Proof. intros f LB Hf. induction LB as [|b LB IH]; [cbn; lia|]. rewrite psum_cons. specialize (Hf (blk_size b)). lia. Qed.
#[using="Type"] Lemma psum_le_len : forall f LB M, (forall s, f s <= M) -> psum f LB <= M * Z.of_nat (length LB).
Proof. intros f LB M Hf. induction LB as [|b LB IH]; [cbn; lia|]. rewrite psum_cons. cbn [length]. specialize (Hf (blk_size b)). lia. Qed.
#[using="Type"] Lemma psum_mono_f : forall f g LB, (forall s, f s <= g s) -> psum f LB <= psum g LB.
Proof. intros f g LB H. induction LB as [|b LB IH]; [cbn; lia|]. rewrite !psum_cons. specialize (H (blk_size b)). lia. Qed.

#[using="Type"] Lemma psum_remove : forall f k (LB : BL) (b : BLK), (forall s, 0 <= f s) -> In b LB -> blk_id b = k -> psum f (lbrm k LB) <= psum f LB - f (blk_size b).
Proof.
  intros f k LB b Hf. induction LB as [|b0 LB IH]; intros HIN E; [destruct HIN|].
  assert (LE : psum f (lbrm k LB) <= psum f LB).
  { clear - Hf. induction LB as [|b1 LB IH]; [cbn; lia|]. unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _); rewrite ?psum_cons; specialize (Hf (blk_size b1)); lia. }
  unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _) as [D|D].
  - destruct HIN as [->|HIN]; [| rewrite !psum_cons; specialize (IH HIN E); lia].
    exfalso. apply Is_true_true_1 in D. rewrite E in D. pose proof (proj2 (am_K_eqb_eq FI AI k k) eq_refl) as Q. rewrite Q in D. discriminate D.
  - rewrite psum_cons. destruct HIN as [->|HIN]; [lia|]. specialize (IH HIN E). specialize (Hf (blk_size b0)). lia.
Qed.
#[using="Type"] Lemma psum_remove_le : forall f k (LB : BL), (forall s, 0 <= f s) -> psum f (lbrm k LB) <= psum f LB.
Proof.
  intros f k LB Hf. induction LB as [|b1 LB IH]; [cbn; lia|]. unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _); rewrite ?psum_cons; specialize (Hf (blk_size b1)); lia.
Qed.

#[using="Type"] Lemma psum_realloc : forall f k (LB : BL) A n (b' : BLK), (forall s, 0 <= f s) -> In (k, A, n) LB ->
  psum f (b' :: lbrm k LB) <= psum f LB + (f (blk_size b') - f n).
Proof. intros f k LB A n b' Hf HIN. rewrite psum_cons. pose proof (psum_remove f k LB (k, A, n) Hf HIN eq_refl) as R. cbn [blk_size snd] in R. lia. Qed.

Definition szok (LB : BL) : Prop := Forall (fun b : BLK => 0 <= blk_size b) LB.
#[using="Type"] Lemma szok_remove : forall k LB, szok LB -> szok (lbrm k LB).
Proof. intros k LB H. unfold szok in *. rewrite Forall_forall in *. intros b Hb. apply H. exact (lb_remove_sub FI AI k LB b Hb). Qed.

#[using="Type"] Lemma lbc_le_psum : forall (g : Z -> Z) c (LB : BL), (forall s, 0 <= g s) -> (forall b, In b LB -> a0_cls (blk_size b) = c -> 1 <= g (blk_size b)) -> lbc FI AI LB c <= psum g LB.
Proof.
  intros g c LB Hg. unfold lbc, lb_cls. induction LB as [|b LB IH]; intros H1; [cbn; lia|].
  cbn [List.filter]. rewrite psum_cons. specialize (IH (fun b' Hb' => H1 b' (or_intror Hb'))).
  destruct (a0_cls (blk_size b) =? c) eqn:E; [apply Z.eqb_eq in E; cbn [length]; specialize (H1 b (or_introl eq_refl) E); lia| specialize (Hg (blk_size b)); lia].
Qed.
#[using="Type"] Lemma lbc_le_psumM : forall (g : Z -> Z) M c (LB : BL), 0 <= M -> (forall s, 0 <= g s) -> (forall b, In b LB -> a0_cls (blk_size b) = c -> M <= g (blk_size b)) -> M * lbc FI AI LB c <= psum g LB.
Proof.
  intros g M c LB HM Hg. unfold lbc, lb_cls. induction LB as [|b LB IH]; intros H1; [cbn; lia|].
  cbn [List.filter]. rewrite psum_cons. specialize (IH (fun b' Hb' => H1 b' (or_intror Hb'))).
  destruct (a0_cls (blk_size b) =? c) eqn:E; [apply Z.eqb_eq in E; cbn [length]; specialize (H1 b (or_introl eq_refl) E); lia| specialize (Hg (blk_size b)); lia].
Qed.

#[using="Type"] Lemma bytes0_le_psum : forall a (LB : BL), 0 <= a < 64513 -> szok LB ->
  (64513 - a) * lb_bytes FI AI (lb_cls FI AI 0 LB) <= 64513 * psum (fun s => Z.max 0 (s - a)) LB.
Proof.
  intros a LB Ha. unfold lb_cls. induction LB as [|b LB IH]; intros SZ; [cbn; lia|].
  apply Forall_cons_iff in SZ. destruct SZ as [S0 SZ]. specialize (IH SZ). cbn [List.filter]. rewrite psum_cons.
  destruct (a0_cls (blk_size b) =? 0) eqn:E.
  - apply Z.eqb_eq in E. apply (a0_cls0_iff _ S0) in E. cbn [lb_bytes fold_right]. fold (lb_bytes FI AI (List.filter (fun b0 : BLK => a0_cls (blk_size b0) =? 0) LB)). nia.
  - pose proof (Z.le_max_l 0 (blk_size b - a)). nia.
Qed.
End W.

Lemma a0_nmin_le : forall n, 1 <= n -> a0_cls n <> 0 -> a0_nmin (a0_cls n) <= n.
Proof.
  intros n Hn NZ. destruct (Z_le_gt_dec n 65536) as [LE|GT].
  - pose proof (a0_chk_ok (fun n => (a0_cls n =? 0) || (a0_nmin (a0_cls n) <=? n)) (Z.to_nat 65536) 1 ltac:(vm_compute; reflexivity) n ltac:(lia)) as X0.
    cbv beta in X0. apply orb_true_iff in X0. destruct X0 as [X0|X0]; [apply Z.eqb_eq in X0; contradiction| apply Z.leb_le in X0; exact X0].
  - exfalso. apply NZ. apply a0_cls0_iff; lia.
Qed.
Lemma a0_cls_low : forall n, 0 <= n -> (a0_cls n = 1 -> n <= 16) /\ a0_cls n <> 5 /\ a0_cls n <> 31.
Proof.
  intros n Hn. destruct (Z_le_gt_dec n 65536) as [LE|GT].
  - pose proof (a0_chk_ok (fun n => ((negb (a0_cls n =? 1)) || (n <=? 16)) && negb (a0_cls n =? 5) && negb (a0_cls n =? 31)) (Z.to_nat 65537) 0 ltac:(vm_compute; reflexivity) n ltac:(lia)) as X0.
    cbv beta in X0. apply andb_true_iff in X0. destruct X0 as [X0 X2]. apply andb_true_iff in X0. destruct X0 as [X0 X1].
    split; [intros E; rewrite E in X0; cbn in X0; apply Z.leb_le in X0; exact X0|]. split; [intros E; rewrite E in X1; discriminate X1| intros E; rewrite E in X2; discriminate X2].
  - assert (E0 : a0_cls n = 0) by (apply a0_cls0_iff; lia). rewrite E0. split; [discriminate|]. split; discriminate.
Qed.
