(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CT_NBT : Z := 45000.
Definition CT_SMB : Z := 3145728.
Definition CT_NB63 : Z := 4.
Definition CT_BIGB : Z := 167772160.
Definition CT_NSEC : Z := 6.
Definition CT_MAXREQ : Z := 100663296.   (* [comment removed for export] *)
Definition ASAN_SEC_MIN : Z := 64513.

(* [comment removed for export] *)
Definition smsz (n : Z) : Z := if n <? MMAP_THRESHOLD then n else 0.
Definition bigb (n : Z) : Z := if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) else 0.
Definition isbig (n : Z) : Z := if MMAP_THRESHOLD <=? n then 1 else 0.
Definition issec (n : Z) : Z := if ASAN_SEC_MIN <=? n then 1 else 0.

Lemma smsz_nonneg n : 0 <= n -> 0 <= smsz n. Proof. intros; unfold smsz; destruct (n <? _); lia. Qed.
Lemma smsz_le n : 0 <= n -> smsz n <= n. Proof. intros; unfold smsz; destruct (n <? _); lia. Qed.
Lemma smsz_small n : n < MMAP_THRESHOLD -> smsz n = n. Proof. intros; unfold smsz; destruct (Z.ltb_spec n MMAP_THRESHOLD); [reflexivity| lia]. Qed.
Lemma bigb_nonneg n : 0 <= n -> 0 <= bigb n.
Proof. intros; unfold bigb; destruct (_ <=? n); [| lia]. unfold round_up_pg, PGSZ. pose proof (Z.land_nonneg (- (n + IB + UNIT)) (4096 - 1)). unfold IB, UNIT in *. lia. Qed.
Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0. Proof. intros; unfold bigb; destruct (Z.leb_spec MMAP_THRESHOLD n); [lia| reflexivity]. Qed.
Lemma round_up_pg_le x : 0 <= x -> round_up_pg x <= x + 4095.
Proof.
  intros. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12).
  rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). lia.
Qed.
Lemma bigb_le n : 0 <= n -> bigb n <= n + 4115.
Proof. intros; unfold bigb; destruct (_ <=? n); [| lia]. pose proof (round_up_pg_le (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia. Qed.
Lemma isbig_01 n : isbig n = 0 \/ isbig n = 1. Proof. unfold isbig; destruct (_ <=? n); auto. Qed.
Lemma issec_01 n : issec n = 0 \/ issec n = 1. Proof. unfold issec; destruct (_ <=? n); auto. Qed.
Lemma isbig_small n : n < MMAP_THRESHOLD -> isbig n = 0. Proof. intros; unfold isbig; destruct (Z.leb_spec MMAP_THRESHOLD n); [lia| reflexivity]. Qed.
Lemma issec_small n : n < ASAN_SEC_MIN -> issec n = 0. Proof. intros; unfold issec; destruct (Z.leb_spec ASAN_SEC_MIN n); [lia| reflexivity]. Qed.

Section Measures.
Context {ptr : Type}.
Implicit Types X Y : list (ptr * Z).

Definition msum (f : Z -> Z) X : Z := fold_right Z.add 0 (map (fun xb => f (snd xb)) X).
Definition smsum X := msum smsz X.
Definition r63 X := msum bigb X.
Definition n63 X := msum isbig X.
Definition nsec X := msum issec X.

Lemma msum_nil f : msum f [] = 0. Proof. reflexivity. Qed.
Lemma msum_cons f x X : msum f (x :: X) = f (snd x) + msum f X. Proof. reflexivity. Qed.
Lemma msum_app f X Y : msum f (X ++ Y) = msum f X + msum f Y.
Proof. unfold msum. rewrite map_app. induction (map _ X) as [|a l IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma msum_perm f X Y : Permutation X Y -> msum f X = msum f Y.
Proof. intros HP. unfold msum. apply (Permutation_map (fun xb => f (snd xb))) in HP. induction HP; cbn; lia. Qed.
Lemma msum_nonneg f X : (forall n, 0 <= n -> 0 <= f n) -> bnonneg X -> 0 <= msum f X.
Proof. intros Hf. induction X as [|x X IH]; intros H; [rewrite msum_nil; lia|]. inversion H; subst. rewrite msum_cons. specialize (IH ltac:(assumption)). pose proof (Hf _ H2). lia. Qed.

(* [comment removed for export] *)
Record meas : Type := mkM { m_cnt : Z; m_sum : Z; m_sm : Z; m_n63 : Z; m_r63 : Z; m_nsec : Z }.
Definition measure X : meas := mkM (zlength X) (bsum X) (smsum X) (n63 X) (r63 X) (nsec X).
Definition mle (a b : meas) : Prop :=
  m_cnt a <= m_cnt b /\ m_sum a <= m_sum b /\ m_sm a <= m_sm b /\ m_n63 a <= m_n63 b /\ m_r63 a <= m_r63 b /\ m_nsec a <= m_nsec b.
Definition madd (a b : meas) : meas :=
  mkM (m_cnt a + m_cnt b) (m_sum a + m_sum b) (m_sm a + m_sm b) (m_n63 a + m_n63 b) (m_r63 a + m_r63 b) (m_nsec a + m_nsec b).
Definition mblk (n : Z) : meas := mkM 1 n (smsz n) (isbig n) (bigb n) (issec n).
Definition m0 : meas := mkM 0 0 0 0 0 0.

Lemma measure_nil : measure [] = m0. Proof. reflexivity. Qed.
Lemma measure_cons x X : measure (x :: X) = madd (mblk (snd x)) (measure X).
Proof. unfold measure, madd, mblk. cbn [m_cnt m_sum m_sm m_n63 m_r63 m_nsec]. unfold zlength. cbn [length]. rewrite Nat2Z.inj_succ, bsum_cons. unfold smsum, r63, n63, nsec. rewrite !msum_cons. f_equal; lia. Qed.
Lemma measure_app X Y : measure (X ++ Y) = madd (measure X) (measure Y).
Proof. unfold measure, madd. cbn [m_cnt m_sum m_sm m_n63 m_r63 m_nsec]. rewrite zlen_app', bsum_app. unfold smsum, r63, n63, nsec. rewrite !msum_app. reflexivity. Qed.
Lemma measure_perm X Y : Permutation X Y -> measure X = measure Y.
Proof. intros HP. unfold measure, smsum, r63, n63, nsec. rewrite (zlen_perm _ _ HP), (bsum_perm _ _ HP), !(msum_perm _ _ _ HP). reflexivity. Qed.
Lemma mle_refl a : mle a a. Proof. unfold mle; lia. Qed.
Lemma mle_trans a b c : mle a b -> mle b c -> mle a c. Proof. unfold mle; lia. Qed.
Lemma madd_mono a b c d : mle a c -> mle b d -> mle (madd a b) (madd c d). Proof. unfold mle, madd; cbn; lia. Qed.
Lemma madd_comm a b : madd a b = madd b a. Proof. unfold madd; f_equal; lia. Qed.
Lemma madd_assoc a b c : madd a (madd b c) = madd (madd a b) c. Proof. unfold madd; cbn; f_equal; lia. Qed.
Lemma madd_m0_l a : madd m0 a = a. Proof. destruct a; unfold madd, m0; cbn; f_equal; lia. Qed.
Lemma madd_m0_r a : madd a m0 = a. Proof. destruct a; unfold madd, m0; cbn; f_equal; lia. Qed.
Lemma mblk_nonneg n : 0 <= n -> mle m0 (mblk n).
Proof. intros. unfold mle, m0, mblk; cbn. pose proof (smsz_nonneg n H). pose proof (bigb_nonneg n H). pose proof (isbig_01 n). pose proof (issec_01 n). lia. Qed.
Lemma measure_nonneg X : bnonneg X -> mle m0 (measure X).
Proof.
  induction X as [|x X IH]; intros H; [rewrite measure_nil; apply mle_refl|]. inversion H; subst.
  rewrite measure_cons. rewrite <- (madd_m0_l m0) at 1. apply madd_mono; [apply mblk_nonneg; assumption| apply IH; assumption].
Qed.
(* [comment removed for export] *)
Lemma mblk_small n B : 0 <= n <= B -> B < ASAN_SEC_MIN -> mle (mblk n) (mkM 1 B B 0 0 0).
Proof.
  intros Hn HB. unfold mle, mblk; cbn. unfold ASAN_SEC_MIN, MMAP_THRESHOLD in *.
  rewrite smsz_small, isbig_small, bigb_small, issec_small by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia). lia.
Qed.

(* [comment removed for export] *)
Definition okC X (n : Z) : Prop :=
  0 <= n /\ bnonneg X
  /\ zlength X + 1 <= CT_NBT
  /\ smsum X + smsz n <= CT_SMB
  /\ n63 X + isbig n <= CT_NB63
  /\ r63 X + bigb n <= CT_BIGB
  /\ nsec X + issec n <= CT_NSEC
  /\ n <= CT_MAXREQ.

Lemma okC_of_meas X n (M : meas) : bnonneg X -> 0 <= n <= 100663296 -> mle (measure X) M ->
  m_cnt M + 1 <= CT_NBT -> m_sm M + smsz n <= CT_SMB -> m_n63 M + isbig n <= CT_NB63 -> m_r63 M + bigb n <= CT_BIGB -> m_nsec M + issec n <= CT_NSEC ->
  okC X n.
Proof. intros HB Hn (L1 & L2 & L3 & L4 & L5 & L6). unfold measure in *; cbn in *. unfold okC, CT_MAXREQ. repeat split; try assumption; lia. Qed.

Lemma okC_perm X Y n : Permutation X Y -> okC X n -> okC Y n.
Proof.
  intros HP (Hn & HB & H). unfold okC. rewrite <- (zlen_perm _ _ HP). unfold smsum, n63, r63, nsec in *. rewrite <- !(msum_perm _ _ _ HP).
  split; [exact Hn|]. split; [eapply bnonneg_perm; eassumption| exact H].
Qed.
End Measures.
