(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte_cases (P : Z -> bool) : forallb (fun i => P (Z.of_nat i)) (seq 0 256) = true -> forall fb, 0 <= fb < 256 -> P fb = true.
Proof.
  intros H fb Hfb. rewrite forallb_forall in H. replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply H. apply in_seq. lia.
Qed.
Lemma land3_bits fb : 0 <= fb -> Z.land fb 3 = 0 -> Z.testbit fb 0 = false /\ Z.testbit fb 1 = false.
Proof.
  intros Hfb H. split.
  - apply (f_equal (fun x => Z.testbit x 0)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 0) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
  - apply (f_equal (fun x => Z.testbit x 1)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 1) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.

(* [comment removed for export] *)
Lemma big_at_zero M a : L5.u8_at RSEGS M a 0 -> L5.u64_at RSEGS M (a + 8) 0 -> L5.u64_at RSEGS M (a + 16) 0 -> L5.u64_at RSEGS M (a + 24) 0 ->
  L5.big_at RSEGS M a (L5.BO 0 0 (L5.BInl 0 0)).
Proof. intros H0 H8 H16 H24. unfold L5.big_at; cbn. repeat split; try assumption; try lia; reflexivity. Qed.
Lemma obj_limbs_zero M : L5C.obj_limbs RSEGS M (L5.BO 0 0 (L5.BInl 0 0)) [].
Proof. unfold L5C.obj_limbs; cbn. repeat split. constructor. Qed.

(* [comment removed for export] *)
Lemma limbs_val_val ws : L5.limbs_val ws = val ws.
Proof. induction ws as [|w t IH]. reflexivity. cbn [L5.limbs_val val]. rewrite IH, M_val. reflexivity. Qed.
Lemma words_ok_of_Forall ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> words_ok ws.
Proof. intros H. unfold words_ok. eapply Forall_impl. 2: exact H. intros a Ha. cbn beta in Ha. unfold wordZ. rewrite M_val. lia. Qed.
Lemma reduced_ws_of ws : L5CSA.reduced ws -> reduced_ws ws.
Proof. intros H. apply reduced_ws_intro. intros NE. destruct H as [H|H]. congruence. unfold nth_w. exact H. Qed.
Lemma length_nwords ws V : Forall (fun w => 0 <= w < 2 ^ 64) ws -> L5CSA.reduced ws -> L5.limbs_val ws = V -> length ws = nwords V.
Proof.
  intros HF HR HV. rewrite <- HV, limbs_val_val. apply reduced_length_nwords. apply words_ok_of_Forall. exact HF. apply reduced_ws_of. exact HR.
Qed.
Lemma limbs_val_nonneg ws : Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= L5.limbs_val ws.
Proof. induction ws as [|w t IH]; intros H. cbn; lia. inversion H; subst. cbn [L5.limbs_val]. specialize (IH ltac:(assumption)). lia. Qed.
(* [comment removed for export] *)
Lemma nwords_le2 V (n : nat) : (n <= 38)%nat -> 0 <= V < 10 ^ Z.of_nat n -> (nwords V <= 2)%nat.
Proof.
  intros Hn HV. apply (proj2 (nwords_le_iff V 2 ltac:(lia))). rewrite Mpow_nat. change (2 ^ (64 * Z.of_nat 2)) with (2 ^ 128).
  eapply Z.lt_le_trans. apply (proj2 HV). eapply Z.le_trans. apply (Z.pow_le_mono_r 10 (Z.of_nat n) 38). lia. lia.
  cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma cap_reserve_ok V (n : nat) : 0 <= V < 10 ^ Z.of_nat n -> Z.of_nat (nwords V) + 1 <= Z.of_nat (BigModel.round_up (num_words_est n)).
Proof.
  intros HV. pose proof (nwords_bound V n HV). pose proof (round_up_ge_S (num_words_est n)). lia.
Qed.
Lemma round_up_Z (n : nat) : L5CSA.round_up (Z.of_nat n) = Z.of_nat (BigModel.round_up n).
Proof.
  unfold L5CSA.round_up. rewrite BigFactsOps.round_up_eq. rewrite Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_div. lia.
Qed.
Lemma ws_is_wlist ws V : Forall (fun w => 0 <= w < 2 ^ 64) ws -> L5.limbs_val ws = V -> length ws = nwords V -> ws = wlist V (nwords V).
Proof.
  intros HF HV HL. rewrite <- HL. rewrite <- HV, limbs_val_val. symmetry. apply wlist_val. apply words_ok_of_Forall. exact HF.
Qed.

(* [comment removed for export] *)
Lemma fb3_facts fb : 0 <= fb < 256 -> Z.land fb 3 = 0 ->
  Z.land fb 253 = fb /\ Z.land (Z.lor fb 1) 253 = fb + 1 /\ Z.lor fb 0 = fb /\ Z.lor fb 2 = fb + 2 /\ Z.lor (fb + 1) 0 = fb + 1 /\ Z.lor (fb + 1) 2 = fb + 1 + 2
  /\ Z.testbit fb 0 = false /\ Z.testbit (fb + 1) 0 = true /\ Z.testbit (fb + 2) 0 = false /\ Z.testbit (fb + 1 + 2) 0 = true /\ Z.lor fb 1 = fb + 1.
Proof.
  intros Hfb H3.
  pose proof (byte_cases (fun fb => implb (Z.land fb 3 =? 0)
     ((Z.land fb 253 =? fb) && (Z.land (Z.lor fb 1) 253 =? fb + 1) && (Z.lor fb 0 =? fb) && (Z.lor fb 2 =? fb + 2) && (Z.lor (fb + 1) 0 =? fb + 1) && (Z.lor (fb + 1) 2 =? fb + 1 + 2)
      && negb (Z.testbit fb 0) && Z.testbit (fb + 1) 0 && negb (Z.testbit (fb + 2) 0) && Z.testbit (fb + 1 + 2) 0 && (Z.lor fb 1 =? fb + 1))%bool)
     ltac:(vm_compute; reflexivity) fb Hfb) as X. cbn beta in X.
  rewrite (proj2 (Z.eqb_eq _ _) H3) in X. cbn [implb] in X.
  repeat (apply andb_prop in X; destruct X as [X ?Y]).
  repeat split; try (apply Z.eqb_eq; assumption).
  - destruct (Z.testbit fb 0); [discriminate|reflexivity].
  - assumption.
  - destruct (Z.testbit (fb + 2) 0); [discriminate|reflexivity].
  - assumption.
Qed.

(* [comment removed for export] *)
Definition fbW (dyn : bool) : Z := if dyn then 1 else 0.
Definition fbN (dyn ng : bool) : Z := if ng then Z.lor (fbW dyn) 2 else fbW dyn.
Lemma fbN_land2 dyn ng : Z.land (fbN dyn ng) 2 = if ng then 2 else 0. Proof. destruct dyn, ng; reflexivity. Qed.
Lemma fbN_range dyn ng : 0 <= fbN dyn ng <= 3. Proof. destruct dyn, ng; vm_compute; split; discriminate. Qed.
Lemma fbN_bit0 dyn ng : Z.testbit (fbN dyn ng) 0 = dyn. Proof. destruct dyn, ng; reflexivity. Qed.

Lemma assign_fb_res fb dyn ng (n : nat) (grown : bool) :
  0 <= fb < 256 -> Z.land fb 3 = 0 -> (1 <= n)%nat -> (grown = true <-> (3 <= n)%nat) ->
  assign_fb fb (fbN dyn ng) n grown = res_fb fb n ng.
Proof.
  intros Hfb H3 Hn HG. destruct (fb3_facts fb Hfb H3) as (F1 & F2 & F3 & F4 & F5 & F6 & _ & _ & _ & _ & F11).
  unfold assign_fb, res_fb. replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (1 <=? n)%nat with true by (symmetry; apply Nat.leb_le; lia). rewrite fbN_land2.
  destruct grown.
  - replace (3 <=? n)%nat with true by (symmetry; apply Nat.leb_le; apply HG; reflexivity). rewrite F2. destruct ng; cbn [andb]; lia.
  - replace (3 <=? n)%nat with false. 2: { symmetry. apply Nat.leb_gt. destruct (Nat.lt_ge_cases n 3). lia. exfalso. pose proof (proj2 HG ltac:(lia)). discriminate. }
    rewrite F1. destruct ng; cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
Lemma big_at_reflag M M' a f f' (n : nat) st :
  L5.big_at RSEGS M a (L5.BO f n st) -> L5.u8_at RSEGS M' a f' -> 0 <= f' < 256 -> Z.testbit f' 0 = Z.testbit f 0 ->
  L5C.agree_on M M' (a + 8) 24 -> 0 <= a -> a + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M' a (L5.BO f' n st).
Proof.
  intros (B1 & B2 & B3 & B4) U Hf' T0 AG Ha Hn. unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in B3, B4.
  split. exact U. split. exact Hf'.
  split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact B3. }
  rewrite T0. destruct st as [v0 v1|cap q].
  - destruct B4 as (C1 & C2 & C3 & C4). split. exact C1.
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C2. }
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C3. }
    exact C4.
  - destruct B4 as (C1 & C2 & C3 & C4). split. exact C1.
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C2. }
    split. { eapply (L5C.u64_at_agree RSEGS M M'). eapply L5C.agree_on_sub. exact AG. lia. lia. lia. lia. exact C3. }
    exact C4.
Qed.
(* [comment removed for export] *)
Lemma obj_limbs_reflag M M' f f' (n : nat) st ws :
  L5C.obj_limbs RSEGS M (L5.BO f n st) ws ->
  (forall cap q, st = L5.BDyn cap q -> L5C.agree_on M M' q (8 * Z.of_nat (length ws)) /\ 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M' (L5.BO f' n st) ws.
Proof.
  intros (L1 & L2 & L3) HQ. unfold L5C.obj_limbs; cbn [L5.bo_len L5.bo_st]. cbn [L5.bo_len L5.bo_st] in L1, L3.
  split. exact L1. split. exact L2. destruct st as [v0 v1|cap q]. exact L3.
  destruct (HQ cap q eq_refl) as (AG & Q0 & Q1). eapply (L5C.limbs_at_agree RSEGS M M'). exact AG. exact Q0. exact Q1. exact L3.
Qed.

(* [comment removed for export] *)
Lemma firstn_digits_bound ds (j : nat) : (j <= length ds)%nat -> digits_ok (firstn j ds) -> 0 <= dec (firstn j ds) < 10 ^ Z.of_nat j.
Proof.
  intros Hj D. pose proof (dec_bound (firstn j ds) (all_digits_Forall _ D)) as B. rewrite length_firstn, Nat.min_l in B by lia. exact B.
Qed.
Lemma digits_ok_S ds (j : nat) : (j < length ds)%nat -> digits_ok (firstn j ds) -> 48 <= nth j ds 0 <= 57 -> digits_ok (firstn (Datatypes.S j) ds).
Proof.
  intros Hj D C. unfold digits_ok. rewrite (firstn_S_nth ds j Hj). apply Forall_app. split. exact D. constructor. exact C. constructor.
Qed.
Lemma not_digits_ok ds Kb c : (Kb < length ds)%nat -> nth Kb ds 0 = c -> (c < 48 \/ 57 < c) -> ~ digits_ok ds.
Proof. intros HK Hc Hrg D. unfold digits_ok in D. pose proof (proj1 (Forall_nth _ _) D Kb 0 HK) as X. cbn beta in X. lia. Qed.
Lemma vblk_pos m : 0 <= vblk m.
Proof. unfold vblk. destruct (m <? 39)%nat. lia. unfold L5CSA.round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(lia) ltac:(lia)). lia. Qed.

End L5ADK.
