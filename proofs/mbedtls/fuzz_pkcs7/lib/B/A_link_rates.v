(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_link_base A_x509_rates.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_pk_parse_H A_x509_get_name_A A_pkcs7_signer_C A_pkcs7_signers_C A_pk_free A_pkcs7_free A_pkcs7_getcerts A_pkcs7_parse_C A_fuzz_entry A_link_budgets.
Open Scope Z_scope.

Local Notation PHIn := A_x509_get_name_A.PHIn.
Local Notation FFRn := A_x509_get_name_A.FFRn.
Local Notation CNTn := A_x509_get_name_A.CNTn.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CNTsi_i : Z -> Z := A_pkcs7_signer_C.CNTsi CNTn.
Definition PHIsi_i : Z -> Z := A_pkcs7_signer_C.PHIsi PHIn CNTn.
Definition FFRsi_i : Z -> Z -> Z := A_pkcs7_signer_C.FFRsi FFRn CNTn.
Definition CNTs_i : Z -> Z := A_pkcs7_signers_C.CNTs CNTsi_i.
Definition PHIs_i : Z -> Z := A_pkcs7_signers_C.PHIs PHIsi_i CNTsi_i.
Definition FFRs_i : Z -> Z -> Z := A_pkcs7_signers_C.FFRs FFRsi_i CNTsi_i.

Definition MC (d : Z) : Z := Z.max 0 (fr_charge d).
Lemma MC0 : forall d, 0 <= MC d. Proof. intros d. unfold MC. lia. Qed.
Definition RS (d : Z) : Z := RN (d + 2) + 2 * MC (d + 2) + 14 * MC (d + 1).
Definition KS (d : Z) : Z := 4 * MC (d + 1).

Lemma CNTs_i_le : forall n, 0 <= n -> CNTs_i n <= rate12 8 n + 1.
Proof.
  intros n Hn. unfold CNTs_i, A_pkcs7_signers_C.CNTs, CNTsi_i, A_pkcs7_signer_C.CNTsi.
  pose proof (CNTn_rate n Hn) as C1. pose proof (rate12_div2 1 n ltac:(lia) Hn) as C2. pose proof (rate12_add 2 6 n) as A1.
  change (6 * 1) with 6 in C2. change (2 + 6) with 8 in A1. lia.
Qed.
Lemma PHIs_i_le : forall n, 0 <= n -> PHIs_i n <= rate12 2656 n + 400.
Proof.
  intros n Hn. unfold PHIs_i, A_pkcs7_signers_C.PHIs, PHIsi_i, A_pkcs7_signer_C.PHIsi, AVOL_CALL.
  pose proof (PHIn_rate n Hn) as C1. pose proof (rate12_div2 400 n ltac:(lia) Hn) as C2. pose proof (rate12_add 256 (6 * 400) n) as A1.
  change (256 + 6 * 400) with 2656 in A1. lia.
Qed.
Lemma FFRs_i_le : forall n d, 0 <= n -> FFRs_i n d <= rate12 (RS d) n + KS d.
Proof.
  intros n d Hn. unfold FFRs_i, A_pkcs7_signers_C.FFRs, FFRsi_i, A_pkcs7_signer_C.FFRsi.
  replace (d + 1 + 1) with (d + 2) by lia. fold (MC (d + 2)). fold (MC (d + 1)).
  pose proof (MC0 (d + 1)) as M1. pose proof (MC0 (d + 2)) as M2.
  pose proof (FFRn_rate n (d + 2) Hn) as F1.
  assert (T1 : CNTn n * MC (d + 2) <= rate12 (2 * MC (d + 2)) n).
  { eapply Z.le_trans; [apply Z.mul_le_mono_nonneg_r; [exact M2| exact (CNTn_rate n Hn)]|].
    rewrite (Z.mul_comm (rate12 2 n)). rewrite (Z.mul_comm 2). apply rate12_scale. exact M2. }
  assert (T2 : (n / 2 + 2) * MC (d + 1) <= rate12 (6 * MC (d + 1)) n + 2 * MC (d + 1)).
  { pose proof (rate12_div2 (MC (d + 1)) n M1 Hn) as D1. lia. }
  assert (T3 : (A_pkcs7_signers_C.CNTs CNTsi_i n + 1) * MC (d + 1) <= rate12 (8 * MC (d + 1)) n + 2 * MC (d + 1)).
  { pose proof (CNTs_i_le n Hn) as CS. unfold CNTs_i in CS.
    eapply Z.le_trans; [apply Z.mul_le_mono_nonneg_r; [exact M1| apply Z.add_le_mono_r; exact CS]|].
    pose proof (rate12_scale (MC (d + 1)) 8 n M1) as S2. rewrite (Z.mul_comm (MC (d + 1)) 8) in S2. lia. }
  pose proof (rate12_add (RN (d + 2)) (2 * MC (d + 2)) n) as A1.
  pose proof (rate12_add (RN (d + 2) + 2 * MC (d + 2)) (6 * MC (d + 1)) n) as A2.
  pose proof (rate12_add (RN (d + 2) + 2 * MC (d + 2) + 6 * MC (d + 1)) (8 * MC (d + 1)) n) as A3.
  replace (RN (d + 2) + 2 * MC (d + 2) + 6 * MC (d + 1) + 8 * MC (d + 1)) with (RS d) in A3 by (unfold RS; lia).
  unfold KS. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHIg_i : Z -> Z := PHIc_i.
Definition FFRg_i : Z -> Z -> Z := A_pkcs7_getcerts.FFRg FFRc_i.
Definition CNTg_i : Z -> Z := CNTc_i.

Definition PJ_CNT (n : Z) : Z := rate12 8 n + (KCC + 1).
Definition PJ_PHI (n : Z) : Z := rate12 2656 n + (KCP + 400).
Definition PJ_FFR (n d : Z) : Z :=
  if 0 <=? d then rate12 (Z.max (RCF (d + 1)) (RS d)) n + (KCF (d + 1) + KS d) else FFRg_i n d + FFRs_i n d.

Lemma KCC0 : 0 <= KCC. Proof. vm_compute. discriminate. Qed.
Lemma KCP0 : 0 <= KCP. Proof. vm_compute. discriminate. Qed.
Lemma KCF0 : forall d, 0 <= KCF d.
Proof.
  intros d. unfold KCF. pose proof (A_pk_parse_H.PKP_FFR0 0 (d + 1) ltac:(lia)). pose proof KCC0.
  assert (0 <= A_pk_free.FFRpk 0 0) by (unfold A_pk_free.FFRpk, fr_charge; lia). unfold fr_charge in *. lia.
Qed.
Lemma KS0 : forall d, 0 <= KS d. Proof. intros d. unfold KS. pose proof (MC0 (d + 1)). lia. Qed.
Lemma RCF0 : forall d, 0 <= RCF d. Proof. intros d. unfold RCF, RCC. pose proof (RJF0 d). lia. Qed.

Lemma CNTs_i_mono : forall n n', 0 <= n <= n' -> 0 <= CNTs_i n <= CNTs_i n'.
Proof. exact (A_link_budgets.CNTs_mono _ (A_link_budgets.CNTsi_mono _ A_x509_get_name_A.CNTn_mono)). Qed.
Lemma PHIs_i_mono : forall n n', 0 <= n <= n' -> 0 <= PHIs_i n <= PHIs_i n'.
Proof.
  exact (A_link_budgets.PHIs_mono _ _ (A_link_budgets.PHIsi_mono _ _ A_x509_get_name_A.PHIn_mono A_x509_get_name_A.CNTn_mono)
           (A_link_budgets.CNTsi_mono _ A_x509_get_name_A.CNTn_mono)).
Qed.
Lemma FFRs_i_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRs_i n d <= FFRs_i n' d.
Proof.
  exact (A_link_budgets.FFRs_mono _ _ (A_link_budgets.FFRsi_mono _ _ A_x509_get_name_A.FFRn_mono A_x509_get_name_A.CNTn_mono)
           (A_link_budgets.CNTsi_mono _ A_x509_get_name_A.CNTn_mono)).
Qed.
Lemma FFRg_i_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRg_i n d <= FFRg_i n' d.
Proof. intros n n' d H. unfold FFRg_i, A_pkcs7_getcerts.FFRg. exact (FFRc_i_mono n n' (d + 1) H). Qed.

Lemma PJ_CNT_mono : forall n n', 0 <= n <= n' -> 0 <= PJ_CNT n <= PJ_CNT n'.
Proof.
  intros n n' H. unfold PJ_CNT. pose proof KCC0. pose proof (rate12_nonneg 8 n ltac:(lia) ltac:(lia)). pose proof (rate12_mono_n 8 n n' ltac:(lia) H). lia.
Qed.
Lemma PJ_PHI_mono : forall n n', 0 <= n <= n' -> 0 <= PJ_PHI n <= PJ_PHI n'.
Proof.
  intros n n' H. unfold PJ_PHI. pose proof KCP0. pose proof (rate12_nonneg 2656 n ltac:(lia) ltac:(lia)). pose proof (rate12_mono_n 2656 n n' ltac:(lia) H). lia.
Qed.
Lemma PJ_FFR_mono : forall n n' d, 0 <= n <= n' -> 0 <= PJ_FFR n d <= PJ_FFR n' d.
Proof.
  intros n n' d H. unfold PJ_FFR. destruct (0 <=? d).
  - pose proof (RCF0 (d + 1)). pose proof (KCF0 (d + 1)). pose proof (KS0 d).
    pose proof (rate12_nonneg (Z.max (RCF (d + 1)) (RS d)) n ltac:(lia) ltac:(lia)). pose proof (rate12_mono_n (Z.max (RCF (d + 1)) (RS d)) n n' ltac:(lia) H). lia.
  - pose proof (FFRg_i_mono n n' d H). pose proof (FFRs_i_mono n n' d H). lia.
Qed.
Lemma PJ_CNT_joint : forall a b, 0 <= a -> 0 <= b -> CNTg_i a + CNTs_i b <= PJ_CNT (a + b).
Proof.
  intros a b Ha Hb. unfold PJ_CNT, CNTg_i. pose proof (CNTc_i_le a Ha). pose proof (CNTs_i_le b Hb).
  pose proof (rate12_mono_r RCC 8 a ltac:(unfold RCC; lia) Ha). pose proof (rate12_sadd 8 a b). lia.
Qed.
Lemma PJ_PHI_joint : forall a b, 0 <= a -> 0 <= b -> PHIg_i a + PHIs_i b <= PJ_PHI (a + b).
Proof.
  intros a b Ha Hb. unfold PJ_PHI, PHIg_i. pose proof (PHIc_i_le a Ha). pose proof (PHIs_i_le b Hb).
  pose proof (rate12_mono_r RCP 2656 a ltac:(vm_compute; discriminate) Ha). pose proof (rate12_sadd 2656 a b). lia.
Qed.
Lemma PJ_FFR_joint : forall a b d, 0 <= a -> 0 <= b -> FFRg_i a d + FFRs_i b d <= PJ_FFR (a + b) d.
Proof.
  intros a b d Ha Hb. unfold PJ_FFR. destruct (0 <=? d) eqn:E.
  - apply Z.leb_le in E. unfold FFRg_i, A_pkcs7_getcerts.FFRg.
    pose proof (FFRc_i_le a (d + 1) Ha ltac:(lia)). pose proof (FFRs_i_le b d Hb).
    pose proof (rate12_mono_r (RCF (d + 1)) (Z.max (RCF (d + 1)) (RS d)) a ltac:(lia) Ha).
    pose proof (rate12_mono_r (RS d) (Z.max (RCF (d + 1)) (RS d)) b ltac:(lia) Hb).
    pose proof (rate12_sadd (Z.max (RCF (d + 1)) (RS d)) a b). lia.
  - pose proof (FFRg_i_mono a (a + b) d ltac:(lia)). pose proof (FFRs_i_mono b (a + b) d ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHIf_i : Z -> Z := A_pkcs7_free.PHIp7f A_pk_free.PHIpk.
Definition FFRf_i : Z -> Z -> Z := A_pkcs7_free.FFRp7f A_pk_free.FFRpk.
Definition CNTp_i : Z -> Z := A_pkcs7_parse_C.CNTp PJ_CNT.
Definition PHIp_i : Z -> Z := A_pkcs7_parse_C.PHIp PJ_PHI PJ_CNT PHIf_i.
Definition FFRp_i : Z -> Z -> Z := A_pkcs7_parse_C.FFRp PJ_FFR PJ_CNT FFRf_i.
Definition PHItop : Z -> Z := A_fuzz_entry.PHI PHIp_i CNTp_i PHIf_i.
Definition FFRtop : Z -> Z := A_fuzz_entry.FFR FFRp_i CNTp_i FFRf_i.

Definition KTOP : Z := 5 + (KCF 3 + KS 2) + 2 * (42 + 3 * (KCC + 2)).
Definition FFFRc : Z := 15 * 2 ^ 26 + KTOP.
Definition FPHIc : Z := 2 * 2 ^ 26 + 14853428566 + (KCP + 400).

Lemma RS_2 : RS 2 = 120. Proof. vm_compute. reflexivity. Qed.

Lemma FFRtop_max : forall n, 0 <= n < 2 ^ 26 -> 0 <= FFRtop n <= FFFRc.
Proof.
  intros n Hn. unfold FFRtop, A_fuzz_entry.FFR, FFRp_i, A_pkcs7_parse_C.FFRp, CNTp_i, A_pkcs7_parse_C.CNTp, FFRf_i, A_pkcs7_free.FFRp7f, A_pk_free.FFRpk.
  change (1 + 1) with 2. unfold PJ_FFR. change (0 <=? 2) with true. cbv iota. change (2 + 1) with 3. rewrite RCF_3, RS_2. change (Z.max 132 120) with 132.
  unfold PJ_CNT. change (fr_charge 0) with 3. change (Z.max 0 3) with 3. change (Z.max 0 (fr_charge 2)) with 5.
  pose proof (rate12_nonneg 8 n ltac:(lia) ltac:(lia)) as R8. pose proof (rate12_nonneg 132 n ltac:(lia) ltac:(lia)) as R132.
  pose proof (rate12_scale 6 8 n ltac:(lia)) as S1. pose proof (rate12_add 132 (6 * 8) n) as A1. change (132 + 6 * 8) with (12 * 15) in A1. rewrite (rate12_lin 15 n) in A1.
  pose proof KCC0. pose proof (KCF0 3). pose proof (KS0 2). unfold FFFRc, KTOP. lia.
Qed.

Lemma PHItop_max : forall n, 0 <= n < 2 ^ 26 -> 0 <= PHItop n <= FPHIc.
Proof.
  intros n Hn. unfold PHItop, A_fuzz_entry.PHI, PHIp_i, A_pkcs7_parse_C.PHIp, CNTp_i, A_pkcs7_parse_C.CNTp, PHIf_i, A_pkcs7_free.PHIp7f, A_pk_free.PHIpk, AVOL_CALL.
  unfold PJ_PHI. pose proof (rate12_nonneg 2656 n ltac:(lia) ltac:(lia)) as R0.
  assert (R1 : rate12 2656 n <= 14853428566).
  { unfold rate12. apply Z.div_le_upper_bound; [lia|]. lia. }
  pose proof KCP0. unfold FPHIc. lia.
Qed.

(* [comment removed for export] *)
Lemma HVF_closed : 402392064 + 2 ^ 28 + 4 * FPHIc + 8 * AVOL_CALL <= AVOL_MAX.
Proof. vm_compute. discriminate. Qed.
Lemma HFRF_closed : 63 + 4 * FFFRc + 16 <= FR_MAX.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[global] Hint Resolve PJ_PHI_mono PJ_FFR_mono PJ_CNT_mono PJ_PHI_joint PJ_FFR_joint PJ_CNT_joint
  XJ_PHI0 XJ_FFR0 XJ_CNT0 XJ_PHI_mono XJ_FFR_mono XJ_CNT_mono XJ_PHI_sadd XJ_FFR_sadd XJ_CNT_sadd
  XJ_PHIq_le XJ_FFRq_le XJ_CNTq_le XJ_PHIs_le XJ_FFRs_le XJ_CNTs_le XJ_PHIp_le XJ_FFRp_le XJ_CNTp_le XJ_PHIk_le XJ_FFRk_le XJ_CNTk_le
  CJ_PHI0 CJ_FFR0 CJ_CNT0 CJ_PHI_mono CJ_FFR_mono CJ_CNT_mono CJ_PHI_sadd CJ_FFR_sadd CJ_CNT_sadd
  CJ_PHIn_le CJ_FFRn_le CJ_CNTn_le CJ_PHIx_le CJ_FFRx_le CJ_CNTx_le
  PHIsan_mono FFRsan_mono CNTsan_mono FFRgs_mono FFRks_mono : alink_bud.
Ltac alink_rates :=
  first [ exact PJ_PHI_mono | exact PJ_FFR_mono | exact PJ_CNT_mono | exact PJ_PHI_joint | exact PJ_FFR_joint | exact PJ_CNT_joint
        | exact XJ_PHI0 | exact XJ_FFR0 | exact XJ_CNT0 | exact XJ_PHI_mono | exact XJ_FFR_mono | exact XJ_CNT_mono | exact XJ_PHI_sadd | exact XJ_FFR_sadd | exact XJ_CNT_sadd
        | exact XJ_PHIq_le | exact XJ_FFRq_le | exact XJ_CNTq_le | exact XJ_PHIs_le | exact XJ_FFRs_le | exact XJ_CNTs_le
        | exact XJ_PHIp_le | exact XJ_FFRp_le | exact XJ_CNTp_le | exact XJ_PHIk_le | exact XJ_FFRk_le | exact XJ_CNTk_le
        | exact CJ_PHI0 | exact CJ_FFR0 | exact CJ_CNT0 | exact CJ_PHI_mono | exact CJ_FFR_mono | exact CJ_CNT_mono | exact CJ_PHI_sadd | exact CJ_FFR_sadd | exact CJ_CNT_sadd
        | exact CJ_PHIn_le | exact CJ_FFRn_le | exact CJ_CNTn_le | exact CJ_PHIx_le | exact CJ_FFRx_le | exact CJ_CNTx_le
        | exact PHIsan_mono | exact FFRsan_mono | exact CNTsan_mono | exact FFRgs_mono | exact FFRks_mono
        | exact PHIc_i_mono | exact FFRc_i_mono | exact CNTc_i_mono | exact FFRg_i_mono | exact PHIs_i_mono | exact FFRs_i_mono | exact CNTs_i_mono
        | exact A_pk_parse_H.PKP_PHI0 | exact A_pk_parse_H.PKP_PHI_mono | exact A_pk_parse_H.PKP_FFR0 | exact A_pk_parse_H.PKP_FFR_mono | exact A_pk_parse_H.PKP_CNT0 | exact A_pk_parse_H.PKP_C24_0 ].
