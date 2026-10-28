(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_x509_get_name_A A_x509_parse_san_C A_x509_san_ext_bud A_x509_get_san A_x509_akid A_x509_policies_B
     A_asn1_trav A_asn1_seq_cb A_asn1_get_seq_of A_x509_crt_parse A_pk_parse_G0 A_pk_parse_H A_pk_free A_x509_crt_free A_x509_get_sig_alg.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_rates () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_sig_alg.X509_SIG_ALG_FFR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_G0.PKP_FFR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.FFRpk"; "Stdlib.ZArith.BinInt.Z.mul"; "KCC"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rate12 (r n : Z) : Z := (n * r) / 12.

Lemma rate12_nonneg : forall r n, 0 <= r -> 0 <= n -> 0 <= rate12 r n.
Proof. intros r n Hr Hn. unfold rate12. apply Z.div_pos; nia. Qed.
Lemma rate12_mono_n : forall r a b, 0 <= r -> 0 <= a <= b -> rate12 r a <= rate12 r b.
Proof. intros r a b Hr H. unfold rate12. apply Z.div_le_mono; nia. Qed.
Lemma rate12_mono_r : forall r r' n, r <= r' -> 0 <= n -> rate12 r n <= rate12 r' n.
Proof. intros r r' n Hr Hn. unfold rate12. apply Z.div_le_mono; nia. Qed.
Lemma rate12_sadd : forall r a b, rate12 r a + rate12 r b <= rate12 r (a + b).
Proof.
  intros r a b. unfold rate12. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le (a * r) 12 ltac:(lia)). pose proof (Z.mul_div_le (b * r) 12 ltac:(lia)). nia.
Qed.
Lemma rate12_add : forall r1 r2 n, rate12 r1 n + rate12 r2 n <= rate12 (r1 + r2) n.
Proof.
  intros r1 r2 n. unfold rate12. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le (n * r1) 12 ltac:(lia)). pose proof (Z.mul_div_le (n * r2) 12 ltac:(lia)). nia.
Qed.
Lemma rate12_scale : forall k r n, 0 <= k -> k * rate12 r n <= rate12 (k * r) n.
Proof.
  intros k r n Hk. unfold rate12. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (n * r) 12 ltac:(lia)). nia.
Qed.
Lemma rate12_lin : forall c n, rate12 (12 * c) n = c * n.
Proof. intros c n. unfold rate12. replace (n * (12 * c)) with (c * n * 12) by lia. apply Z.div_mul. lia. Qed.
(* [comment removed for export] *)
Lemma rate12_div6 : forall c n, 0 <= c -> 0 <= n -> (n / 6) * c <= rate12 (2 * c) n.
Proof. intros c n Hc Hn. unfold rate12. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le n 6 ltac:(lia)). nia. Qed.
Lemma rate12_div4 : forall c n, 0 <= c -> 0 <= n -> (n / 4) * c <= rate12 (3 * c) n.
Proof. intros c n Hc Hn. unfold rate12. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le n 4 ltac:(lia)). nia. Qed.
Lemma rate12_div2 : forall c n, 0 <= c -> 0 <= n -> (n / 2) * c <= rate12 (6 * c) n.
Proof. intros c n Hc Hn. unfold rate12. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le n 2 ltac:(lia)). nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation PHIn := A_x509_get_name_A.PHIn.
Local Notation FFRn := A_x509_get_name_A.FFRn.
Local Notation CNTn := A_x509_get_name_A.CNTn.
(* [comment removed for export] *)
Definition FFRps_n : Z -> Z -> Z := A_x509_parse_san_C.FFRps FFRn.
(* [comment removed for export] *)
Definition PHIsan : Z -> Z := A_x509_san_ext_bud.PHIx PHIn CNTn.
Definition FFRsan : Z -> Z -> Z := A_x509_san_ext_bud.FFRx FFRps_n CNTn.
Definition CNTsan : Z -> Z := A_x509_san_ext_bud.CNTx.
(* [comment removed for export] *)
Definition FFRgs : Z -> Z -> Z := A_x509_get_san.FFRg FFRsan.
Definition FFRks : Z -> Z -> Z := A_x509_akid.FFRk FFRsan.

Lemma FFRps_n_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRps_n n d <= FFRps_n n' d.
Proof. intros n n' d H. unfold FFRps_n, A_x509_parse_san_C.FFRps. exact (A_x509_get_name_A.FFRn_mono n n' (d + 1) H). Qed.
Lemma PHIsan_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsan n <= PHIsan n'.
Proof. exact (A_x509_san_ext_bud.PHIx_mono PHIn CNTn A_x509_get_name_A.PHIn_mono A_x509_get_name_A.CNTn_mono). Qed.
Lemma FFRsan_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsan n d <= FFRsan n' d.
Proof. exact (A_x509_san_ext_bud.FFRx_mono FFRps_n CNTn FFRps_n_mono A_x509_get_name_A.CNTn_mono). Qed.
Lemma CNTsan_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsan n <= CNTsan n'.
Proof. exact A_x509_san_ext_bud.CNTx_mono. Qed.
Lemma FFRgs_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRgs n d <= FFRgs n' d.
Proof. intros n n' d H. unfold FFRgs, A_x509_get_san.FFRg. exact (FFRsan_mono n n' (d + 1) H). Qed.
Lemma FFRks_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRks n d <= FFRks n' d.
Proof. intros n n' d H. unfold FFRks, A_x509_akid.FFRk. exact (FFRsan_mono n n' (d + 1) H). Qed.

(* [comment removed for export] *)
Definition RN (e : Z) : Z := 2 * (Z.max 0 (fr_charge (e + 1)) + fr_charge 0).          (* [comment removed for export] *)
Definition RSAN (t : Z) : Z := RN (t + 2) + 2 * fr_charge 0 + 6 * (Z.max 0 (fr_charge (t + 1)) + fr_charge 0).   (* [comment removed for export] *)
Definition RPOL (e : Z) : Z := 3 * Z.max 0 (fr_charge (e + 1)).                        (* [comment removed for export] *)
Definition RSEQ : Z := 6 * fr_charge 0.                                                (* [comment removed for export] *)

Lemma RN0 : forall e, 0 <= RN e. Proof. intros e. unfold RN, fr_charge. lia. Qed.

Lemma FFRn_rate : forall a e, 0 <= a -> FFRn a e <= rate12 (RN e) a.
Proof.
  intros a e Ha. unfold A_x509_get_name_A.FFRn, RN. set (M := Z.max 0 (fr_charge (e + 1))). assert (M0 : 0 <= M) by (subst M; lia).
  pose proof (rate12_div6 (M + fr_charge 0) a ltac:(unfold fr_charge; lia) Ha) as H. lia.
Qed.
Lemma PHIn_rate : forall a, 0 <= a -> PHIn a <= rate12 256 a.
Proof. intros a Ha. unfold A_x509_get_name_A.PHIn, AVOL_CALL. pose proof (rate12_div6 128 a ltac:(lia) Ha) as H. change (2 * 128) with 256 in H. lia. Qed.
Lemma CNTn_rate : forall a, 0 <= a -> CNTn a <= rate12 2 a.
Proof. intros a Ha. unfold A_x509_get_name_A.CNTn. pose proof (rate12_div6 1 a ltac:(lia) Ha) as H. change (2 * 1) with 2 in H. lia. Qed.

Lemma FFRsan_rate : forall a t, 0 <= a -> FFRsan a t <= rate12 (RSAN t) a.
Proof.
  intros a t Ha. unfold FFRsan, A_x509_san_ext_bud.FFRx, FFRps_n, A_x509_parse_san_C.FFRps, RSAN.
  pose proof (FFRn_rate a (t + 1 + 1) Ha) as H1. replace (t + 1 + 1) with (t + 2) in H1 by lia.
  replace (t + 1 + 1) with (t + 2) by lia.
  set (M := Z.max 0 (fr_charge (t + 1))). assert (M0 : 0 <= M) by (subst M; lia).
  pose proof (rate12_div6 (fr_charge 0) a ltac:(unfold fr_charge; lia) Ha) as H2. unfold A_x509_get_name_A.CNTn.
  pose proof (rate12_div2 (M + fr_charge 0) a ltac:(unfold fr_charge; lia) Ha) as H3.
  pose proof (rate12_add (RN (t + 2)) (2 * fr_charge 0) a) as A1.
  pose proof (rate12_add (RN (t + 2) + 2 * fr_charge 0) (6 * (M + fr_charge 0)) a) as A2.
  lia.
Qed.
Lemma PHIsan_rate : forall a, 0 <= a -> PHIsan a <= rate12 256 a.
Proof. intros a Ha. unfold PHIsan, A_x509_san_ext_bud.PHIx, AVOL_CALL. pose proof (PHIn_rate a Ha). lia. Qed.
Lemma CNTsan_rate : forall a, 0 <= a -> CNTsan a <= rate12 6 a.
Proof. intros a Ha. unfold CNTsan, A_x509_san_ext_bud.CNTx. pose proof (rate12_div2 1 a ltac:(lia) Ha) as H. change (6 * 1) with 6 in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RXP : Z := 384.                                        (* [comment removed for export] *)
Definition RXF (e : Z) : Z := Z.max (Z.max RSEQ (RSAN (e + 2))) (RPOL (e + 1)).
Definition RXC : Z := 6.
Definition XJ_PHI (a : Z) : Z := rate12 RXP a.
Definition XJ_FFR (a e : Z) : Z := rate12 (RXF e) a.
Definition XJ_CNT (a : Z) : Z := rate12 RXC a.

Lemma RXF0 : forall e, 0 <= RXF e. Proof. intros e. unfold RXF, RSEQ, fr_charge. lia. Qed.

Lemma XJ_PHI0 : forall a, 0 <= a -> 0 <= XJ_PHI a. Proof. intros a Ha. apply rate12_nonneg; [unfold RXP; lia| exact Ha]. Qed.
Lemma XJ_FFR0 : forall a e, 0 <= a -> 0 <= XJ_FFR a e. Proof. intros a e Ha. apply rate12_nonneg; [apply RXF0| exact Ha]. Qed.
Lemma XJ_CNT0 : forall a, 0 <= a -> 0 <= XJ_CNT a. Proof. intros a Ha. apply rate12_nonneg; [unfold RXC; lia| exact Ha]. Qed.
Lemma XJ_PHI_mono : forall a b, 0 <= a <= b -> XJ_PHI a <= XJ_PHI b. Proof. intros a b H. apply rate12_mono_n; [unfold RXP; lia| exact H]. Qed.
Lemma XJ_FFR_mono : forall a b e, 0 <= a <= b -> XJ_FFR a e <= XJ_FFR b e. Proof. intros a b e H. apply rate12_mono_n; [apply RXF0| exact H]. Qed.
Lemma XJ_CNT_mono : forall a b, 0 <= a <= b -> XJ_CNT a <= XJ_CNT b. Proof. intros a b H. apply rate12_mono_n; [unfold RXC; lia| exact H]. Qed.
Lemma XJ_PHI_sadd : forall a b, 0 <= a -> 0 <= b -> XJ_PHI a + XJ_PHI b <= XJ_PHI (a + b). Proof. intros a b _ _. apply rate12_sadd. Qed.
Lemma XJ_FFR_sadd : forall a b e, 0 <= a -> 0 <= b -> XJ_FFR a e + XJ_FFR b e <= XJ_FFR (a + b) e. Proof. intros a b e _ _. apply rate12_sadd. Qed.
Lemma XJ_CNT_sadd : forall a b, 0 <= a -> 0 <= b -> XJ_CNT a + XJ_CNT b <= XJ_CNT (a + b). Proof. intros a b _ _. apply rate12_sadd. Qed.

(* [comment removed for export] *)
Lemma XJ_PHIq_le : forall a, 0 <= a -> A_asn1_trav.TRAV_PHI a <= XJ_PHI a.
Proof.
  intros a Ha. unfold A_asn1_trav.TRAV_PHI, A_asn1_seq_cb.ASN1_SEQ_CB_PHI, AVOL_CALL, XJ_PHI, RXP.
  pose proof (rate12_div2 (2 * 32 + 0) a ltac:(lia) Ha) as H. change (6 * (2 * 32 + 0)) with 384 in H. exact H.
Qed.
Lemma XJ_FFRq_le : forall a e, 0 <= a -> A_asn1_get_seq_of.FFRq a (e + 1) <= XJ_FFR a e.
Proof.
  intros a e Ha. unfold A_asn1_get_seq_of.FFRq, A_asn1_trav.TRAV_FFR, XJ_FFR.
  pose proof (rate12_div2 (fr_charge 0) a ltac:(unfold fr_charge; lia) Ha) as H.
  pose proof (rate12_mono_r (6 * fr_charge 0) (RXF e) a ltac:(unfold RXF, RSEQ; lia) Ha). lia.
Qed.
Lemma XJ_CNTq_le : forall a, 0 <= a -> A_asn1_get_seq_of.CNTq a <= XJ_CNT a.
Proof. intros a Ha. unfold A_asn1_get_seq_of.CNTq, XJ_CNT, RXC. pose proof (rate12_div2 1 a ltac:(lia) Ha) as H. change (6 * 1) with 6 in H. lia. Qed.
(* [comment removed for export] *)
Lemma XJ_PHIs_le : forall a, 0 <= a -> PHIsan a <= XJ_PHI a.
Proof. intros a Ha. pose proof (PHIsan_rate a Ha). pose proof (rate12_mono_r 256 RXP a ltac:(unfold RXP; lia) Ha). unfold XJ_PHI. lia. Qed.
Lemma XJ_FFRs_le : forall a e, 0 <= a -> FFRgs a (e + 1) <= XJ_FFR a e.
Proof.
  intros a e Ha. unfold FFRgs, A_x509_get_san.FFRg, XJ_FFR. pose proof (FFRsan_rate a (e + 1 + 1) Ha) as H. replace (e + 1 + 1) with (e + 2) in * by lia.
  pose proof (rate12_mono_r (RSAN (e + 2)) (RXF e) a ltac:(unfold RXF; lia) Ha). lia.
Qed.
Lemma XJ_CNTs_le : forall a, 0 <= a -> CNTsan a <= XJ_CNT a.
Proof. intros a Ha. unfold XJ_CNT, RXC. exact (CNTsan_rate a Ha). Qed.
(* [comment removed for export] *)
Lemma XJ_PHIp_le : forall a, 0 <= a -> A_x509_policies_B.PHIpol a <= XJ_PHI a.
Proof. intros a Ha. unfold A_x509_policies_B.PHIpol. exact (XJ_PHI0 a Ha). Qed.
Lemma XJ_FFRp_le : forall a e, 0 <= a -> A_x509_policies_B.FFRpol a (e + 1) <= XJ_FFR a e.
Proof.
  intros a e Ha. unfold A_x509_policies_B.FFRpol, XJ_FFR. set (M := Z.max 0 (fr_charge (e + 1 + 1))). assert (M0 : 0 <= M) by (subst M; lia).
  pose proof (rate12_div4 M a M0 Ha) as H.
  pose proof (rate12_mono_r (3 * M) (RXF e) a ltac:(unfold RXF, RPOL; subst M; lia) Ha). lia.
Qed.
Lemma XJ_CNTp_le : forall a, 0 <= a -> A_x509_policies_B.CNTpol a <= XJ_CNT a.
Proof.
  intros a Ha. unfold A_x509_policies_B.CNTpol, XJ_CNT, RXC. pose proof (rate12_div4 1 a ltac:(lia) Ha) as H. change (3 * 1) with 3 in H.
  pose proof (rate12_mono_r 3 6 a ltac:(lia) Ha). lia.
Qed.
(* [comment removed for export] *)
Lemma XJ_PHIk_le : forall a, 0 <= a -> PHIsan a <= XJ_PHI a. Proof. exact XJ_PHIs_le. Qed.
Lemma XJ_FFRk_le : forall a e, 0 <= a -> FFRks a (e + 1) <= XJ_FFR a e.
Proof. intros a e Ha. unfold FFRks, A_x509_akid.FFRk. exact (XJ_FFRs_le a e Ha). Qed.
Lemma XJ_CNTk_le : forall a, 0 <= a -> CNTsan a <= XJ_CNT a. Proof. exact XJ_CNTs_le. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RJP : Z := 384.
Definition RJF (e : Z) : Z := Z.max (RN (e + 1)) (RXF (e + 1)).
Definition RJC : Z := 6.
Definition CJ_PHI (a : Z) : Z := rate12 RJP a.
Definition CJ_FFR (a e : Z) : Z := rate12 (RJF e) a.
Definition CJ_CNT (a : Z) : Z := rate12 RJC a.

Lemma RJF0 : forall e, 0 <= RJF e. Proof. intros e. unfold RJF. pose proof (RN0 (e + 1)). lia. Qed.

Lemma CJ_PHI0 : forall a, 0 <= a -> 0 <= CJ_PHI a. Proof. intros a Ha. apply rate12_nonneg; [unfold RJP; lia| exact Ha]. Qed.
Lemma CJ_FFR0 : forall a e, 0 <= a -> 0 <= CJ_FFR a e. Proof. intros a e Ha. apply rate12_nonneg; [apply RJF0| exact Ha]. Qed.
Lemma CJ_CNT0 : forall a, 0 <= a -> 0 <= CJ_CNT a. Proof. intros a Ha. apply rate12_nonneg; [unfold RJC; lia| exact Ha]. Qed.
Lemma CJ_PHI_mono : forall a b, 0 <= a <= b -> CJ_PHI a <= CJ_PHI b. Proof. intros a b H. apply rate12_mono_n; [unfold RJP; lia| exact H]. Qed.
Lemma CJ_FFR_mono : forall a b e, 0 <= a <= b -> CJ_FFR a e <= CJ_FFR b e. Proof. intros a b e H. apply rate12_mono_n; [apply RJF0| exact H]. Qed.
Lemma CJ_CNT_mono : forall a b, 0 <= a <= b -> CJ_CNT a <= CJ_CNT b. Proof. intros a b H. apply rate12_mono_n; [unfold RJC; lia| exact H]. Qed.
Lemma CJ_PHI_sadd : forall a b, 0 <= a -> 0 <= b -> CJ_PHI a + CJ_PHI b <= CJ_PHI (a + b). Proof. intros a b _ _. apply rate12_sadd. Qed.
Lemma CJ_FFR_sadd : forall a b e, 0 <= a -> 0 <= b -> CJ_FFR a e + CJ_FFR b e <= CJ_FFR (a + b) e. Proof. intros a b e _ _. apply rate12_sadd. Qed.
Lemma CJ_CNT_sadd : forall a b, 0 <= a -> 0 <= b -> CJ_CNT a + CJ_CNT b <= CJ_CNT (a + b). Proof. intros a b _ _. apply rate12_sadd. Qed.
(* [comment removed for export] *)
Lemma CJ_PHIn_le : forall a, 0 <= a -> PHIn a <= CJ_PHI a.
Proof. intros a Ha. pose proof (PHIn_rate a Ha). pose proof (rate12_mono_r 256 RJP a ltac:(unfold RJP; lia) Ha). unfold CJ_PHI. lia. Qed.
Lemma CJ_FFRn_le : forall a e, 0 <= a -> FFRn a (e + 1) <= CJ_FFR a e.
Proof. intros a e Ha. pose proof (FFRn_rate a (e + 1) Ha). pose proof (rate12_mono_r (RN (e + 1)) (RJF e) a ltac:(unfold RJF; lia) Ha). unfold CJ_FFR. lia. Qed.
Lemma CJ_CNTn_le : forall a, 0 <= a -> CNTn a <= CJ_CNT a.
Proof. intros a Ha. pose proof (CNTn_rate a Ha). pose proof (rate12_mono_r 2 RJC a ltac:(unfold RJC; lia) Ha). unfold CJ_CNT. lia. Qed.
(* [comment removed for export] *)
Lemma CJ_PHIx_le : forall a, 0 <= a -> XJ_PHI a <= CJ_PHI a.
Proof. intros a Ha. unfold XJ_PHI, CJ_PHI, RXP, RJP. lia. Qed.
Lemma CJ_FFRx_le : forall a e, 0 <= a -> XJ_FFR a (e + 1) <= CJ_FFR a e.
Proof. intros a e Ha. unfold XJ_FFR, CJ_FFR. apply rate12_mono_r; [unfold RJF; lia| exact Ha]. Qed.
Lemma CJ_CNTx_le : forall a, 0 <= a -> XJ_CNT a <= CJ_CNT a.
Proof. intros a Ha. unfold XJ_CNT, CJ_CNT, RXC, RJC. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation PKP_PHI := A_pk_parse_G0.PKP_PHI.
Local Notation PKP_FFR := A_pk_parse_G0.PKP_FFR.
Local Notation PKP_CNT := A_pk_parse_G0.PKP_CNT.
Local Notation PHIcf_i := (A_x509_crt_free.PHIcf A_pk_free.PHIpk).
Local Notation FFRcf_i := (A_x509_crt_free.FFRcf A_pk_free.FFRpk).
Definition PHIc_i : Z -> Z := A_x509_crt_parse.PHIc PKP_PHI PKP_CNT PHIcf_i CJ_PHI CJ_CNT.
Definition FFRc_i : Z -> Z -> Z := A_x509_crt_parse.FFRc PKP_FFR PKP_CNT FFRcf_i CJ_FFR CJ_CNT.
Definition CNTc_i : Z -> Z := A_x509_crt_parse.CNTc PKP_CNT CJ_CNT.

(* [comment removed for export] *)
Definition RCC : Z := 6.
Definition KCC : Z := 2 + PKP_CNT.
Definition RCF (d : Z) : Z := RJF d + 3 * RCC.                   (* [comment removed for export] *)
Definition KCF (d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_x509_rates ()) "(0.(0.(0.(0.(1.=(2.(0.O1.+1.)))(1.=(3.=)))(4.=(0.O1.+1.)))(5.==))(6.(2.=)$7.))")
(* [comment removed for export] *).
Definition RCP : Z := 12 * 22 + RJP.                             (* [comment removed for export] *)
Definition KCP : Z := AVOL_CALL + A_x509_get_sig_alg.X509_SIG_ALG_PHI + PKP_PHI 0 + A_pk_free.PHIpk 0.

Lemma CNTc_i_le : forall n, 0 <= n -> CNTc_i n <= rate12 RCC n + KCC.
Proof. intros n Hn. unfold CNTc_i, A_x509_crt_parse.CNTc, CJ_CNT, RJC, RCC, KCC. lia. Qed.
Lemma CNTc_i_mono : forall n n', 0 <= n <= n' -> 0 <= CNTc_i n <= CNTc_i n'.
Proof.
  intros n n' H. unfold CNTc_i, A_x509_crt_parse.CNTc, PKP_CNT. pose proof (CJ_CNT0 n ltac:(lia)). pose proof (CJ_CNT_mono n n' H). lia.
Qed.

Lemma PKP_PHI_lin : forall n, PKP_PHI n = PKP_PHI 0 + 20 * n.
Proof.
  intros n. unfold A_pk_parse_G0.PKP_PHI, A_rsa_parse_pubkey.RSA_PP_PHI, A_pk_ecparams_stmt.pk_ecparams_PHI, A_pk_ecc_set_pubkey.pk_set_pubkey_PHI,
    A_ecp_stmtA.point_read_PHIn, A_mpi_read_binary_stmt.MPI_RB_PHI. lia.
Qed.
Lemma PHIc_i_le : forall n, 0 <= n -> PHIc_i n <= rate12 RCP n + KCP.
Proof.
  intros n Hn. unfold PHIc_i, A_x509_crt_parse.PHIc, A_x509_crt_parse.KVc, A_x509_crt_free.PHIcf, CJ_PHI, RCP, KCP.
  rewrite (PKP_PHI_lin n). replace (A_pk_free.PHIpk (A_x509_crt_parse.CNTc PKP_CNT CJ_CNT n)) with (A_pk_free.PHIpk 0) by reflexivity.
  pose proof (rate12_add (12 * 22) RJP n) as A1. rewrite (rate12_lin 22 n) in A1. lia.
Qed.
Lemma PHIc_i_mono : forall n n', 0 <= n <= n' -> 0 <= PHIc_i n <= PHIc_i n'.
Proof.
  intros n n' H. unfold PHIc_i, A_x509_crt_parse.PHIc, A_x509_crt_parse.KVc, A_x509_crt_free.PHIcf.
  replace (A_pk_free.PHIpk (A_x509_crt_parse.CNTc PKP_CNT CJ_CNT n)) with (A_pk_free.PHIpk 0) by reflexivity.
  replace (A_pk_free.PHIpk (A_x509_crt_parse.CNTc PKP_CNT CJ_CNT n')) with (A_pk_free.PHIpk 0) by reflexivity.
  pose proof (A_pk_parse_H.PKP_PHI0 n ltac:(lia)). pose proof (A_pk_parse_H.PKP_PHI_mono n n' H).
  pose proof (CJ_PHI0 n ltac:(lia)). pose proof (CJ_PHI_mono n n' H).
  unfold A_x509_get_sig_alg.X509_SIG_ALG_PHI, A_pk_free.PHIpk, AVOL_CALL. lia.
Qed.

Lemma FFRc_i_le : forall n d, 0 <= n -> 0 <= d -> FFRc_i n d <= rate12 (RCF d) n + KCF d.
Proof.
  intros n d Hn Hd. unfold FFRc_i, A_x509_crt_parse.FFRc, A_x509_crt_parse.KFc, A_x509_crt_free.FFRcf, A_x509_crt_parse.CNTc, CJ_FFR, CJ_CNT, RCF, KCF, KCC, RJC, RCC.
  replace (PKP_FFR n (d + 1)) with (PKP_FFR 0 (d + 1)) by reflexivity.
  replace (A_pk_free.FFRpk (2 + PKP_CNT + rate12 6 n) 0) with (A_pk_free.FFRpk 0 0) by reflexivity.
  replace (Z.max 0 (fr_charge 0)) with (fr_charge 0) by (unfold fr_charge; lia).
  pose proof (rate12_scale 3 6 n ltac:(lia)) as S1. pose proof (rate12_add (RJF d) (3 * 6) n) as A1.
  unfold fr_charge in *. lia.
Qed.
Lemma FFRc_i_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRc_i n d <= FFRc_i n' d.
Proof.
  intros n n' d H. unfold FFRc_i, A_x509_crt_parse.FFRc, A_x509_crt_parse.KFc, A_x509_crt_free.FFRcf.
  pose proof (CNTc_i_mono n n' H) as CM. unfold CNTc_i in CM.
  replace (PKP_FFR n (d + 1)) with (PKP_FFR 0 (d + 1)) by reflexivity. replace (PKP_FFR n' (d + 1)) with (PKP_FFR 0 (d + 1)) by reflexivity.
  replace (A_pk_free.FFRpk (A_x509_crt_parse.CNTc PKP_CNT CJ_CNT n) 0) with (A_pk_free.FFRpk 0 0) by reflexivity.
  replace (A_pk_free.FFRpk (A_x509_crt_parse.CNTc PKP_CNT CJ_CNT n') 0) with (A_pk_free.FFRpk 0 0) by reflexivity.
  pose proof (A_pk_parse_H.PKP_FFR0 0 (d + 1) ltac:(lia)). pose proof (CJ_FFR0 n d ltac:(lia)). pose proof (CJ_FFR_mono n n' d H).
  assert (F0 : 0 <= A_pk_free.FFRpk 0 0) by (unfold A_pk_free.FFRpk, fr_charge; lia).
  replace (Z.max 0 (fr_charge 0)) with 3 by (unfold fr_charge; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma RCF_3 : RCF 3 = 132. Proof. vm_compute. reflexivity. Qed.
