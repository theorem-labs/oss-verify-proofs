(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AEvtS AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib A_x509_seq_stmtsE A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_x509_get_sig_alg A_pk_parse_G0 A_x509_crt_ext_A A_x509_crt_free A_pk_free A_x509_san_ext_A A_x509_san_ext_bud A_x509_parse_san_C A_x509_get_name_A A_asn1_seq_cb A_asn1_trav A_asn1_get_seq_of A_asn1_get_seq_of_A
  A_x509_policies_A A_x509_policies_B A_x509_get_san A_x509_get_san_A A_x509_akid A_x509_akid_A A_x509_parse_san_A.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_link_adapt () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "J4.j41"; "Stdlib.ZArith.BinInt.Z.add"; "J4.j42"; "j42"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_seq_of.FFRq"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_san.FFRg"; "FFRsan"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.FFRpol"; "RocqVerifyHarness.AgentSubmission.B.A_x509_akid.FFRk"; "j41_facts"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_trav.TRAV_PHI"; "PHIsan"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.PHIpol"; "TRAV_PHI_mono"; "PHIsan_mono"; "PHIpol_mono"; "TRAV_PHI_sadd"; "PHIsan_sadd"; "PHIpol_sadd"; "j42_facts"; "FFRq_mono"; "FFRgs_mono"; "FFRpol_mono"; "FFRks_mono"; "FFRq_sadd"; "FFRgs_sadd"; "FFRpol_sadd"; "FFRks_sadd"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_seq_of.CNTq"; "CNTsan"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.CNTpol"; "CNTq_mono"; "CNTsan_mono"; "CNTpol_mono"; "CNTq_sadd"; "CNTsan_sadd"; "CNTpol_sadd"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.PHIn"; "PHIext"; "Z1"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.PHIn_mono"; "PHIext_mono1"; "Z1_mono"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.PHIn_sadd"; "PHIext_sadd"; "Z1_sadd"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.FFRn"; "FFRext"; "Z2"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.FFRn_mono"; "FFRext_mono2"; "Z2_mono"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.FFRn_sadd"; "FFRext_sadd"; "Z2_sadd"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.CNTn"; "CNText"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.CNTn_mono"; "CNText_mono1"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.CNTn_sadd"; "CNText_sadd"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_seq_of_A.STKq"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_san_A.STKg"; "STKsanx"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_A.STKpol"; "RocqVerifyHarness.AgentSubmission.B.A_x509_akid_A.STKk"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_sig_alg.X509_SIG_ALG_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_setsh"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.STKn"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_G0.PKP_STK"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_ext_A.STKx"; "STKext"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_free.STKcf"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.STKpk"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_free.PHIcf"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.PHIpk"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_free.FFRcf"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.FFRpk"].


Definition ffr_clamp (F : Z -> Z -> Z) (n d : Z) : Z := F n (Z.max 0 d).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHIsan : Z -> Z := A_x509_san_ext_bud.PHIx A_x509_get_name_A.PHIn A_x509_get_name_A.CNTn.
Definition FFRsan : Z -> Z -> Z := A_x509_san_ext_bud.FFRx (A_x509_parse_san_C.FFRps A_x509_get_name_A.FFRn) A_x509_get_name_A.CNTn.
Definition CNTsan : Z -> Z := A_x509_san_ext_bud.CNTx.
Lemma PHIsan_mono : mono1 PHIsan.
Proof. exact (A_x509_san_ext_bud.PHIx_mono _ _ A_x509_get_name_A.PHIn_mono A_x509_get_name_A.CNTn_mono). Qed.
Lemma PHIsan_sadd : sadd1 PHIsan.
Proof. exact (A_x509_san_ext_bud.PHIx_sadd _ _ A_x509_get_name_A.PHIn_sadd A_x509_get_name_A.CNTn_sadd). Qed.
Lemma FFRsan_mono : mono2 FFRsan.
Proof. exact (A_x509_san_ext_bud.FFRx_mono _ _ (FFRps_mono _ A_x509_get_name_A.FFRn_mono) A_x509_get_name_A.CNTn_mono). Qed.
Lemma FFRsan_sadd : sadd2 FFRsan.
Proof. exact (A_x509_san_ext_bud.FFRx_sadd _ _ (FFRps_sadd _ A_x509_get_name_A.FFRn_sadd) A_x509_get_name_A.CNTn_sadd). Qed.
Lemma CNTsan_mono : mono1 CNTsan.
Proof. exact A_x509_san_ext_bud.CNTx_mono. Qed.
Lemma CNTsan_sadd : sadd1 CNTsan.
Proof. exact A_x509_san_ext_bud.CNTx_sadd. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L2431248216.5 L51796692231.5L56910101129.500000800=00ES1n2n'1HS1k1KS1n2n'1H". (* [comment removed for export] *)
Lemma div_mono_nn : forall k, 0 < k -> forall n n', 0 <= n <= n' -> 0 <= n / k <= n' / k.
Proof. intros k K n n' H. split; [apply Z.div_pos; lia| apply Z.div_le_mono; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020=L1446784477.7L1446947031.600000900>S1k1K1a1AS1k1K". (* [comment removed for export] *)
Lemma div_sadd : forall k, 0 < k -> forall a b, 0 <= a -> 0 <= b -> a / k + b / k <= (a + b) / k.
Proof.
  intros k K a b A B. pose proof (Z.div_mod a k ltac:(lia)). pose proof (Z.div_mod b k ltac:(lia)).
  pose proof (Z.mod_pos_bound a k K). pose proof (Z.mod_pos_bound b k K).
  apply Z.div_le_lower_bound; [exact K|]. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section J4.
  Variables (P1 P2 P3 P4 : Z -> Z) (F1 F2 F3 F4 : Z -> Z -> Z).
  Hypothesis M1 : mono1 P1. Hypothesis M2 : mono1 P2. Hypothesis M3 : mono1 P3. Hypothesis M4 : mono1 P4.
  Hypothesis S1 : sadd1 P1. Hypothesis S2 : sadd1 P2. Hypothesis S3 : sadd1 P3. Hypothesis S4 : sadd1 P4.
  Hypothesis N1 : mono2 F1. Hypothesis N2 : mono2 F2. Hypothesis N3 : mono2 F3. Hypothesis N4 : mono2 F4.
  Hypothesis T1 : sadd2 F1. Hypothesis T2 : sadd2 F2. Hypothesis T3 : sadd2 F3. Hypothesis T4 : sadd2 F4.
  Definition j41 (n : Z) : Z := P1 n + P2 n + P3 n + P4 n.
  Definition j42 (n e : Z) : Z := F1 n (e + 1) + F2 n (e + 1) + F3 n (e + 1) + F4 n (e + 1).
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L12656237039.30L26841586358.30L27674536281.30L29954497180.30L30947718573.26L30947864614.27L30949952542.28L30949952925.29L36332329362.30L51638007752.31L53353327478.3200000H00_01601M01R01W01\01a02;02X034S2P12P22P32P41a2H02H12H2S2P12P22P32P41a1H2H02H1S2P12P22P32P41a1H2H02H2S2P12P22P32P41a1H2H12H2S1a1AS1a1AS1a1AS1a1AS2P12P22P32P41a1H2H02H12H2S2P12P22P32P41a1b2H02H12H22H3S2P12P22P32P41a1b1H2H02H12H2". (* [comment removed for export] *)
  #[using="M1 M2 M3 M4 S1 S2 S3 S4"] Lemma j41_facts : ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(0.Pa,$1.P,(2.=R1.)(2.=(3.R2.))(0.Pa,$1.Pb,$1.P,(0.(2.=R2.)(2.R2.R1.))(2.(3.R3.)(3.R2.))(0.Pa,$1.Pb,$1.P,(2.=R2.)P,(2.=R2.)(2.(4.(3.R4.)(3.R3.))(3.(4.R4.R3.)))(0.Pa,$1.P,(2.=R1.)(2.A1.VP1,R2.(3.R2.))(0.Pa,$1.P,(2.=R1.)(2.A1.VP2,R2.(3.R2.))(0.Pa,$1.P,(2.=R1.)(2.A1.VP3,R2.(3.R2.))Pa,$1.P,(2.=R1.)(2.A1.VP4,R2.(3.R2.))))))))")
(* [comment removed for export] *).
  Proof.
    unfold j41. split; [| split; [| split; [| split; [| split; [| split]]]]].
    - intros a A. pose proof (M1 a a ltac:(lia)). pose proof (M2 a a ltac:(lia)). pose proof (M3 a a ltac:(lia)). pose proof (M4 a a ltac:(lia)). lia.
    - intros a b H. pose proof (M1 a b H). pose proof (M2 a b H). pose proof (M3 a b H). pose proof (M4 a b H). lia.
    - intros a b A B. pose proof (S1 a b A B). pose proof (S2 a b A B). pose proof (S3 a b A B). pose proof (S4 a b A B). lia.
    - intros a A. pose proof (M1 a a ltac:(lia)). pose proof (M2 a a ltac:(lia)). pose proof (M3 a a ltac:(lia)). pose proof (M4 a a ltac:(lia)). lia.
    - intros a A. pose proof (M1 a a ltac:(lia)). pose proof (M2 a a ltac:(lia)). pose proof (M3 a a ltac:(lia)). pose proof (M4 a a ltac:(lia)). lia.
    - intros a A. pose proof (M1 a a ltac:(lia)). pose proof (M2 a a ltac:(lia)). pose proof (M3 a a ltac:(lia)). pose proof (M4 a a ltac:(lia)). lia.
    - intros a A. pose proof (M1 a a ltac:(lia)). pose proof (M2 a a ltac:(lia)). pose proof (M3 a a ltac:(lia)). pose proof (M4 a a ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L22163277819.31L29763563164.32L30947718573.27L30947864614.28L30949952542.29L30949952925.30L50580436587.33L51629125369.31L58959238762.31L60463541728.31L66858127719.3100000I00h00m01201701<01Z02402M02f03BS2F12F22F32F41a1e1H2H02H2S2F12F22F32F41a1b1e2H02H12H22H3S1a1AS1a1AS1a1AS1a1AS2F12F22F32F41a1b1e1H2H02H12H2S2F12F22F32F41a1e2H02H12H2S2F12F22F32F41a1e1H2H02H1S2F12F22F32F41a1e1H2H12H2S2F12F22F32F41a1e1H2H02H12H2". (* [comment removed for export] *)
  #[using="N1 N2 N3 N4 T1 T2 T3 T4"] Lemma j42_facts : ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(0.Pa,$1.Pe,$1.P,(2.=R2.)(2.=(5.R3.R2.))(0.Pa,$1.Pb,$1.Pe,$1.P,(0.(2.=R3.)(2.R3.R2.))(2.(5.R4.R2.)(5.R3.R2.))(0.Pa,$1.Pb,$1.Pe,$1.P,(2.=R3.)P,(2.=R3.)(2.(4.(5.R5.R3.)(5.R4.R3.))(5.(4.R5.R4.)R3.))(0.Pa,$1.Pe,$1.P,(2.=R2.)(2.A2.VF1,R3.(4.R2.+1.)(5.R3.R2.))(0.Pa,$1.Pe,$1.P,(2.=R2.)(2.A2.VF2,R3.(4.R2.+1.)(5.R3.R2.))(0.Pa,$1.Pe,$1.P,(2.=R2.)(2.A2.VF3,R3.(4.R2.+1.)(5.R3.R2.))Pa,$1.Pe,$1.P,(2.=R2.)(2.A2.VF4,R3.(4.R2.+1.)(5.R3.R2.))))))))")
(* [comment removed for export] *).
  Proof.
    unfold j42. split; [| split; [| split; [| split; [| split; [| split]]]]].
    - intros a e A. pose proof (N1 a a (e + 1) ltac:(lia)). pose proof (N2 a a (e + 1) ltac:(lia)). pose proof (N3 a a (e + 1) ltac:(lia)). pose proof (N4 a a (e + 1) ltac:(lia)). lia.
    - intros a b e H. pose proof (N1 a b (e + 1) H). pose proof (N2 a b (e + 1) H). pose proof (N3 a b (e + 1) H). pose proof (N4 a b (e + 1) H). lia.
    - intros a b e A B. pose proof (T1 a b (e + 1) A B). pose proof (T2 a b (e + 1) A B). pose proof (T3 a b (e + 1) A B). pose proof (T4 a b (e + 1) A B). lia.
    - intros a e A. pose proof (N1 a a (e + 1) ltac:(lia)). pose proof (N2 a a (e + 1) ltac:(lia)). pose proof (N3 a a (e + 1) ltac:(lia)). pose proof (N4 a a (e + 1) ltac:(lia)). lia.
    - intros a e A. pose proof (N1 a a (e + 1) ltac:(lia)). pose proof (N2 a a (e + 1) ltac:(lia)). pose proof (N3 a a (e + 1) ltac:(lia)). pose proof (N4 a a (e + 1) ltac:(lia)). lia.
    - intros a e A. pose proof (N1 a a (e + 1) ltac:(lia)). pose proof (N2 a a (e + 1) ltac:(lia)). pose proof (N3 a a (e + 1) ltac:(lia)). pose proof (N4 a a (e + 1) ltac:(lia)). lia.
    - intros a e A. pose proof (N1 a a (e + 1) ltac:(lia)). pose proof (N2 a a (e + 1) ltac:(lia)). pose proof (N3 a a (e + 1) ltac:(lia)). pose proof (N4 a a (e + 1) ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End J4.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.3000001S". (* [comment removed for export] *)
Lemma TRAV_PHI_mono : mono1 A_asn1_trav.TRAV_PHI.
Proof. intros n n' H. unfold A_asn1_trav.TRAV_PHI, A_asn1_seq_cb.ASN1_SEQ_CB_PHI, AVOL_CALL. pose proof (div_mono_nn 2 ltac:(lia) n n' H). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422379900.4000001S". (* [comment removed for export] *)
Lemma TRAV_PHI_sadd : sadd1 A_asn1_trav.TRAV_PHI.
Proof. intros a b A B. unfold A_asn1_trav.TRAV_PHI, A_asn1_seq_cb.ASN1_SEQ_CB_PHI, AVOL_CALL. pose proof (div_sadd 2 ltac:(lia) a b A B). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.4000001S". (* [comment removed for export] *)
Lemma FFRq_mono : mono2 A_asn1_get_seq_of.FFRq.
Proof. intros n n' d H. unfold A_asn1_get_seq_of.FFRq, A_asn1_trav.TRAV_FFR, fr_charge. pose proof (div_mono_nn 2 ltac:(lia) n n' H). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422379900.5000001S". (* [comment removed for export] *)
Lemma FFRq_sadd : sadd2 A_asn1_get_seq_of.FFRq.
Proof. intros a b d A B. unfold A_asn1_get_seq_of.FFRq, A_asn1_trav.TRAV_FFR, fr_charge. pose proof (div_sadd 2 ltac:(lia) a b A B). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.3000001S". (* [comment removed for export] *)
Lemma CNTq_mono : mono1 A_asn1_get_seq_of.CNTq.
Proof. intros n n' H. unfold A_asn1_get_seq_of.CNTq. exact (div_mono_nn 2 ltac:(lia) n n' H). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422379900.4000001S". (* [comment removed for export] *)
Lemma CNTq_sadd : sadd1 A_asn1_get_seq_of.CNTq.
Proof. intros a b A B. unfold A_asn1_get_seq_of.CNTq. exact (div_sadd 2 ltac:(lia) a b A B). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7386141759.3000001S". (* [comment removed for export] *)
Lemma PHIpol_mono : mono1 A_x509_policies_B.PHIpol.
Proof. intros n n' H. unfold A_x509_policies_B.PHIpol. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62675882313.4000001S". (* [comment removed for export] *)
Lemma PHIpol_sadd : sadd1 A_x509_policies_B.PHIpol.
Proof. intros a b A B. unfold A_x509_policies_B.PHIpol. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40818989526.4000001S". (* [comment removed for export] *)
Lemma FFRpol_mono : mono2 A_x509_policies_B.FFRpol.
Proof. intros n n' d H. unfold A_x509_policies_B.FFRpol. pose proof (div_mono_nn 4 ltac:(lia) n n' H). pose proof (Z.le_max_l 0 (fr_charge (d + 1))). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40819154140.5000001S". (* [comment removed for export] *)
Lemma FFRpol_sadd : sadd2 A_x509_policies_B.FFRpol.
Proof. intros a b d A B. unfold A_x509_policies_B.FFRpol. pose proof (div_sadd 4 ltac:(lia) a b A B). pose proof (Z.le_max_l 0 (fr_charge (d + 1))). nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40818989526.3000001S". (* [comment removed for export] *)
Lemma CNTpol_mono : mono1 A_x509_policies_B.CNTpol.
Proof. intros n n' H. unfold A_x509_policies_B.CNTpol. exact (div_mono_nn 4 ltac:(lia) n n' H). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40819154140.4000001S". (* [comment removed for export] *)
Lemma CNTpol_sadd : sadd1 A_x509_policies_B.CNTpol.
Proof. intros a b A B. unfold A_x509_policies_B.CNTpol. exact (div_sadd 4 ltac:(lia) a b A B). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma FFRgs_mono : mono2 (A_x509_get_san.FFRg FFRsan).
Proof. intros n n' d H. unfold A_x509_get_san.FFRg. exact (FFRsan_mono n n' (d + 1) H). Qed.
Lemma FFRgs_sadd : sadd2 (A_x509_get_san.FFRg FFRsan).
Proof. intros a b d A B. unfold A_x509_get_san.FFRg. exact (FFRsan_sadd a b (d + 1) A B). Qed.
Lemma FFRks_mono : mono2 (A_x509_akid.FFRk FFRsan).
Proof. intros n n' d H. unfold A_x509_akid.FFRk. exact (FFRsan_mono n n' (d + 1) H). Qed.
Lemma FFRks_sadd : sadd2 (A_x509_akid.FFRk FFRsan).
Proof. intros a b d A B. unfold A_x509_akid.FFRk. exact (FFRsan_sadd a b (d + 1) A B). Qed.

Definition PHIext : Z -> Z := j41 A_asn1_trav.TRAV_PHI PHIsan A_x509_policies_B.PHIpol PHIsan.
Definition FFRext : Z -> Z -> Z := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(6.$7.(8.$9.)$:.(;.$9.))")
(* [comment removed for export] *).
Definition CNText : Z -> Z := j41 A_asn1_get_seq_of.CNTq CNTsan A_x509_policies_B.CNTpol CNTsan.
Definition PHIext_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(<.$=.$>.$?.$>.$10.$11.$12.$11.$13.$14.$15.$14.)")
(* [comment removed for export] *).
Definition FFRext_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(16.$7.(8.$9.)$:.(;.$9.)$17.$18.$19.$1:.$1;.$1<.$1=.$1>.)")
(* [comment removed for export] *).
Definition CNText_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(<.$1?.$20.$21.$20.$22.$23.$24.$23.$25.$26.$27.$26.)")
(* [comment removed for export] *).

Lemma PHIext0 : forall a, 0 <= a -> 0 <= PHIext a. Proof. exact (proj1 PHIext_facts). Qed.
Lemma PHIext_mono : forall a b, 0 <= a <= b -> PHIext a <= PHIext b. Proof. exact (proj1 (proj2 PHIext_facts)). Qed.
Lemma PHIext_sadd : forall a b, 0 <= a -> 0 <= b -> PHIext a + PHIext b <= PHIext (a + b). Proof. exact (proj1 (proj2 (proj2 PHIext_facts))). Qed.
Lemma PHIext_le1 : forall a, 0 <= a -> A_asn1_trav.TRAV_PHI a <= PHIext a. Proof. exact (proj1 (proj2 (proj2 (proj2 PHIext_facts)))). Qed.
Lemma PHIext_le2 : forall a, 0 <= a -> PHIsan a <= PHIext a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 PHIext_facts))))). Qed.
Lemma PHIext_le3 : forall a, 0 <= a -> A_x509_policies_B.PHIpol a <= PHIext a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PHIext_facts)))))). Qed.
Lemma CNText0 : forall a, 0 <= a -> 0 <= CNText a. Proof. exact (proj1 CNText_facts). Qed.
Lemma CNText_mono : forall a b, 0 <= a <= b -> CNText a <= CNText b. Proof. exact (proj1 (proj2 CNText_facts)). Qed.
Lemma CNText_sadd : forall a b, 0 <= a -> 0 <= b -> CNText a + CNText b <= CNText (a + b). Proof. exact (proj1 (proj2 (proj2 CNText_facts))). Qed.
Lemma CNText_le1 : forall a, 0 <= a -> A_asn1_get_seq_of.CNTq a <= CNText a. Proof. exact (proj1 (proj2 (proj2 (proj2 CNText_facts)))). Qed.
Lemma CNText_le2 : forall a, 0 <= a -> CNTsan a <= CNText a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 CNText_facts))))). Qed.
Lemma CNText_le3 : forall a, 0 <= a -> A_x509_policies_B.CNTpol a <= CNText a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CNText_facts)))))). Qed.
Lemma FFRext0 : forall a e, 0 <= a -> 0 <= FFRext a e. Proof. exact (proj1 FFRext_facts). Qed.
Lemma FFRext_mono : forall a b e, 0 <= a <= b -> FFRext a e <= FFRext b e. Proof. exact (proj1 (proj2 FFRext_facts)). Qed.
Lemma FFRext_sadd : forall a b e, 0 <= a -> 0 <= b -> FFRext a e + FFRext b e <= FFRext (a + b) e. Proof. exact (proj1 (proj2 (proj2 FFRext_facts))). Qed.
Lemma FFRext_le1 : forall a e, 0 <= a -> A_asn1_get_seq_of.FFRq a (e + 1) <= FFRext a e. Proof. exact (proj1 (proj2 (proj2 (proj2 FFRext_facts)))). Qed.
Lemma FFRext_le2 : forall a e, 0 <= a -> (A_x509_get_san.FFRg FFRsan) a (e + 1) <= FFRext a e. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 FFRext_facts))))). Qed.
Lemma FFRext_le3 : forall a e, 0 <= a -> A_x509_policies_B.FFRpol a (e + 1) <= FFRext a e. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FFRext_facts)))))). Qed.
Lemma FFRext_le4 : forall a e, 0 <= a -> (A_x509_akid.FFRk FFRsan) a (e + 1) <= FFRext a e. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 FFRext_facts)))))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Z1 (n : Z) : Z := 0.
Definition Z2 (n e : Z) : Z := 0.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7386141759.3000001S". (* [comment removed for export] *)
Lemma Z1_mono : mono1 Z1. Proof. intros n n' H. unfold Z1. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62675882313.4000001S". (* [comment removed for export] *)
Lemma Z1_sadd : sadd1 Z1. Proof. intros a b A B. unfold Z1. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7386141759.4000001S". (* [comment removed for export] *)
Lemma Z2_mono : mono2 Z2. Proof. intros n n' d H. unfold Z2. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62675882313.5000001S". (* [comment removed for export] *)
Lemma Z2_sadd : sadd2 Z2. Proof. intros a b d A B. unfold Z2. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2431248216.3 L58373962147.500000800DS1n2n'1HS1n2n'2H02H1". (* [comment removed for export] *)
Lemma PHIext_mono1 : mono1 PHIext. Proof. intros n n' H. pose proof (PHIext0 n ltac:(lia)). pose proof (PHIext_mono n n' H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2431248216.3 L58373962147.500000800DS1n2n'1HS1n2n'2H02H1". (* [comment removed for export] *)
Lemma CNText_mono1 : mono1 CNText. Proof. intros n n' H. pose proof (CNText0 n ltac:(lia)). pose proof (CNText_mono n n' H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2431248216.4 L59022174318.600000800FS1n2n'1HS1n2n'1d2H02H1". (* [comment removed for export] *)
Lemma FFRext_mono2 : mono2 FFRext. Proof. intros n n' d H. pose proof (FFRext0 n d ltac:(lia)). pose proof (FFRext_mono n n' d H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Definition PHIcj : Z -> Z := j41 A_x509_get_name_A.PHIn PHIext Z1 Z1.
Definition FFRcj : Z -> Z -> Z := j42 A_x509_get_name_A.FFRn FFRext Z2 Z2.
Definition CNTcj : Z -> Z := j41 A_x509_get_name_A.CNTn CNText Z1 Z1.
Definition PHIcj_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(<.$28.$29.$2:.$2:.$2;.$2<.$2=.$2=.$2>.$2?.$30.$30.)")
(* [comment removed for export] *).
Definition FFRcj_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(16.$31.$32.$33.$33.$34.$35.$36.$36.$37.$38.$39.$39.)")
(* [comment removed for export] *).
Definition CNTcj_facts := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(<.$3:.$3;.$2:.$2:.$3<.$3=.$2=.$2=.$3>.$3?.$30.$30.)")
(* [comment removed for export] *).
Lemma PHIcj0 : forall a, 0 <= a -> 0 <= PHIcj a. Proof. exact (proj1 PHIcj_facts). Qed.
Lemma PHIcj_mono : forall a b, 0 <= a <= b -> PHIcj a <= PHIcj b. Proof. exact (proj1 (proj2 PHIcj_facts)). Qed.
Lemma PHIcj_sadd : forall a b, 0 <= a -> 0 <= b -> PHIcj a + PHIcj b <= PHIcj (a + b). Proof. exact (proj1 (proj2 (proj2 PHIcj_facts))). Qed.
Lemma PHIcj_le1 : forall a, 0 <= a -> A_x509_get_name_A.PHIn a <= PHIcj a. Proof. exact (proj1 (proj2 (proj2 (proj2 PHIcj_facts)))). Qed.
Lemma PHIcj_le2 : forall a, 0 <= a -> PHIext a <= PHIcj a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 PHIcj_facts))))). Qed.
Lemma CNTcj0 : forall a, 0 <= a -> 0 <= CNTcj a. Proof. exact (proj1 CNTcj_facts). Qed.
Lemma CNTcj_mono : forall a b, 0 <= a <= b -> CNTcj a <= CNTcj b. Proof. exact (proj1 (proj2 CNTcj_facts)). Qed.
Lemma CNTcj_sadd : forall a b, 0 <= a -> 0 <= b -> CNTcj a + CNTcj b <= CNTcj (a + b). Proof. exact (proj1 (proj2 (proj2 CNTcj_facts))). Qed.
Lemma CNTcj_le1 : forall a, 0 <= a -> A_x509_get_name_A.CNTn a <= CNTcj a. Proof. exact (proj1 (proj2 (proj2 (proj2 CNTcj_facts)))). Qed.
Lemma CNTcj_le2 : forall a, 0 <= a -> CNText a <= CNTcj a. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 CNTcj_facts))))). Qed.
Lemma FFRcj0 : forall a e, 0 <= a -> 0 <= FFRcj a e. Proof. exact (proj1 FFRcj_facts). Qed.
Lemma FFRcj_mono : forall a b e, 0 <= a <= b -> FFRcj a e <= FFRcj b e. Proof. exact (proj1 (proj2 FFRcj_facts)). Qed.
Lemma FFRcj_sadd : forall a b e, 0 <= a -> 0 <= b -> FFRcj a e + FFRcj b e <= FFRcj (a + b) e. Proof. exact (proj1 (proj2 (proj2 FFRcj_facts))). Qed.
Lemma FFRcj_le1 : forall a e, 0 <= a -> A_x509_get_name_A.FFRn a (e + 1) <= FFRcj a e. Proof. exact (proj1 (proj2 (proj2 (proj2 FFRcj_facts)))). Qed.
Lemma FFRcj_le2 : forall a e, 0 <= a -> FFRext a (e + 1) <= FFRcj a e. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 FFRcj_facts))))). Qed.
#[global] Hint Resolve PHIcj0 PHIcj_mono PHIcj_sadd PHIcj_le1 PHIcj_le2 CNTcj0 CNTcj_mono CNTcj_sadd CNTcj_le1 CNTcj_le2 FFRcj0 FFRcj_mono FFRcj_sadd FFRcj_le1 FFRcj_le2 : alink_bud.

(* [comment removed for export] *)
Definition STKsanx (R : art_layout) : Z := A_x509_san_ext_A.STKx R (A_x509_parse_san_A.STKps R (A_x509_get_name_A.STKn R)).
Definition STKext (R : art_layout) : Z := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(40.+100.(40.(4.(41.O1.)+80.)(40.(4.+<0.(42.O1.))(40.(43.O1.)(40.(44.O1.(45.O1.))(40.(46.O1.)(47.O1.(45.O1.))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition STKcrt (R : art_layout) : Z := ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "(40.(4.$48.+80.)(40.(4.(41.O1.)+1?0.)(40.(4.(42.O1.)+190.)(40.(4.(49.O1.)+40.)(40.(4.(4:.O1.)+40.)(40.(4;.O1.)(40.(4<.O1.)(40.(4=.O1.)(40.(4>.O1.(4?.O1.))(50.O1.(51.O1.)))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L42562250348.2000008S1R4STKc". (* [comment removed for export] *)
Lemma FSTKc_p : forall R STKc, 112 + STKp_c R STKc <= FSTKc R STKc. Proof. intros. unfold FSTKc. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L67550400417.2000008S1R4STKc". (* [comment removed for export] *)
Lemma FSTKc_f : forall R STKc, 112 + A_pkcs7_free.STKp7f R (A_pk_free.STKpk R) <= FSTKc R STKc. Proof. intros. unfold FSTKc. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38605376102.2000008S1R4STKc". (* [comment removed for export] *)
Lemma FSTKc_1 : forall R STKc, 128 + arl_need_smalloc R <= FSTKc R STKc. Proof. intros. unfold FSTKc. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38605376102.2000008S1R4STKc". (* [comment removed for export] *)
Lemma FSTKc_2 : forall R STKc, 128 + arl_need_setsh R <= FSTKc R STKc. Proof. intros. unfold FSTKc. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38605376102.2000008S1R4STKc". (* [comment removed for export] *)
Lemma FSTKc_3 : forall R STKc, 128 + arl_need_amem R <= FSTKc R STKc. Proof. intros. unfold FSTKc. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38977236358.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g1 : forall R, A_x509_get_sig_alg.X509_SIG_ALG_STACK_A + 128 <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L10313438858.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g2 : forall R, arl_need_amem R + 496 <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L44290404746.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g3 : forall R, arl_need_bcmp R + 400 <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30752033930.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g4 : forall R, arl_need_malloc R + 64 <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30752033930.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g5 : forall R, arl_need_free R + 64 <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L32618318805.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt_g6 : forall R, arl_need_setsh R <= STKcrt R. Proof. intros R. unfold STKcrt. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[global] Hint Resolve STKcrt_g1 STKcrt_g2 STKcrt_g3 STKcrt_g4 STKcrt_g5 STKcrt_g6 : alink_bud.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L57982564375.1000003S1R". (* [comment removed for export] *)
Lemma STKcrt0 : forall R, 0 <= STKcrt R.
Proof. intros R. unfold STKcrt, A_x509_get_sig_alg.X509_SIG_ALG_STACK_A. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Section STKcrtFacts.
  Variable R : art_layout.
  Hypothesis LO : A_link_layout.a_layout_ok R.
  Let NS : 0 <= arl_need_smalloc R := A_link_layout.alo_need_smalloc R LO.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L61670945659.3000006S1R2NS". (* [comment removed for export] *)
  #[using="LO NS"] Lemma STKcrt_n : A_x509_get_name_A.STKn R <= STKcrt R + 48 + arl_need_smalloc R. Proof. unfold STKcrt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L61670945659.3000006S1R2NS". (* [comment removed for export] *)
  #[using="LO NS"] Lemma STKcrt_k : A_pk_parse_G0.PKP_STK R <= STKcrt R + 48 + arl_need_smalloc R. Proof. unfold STKcrt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L57115092076.3000006S1R2NS". (* [comment removed for export] *)
  #[using="LO NS"] Lemma STKcrt_x : A_x509_crt_ext_A.STKx R (STKext R) <= STKcrt R + 48 + arl_need_smalloc R. Proof. unfold STKcrt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L57115092076.3000006S1R2NS". (* [comment removed for export] *)
  #[using="LO NS"] Lemma STKcrt_f : A_x509_crt_free.STKcf R (A_pk_free.STKpk R) <= STKcrt R + 48 + arl_need_smalloc R. Proof. unfold STKcrt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End STKcrtFacts.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L14253635293.2L65242977856.300000600;S1k2HkS1k1H". (* [comment removed for export] *)
Lemma PHIcf_i0 : forall k, 0 <= k -> 0 <= A_x509_crt_free.PHIcf A_pk_free.PHIpk k.
Proof. intros k Hk. pose proof (PHIcf_mono _ PHIpk_mono0 k k ltac:(lia)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L14253635293.3L53653870078.400000600=S1k2HkS1k1e1H". (* [comment removed for export] *)
Lemma FFRcf_i0 : forall k e, 0 <= k -> 0 <= A_x509_crt_free.FFRcf A_pk_free.FFRpk k e.
Proof. intros k e Hk. pose proof (FFRcf_mono _ FFRpk_mono0 k k e ltac:(lia)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24811404733.4000008S1a1b2H0". (* [comment removed for export] *)
Lemma PHIcf_i_mono : ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "Pa,$1.Pb,$1.P,(0.(2.=R2.)(2.R2.R1.))(2.(52.$53.R3.)(52.$53.R2.))")
(* [comment removed for export] *).
Proof. intros a b H. pose proof (PHIcf_mono _ PHIpk_mono0 a b H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29282563609.500000:S1a1b1e2H0". (* [comment removed for export] *)
Lemma FFRcf_i_mono : ltac2:(CDefT.buildp (gd_tbl_A_link_adapt ()) "Pa,$1.Pb,$1.Pe,$1.P,(0.(2.=R3.)(2.R3.R2.))(2.(54.$55.R4.R2.)(54.$55.R3.R2.))")
(* [comment removed for export] *).
Proof. intros a b e H. pose proof (FFRcf_mono _ FFRpk_mono0 a b e H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[global] Hint Resolve STKcrt0 STKcrt_n STKcrt_k STKcrt_x STKcrt_f PHIcf_i0 FFRcf_i0 PHIcf_i_mono FFRcf_i_mono : alink_bud.
#[global] Hint Unfold STKext : alink_unf0.
#[global] Hint Unfold STKext STKsanx : alink_unf.

#[global] Hint Resolve PHIsan_mono FFRsan_mono CNTsan_mono PHIext0 PHIext_mono PHIext_sadd PHIext_le1 PHIext_le2 PHIext_le3 CNText0 CNText_mono CNText_sadd CNText_le1 CNText_le2 CNText_le3 FFRext0 FFRext_mono FFRext_sadd FFRext_le1 FFRext_le2 FFRext_le3 FFRext_le4 : alink_bud.

(* [comment removed for export] *)
Ltac alink_fstk := first [ exact (STKcrt_g1 _) | exact (STKcrt_g2 _) | exact (STKcrt_g3 _) | exact (STKcrt_g4 _) | exact (STKcrt_g5 _) | exact (STKcrt_g6 _) | exact (STKcrt0 _) | exact (FSTKc_p _ _) | exact (FSTKc_f _ _) | exact (FSTKc_1 _ _) | exact (FSTKc_2 _ _) | exact (FSTKc_3 _ _) ].
