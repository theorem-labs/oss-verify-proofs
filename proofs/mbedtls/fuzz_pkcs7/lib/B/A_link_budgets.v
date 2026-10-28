(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_link_base.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_x509_get_name_A A_pkcs7_signer_C A_pkcs7_signers_C A_pk_free A_x509_crt_free A_pkcs7_free A_pkcs7_getcerts A_pkcs7_parse_A A_pkcs7_parse_C
  A_pkcs7_signer_A A_pkcs7_signer_I A_pkcs7_signers_A A_x509_parse_san_A A_x509_parse_san_C A_x509_san_ext_A A_x509_san_ext_bud.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_budgets () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "jsum1"; "jsum2"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_bud.FFRx"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_parse_A.STKp"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_getcerts.STKg"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_A.STKs"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signer_I.STKsg"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.STKn"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_free.STKp7f"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.STKpk"; "Stdlib.ZArith.BinInt.Z.max"; "STKp_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_setsh"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"].



(* [comment removed for export] *)
Notation mono1 F := (forall n n', 0 <= n <= n' -> 0 <= F n <= F n') (only parsing).
Notation mono2 F := (forall n n' d, 0 <= n <= n' -> 0 <= F n d <= F n' d) (only parsing).
Notation sadd1 F := (forall a b, 0 <= a -> 0 <= b -> F a + F b <= F (a + b)) (only parsing).
Notation sadd2 F := (forall a b d, 0 <= a -> 0 <= b -> F a d + F b d <= F (a + b) d) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PHIn_sadd : sadd1 A_x509_get_name_A.PHIn.
Proof. exact A_x509_get_name_A.PHIn_sadd. Qed.   (* [comment removed for export] *)
Lemma CNTn_sadd : sadd1 A_x509_get_name_A.CNTn.
Proof. exact A_x509_get_name_A.CNTn_sadd. Qed.
Lemma FFRn_sadd : sadd2 A_x509_get_name_A.FFRn.
Proof. exact A_x509_get_name_A.FFRn_sadd. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Signer.
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z).
  Hypothesis PM : mono1 PHIn. Hypothesis FM : mono2 FFRn. Hypothesis CM : mono1 CNTn.
  #[using="CM"] Lemma CNTsi_mono : mono1 (A_pkcs7_signer_C.CNTsi CNTn).
  Proof. exact CM. Qed.
  #[using="PM CM"] Lemma PHIsi_mono : mono1 (A_pkcs7_signer_C.PHIsi PHIn CNTn).
  Proof. intros n n' H. pose proof (PM n n' H). pose proof (CM n n' H). unfold A_pkcs7_signer_C.PHIsi, AVOL_CALL. lia. Qed.
  #[using="FM CM"] Lemma FFRsi_mono : mono2 (A_pkcs7_signer_C.FFRsi FFRn CNTn).
  Proof.
    intros n n' d H. pose proof (FM n n' (d + 1) H). pose proof (CM n n' H). unfold A_pkcs7_signer_C.FFRsi.
    pose proof (Z.le_max_l 0 (fr_charge (d + 1))). nia.
  Qed.
  Hypothesis PS : sadd1 PHIn. Hypothesis FS : sadd2 FFRn. Hypothesis CS : sadd1 CNTn.
  #[using="CS"] Lemma CNTsi_sadd : sadd1 (A_pkcs7_signer_C.CNTsi CNTn).
  Proof. exact CS. Qed.
  #[using="PS CS"] Lemma PHIsi_sadd : sadd1 (A_pkcs7_signer_C.PHIsi PHIn CNTn).
  Proof. intros a b Ha Hb. pose proof (PS a b Ha Hb). pose proof (CS a b Ha Hb). unfold A_pkcs7_signer_C.PHIsi, AVOL_CALL. lia. Qed.
  #[using="FS CS"] Lemma FFRsi_sadd : sadd2 (A_pkcs7_signer_C.FFRsi FFRn CNTn).
  Proof.
    intros a b d Ha Hb. pose proof (FS a b (d + 1) Ha Hb). pose proof (CS a b Ha Hb). unfold A_pkcs7_signer_C.FFRsi.
    pose proof (Z.le_max_l 0 (fr_charge (d + 1))). nia.
  Qed.
End Signer.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Signers.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z).
  Hypothesis PM : mono1 PHIsi. Hypothesis FM : mono2 FFRsi. Hypothesis CM : mono1 CNTsi.
  #[using="Type"] Lemma half_mono : forall n n', 0 <= n <= n' -> 0 <= n / 2 <= n' / 2.
  Proof. intros n n' H. split; [apply Z.div_pos; lia| apply Z.div_le_mono; lia]. Qed.
  #[using="CM"] Lemma CNTs_mono : mono1 (A_pkcs7_signers_C.CNTs CNTsi).
  Proof. intros n n' H. pose proof (CM n n' H). pose proof (half_mono n n' H). unfold A_pkcs7_signers_C.CNTs. lia. Qed.
  #[using="PM CM"] Lemma PHIs_mono : mono1 (A_pkcs7_signers_C.PHIs PHIsi CNTsi).
  Proof.
    intros n n' H. pose proof (PM n n' H). pose proof (CNTs_mono n n' H). pose proof (half_mono n n' H).
    unfold A_pkcs7_signers_C.PHIs, AVOL_CALL. lia.
  Qed.
  #[using="FM CM"] Lemma FFRs_mono : mono2 (A_pkcs7_signers_C.FFRs FFRsi CNTsi).
  Proof.
    intros n n' d H. pose proof (FM n n' (d + 1) H). pose proof (CNTs_mono n n' H). pose proof (half_mono n n' H).
    unfold A_pkcs7_signers_C.FFRs. pose proof (Z.le_max_l 0 (fr_charge (d + 1))). nia.
  Qed.
End Signers.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PHIpk_mono0 : mono1 A_pk_free.PHIpk.
Proof. intros n n' H. unfold A_pk_free.PHIpk, AVOL_CALL. lia. Qed.
Lemma FFRpk_mono0 : mono2 A_pk_free.FFRpk.
Proof. intros n n' d H. unfold A_pk_free.FFRpk, fr_charge. lia. Qed.
Section Free.
  Variables (PHIpk : Z -> Z) (FFRpk : Z -> Z -> Z).
  Hypothesis PM : mono1 PHIpk. Hypothesis FM : mono2 FFRpk.
  #[using="PM"] Lemma PHIp7f_mono : mono1 (A_pkcs7_free.PHIp7f PHIpk).
  Proof. exact PM. Qed.
  #[using="FM"] Lemma FFRp7f_mono : mono2 (A_pkcs7_free.FFRp7f FFRpk).
  Proof. intros n n' d H. pose proof (FM n n' d H). unfold A_pkcs7_free.FFRp7f. pose proof (Z.le_max_l 0 (fr_charge d)). nia. Qed.
  #[using="PM"] Lemma PHIcf_mono : mono1 (A_x509_crt_free.PHIcf PHIpk).
  Proof. exact PM. Qed.
  #[using="FM"] Lemma FFRcf_mono : mono2 (A_x509_crt_free.FFRcf FFRpk).
  Proof. intros n n' d H. pose proof (FM n n' d H). unfold A_x509_crt_free.FFRcf. pose proof (Z.le_max_l 0 (fr_charge d)). nia. Qed.
End Free.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FFRg_mono : forall FFRc : Z -> Z -> Z, mono2 FFRc -> mono2 (A_pkcs7_getcerts.FFRg FFRc).
Proof. intros FFRc FM n n' d H. unfold A_pkcs7_getcerts.FFRg. exact (FM n n' (d + 1) H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition jsum1 (G S : Z -> Z) (n : Z) : Z := G n + S n.
Definition jsum2 (G S : Z -> Z -> Z) (n d : Z) : Z := G n d + S n d.
Section Joint.
  Variables (PHIg : Z -> Z) (FFRg : Z -> Z -> Z) (CNTg : Z -> Z) (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z).
  Hypothesis PG : mono1 PHIg. Hypothesis FG : mono2 FFRg. Hypothesis CG : mono1 CNTg.
  Hypothesis PS : mono1 PHIs. Hypothesis FS : mono2 FFRs. Hypothesis CS : mono1 CNTs.
  #[using="Type"] Lemma jsum1_mono : forall G S : Z -> Z, mono1 G -> mono1 S -> mono1 (jsum1 G S).
  Proof. intros G S HG HS n n' H. pose proof (HG n n' H). pose proof (HS n n' H). unfold jsum1. lia. Qed.
  #[using="Type"] Lemma jsum2_mono : forall G S : Z -> Z -> Z, mono2 G -> mono2 S -> mono2 (jsum2 G S).
  Proof. intros G S HG HS n n' d H. pose proof (HG n n' d H). pose proof (HS n n' d H). unfold jsum2. lia. Qed.
  #[using="Type"] Lemma jsum1_joint : ltac2:(CDefT.buildp (gd_tbl_A_link_budgets ()) "PG,P,$0.$0.PS,P,$0.$0.P,Pn,$0.Pn',$0.P,(1.(2.=R2.)(2.R2.R1.))(1.(2.=A1.R5.R3.)(2.A1.R5.R3.A1.R5.R2.))P,Pn,$0.Pn',$0.P,(1.(2.=R2.)(2.R2.R1.))(1.(2.=A1.R5.R3.)(2.A1.R5.R3.A1.R5.R2.))Pa,$0.Pb,$0.P,(2.=R2.)P,(2.=R2.)(2.(3.A1.R8.R4.A1.R7.R3.)(4.R8.R7.(3.R4.R3.)))")
(* [comment removed for export] *).
  Proof. intros G S HG HS a b Ha Hb. pose proof (HG a (a + b) ltac:(lia)). pose proof (HS b (a + b) ltac:(lia)). unfold jsum1. lia. Qed.
  #[using="Type"] Lemma jsum2_joint : ltac2:(CDefT.buildp (gd_tbl_A_link_budgets ()) "PG,P,$0.P,$0.$0.PS,P,$0.P,$0.$0.P,Pn,$0.Pn',$0.Pd,$0.P,(1.(2.=R3.)(2.R3.R2.))(1.(2.=A2.R6.R4.R2.)(2.A2.R6.R4.R2.A2.R6.R3.R2.))P,Pn,$0.Pn',$0.Pd,$0.P,(1.(2.=R3.)(2.R3.R2.))(1.(2.=A2.R6.R4.R2.)(2.A2.R6.R4.R2.A2.R6.R3.R2.))Pa,$0.Pb,$0.Pd,$0.P,(2.=R3.)P,(2.=R3.)(2.(3.A2.R9.R5.R3.A2.R8.R4.R3.)(5.R9.R8.(3.R5.R4.)R3.))")
(* [comment removed for export] *).
  Proof. intros G S HG HS a b d Ha Hb. pose proof (HG a (a + b) d ltac:(lia)). pose proof (HS b (a + b) d ltac:(lia)). unfold jsum2. lia. Qed.
End Joint.

Section Parse.
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z) (PHIf : Z -> Z) (FFRf : Z -> Z -> Z).
  Hypothesis PJ : mono1 PHIj. Hypothesis FJ : mono2 FFRj. Hypothesis CJ : mono1 CNTj.
  Hypothesis PF : mono1 PHIf. Hypothesis FF : mono2 FFRf.
  #[using="CJ"] Lemma CNTp_mono : mono1 (A_pkcs7_parse_C.CNTp CNTj).
  Proof. intros n n' H. pose proof (CJ n n' H). unfold A_pkcs7_parse_C.CNTp. lia. Qed.
  #[using="CJ"] Lemma CNTp_nonneg : forall n, 0 <= n -> 0 <= A_pkcs7_parse_C.CNTp CNTj n.
  Proof. intros n H. pose proof (CNTp_mono n n ltac:(lia)). lia. Qed.
  #[using="PJ CJ PF"] Lemma PHIp_mono : mono1 (A_pkcs7_parse_C.PHIp PHIj CNTj PHIf).
  Proof.
    intros n n' H. pose proof (PJ n n' H). pose proof (CNTp_mono n n' H) as C. pose proof (PF _ _ C). unfold A_pkcs7_parse_C.PHIp, AVOL_CALL. lia.
  Qed.
  #[using="FJ CJ FF"] Lemma FFRp_mono : mono2 (A_pkcs7_parse_C.FFRp FFRj CNTj FFRf).
  Proof.
    intros n n' d H. pose proof (FJ n n' (d + 1) H). pose proof (CNTp_mono n n' H) as C. pose proof (FF _ _ 0 C). unfold A_pkcs7_parse_C.FFRp. lia.
  Qed.
  #[using="FJ CJ FF"] Lemma FFRp_nonneg : forall n d, 0 <= n -> 0 <= A_pkcs7_parse_C.FFRp FFRj CNTj FFRf n d.
  Proof. intros n d H. pose proof (FFRp_mono n n d ltac:(lia)). lia. Qed.
End Parse.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FFRps_mono : forall FFRn : Z -> Z -> Z, mono2 FFRn -> mono2 (A_x509_parse_san_C.FFRps FFRn).
Proof. intros FFRn FM n n' d H. unfold A_x509_parse_san_C.FFRps. exact (FM n n' (d + 1) H). Qed.
Lemma FFRps_sadd : forall FFRn : Z -> Z -> Z, sadd2 FFRn -> sadd2 (A_x509_parse_san_C.FFRps FFRn).
Proof. intros FFRn FS a b d Ha Hb. unfold A_x509_parse_san_C.FFRps. exact (FS a b (d + 1) Ha Hb). Qed.
Lemma CNTx_mono : mono1 A_x509_san_ext_bud.CNTx.
Proof. exact A_x509_san_ext_bud.CNTx_mono. Qed.
Lemma PHIx_mono : forall PHIp CNTp : Z -> Z, mono1 PHIp -> mono1 CNTp -> mono1 (A_x509_san_ext_bud.PHIx PHIp CNTp).
Proof. intros PHIp CNTp PM CM. exact (A_x509_san_ext_bud.PHIx_mono PHIp CNTp PM CM). Qed.
Lemma FFRx_mono : ltac2:(CDefT.buildp (gd_tbl_A_link_budgets ()) "PFFRp,P,$0.P,$0.$0.PCNTp,P,$0.$0.P,Pn,$0.Pn',$0.Pd,$0.P,(1.(2.=R3.)(2.R3.R2.))(1.(2.=A2.R6.R4.R2.)(2.A2.R6.R4.R2.A2.R6.R3.R2.))P,Pn,$0.Pn',$0.P,(1.(2.=R2.)(2.R2.R1.))(1.(2.=A1.R5.R3.)(2.A1.R5.R3.A1.R5.R2.))Pn,$0.Pn',$0.Pd,$0.P,(1.(2.=R3.)(2.R3.R2.))(1.(2.=(6.R8.R7.R4.R2.))(2.(6.R8.R7.R4.R2.)(6.R8.R7.R3.R2.)))")
(* [comment removed for export] *).
Proof. intros FFRp CNTp FM CM. exact (A_x509_san_ext_bud.FFRx_mono FFRp CNTp FM CM). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STKp_c (R : art_layout) (STKc : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_link_budgets ()) "(7.O2.(8.O2.O1.)(9.O2.(:.O2.(;.O2.)))(<.O2.(=.O2.)))")
(* [comment removed for export] *).
Definition FSTKc (R : art_layout) (STKc : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_link_budgets ()) "(3.+80.(>.(?.O2.O1.)(>.(<.O2.(=.O2.))(>.(10.O2.)(>.(11.O2.)(12.O2.))))))")
(* [comment removed for export] *).

#[global] Hint Resolve A_x509_get_name_A.PHIn_mono A_x509_get_name_A.FFRn_mono A_x509_get_name_A.CNTn_mono A_x509_get_name_A.STKn0
  PHIn_sadd CNTn_sadd FFRn_sadd CNTsi_mono PHIsi_mono FFRsi_mono CNTsi_sadd PHIsi_sadd FFRsi_sadd CNTs_mono PHIs_mono FFRs_mono
  PHIpk_mono0 FFRpk_mono0 PHIp7f_mono FFRp7f_mono PHIcf_mono FFRcf_mono FFRg_mono jsum1_mono jsum2_mono jsum1_joint jsum2_joint
  CNTp_mono CNTp_nonneg PHIp_mono FFRp_mono FFRp_nonneg FFRps_mono FFRps_sadd CNTx_mono PHIx_mono FFRx_mono
  A_pk_free.PHIpk0 A_pk_free.FFRpk0 A_pk_free.PHIpk_mono A_pk_free.FFRpk_mono : alink_bud.
(* [comment removed for export] *)
#[global] Hint Unfold FSTKc STKp_c : alink_unf0.
#[global] Hint Unfold A_pk_free.STKpk A_x509_crt_free.STKcf A_pkcs7_free.STKp7f A_x509_get_name_A.STKn A_x509_parse_san_A.STKps A_x509_san_ext_A.STKx
  A_pkcs7_signer_A.STKsg A_pkcs7_signers_A.STKs A_pkcs7_getcerts.STKg A_pkcs7_parse_A.STKp : alink_unf.
