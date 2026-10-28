(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap U_heap_laws U_platform_zeroize U_platform_zeroize_proof U_asn1_get_alg_A U_asn1_get_alg U_oid_md_alg U_oid_sig_alg_A U_fuzz_entry U_pkcs7_free U_pkcs7_parse U_pkcs7_signers U_pkcs7_getcerts U_x509_get_dates U_x509_get_uid U_x509_crt_parse U_oid_x509_ext U_x509_crt_ext U_x509_basic U_x509_skid U_x509_akid U_x509_policies. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract RepCrt CrtStmts CrtRelStmts CrtParseStmts SInv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_fuzz_top () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"].


Lemma U_layout_facts sp0 : ltac2:(CDefT.buildp (gd_tbl_P_fuzz_top ()) "(0.(1.$2.(3.(4.O1.))+3?:98.)(0.(5.(4.O1.)$6.+8.)(0.(7.=(8.(4.O1.)))(0.(7.(8.(4.O1.))+2710.)(0.Pa,$2.P,(9.(4.O1.)R1.)(:.(4.O1.)R2.)(0.(0.(7.(;.(4.O1.))(<.(4.O1.)))(7.(=.(4.O1.))(>.(4.O1.))))(7.(=.(4.O1.))(?.(4.O1.)))))))))")
(* [comment removed for export] *).
Proof.
  split; [reflexivity|]. split.
  { unfold const_at, U_MEMSET_FUNC. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia. }
  split; [cbn; lia|]. split; [cbn; lia|]. split; [exact U_static_written|]. split; [cbn; lia|].
  pose proof (@alloc_ceiling_lo (U_layout sp0)) as ACLO. change (hl_data_hi (U_layout sp0)) with 0x7e000. lia.
Qed.

Lemma U_layout_facts2 sp0 : hl_calloc (U_layout sp0) = 0x3f960 /\ const_at (U_layout sp0) U_OID_MD_ALG_TBL 440.
Proof.
  split; [reflexivity|].
  unfold const_at, U_OID_MD_ALG_TBL. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma U_layout_facts3 sp0 : const_at (U_layout sp0) U_OID_SIG_ALG_TBL 560.
Proof.
  unfold const_at, U_OID_SIG_ALG_TBL. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma U_layout_facts4 sp0 : const_at (U_layout sp0) U_OID_X509_EXT_TBL 320.
Proof.
  unfold const_at, U_OID_X509_EXT_TBL. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Section Top.
  Variable sp0 : word.
  Variable PK : pk_class usegs.
  Variable SI : sinv (U_layout sp0).
  Hypothesis PKFREE : pk_free_stmt2 usegs (U_layout sp0) (U_HI sp0) PK 0x29c28.                (* [comment removed for export] *)
  Hypothesis PKPARSE : pk_parse_subpubkey_stmt usegs (U_layout sp0) (U_HI sp0) PK SI 0x292a8. (* [comment removed for export] *)

  #[using="PK PKFREE PKPARSE"] Theorem fuzz_entry_top : fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) SI 0x1d6ec.
  Proof.
    ddestruct (U_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). destruct (U_layout_facts2 sp0) as [F8 F9]. pose proof (U_layout_facts3 sp0) as F10.
    pose proof (U_asn1_get_alg_spec (U_layout sp0) (U_platform_zeroize_spec (U_layout sp0))) as GETALG.
    pose proof (U_x509_crt_ext_spec (U_layout sp0) (U_HI sp0) F1 F8 (U_layout_facts4 sp0) F3 F5 F6 F7 U_x509_basic_spec U_x509_skid_spec
                  (U_x509_akid_spec (U_layout sp0) (U_HI sp0) F8 F1 F3) (U_x509_policies_spec (U_layout sp0) (U_HI sp0) F8 F3)) as CRTEXT.
    pose proof (U_x509_crt_parse_spec (U_layout sp0) (U_HI sp0) PK SI F1 F8 F2 F9 F10 F3 F5 F6 F7 (U_heap_nodup sp0) PKFREE PKPARSE
                  U_x509_get_dates_spec U_x509_get_uid_spec CRTEXT) as CRTPARSE.
    apply (fuzz_entry sp0 (option (p7_own * p7_junk)) (pkcs7_at usegs PK) SI).
    - exact (U_pkcs7_parse_der_spec (U_layout sp0) (U_HI sp0) PK SI F1 F8 F2 F9 F3 F4 F5 F6 F7 (U_heap_nodup sp0) PKFREE GETALG
               (U_pkcs7_getcerts_spec (U_layout sp0) (U_HI sp0) PK SI F3 F6 F7 CRTPARSE)
               (U_pkcs7_getsigners_spec (U_layout sp0) (U_HI sp0) F1 F8 F2 F3 F5 F6 F7 (U_heap_nodup sp0) GETALG)).
    - exact (U_pkcs7_free_spec (U_layout sp0) (U_HI sp0) PK F1 F2 F3 F4 F5 F6 F7 (U_heap_nodup sp0) PKFREE).
  Qed.
End Top.

(* [comment removed for export] *)
