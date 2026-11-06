(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap P_heap_laws P_platform_zeroize P_platform_zeroize_proof
     P_asn1_get_alg_A P_asn1_get_alg P_oid_md_alg P_oid_sig_alg_A P_pkcs7_top P_fuzz_entry P_pkcs7_free P_pkcs7_parse P_pkcs7_signers P_pkcs7_getcerts
     P_x509_get_dates P_x509_get_uid P_x509_crt_parse P_oid_x509_ext P_x509_crt_ext P_x509_basic P_x509_skid P_x509_akid P_x509_policies.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract RepCrt CrtStmts CrtRelStmts CrtParseStmts SInv CrtExtStmts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_fuzz_top () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.hl_free"; "OSSVerify.KrLib.P.P_layout.P_layout"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"].


Lemma P_layout_facts sp0 : ltac2:(CDefT.buildp (gd_tbl_P_fuzz_top ()) "(0.(1.$2.(3.(4.O1.))+3<3:0.)(0.(5.(4.O1.)$6.+8.)(0.(7.=(8.(4.O1.)))(0.(7.(8.(4.O1.))+2710.)(0.Pa,$2.P,(9.(4.O1.)R1.)(:.(4.O1.)R2.)(0.(0.(7.(;.(4.O1.))(<.(4.O1.)))(7.(=.(4.O1.))(>.(4.O1.))))(7.(=.(4.O1.))(?.(4.O1.)))))))))")
(* [comment removed for export] *).
Proof.
  split; [reflexivity|]. split.
  { unfold const_at, P_MEMSET_FUNC. cbn [hl_data_lo hl_data_hi hl_written P_layout]. unfold P_written. split; [lia|]. split; [lia|]. intros a Ha. lia. }
  split; [cbn; lia|]. split; [cbn; lia|]. split; [exact P_static_written|]. split; [cbn; lia|].
  pose proof (@alloc_ceiling_lo (P_layout sp0)) as ACLO. change (hl_data_hi (P_layout sp0)) with 0x7b000. lia.
Qed.

Lemma P_layout_facts2 sp0 : hl_calloc (P_layout sp0) = 0x3c268 /\ const_at (P_layout sp0) P_OID_MD_ALG_TBL 440.
Proof.
  split; [reflexivity|].
  unfold const_at, P_OID_MD_ALG_TBL. cbn [hl_data_lo hl_data_hi hl_written P_layout]. unfold P_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma P_layout_facts3 sp0 : const_at (P_layout sp0) P_OID_SIG_ALG_TBL 560.
Proof.
  unfold const_at, P_OID_SIG_ALG_TBL. cbn [hl_data_lo hl_data_hi hl_written P_layout]. unfold P_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma P_layout_facts4 sp0 : const_at (P_layout sp0) P_OID_X509_EXT_TBL 320.
Proof.
  unfold const_at, P_OID_X509_EXT_TBL. cbn [hl_data_lo hl_data_hi hl_written P_layout]. unfold P_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Section Top.
  Variable sp0 : word.
  Variable PK : pk_class psegs.
  Variable SI : sinv (P_layout sp0).
  Hypothesis PKFREE : pk_free_stmt2 psegs (P_layout sp0) (P_HI sp0) PK 0x279c4.                (* [comment removed for export] *)
  Hypothesis PKPARSE : pk_parse_subpubkey_stmt psegs (P_layout sp0) (P_HI sp0) PK SI 0x27230. (* [comment removed for export] *)

  #[using="PK PKFREE PKPARSE"] Theorem fuzz_entry_top : fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) SI 0x1d26c.
  Proof.
    ddestruct (P_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). destruct (P_layout_facts2 sp0) as [F8 F9]. pose proof (P_layout_facts3 sp0) as F10.
    pose proof (P_asn1_get_alg_spec (P_layout sp0) (P_platform_zeroize_spec (P_layout sp0))) as GETALG.
    pose proof (P_x509_crt_ext_spec (P_layout sp0) (P_HI sp0) F1 F8 (P_layout_facts4 sp0) F3 F5 F6 F7 P_x509_basic_spec P_x509_skid_spec
                  (P_x509_akid_spec (P_layout sp0) (P_HI sp0) F8 F1 F3) (P_x509_policies_spec (P_layout sp0) (P_HI sp0) F8 F3)) as CRTEXT.
    pose proof (P_x509_crt_parse_spec (P_layout sp0) (P_HI sp0) PK SI F1 F8 F2 F9 F10 F3 F5 F6 F7 (P_heap_nodup sp0) PKFREE PKPARSE
                  P_x509_get_dates_spec P_x509_get_uid_spec CRTEXT) as CRTPARSE.
    apply (fuzz_entry sp0 (option (p7_own * p7_junk)) (pkcs7_at psegs PK) SI).
    - exact (P_pkcs7_parse_der_spec (P_layout sp0) (P_HI sp0) PK SI F1 F8 F2 F9 F3 F4 F5 F6 F7 (P_heap_nodup sp0) PKFREE GETALG
               (P_pkcs7_getcerts_spec (P_layout sp0) (P_HI sp0) PK SI F3 F6 F7 CRTPARSE)
               (P_pkcs7_getsigners_spec (P_layout sp0) (P_HI sp0) F1 F8 F2 F3 F5 F6 F7 (P_heap_nodup sp0) GETALG)).
    - exact (P_pkcs7_free_spec (P_layout sp0) (P_HI sp0) PK F1 F2 F3 F4 F5 F6 F7 (P_heap_nodup sp0) PKFREE).
  Qed.
End Top.

(* [comment removed for export] *)
