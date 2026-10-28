(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_I1_defs Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_I1_const Fz_I1_reason Fz_I1_stubk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sw0_BN : stub_w0_spec 0x51123c 0x1800064 0x51125c. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BN : stub_w1_spec 0x51125c 0x511270 0x59b500. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BN : stub_w2_spec 0x511270. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_RSA : stub_w0_spec 0x511284 0x2000064 0x5112a4. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_RSA : stub_w1_spec 0x5112a4 0x5112b8 0x59b6c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_RSA : stub_w2_spec 0x5112b8. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DH : stub_w0_spec 0x5112cc 0x280007f 0x5112ec. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DH : stub_w1_spec 0x5112ec 0x511300 0x59bd20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DH : stub_w2_spec 0x511300. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_EVP : stub_w0_spec 0x511314 0x300008f 0x511334. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_EVP : stub_w1_spec 0x511334 0x511348 0x59bfa0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_EVP : stub_w2_spec 0x511348. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_BUF : stub_w0_spec 0x51135c 0x0 0x511378. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BUF : stub_w1_spec 0x511378 0x51138c 0xf88e0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BUF : stub_w2_spec 0x51138c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OBJ : stub_w0_spec 0x5113a0 0x4000066 0x5113c0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OBJ : stub_w1_spec 0x5113c0 0x5113d4 0x59c960. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OBJ : stub_w2_spec 0x5113d4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PEM : stub_w0_spec 0x5113e8 0x4800064 0x511408. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PEM : stub_w1_spec 0x511408 0x51141c 0x59c9c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PEM : stub_w2_spec 0x51141c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DSA : stub_w0_spec 0x511430 0x5000072 0x511450. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DSA : stub_w1_spec 0x511450 0x511464 0x59cc80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DSA : stub_w2_spec 0x511464. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_X509 : stub_w0_spec 0x511478 0x580006e 0x511498. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_X509 : stub_w1_spec 0x511498 0x5114ac 0x59cde0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_X509 : stub_w2_spec 0x5114ac. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ASN1 : stub_w0_spec 0x5114c0 0x68000ab 0x5114e0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ASN1 : stub_w1_spec 0x5114e0 0x5114f4 0x59d1a0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ASN1 : stub_w2_spec 0x5114f4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CONF : stub_w0_spec 0x511508 0x700006e 0x511528. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CONF : stub_w1_spec 0x511528 0x51153c 0x59dac0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CONF : stub_w2_spec 0x51153c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CRYPTO : stub_w0_spec 0x511550 0x7800075 0x511570. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CRYPTO : stub_w1_spec 0x511570 0x511584 0x59dce0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CRYPTO : stub_w2_spec 0x511584. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_COMP : stub_w0_spec 0x511598 0x14800066 0x5115b8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_COMP : stub_w1_spec 0x5115b8 0x5115cc 0x59df60. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_COMP : stub_w2_spec 0x5115cc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_EC : stub_w0_spec 0x5115e0 0x8000073 0x511600. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_EC : stub_w1_spec 0x511600 0x511614 0x59e040. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_EC : stub_w2_spec 0x511614. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_BIO : stub_w0_spec 0x511628 0x10000064 0x511648. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BIO : stub_w1_spec 0x511648 0x51165c 0x59e640. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BIO : stub_w2_spec 0x51165c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PKCS7 : stub_w0_spec 0x511670 0x10800075 0x511690. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PKCS7 : stub_w1_spec 0x511690 0x5116a4 0x59ea00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PKCS7 : stub_w2_spec 0x5116a4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_X509V3 : stub_w0_spec 0x5116b8 0x11000076 0x5116d8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_X509V3 : stub_w1_spec 0x5116d8 0x5116ec 0x59ed00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_X509V3 : stub_w2_spec 0x5116ec. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PKCS12 : stub_w0_spec 0x511700 0x11800073 0x511720. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PKCS12 : stub_w1_spec 0x511720 0x511734 0x59f2c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PKCS12 : stub_w2_spec 0x511734. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_RAND : stub_w0_spec 0x511748 0x12000066 0x511768. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_RAND : stub_w1_spec 0x511768 0x51177c 0x59f480. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_RAND : stub_w2_spec 0x51177c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DSO : stub_w0_spec 0x511790 0x12800064 0x5117b0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DSO : stub_w1_spec 0x5117b0 0x5117c4 0x59f800. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DSO : stub_w2_spec 0x5117c4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_TS : stub_w0_spec 0x5117d8 0x17800084 0x5117f8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_TS : stub_w1_spec 0x5117f8 0x51180c 0x59f960. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_TS : stub_w2_spec 0x51180c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_HTTP : stub_w0_spec 0x511820 0x1e80006c 0x511840. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_HTTP : stub_w1_spec 0x511840 0x511854 0x59fc80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_HTTP : stub_w2_spec 0x511854. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OCSP : stub_w0_spec 0x511868 0x13800065 0x511888. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OCSP : stub_w1_spec 0x511888 0x51189c 0x59ff20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OCSP : stub_w2_spec 0x51189c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_UI : stub_w0_spec 0x5118b0 0x14000068 0x5118d0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_UI : stub_w1_spec 0x5118d0 0x5118e4 0x5a0120. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_UI : stub_w2_spec 0x5118e4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CMS : stub_w0_spec 0x5118f8 0x17000063 0x511918. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CMS : stub_w1_spec 0x511918 0x51192c 0x5a0220. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CMS : stub_w2_spec 0x51192c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CRMF : stub_w0_spec 0x511940 0x1c000064 0x511960. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CRMF : stub_w1_spec 0x511960 0x511974 0x5a0a20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CRMF : stub_w2_spec 0x511974. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CMP : stub_w0_spec 0x511988 0x1d00008b 0x5119a8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CMP : stub_w1_spec 0x5119a8 0x5119bc 0x5a0c80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CMP : stub_w2_spec 0x5119bc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CT : stub_w0_spec 0x5119d0 0x1900006c 0x5119f0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CT : stub_w1_spec 0x5119f0 0x511a04 0x5a14e0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CT : stub_w2_spec 0x511a04. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ESS : stub_w0_spec 0x511a18 0x1b00006b 0x511a38. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ESS : stub_w1_spec 0x511a38 0x511a4c 0x5a1640. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ESS : stub_w2_spec 0x511a4c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ASYNC : stub_w0_spec 0x511a60 0x19800065 0x511a80. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ASYNC : stub_w1_spec 0x511a80 0x511a94 0x5a1700. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ASYNC : stub_w2_spec 0x511a94. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_SM2 : stub_w0_spec 0x511aa8 0x1a800064 0x511ac8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_SM2 : stub_w1_spec 0x511ac8 0x511adc 0x5a1780. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_SM2 : stub_w2_spec 0x511adc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OSSL_STORE : stub_w0_spec 0x511af0 0x1600006b 0x511b10. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OSSL_STORE : stub_w1_spec 0x511b10 0x511b24 0x5a18a0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OSSL_STORE : stub_w2_spec 0x511b24. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PROP : stub_w0_spec 0x511b38 0x1b800064 0x511b58. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PROP : stub_w1_spec 0x511b58 0x511b6c 0x5a1aa0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PROP : stub_w2_spec 0x511b6c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PROV : stub_w0_spec 0x511b80 0x1c8000b8 0x511ba0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PROV : stub_w1_spec 0x511ba0 0x511bb4 0x5a1b80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PROV : stub_w2_spec 0x511bb4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.

Section Stubs.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ERS : ers_stmt RT GOBJ.
Hypothesis C_ELC : err_const_stmt RT GOBJ.

Theorem stub_BN : stub_stmt RT GOBJ 0x51123c 0x59b500 0x511270 22.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x51123c 0x1800064 0x59b500 0x51125c 0x511270 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BN sw1_BN sw2_BN 22). Qed.
Theorem stub_RSA : stub_stmt RT GOBJ 0x511284 0x59b6c0 0x5112b8 81.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511284 0x2000064 0x59b6c0 0x5112a4 0x5112b8 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_RSA sw1_RSA sw2_RSA 81). Qed.
Theorem stub_DH : stub_stmt RT GOBJ 0x5112cc 0x59bd20 0x511300 31.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5112cc 0x280007f 0x59bd20 0x5112ec 0x511300 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DH sw1_DH sw2_DH 31). Qed.
Theorem stub_EVP : stub_stmt RT GOBJ 0x511314 0x59bfa0 0x511348 125.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511314 0x300008f 0x59bfa0 0x511334 0x511348 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_EVP sw1_EVP sw2_EVP 125). Qed.
Theorem stub_BUF : stub_stmt RT GOBJ 0x51135c 0xf88e0 0x51138c 0.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x51135c 0x0 0xf88e0 0x511378 0x51138c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BUF sw1_BUF sw2_BUF 0). Qed.
Theorem stub_OBJ : stub_stmt RT GOBJ 0x5113a0 0x59c960 0x5113d4 3.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5113a0 0x4000066 0x59c960 0x5113c0 0x5113d4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OBJ sw1_OBJ sw2_OBJ 3). Qed.
Theorem stub_PEM : stub_stmt RT GOBJ 0x5113e8 0x59c9c0 0x51141c 34.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5113e8 0x4800064 0x59c9c0 0x511408 0x51141c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PEM sw1_PEM sw2_PEM 34). Qed.
Theorem stub_DSA : stub_stmt RT GOBJ 0x511430 0x59cc80 0x511464 16.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511430 0x5000072 0x59cc80 0x511450 0x511464 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DSA sw1_DSA sw2_DSA 16). Qed.
Theorem stub_X509 : stub_stmt RT GOBJ 0x511478 0x59cde0 0x5114ac 47.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511478 0x580006e 0x59cde0 0x511498 0x5114ac ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_X509 sw1_X509 sw2_X509 47). Qed.
Theorem stub_ASN1 : stub_stmt RT GOBJ 0x5114c0 0x59d1a0 0x5114f4 117.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5114c0 0x68000ab 0x59d1a0 0x5114e0 0x5114f4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ASN1 sw1_ASN1 sw2_ASN1 117). Qed.
Theorem stub_CONF : stub_stmt RT GOBJ 0x511508 0x59dac0 0x51153c 27.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511508 0x700006e 0x59dac0 0x511528 0x51153c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CONF sw1_CONF sw2_CONF 27). Qed.
Theorem stub_CRYPTO : stub_stmt RT GOBJ 0x511550 0x59dce0 0x511584 31.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511550 0x7800075 0x59dce0 0x511570 0x511584 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CRYPTO sw1_CRYPTO sw2_CRYPTO 31). Qed.
Theorem stub_COMP : stub_stmt RT GOBJ 0x511598 0x59df60 0x5115cc 10.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511598 0x14800066 0x59df60 0x5115b8 0x5115cc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_COMP sw1_COMP sw2_COMP 10). Qed.
Theorem stub_EC : stub_stmt RT GOBJ 0x5115e0 0x59e040 0x511614 76.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5115e0 0x8000073 0x59e040 0x511600 0x511614 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_EC sw1_EC sw2_EC 76). Qed.
Theorem stub_BIO : stub_stmt RT GOBJ 0x511628 0x59e640 0x51165c 47.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511628 0x10000064 0x59e640 0x511648 0x51165c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BIO sw1_BIO sw2_BIO 47). Qed.
Theorem stub_PKCS7 : stub_stmt RT GOBJ 0x511670 0x59ea00 0x5116a4 38.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511670 0x10800075 0x59ea00 0x511690 0x5116a4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PKCS7 sw1_PKCS7 sw2_PKCS7 38). Qed.
Theorem stub_X509V3 : stub_stmt RT GOBJ 0x5116b8 0x59ed00 0x5116ec 73.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5116b8 0x11000076 0x59ed00 0x5116d8 0x5116ec ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_X509V3 sw1_X509V3 sw2_X509V3 73). Qed.
Theorem stub_PKCS12 : stub_stmt RT GOBJ 0x511700 0x59f2c0 0x511734 22.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511700 0x11800073 0x59f2c0 0x511720 0x511734 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PKCS12 sw1_PKCS12 sw2_PKCS12 22). Qed.
Theorem stub_RAND : stub_stmt RT GOBJ 0x511748 0x59f480 0x51177c 45.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511748 0x12000066 0x59f480 0x511768 0x51177c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_RAND sw1_RAND sw2_RAND 45). Qed.
Theorem stub_DSO : stub_stmt RT GOBJ 0x511790 0x59f800 0x5117c4 16.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511790 0x12800064 0x59f800 0x5117b0 0x5117c4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DSO sw1_DSO sw2_DSO 16). Qed.
Theorem stub_TS : stub_stmt RT GOBJ 0x5117d8 0x59f960 0x51180c 39.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5117d8 0x17800084 0x59f960 0x5117f8 0x51180c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_TS sw1_TS sw2_TS 39). Qed.
Theorem stub_HTTP : stub_stmt RT GOBJ 0x511820 0x59fc80 0x511854 32.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511820 0x1e80006c 0x59fc80 0x511840 0x511854 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_HTTP sw1_HTTP sw2_HTTP 32). Qed.
Theorem stub_OCSP : stub_stmt RT GOBJ 0x511868 0x59ff20 0x51189c 25.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511868 0x13800065 0x59ff20 0x511888 0x51189c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OCSP sw1_OCSP sw2_OCSP 25). Qed.
Theorem stub_UI : stub_stmt RT GOBJ 0x5118b0 0x5a0120 0x5118e4 13.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5118b0 0x14000068 0x5a0120 0x5118d0 0x5118e4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_UI sw1_UI sw2_UI 13). Qed.
Theorem stub_CMS : stub_stmt RT GOBJ 0x5118f8 0x5a0220 0x51192c 102.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5118f8 0x17000063 0x5a0220 0x511918 0x51192c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CMS sw1_CMS sw2_CMS 102). Qed.
Theorem stub_CRMF : stub_stmt RT GOBJ 0x511940 0x5a0a20 0x511974 30.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511940 0x1c000064 0x5a0a20 0x511960 0x511974 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CRMF sw1_CRMF sw2_CRMF 30). Qed.
Theorem stub_CMP : stub_stmt RT GOBJ 0x511988 0x5a0c80 0x5119bc 106.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511988 0x1d00008b 0x5a0c80 0x5119a8 0x5119bc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CMP sw1_CMP sw2_CMP 106). Qed.
Theorem stub_CT : stub_stmt RT GOBJ 0x5119d0 0x5a14e0 0x511a04 17.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5119d0 0x1900006c 0x5a14e0 0x5119f0 0x511a04 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CT sw1_CT sw2_CT 17). Qed.
Theorem stub_ESS : stub_stmt RT GOBJ 0x511a18 0x5a1640 0x511a4c 9.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511a18 0x1b00006b 0x5a1640 0x511a38 0x511a4c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ESS sw1_ESS sw2_ESS 9). Qed.
Theorem stub_ASYNC : stub_stmt RT GOBJ 0x511a60 0x5a1700 0x511a94 4.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511a60 0x19800065 0x5a1700 0x511a80 0x511a94 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ASYNC sw1_ASYNC sw2_ASYNC 4). Qed.
Theorem stub_SM2 : stub_stmt RT GOBJ 0x511aa8 0x5a1780 0x511adc 14.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511aa8 0x1a800064 0x5a1780 0x511ac8 0x511adc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_SM2 sw1_SM2 sw2_SM2 14). Qed.
Theorem stub_OSSL_STORE : stub_stmt RT GOBJ 0x511af0 0x5a18a0 0x511b24 25.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511af0 0x1600006b 0x5a18a0 0x511b10 0x511b24 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OSSL_STORE sw1_OSSL_STORE sw2_OSSL_STORE 25). Qed.
Theorem stub_PROP : stub_stmt RT GOBJ 0x511b38 0x5a1aa0 0x511b6c 11.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511b38 0x1b800064 0x5a1aa0 0x511b58 0x511b6c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PROP sw1_PROP sw2_PROP 11). Qed.
Theorem stub_PROV : stub_stmt RT GOBJ 0x511b80 0x5a1b80 0x511bb4 160.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x511b80 0x1c8000b8 0x5a1b80 0x511ba0 0x511bb4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PROV sw1_PROV sw2_PROV 160). Qed.
End Stubs.
