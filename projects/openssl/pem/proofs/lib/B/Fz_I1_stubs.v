(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_I1_defs Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_I1_const Fz_I1_reason Fz_I1_stubk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sw0_BN : stub_w0_spec 0x54992c 0x1800064 0x54994c. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BN : stub_w1_spec 0x54994c 0x549960 0x5d3780. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BN : stub_w2_spec 0x549960. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_RSA : stub_w0_spec 0x549974 0x2000064 0x549994. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_RSA : stub_w1_spec 0x549994 0x5499a8 0x5d3940. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_RSA : stub_w2_spec 0x5499a8. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DH : stub_w0_spec 0x5499bc 0x280007f 0x5499dc. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DH : stub_w1_spec 0x5499dc 0x5499f0 0x5d3fa0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DH : stub_w2_spec 0x5499f0. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_EVP : stub_w0_spec 0x549a04 0x300008f 0x549a24. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_EVP : stub_w1_spec 0x549a24 0x549a38 0x5d4220. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_EVP : stub_w2_spec 0x549a38. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_BUF : stub_w0_spec 0x549a4c 0x0 0x549a68. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BUF : stub_w1_spec 0x549a68 0x549a7c 0xf1c20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BUF : stub_w2_spec 0x549a7c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OBJ : stub_w0_spec 0x549a90 0x4000066 0x549ab0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OBJ : stub_w1_spec 0x549ab0 0x549ac4 0x5d4be0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OBJ : stub_w2_spec 0x549ac4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PEM : stub_w0_spec 0x549ad8 0x4800064 0x549af8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PEM : stub_w1_spec 0x549af8 0x549b0c 0x5d4c40. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PEM : stub_w2_spec 0x549b0c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DSA : stub_w0_spec 0x549b20 0x5000072 0x549b40. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DSA : stub_w1_spec 0x549b40 0x549b54 0x5d4f00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DSA : stub_w2_spec 0x549b54. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_X509 : stub_w0_spec 0x549b68 0x580006e 0x549b88. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_X509 : stub_w1_spec 0x549b88 0x549b9c 0x5d5060. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_X509 : stub_w2_spec 0x549b9c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ASN1 : stub_w0_spec 0x549bb0 0x68000ab 0x549bd0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ASN1 : stub_w1_spec 0x549bd0 0x549be4 0x5d5420. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ASN1 : stub_w2_spec 0x549be4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CONF : stub_w0_spec 0x549bf8 0x700006e 0x549c18. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CONF : stub_w1_spec 0x549c18 0x549c2c 0x5d5d40. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CONF : stub_w2_spec 0x549c2c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CRYPTO : stub_w0_spec 0x549c40 0x7800075 0x549c60. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CRYPTO : stub_w1_spec 0x549c60 0x549c74 0x5d5f60. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CRYPTO : stub_w2_spec 0x549c74. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_COMP : stub_w0_spec 0x549c88 0x14800066 0x549ca8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_COMP : stub_w1_spec 0x549ca8 0x549cbc 0x5d61e0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_COMP : stub_w2_spec 0x549cbc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_EC : stub_w0_spec 0x549cd0 0x8000073 0x549cf0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_EC : stub_w1_spec 0x549cf0 0x549d04 0x5d62c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_EC : stub_w2_spec 0x549d04. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_BIO : stub_w0_spec 0x549d18 0x10000064 0x549d38. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_BIO : stub_w1_spec 0x549d38 0x549d4c 0x5d68c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_BIO : stub_w2_spec 0x549d4c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PKCS7 : stub_w0_spec 0x549d60 0x10800075 0x549d80. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PKCS7 : stub_w1_spec 0x549d80 0x549d94 0x5d6c80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PKCS7 : stub_w2_spec 0x549d94. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_X509V3 : stub_w0_spec 0x549da8 0x11000076 0x549dc8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_X509V3 : stub_w1_spec 0x549dc8 0x549ddc 0x5d6f80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_X509V3 : stub_w2_spec 0x549ddc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PKCS12 : stub_w0_spec 0x549df0 0x11800073 0x549e10. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PKCS12 : stub_w1_spec 0x549e10 0x549e24 0x5d7540. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PKCS12 : stub_w2_spec 0x549e24. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_RAND : stub_w0_spec 0x549e38 0x12000066 0x549e58. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_RAND : stub_w1_spec 0x549e58 0x549e6c 0x5d7700. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_RAND : stub_w2_spec 0x549e6c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_DSO : stub_w0_spec 0x549e80 0x12800064 0x549ea0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_DSO : stub_w1_spec 0x549ea0 0x549eb4 0x5d7a80. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_DSO : stub_w2_spec 0x549eb4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_TS : stub_w0_spec 0x549ec8 0x17800084 0x549ee8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_TS : stub_w1_spec 0x549ee8 0x549efc 0x5d7be0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_TS : stub_w2_spec 0x549efc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_HTTP : stub_w0_spec 0x549f10 0x1e80006c 0x549f30. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_HTTP : stub_w1_spec 0x549f30 0x549f44 0x5d7f00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_HTTP : stub_w2_spec 0x549f44. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OCSP : stub_w0_spec 0x549f58 0x13800065 0x549f78. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OCSP : stub_w1_spec 0x549f78 0x549f8c 0x5d81a0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OCSP : stub_w2_spec 0x549f8c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_UI : stub_w0_spec 0x549fa0 0x14000068 0x549fc0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_UI : stub_w1_spec 0x549fc0 0x549fd4 0x5d83a0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_UI : stub_w2_spec 0x549fd4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CMS : stub_w0_spec 0x549fe8 0x17000063 0x54a008. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CMS : stub_w1_spec 0x54a008 0x54a01c 0x5d84a0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CMS : stub_w2_spec 0x54a01c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CRMF : stub_w0_spec 0x54a030 0x1c000064 0x54a050. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CRMF : stub_w1_spec 0x54a050 0x54a064 0x5d8ca0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CRMF : stub_w2_spec 0x54a064. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CMP : stub_w0_spec 0x54a078 0x1d00008b 0x54a098. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CMP : stub_w1_spec 0x54a098 0x54a0ac 0x5d8f00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CMP : stub_w2_spec 0x54a0ac. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_CT : stub_w0_spec 0x54a0c0 0x1900006c 0x54a0e0. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_CT : stub_w1_spec 0x54a0e0 0x54a0f4 0x5d9760. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_CT : stub_w2_spec 0x54a0f4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ESS : stub_w0_spec 0x54a108 0x1b00006b 0x54a128. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ESS : stub_w1_spec 0x54a128 0x54a13c 0x5d98c0. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ESS : stub_w2_spec 0x54a13c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_ASYNC : stub_w0_spec 0x54a150 0x19800065 0x54a170. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_ASYNC : stub_w1_spec 0x54a170 0x54a184 0x5d9980. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_ASYNC : stub_w2_spec 0x54a184. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_SM2 : stub_w0_spec 0x54a198 0x1a800064 0x54a1b8. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_SM2 : stub_w1_spec 0x54a1b8 0x54a1cc 0x5d9a00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_SM2 : stub_w2_spec 0x54a1cc. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_OSSL_STORE : stub_w0_spec 0x54a1e0 0x1600006b 0x54a200. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_OSSL_STORE : stub_w1_spec 0x54a200 0x54a214 0x5d9b20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_OSSL_STORE : stub_w2_spec 0x54a214. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PROP : stub_w0_spec 0x54a228 0x1b800064 0x54a248. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PROP : stub_w1_spec 0x54a248 0x54a25c 0x5d9d20. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PROP : stub_w2_spec 0x54a25c. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.
Lemma sw0_PROV : stub_w0_spec 0x54a270 0x1c8000b8 0x54a290. Proof. unfold stub_w0_spec. intros until lo. intros ST LO0 LO HTOP MI. stub_w0_tac sp m ST. Qed.
Lemma sw1_PROV : stub_w1_spec 0x54a290 0x54a2a4 0x5d9e00. Proof. unfold stub_w1_spec. intros until v. intros VR ST LO0 LO HTOP MI. stub_w1_tac sp m v. Qed.
Lemma sw2_PROV : stub_w2_spec 0x54a2a4. Proof. unfold stub_w2_spec. intros until s0v. intros FR ST LO0 LO HTOP MI. stub_w2_tac sp m FR ST. Qed.

Section Stubs.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ERS : ers_stmt RT GOBJ.
Hypothesis C_ELC : err_const_stmt RT GOBJ.

Theorem stub_BN : stub_stmt RT GOBJ 0x54992c 0x5d3780 0x549960 22.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54992c 0x1800064 0x5d3780 0x54994c 0x549960 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BN sw1_BN sw2_BN 22). Qed.
Theorem stub_RSA : stub_stmt RT GOBJ 0x549974 0x5d3940 0x5499a8 81.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549974 0x2000064 0x5d3940 0x549994 0x5499a8 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_RSA sw1_RSA sw2_RSA 81). Qed.
Theorem stub_DH : stub_stmt RT GOBJ 0x5499bc 0x5d3fa0 0x5499f0 31.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x5499bc 0x280007f 0x5d3fa0 0x5499dc 0x5499f0 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DH sw1_DH sw2_DH 31). Qed.
Theorem stub_EVP : stub_stmt RT GOBJ 0x549a04 0x5d4220 0x549a38 125.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549a04 0x300008f 0x5d4220 0x549a24 0x549a38 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_EVP sw1_EVP sw2_EVP 125). Qed.
Theorem stub_BUF : stub_stmt RT GOBJ 0x549a4c 0xf1c20 0x549a7c 0.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549a4c 0x0 0xf1c20 0x549a68 0x549a7c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BUF sw1_BUF sw2_BUF 0). Qed.
Theorem stub_OBJ : stub_stmt RT GOBJ 0x549a90 0x5d4be0 0x549ac4 3.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549a90 0x4000066 0x5d4be0 0x549ab0 0x549ac4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OBJ sw1_OBJ sw2_OBJ 3). Qed.
Theorem stub_PEM : stub_stmt RT GOBJ 0x549ad8 0x5d4c40 0x549b0c 34.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549ad8 0x4800064 0x5d4c40 0x549af8 0x549b0c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PEM sw1_PEM sw2_PEM 34). Qed.
Theorem stub_DSA : stub_stmt RT GOBJ 0x549b20 0x5d4f00 0x549b54 16.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549b20 0x5000072 0x5d4f00 0x549b40 0x549b54 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DSA sw1_DSA sw2_DSA 16). Qed.
Theorem stub_X509 : stub_stmt RT GOBJ 0x549b68 0x5d5060 0x549b9c 47.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549b68 0x580006e 0x5d5060 0x549b88 0x549b9c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_X509 sw1_X509 sw2_X509 47). Qed.
Theorem stub_ASN1 : stub_stmt RT GOBJ 0x549bb0 0x5d5420 0x549be4 117.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549bb0 0x68000ab 0x5d5420 0x549bd0 0x549be4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ASN1 sw1_ASN1 sw2_ASN1 117). Qed.
Theorem stub_CONF : stub_stmt RT GOBJ 0x549bf8 0x5d5d40 0x549c2c 27.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549bf8 0x700006e 0x5d5d40 0x549c18 0x549c2c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CONF sw1_CONF sw2_CONF 27). Qed.
Theorem stub_CRYPTO : stub_stmt RT GOBJ 0x549c40 0x5d5f60 0x549c74 31.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549c40 0x7800075 0x5d5f60 0x549c60 0x549c74 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CRYPTO sw1_CRYPTO sw2_CRYPTO 31). Qed.
Theorem stub_COMP : stub_stmt RT GOBJ 0x549c88 0x5d61e0 0x549cbc 10.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549c88 0x14800066 0x5d61e0 0x549ca8 0x549cbc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_COMP sw1_COMP sw2_COMP 10). Qed.
Theorem stub_EC : stub_stmt RT GOBJ 0x549cd0 0x5d62c0 0x549d04 76.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549cd0 0x8000073 0x5d62c0 0x549cf0 0x549d04 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_EC sw1_EC sw2_EC 76). Qed.
Theorem stub_BIO : stub_stmt RT GOBJ 0x549d18 0x5d68c0 0x549d4c 47.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549d18 0x10000064 0x5d68c0 0x549d38 0x549d4c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_BIO sw1_BIO sw2_BIO 47). Qed.
Theorem stub_PKCS7 : stub_stmt RT GOBJ 0x549d60 0x5d6c80 0x549d94 38.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549d60 0x10800075 0x5d6c80 0x549d80 0x549d94 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PKCS7 sw1_PKCS7 sw2_PKCS7 38). Qed.
Theorem stub_X509V3 : stub_stmt RT GOBJ 0x549da8 0x5d6f80 0x549ddc 73.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549da8 0x11000076 0x5d6f80 0x549dc8 0x549ddc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_X509V3 sw1_X509V3 sw2_X509V3 73). Qed.
Theorem stub_PKCS12 : stub_stmt RT GOBJ 0x549df0 0x5d7540 0x549e24 22.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549df0 0x11800073 0x5d7540 0x549e10 0x549e24 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PKCS12 sw1_PKCS12 sw2_PKCS12 22). Qed.
Theorem stub_RAND : stub_stmt RT GOBJ 0x549e38 0x5d7700 0x549e6c 45.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549e38 0x12000066 0x5d7700 0x549e58 0x549e6c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_RAND sw1_RAND sw2_RAND 45). Qed.
Theorem stub_DSO : stub_stmt RT GOBJ 0x549e80 0x5d7a80 0x549eb4 16.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549e80 0x12800064 0x5d7a80 0x549ea0 0x549eb4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_DSO sw1_DSO sw2_DSO 16). Qed.
Theorem stub_TS : stub_stmt RT GOBJ 0x549ec8 0x5d7be0 0x549efc 39.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549ec8 0x17800084 0x5d7be0 0x549ee8 0x549efc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_TS sw1_TS sw2_TS 39). Qed.
Theorem stub_HTTP : stub_stmt RT GOBJ 0x549f10 0x5d7f00 0x549f44 32.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549f10 0x1e80006c 0x5d7f00 0x549f30 0x549f44 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_HTTP sw1_HTTP sw2_HTTP 32). Qed.
Theorem stub_OCSP : stub_stmt RT GOBJ 0x549f58 0x5d81a0 0x549f8c 25.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549f58 0x13800065 0x5d81a0 0x549f78 0x549f8c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OCSP sw1_OCSP sw2_OCSP 25). Qed.
Theorem stub_UI : stub_stmt RT GOBJ 0x549fa0 0x5d83a0 0x549fd4 13.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549fa0 0x14000068 0x5d83a0 0x549fc0 0x549fd4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_UI sw1_UI sw2_UI 13). Qed.
Theorem stub_CMS : stub_stmt RT GOBJ 0x549fe8 0x5d84a0 0x54a01c 102.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x549fe8 0x17000063 0x5d84a0 0x54a008 0x54a01c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CMS sw1_CMS sw2_CMS 102). Qed.
Theorem stub_CRMF : stub_stmt RT GOBJ 0x54a030 0x5d8ca0 0x54a064 30.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a030 0x1c000064 0x5d8ca0 0x54a050 0x54a064 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CRMF sw1_CRMF sw2_CRMF 30). Qed.
Theorem stub_CMP : stub_stmt RT GOBJ 0x54a078 0x5d8f00 0x54a0ac 106.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a078 0x1d00008b 0x5d8f00 0x54a098 0x54a0ac ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CMP sw1_CMP sw2_CMP 106). Qed.
Theorem stub_CT : stub_stmt RT GOBJ 0x54a0c0 0x5d9760 0x54a0f4 17.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a0c0 0x1900006c 0x5d9760 0x54a0e0 0x54a0f4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_CT sw1_CT sw2_CT 17). Qed.
Theorem stub_ESS : stub_stmt RT GOBJ 0x54a108 0x5d98c0 0x54a13c 9.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a108 0x1b00006b 0x5d98c0 0x54a128 0x54a13c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ESS sw1_ESS sw2_ESS 9). Qed.
Theorem stub_ASYNC : stub_stmt RT GOBJ 0x54a150 0x5d9980 0x54a184 4.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a150 0x19800065 0x5d9980 0x54a170 0x54a184 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_ASYNC sw1_ASYNC sw2_ASYNC 4). Qed.
Theorem stub_SM2 : stub_stmt RT GOBJ 0x54a198 0x5d9a00 0x54a1cc 14.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a198 0x1a800064 0x5d9a00 0x54a1b8 0x54a1cc ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_SM2 sw1_SM2 sw2_SM2 14). Qed.
Theorem stub_OSSL_STORE : stub_stmt RT GOBJ 0x54a1e0 0x5d9b20 0x54a214 25.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a1e0 0x1600006b 0x5d9b20 0x54a200 0x54a214 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_OSSL_STORE sw1_OSSL_STORE sw2_OSSL_STORE 25). Qed.
Theorem stub_PROP : stub_stmt RT GOBJ 0x54a228 0x5d9d20 0x54a25c 11.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a228 0x1b800064 0x5d9d20 0x54a248 0x54a25c ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PROP sw1_PROP sw2_PROP 11). Qed.
Theorem stub_PROV : stub_stmt RT GOBJ 0x54a270 0x5d9e00 0x54a2a4 160.
Proof. exact (stub_cps_gen RT GOBJ AF AFP C_ERS C_ELC 0x54a270 0x1c8000b8 0x5d9e00 0x54a290 0x54a2a4 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) eq_refl sw0_PROV sw1_PROV sw2_PROV 160). Qed.
End Stubs.
