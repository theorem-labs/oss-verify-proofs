(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap U_heap_laws U_platform_zeroize U_platform_zeroize_proof U_asn1_get_alg_A U_asn1_get_alg U_oid_md_alg U_oid_sig_alg_A U_fuzz_entry U_pkcs7_free U_pkcs7_parse U_pkcs7_signers U_pkcs7_getcerts U_x509_get_dates U_x509_get_uid U_x509_crt_parse U_oid_x509_ext U_x509_crt_ext U_x509_basic U_x509_skid U_x509_akid U_x509_policies. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract RepCrt CrtStmts CrtRelStmts CrtParseStmts SInv. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_fuzz_top () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.hl_free"; "OSSVerify.KrLib.U.U_layout.U_layout"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.U.U_platform_zeroize.U_MEMSET_FUNC"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"].


Lemma U_layout_facts sp0 : ltac2:(CDefT.buildp (gd_tbl_P_fuzz_top ()) "(0.(1.$2.(3.(4.O1.))+3?:98.)(0.(5.(4.O1.)$6.+8.)(0.(7.=(8.(4.O1.)))(0.(7.(8.(4.O1.))+2710.)(0.Pa,$2.P,(9.(4.O1.)R1.)(:.(4.O1.)R2.)(0.(0.(7.(;.(4.O1.))(<.(4.O1.)))(7.(=.(4.O1.))(>.(4.O1.))))(7.(=.(4.O1.))(?.(4.O1.)))))))))")
(* [comment removed for export] *).
Proof.
  pose proof (hl_ceil_lo (U_layout sp0)) as ceil_floor.
  unfold alloc_ceiling.
  refine (conj eq_refl _).
  refine (conj _ (conj _ (conj _ (conj U_static_written _)))).
  - unfold const_at, U_MEMSET_FUNC; cbn [U_layout hl_data_lo hl_data_hi hl_written].
    refine (conj _ (conj _ _)); [lia | lia |].
    intros addr in_range; unfold U_written; lia.
  - cbn; lia.
  - cbn; lia.
  - revert ceil_floor; cbn [U_layout hl_img_lo hl_img_hi hl_data_lo hl_data_hi].
    intro ceil_floor; lia.
Qed.

Lemma U_layout_facts2 sp0 : hl_calloc (U_layout sp0) = 0x3f960 /\ const_at (U_layout sp0) U_OID_MD_ALG_TBL 440.
Proof.
  split; [reflexivity |].
  unfold const_at, U_OID_MD_ALG_TBL; cbn [U_layout hl_data_lo hl_data_hi hl_written].
  split; [lia | split; [lia |]].
  intros addr in_range written; unfold U_written in written; lia.
Qed.

Lemma U_layout_facts3 sp0 : const_at (U_layout sp0) U_OID_SIG_ALG_TBL 560.
Proof.
  unfold const_at, U_OID_SIG_ALG_TBL; cbn [U_layout hl_data_lo hl_data_hi hl_written].
  split; [lia | split; [lia |]].
  intros addr in_range written; unfold U_written in written; lia.
Qed.

Lemma U_layout_facts4 sp0 : const_at (U_layout sp0) U_OID_X509_EXT_TBL 320.
Proof.
  unfold const_at, U_OID_X509_EXT_TBL; cbn [U_layout hl_data_lo hl_data_hi hl_written].
  split; [lia | split; [lia |]].
  intros addr in_range written; unfold U_written in written; lia.
Qed.

Section Top.
  Variable sp0 : word.
  Variable PK : pk_class usegs.
  Variable SI : sinv (U_layout sp0).
  Hypothesis PKFREE : pk_free_stmt2 usegs (U_layout sp0) (U_HI sp0) PK 0x29c28.                (* [comment removed for export] *)
  Hypothesis PKPARSE : pk_parse_subpubkey_stmt usegs (U_layout sp0) (U_HI sp0) PK SI 0x292a8. (* [comment removed for export] *)

  #[using="PK PKFREE PKPARSE"] Theorem fuzz_entry_top : fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) SI 0x1d6ec.
  Proof.
    pose proof (U_heap_nodup sp0) as heap_nodup.
    destruct (U_layout_facts sp0)
      as (free_at & memset_const & stack_nonneg & stack_cap & static_written & data_in_img & data_ceil).
    destruct (U_layout_facts2 sp0) as (calloc_at & mdtbl_const).
    pose proof (U_layout_facts3 sp0) as sigtbl_const.
    pose proof (U_layout_facts4 sp0) as exttbl_const.
    pose proof (U_asn1_get_alg_spec (U_layout sp0) (U_platform_zeroize_spec (U_layout sp0))) as getalg.
    pose proof (U_x509_crt_ext_spec (U_layout sp0) (U_HI sp0) free_at calloc_at exttbl_const
                  stack_nonneg static_written data_in_img data_ceil
                  U_x509_basic_spec U_x509_skid_spec
                  (U_x509_akid_spec (U_layout sp0) (U_HI sp0) eq_refl eq_refl stack_nonneg)
                  (U_x509_policies_spec (U_layout sp0) (U_HI sp0) eq_refl stack_nonneg)) as crtext.
    pose proof (U_x509_crt_parse_spec (U_layout sp0) (U_HI sp0) PK SI free_at calloc_at memset_const
                  mdtbl_const sigtbl_const stack_nonneg static_written data_in_img data_ceil heap_nodup
                  PKFREE PKPARSE U_x509_get_dates_spec U_x509_get_uid_spec crtext) as crtparse.
    pose proof (U_pkcs7_getcerts_spec (U_layout sp0) (U_HI sp0) PK SI stack_nonneg data_in_img data_ceil
                  crtparse) as getcerts.
    pose proof (U_pkcs7_getsigners_spec (U_layout sp0) (U_HI sp0) free_at calloc_at memset_const
                  stack_nonneg static_written data_in_img data_ceil heap_nodup getalg) as getsigners.
    pose proof (U_pkcs7_free_spec (U_layout sp0) (U_HI sp0) PK free_at memset_const stack_nonneg
                  stack_cap static_written data_in_img data_ceil heap_nodup PKFREE) as free_ok.
    pose proof (U_pkcs7_parse_der_spec (U_layout sp0) (U_HI sp0) PK SI free_at calloc_at memset_const
                  mdtbl_const stack_nonneg stack_cap static_written data_in_img data_ceil heap_nodup
                  PKFREE getalg getcerts getsigners) as parse_ok.
    exact (fuzz_entry sp0 _ (pkcs7_at usegs PK) SI parse_ok free_ok).
  Qed.
End Top.

(* [comment removed for export] *)
