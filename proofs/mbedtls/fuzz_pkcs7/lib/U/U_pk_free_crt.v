(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts RepRsa RepCrt CrtStmts CrtRelStmts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_asn1_get_sequence_of_A U_pk_free.
Import ListNotations.
Open Scope Z_scope.

Section Crt.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable MT : list modp_ent.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_MSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis CA_RSA : const_at L (U_RSA_INFO + 80) 8.
  Hypothesis CA_EC : forall e, In e U_EC_INFOS -> const_at L (e + 80) 8.

  #[using="HFREE HLS SW DIMG HND CA_MSF CA_RSA CA_EC"] Lemma U_pk_free_spec2 : pk_free_stmt2 usegs L HI (PKC_inst usegs U_RSA_INFO U_EC_INFOS MT) U_PK_FREE.
  Proof.
    unfold pk_free_stmt2. intros.
    eapply (U_pk_free_spec L HI MT HFREE HLS SW DIMG HND CA_MSF CA_RSA CA_EC); eassumption.
  Qed.

  End Crt.
