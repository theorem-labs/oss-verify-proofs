(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AMalloc_iface ADepot_iface ARep ALayout AHeapP AFake_iface AFakeK_iface
     ARepQ ASec F_adepot AFake_arep AFake_arepk0 AFake_arepk1 AFake_arepk2 AInstance AInstanceM AInstanceF AFreeAll AZ_kit AZ_fake_heap
     AZ_fserd_iface AZ_hft_iface AZ_hft_rs_iface AZ_huf_iface AZ_blk_iface AZ_block_iface AZ_seq_iface AZ_dframe_iface AZ_tbl AZ_hufinv
     AZ_huf_4x2 AZ_huf_dx41_z AZ_closed_lib AZ_client.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
  Local Notation AIF := (AI_of (@AHI_free rc)).

  Lemma inst_E : AHEAP AIF = AHEAP_P (AH adepot_iface AQUAR ASEC_of).
  Proof. rewrite AI_of_E. rewrite AHI_eq. reflexivity. Qed.
  Lemma inst_EC : aci AIF = aci_I.
  Proof. reflexivity. Qed.
  Lemma inst_sm0k : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AIF fflag afake_rng k.
  Proof. exact (stack_malloc_0k_AI adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AIF inst_E inst_EC). Qed.
  Lemma inst_sm1k : forall k, Z.of_nat k < 8192 -> stack_malloc_1k_stmt AIF fflag afake_rng k.
  Proof. exact (stack_malloc_1k_AI adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AIF inst_E inst_EC). Qed.
  Lemma inst_sm2k : forall k, Z.of_nat k < 4096 -> stack_malloc_2k_stmt AIF fflag afake_rng k.
  Proof. exact (stack_malloc_2k_AI adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AIF inst_E inst_EC). Qed.
  Lemma inst_fflag : fake_flag_law AIF fflag.
  Proof. exact (fake_flag_AI adepot_iface AQUAR ASEC_of aci_I aci_ok1 AIF inst_E inst_EC). Qed.
  Lemma inst_frel : fake_release_law AIF fflag.
  Proof. exact (fake_release_AI adepot_iface AQUAR ASEC_of AH_laws AIF inst_E). Qed.
  Lemma inst_fhl : fake_heap_law AIF.
  Proof. apply fake_heap_AI_of. Qed.
End CANSEC1.

(* [comment removed for export] *)

Theorem lib_stmtsA_closed : lib_stmtsA.
Proof.
  intros rc.
  (* [comment removed for export] *)
  apply (lib_closedA (AI_of (@AHI_free rc)) fflag afake_rng);
    first [ exact inst_sm0k | exact inst_sm1k | exact inst_sm2k | exact inst_fflag | exact inst_frel | exact inst_fhl ].
Qed.

Theorem client_closed : client_stmtZ.
Proof. apply zd_fuzz_one_clientA; apply lib_stmtsA_closed. Qed.
