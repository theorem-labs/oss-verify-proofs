(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase
     AZ_seq_s_sbase AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_last AZ_seq_s_xat AZ_seq_s_a1_at AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_ekit2 AZ_seq_s_lkit2 AZ_seq_s_akit2 AZ_seq_s_xkit AZ_seq_s_ent0 AZ_seq_s_ent1 AZ_seq_s_ent2 AZ_seq_s_ent3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)
Ltac sqs_ent_lastframe H := sqs_blob_seg H 5%nat 8%nat; sqs_blob_seg H 0%nat 4%nat.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_ent_ok : forall P,
  sqs_mem P -> sqs_ranges P -> sqs_side P -> sqs_sep P -> (v_nbSeq P <> 0 -> sqs_tables P) -> sqs_astat P -> sqs_asan P (v_m P) -> sqs_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA ->
  (v_nbSeq P <> 0 -> v_LLT P + 4104 <= 2^47 /\ v_OFT P + 2056 <= 2^47 /\ v_MLT P + 4104 <= 2^47) ->
  (v_nbSeq P <> 0 -> (v_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_LLT P) /\ (v_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= v_OFT P) /\
                    (v_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_MLT P)) ->
  sqs_at_last P -> sqs_at_fin P ->
  (forall OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = v_LOC P -> ai_I0 P OEND LLO LEND LOCV) ->
  sqs_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK.
  destruct (Z.eq_dec (v_CAP P) 0) as [C0|C0].
  - apply (sqs_ent0 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK C0).
  - destruct (Z.eq_dec (v_nbSeq P) 0) as [NB|NB].
    + apply (sqs_ent1 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK C0 NB).
    + destruct (Z.eq_dec (zlen (v_sq P)) 0) as [NS|NS].
      * apply (sqs_ent2 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK C0 NB NS).
      * apply (sqs_ent3 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK C0 NB). remember (zlen (v_sq P)) as n eqn:En. clear - NS En. subst n. lia.
Qed.

End CANSEC1.
