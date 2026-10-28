(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_zkit AZ_seq_l_tkit AZ_seq_l_ibase AZ_seq_l_sbase AZ_seq_l_fin AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_xat AZ_seq_l_la_at AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_ekit2 AZ_seq_l_akit2 AZ_seq_l_en0 AZ_seq_l_en1 AZ_seq_l_en3 AZ_seq_l_en4 AZ_seq_l_en5a AZ_seq_l_en5b AZ_seq_l_en6a AZ_seq_l_en6b AZ_seq_l_en7a AZ_seq_l_en7b AZ_seq_l_en8a AZ_seq_l_en8b AZ_seq_l_en9a AZ_seq_l_en9b AZ_seq_l_en10a AZ_seq_l_en10b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_ent_ok : forall P,
  sql_mem P -> sql_ranges P -> sql_side P -> sql_sep P -> (l_nbSeq P <> 0 -> sql_tables P) -> sql_astat P -> sql_asan P (l_m P) -> sql_pro P ->
  zd_memmoveZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA ->
  (l_nbSeq P <> 0 -> l_LLT P + 4104 <= 2^47 /\ l_OFT P + 2056 <= 2^47 /\ l_MLT P + 4104 <= 2^47) ->
  (l_nbSeq P <> 0 -> (l_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_LLT P) /\ (l_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= l_OFT P) /\
                    (l_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_MLT P)) ->
  sql_at_lastx P -> sql_at_fin P ->
  (forall OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> ai_I0 P OEND) ->
  sql_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK.
  assert (Y : sql_side P) by exact SD. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_side sql_ranges] in Y, RG.
  destruct Y as (_ & _ & Y3 & _ & _ & Y6 & _ & _ & Y9 & _ & _ & Y12 & _). pose proof RG as (_ & _ & _ & _ & _ & _ & _ & R8 & _ & R10 & R11 & _).
  unfold ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH in Y6, Y9.
  set (P := mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) in *.
  destruct (Z.eq_dec nbSeq 0) as [NB|NB].
  - destruct Y6 as [EL|[EL|EL]].
    + destruct (Z.eq_dec CAP 0) as [C0|C0].
      * apply (sql_en0 P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB).
      * apply (sql_en1 P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB).
    + apply (sql_en4 P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL NB).
    + destruct (Z.eq_dec CAP 0) as [C0|C0].
      * exfalso. destruct (Y9 EL) as (X1 & X2). clear - X1 X2 C0 R10 R11. lia.
      * apply (sql_en3 P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB).
  - assert (C0 : CAP <> 0) by (pose proof (Y12 NB) as CP; clear - CP; lia).
    destruct (Z.eq_dec (zlen sq) 0) as [NS|NS].
    + destruct Y6 as [EL|[EL|EL]].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en5a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8) | apply (sql_en5b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8)].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en6a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL NB NS NB8) | apply (sql_en6b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL NB NS NB8)].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en7a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8) | apply (sql_en7b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8)].
    + assert (NS1 : 1 <= zlen sq) by (remember (zlen sq) as n eqn:En; clear - NS En; subst n; pose proof (Zle_0_nat (length sq)); unfold zlen in *; lia).
      destruct Y6 as [EL|[EL|EL]].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en8a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS1 NB8) | apply (sql_en8b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS1 NB8)].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en9a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL NB NS1 NB8) | apply (sql_en9b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL NB NS1 NB8)].
      * destruct (Z_lt_le_dec nbSeq 8) as [NB8|NB8]; [apply (sql_en10a P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS1 NB8) | apply (sql_en10b P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS1 NB8)].
Qed.

End CANSEC1.
