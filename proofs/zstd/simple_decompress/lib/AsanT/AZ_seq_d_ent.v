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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase
     AZ_seq_d_sbase AZ_seq_d_fin AZ_seq_d_last AZ_seq_d_xat AZ_seq_d_ad_at AZ_seq_d_iat AZ_seq_d_ikit AZ_seq_d_ickit AZ_seq_d_ekit2 AZ_seq_d_lkit2 AZ_seq_d_akit2 AZ_seq_d_end AZ_seq_d_ent0 AZ_seq_d_ent1 AZ_seq_d_ent2 AZ_seq_d_ent3 AZ_seq_d_ent4 AZ_seq_d_ent5 AZ_seq_d_ent6.
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

Section CANSEC1. Context {rc : runConstT}.

Lemma sqd_ent_ok : forall P,
  sqd_mem P -> sqd_ranges P -> sqd_side P -> sqd_sep P -> (w_nbSeq P <> 0 -> sqd_tables P) -> sqd_astat P -> sqd_asan P (w_m P) -> sqd_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA ->
  (w_nbSeq P <> 0 -> w_LLT P + 4104 <= 2^47 /\ w_OFT P + 2056 <= 2^47 /\ w_MLT P + 4104 <= 2^47) ->
  (w_nbSeq P <> 0 -> (w_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_LLT P) /\ (w_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= w_OFT P) /\
                    (w_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_MLT P)) ->
  sqd_at_last P -> sqd_at_fin P ->
  (forall OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> LOCV = w_LOC P -> ai_I0 P OEND LLO LEND LOCV) ->
  sqd_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK. pose proof SD as SD'.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_side] in SD'. destruct SD' as (_ & _ & _ & _ & _ & LOC01 & _). unfold ZSTD_not_in_dst, ZSTD_in_dst in LOC01.
  pose (ARGS := (MEM, RG, SD, SEP, TBL, AS, ASN, PRO, MMV, MCP, EXE, TH3, TB3, LASTK, FINK, INITK)).
  destruct LOC01 as [EL|EL].
  - destruct (Z.eq_dec CAP 0) as [C0|C0].
    + apply (sqd_ent0 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL C0).
    + destruct (Z.eq_dec nbSeq 0) as [NB|NB].
      * apply (sqd_ent1 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL C0 NB).
      * destruct (Z.eq_dec (zlen sq) 0) as [NS|NS].
        -- apply (sqd_ent5 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL C0 NB NS).
        -- apply (sqd_ent3 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL C0 NB). cbn [w_sq]. remember (zlen sq) as n eqn:En. clear - NS En. subst n. lia.
  - destruct (Z.eq_dec nbSeq 0) as [NB|NB].
    + apply (sqd_ent2 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL NB).
    + destruct (Z.eq_dec (zlen sq) 0) as [NS|NS].
      * apply (sqd_ent6 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL NB NS).
      * apply (sqd_ent4 _ MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL NB). cbn [w_sq]. remember (zlen sq) as n eqn:En. clear - NS En. subst n. lia.
Qed.

End CANSEC1.
