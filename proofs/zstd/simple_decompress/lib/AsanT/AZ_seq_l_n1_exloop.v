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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_v_x1 AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_ckit AZ_seq_l_xat AZ_seq_l_n1_at.
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

Lemma n1_closeloop_aux : forall (k : nat) P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  n1_ltail P OEND LLO LEND LOCV K ->
  forall (m1 : amem) (c8 c16 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (j va0 va1 va4 vr8 sh5 sh6 : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x12 x17 x20 x23 x24 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 cidx) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl -> ome = ole + mlv -> ole + 8 <= cur < ome -> l_PFX P <= rsrc -> 8 <= cur - rsrc <= 15 ->
  va0 = ole + 8 -> va1 = rsrc - j -> va4 = ole -> vr8 = rsrc - j - 8 -> cur = ole + 8 + j -> sh5 = 2147450880 + cur / 8 -> sh6 = 2147450880 + rsrc / 8 -> sn = l_nbSeq P - K -> 8 <= sn -> 0 <= cidx <= 7 -> 0 <= dll < 2^18 -> 0 <= dml < 2^18 -> 0 <= dof < 2^64 -> sql_ring_ok 8 rl rm ro -> 
  ome - cur <= 8 * (Z.of_nat k + 1) ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 va0) (Z_to_bv 64 va1) x12 (Z_to_bv 64 j) (Z_to_bv 64 va4) (Z_to_bv 64 sh5) (Z_to_bv 64 sh6) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 ome) x23 x24 (Z_to_bv 64 vr8) (Z_to_bv 64 va4) x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8bf1c) (l_fc P) None m1 (seg_rom bsegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LLO LEND LOCV K ST HK CONT1.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  all: cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros m1 c8 c16 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl cur rsrc ome j va0 va1 va4 vr8 sh5 sh6 sn cidx dll dml dof x1 x5 x6 x7 x12 x17 x20 x23 x24 x27 x28 x29 x30 x31 INV LF MF EOME HC HRS HD HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5 HXcloseloop6 HXcloseloop7 HSN HS8 HCI HDL HDM HDO HRING HM.
  all: pose proof CONT1 as CONT0; unfold n1_ltail in CONT1; cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK, CONT1.
  all: pose proof ST as ST0.
  all: pose proof (sql_linv_buf _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 cidx) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as BUFS; cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in BUFS.
  all: pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI. pose proof (sql_linv_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as UFL. pose proof (sql_seq_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (USEQ & RSQ & RSQS).
  all: pose proof (sql_copy_facts _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 cidx) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (BUF & LIT & STK & CFA); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in BUF, LIT, STK, CFA.
  all: pose proof LF as LF0; apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  all: apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  all: apply (sql_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros BUF_ UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG; clear BUF_.
  all: pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in M1.
  all: sd_static_open ST. all: unfold held in RGB.
  all: assert (WMl : wmono bsegs m1 m1) by apply wmono_refl. all: unfold held in S69.
  all: assert (MULL : munch [(cur, cur + 8); (FRB - 2224, FRB)] m1 m1) by apply munch_refl.
  all: assert (RG : 4096 <= B0 /\ B0 <= rsrc /\ rsrc + 8 <= cur /\ cur + 1 <= ome /\ ome + 32 <= B1 /\ B1 < 2^47 /\ 4096 <= ole /\ ole + 8 <= cur /\ 0 <= j /\ 8 <= cur - rsrc <= 15)
         by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 EOME HC HRS HD HXcloseloop1 HXcloseloop2 HXcloseloop5; lia).
  all: destruct (GRAN cur ltac:(clear - RG HD; lia) ltac:(clear - RG; Z.div_mod_to_equations; lia)) as (Z5 & R5); rewrite <- HXcloseloop6 in Z5, R5.
  all: destruct (GRAN rsrc ltac:(clear - RG; lia) ltac:(clear - RG HD; Z.div_mod_to_equations; lia)) as (Z6 & R6); rewrite <- HXcloseloop7 in Z6, R6.
  all: assert (RSH : 2147450880 <= sh5 < 2^45 /\ 2147450880 <= sh6 < 2^45) by (clear - RG HXcloseloop5 HXcloseloop6 HXcloseloop7; Z.div_mod_to_equations; lia).
  all: assert (KDO : va0 + j + 8 <= FRB \/ FRB + 568 <= va0 + j) by (unfold held in S24; clear - S24 RG RGA5 RGA6 HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (KDF : va0 + j + 8 <= FF \/ FF + 256 <= va0 + j) by (unfold held in S55; clear - S55 RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (KAO : va0 + j + 8 <= 2147450880 \/ 17594333495296 <= va0 + j) by (unfold held in S69; clear - S69 RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (ZSH1 : rng RNG (KXSHLO + (va0 + j) / 8) (shspanZ (va0 + j) 8)) by (apply (shz_sub RNG B0 (B1 - B0) (va0 + j) 8 RBUFS); clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (UZ1 : unpZ m1 (va0 + j) (va0 + j + 8)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (va0 + j) (va0 + j + 8) UBUF); unfold KXKEND; clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (ZSH2 : rng RNG (KXSHLO + (va4 + j + 8) / 8) (shspanZ (va4 + j + 8) 8)) by (apply (shz_sub RNG B0 (B1 - B0) (va4 + j + 8) 8 RBUFS); clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (UZ2 : unpZ m1 (va4 + j + 8) (va4 + j + 8 + 8)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (va4 + j + 8) (va4 + j + 8 + 8) UBUF); unfold KXKEND; clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (ZSH3 : rng RNG (KXSHLO + (vr8 + j + 8) / 8) (shspanZ (vr8 + j + 8) 8)) by (apply (shz_sub RNG B0 (B1 - B0) (vr8 + j + 8) 8 RBUFS); clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (UZ3 : unpZ m1 (vr8 + j + 8) (vr8 + j + 8 + 8)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (vr8 + j + 8) (vr8 + j + 8 + 8) UBUF); unfold KXKEND; clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (ZSH4 : rng RNG (KXSHLO + (va1 + j) / 8) (shspanZ (va1 + j) 8)) by (apply (shz_sub RNG B0 (B1 - B0) (va1 + j) 8 RBUFS); clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (UZ4 : unpZ m1 (va1 + j) (va1 + j + 8)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (va1 + j) (va1 + j + 8) UBUF); unfold KXKEND; clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia).
  all: assert (WN0 : rng RNG (va1 + j) 8) by (eapply rng_sub; [exact RBUF | clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia | clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia]).
  all: assert (WN1 : rng RNG (va0 + j) 8) by (eapply rng_sub; [exact RBUF | clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia | clear - RG HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; lia]).

  - pose proof I as IHk. clear CONT0.
    (try hold CONT1; try hold CONT0; try hold IHk; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HM; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold U32; try hold U64; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold Z5; try hold Z6; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO HC HRS HD EOME RSH HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO HC HRS HD EOME RSH HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5;
    kx_autoFLA tt [KAApp FRB 568; KAApp FF 256; KAUnp (va0 + j) 8; KAUnp (va4 + j + 8) 8; KAUnp (vr8 + j + 8) 8; KAUnp (va1 + j) 8; KAApp (va0 + j) 8] [0x8bf1c; 0x8add8; 0x8c010; 0x8c020; 0x8c02c; 0x8c03c] 150%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange va0 4096 (2^47 - 32);
     KZRange va1 4000 (2^47);
     KZRange va4 4096 (2^47);
     KZRange vr8 3990 (2^47);
     KZRange j 0 (2^47);
     KZRange ome 4096 (2^47);
     KZRange sh5 2147450880 (2^45);
     KZRange sh6 2147450880 (2^45);
     KZRange (va0 + j) 4096 (2^47 - 32);
     KZRange (va1 + j) 4096 (2^47 - 40);
     KZRange (va4 + j + 8) 4096 (2^47 - 32);
     KZRange (vr8 + j + 8) 4096 (2^47 - 40);
     KZRange (va4 + j) 4000 (2^47);
     KZRange (vr8 + j) 4000 (2^47);
     KZRange (va0 + j + 8) 4096 (2^47 - 24);
     KZWord sh5 1 0;
     KZWord sh6 1 0;
     KZWr (va0 + j) 8;
     KZDisj (va0 + j) 8 FRB 568;
     KZDisj (va0 + j) 8 FF 256]
    [(va1 + j, 8)]
    [(va1 + j, 8); (va0 + j, 8); (sh5, 1); (sh6, 1)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HM; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in U32; try unfold held in U64; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in Z5; try unfold held in Z6; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bf1c) _ _ _ _) => (exfalso; lia)
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8add8) _ _ _ _) => (eapply CONT1 with (r := sl); [eapply BUFS; [exact MULL | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1 HC; lia | clear - M1 M2 M3 HC EOME; lia] | clear - M1 M2 M3 M4 S1 S2 S3 S4 S5 S6 S7; lia | right; split; [exact LF0 | clear - M1 M3 M4; lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (try hold CONT1; try hold CONT0; try hold IHk; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HM; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold U32; try hold U64; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold Z5; try hold Z6; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO HC HRS HD EOME RSH HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO HC HRS HD EOME RSH HXcloseloop1 HXcloseloop2 HXcloseloop3 HXcloseloop4 HXcloseloop5;
    kx_autoFLA tt [KAApp FRB 568; KAApp FF 256; KAUnp (va0 + j) 8; KAUnp (va4 + j + 8) 8; KAUnp (vr8 + j + 8) 8; KAUnp (va1 + j) 8; KAApp (va0 + j) 8] [0x8bf1c; 0x8add8; 0x8c010; 0x8c020; 0x8c02c; 0x8c03c] 150%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange va0 4096 (2^47 - 32);
     KZRange va1 4000 (2^47);
     KZRange va4 4096 (2^47);
     KZRange vr8 3990 (2^47);
     KZRange j 0 (2^47);
     KZRange ome 4096 (2^47);
     KZRange sh5 2147450880 (2^45);
     KZRange sh6 2147450880 (2^45);
     KZRange (va0 + j) 4096 (2^47 - 32);
     KZRange (va1 + j) 4096 (2^47 - 40);
     KZRange (va4 + j + 8) 4096 (2^47 - 32);
     KZRange (vr8 + j + 8) 4096 (2^47 - 40);
     KZRange (va4 + j) 4000 (2^47);
     KZRange (vr8 + j) 4000 (2^47);
     KZRange (va0 + j + 8) 4096 (2^47 - 24);
     KZWord sh5 1 0;
     KZWord sh6 1 0;
     KZWr (va0 + j) 8;
     KZDisj (va0 + j) 8 FRB 568;
     KZDisj (va0 + j) 8 FF 256]
    [(va1 + j, 8)]
    [(va1 + j, 8); (va0 + j, 8); (sh5, 1); (sh6, 1)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HM; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in U32; try unfold held in U64; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in Z5; try unfold held in Z6; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8bf1c) _ _ _ _) => (eapply (IHk _ OEND LLO LEND LOCV K ST0 HK CONT0) with (cur := cur + 8) (rsrc := rsrc + 8); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; [eapply BUFS; [exact MULL | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1 HC; lia | clear - M1 M2 M3 HC EOME; lia] | exact LF0 | exact MF0 | exact EOME | lia | clear - HRS; lia | clear - HD; lia | lia | lia | lia | lia | lia | clear - HXcloseloop6; Z.div_mod_to_equations; lia | clear - HXcloseloop7; Z.div_mod_to_equations; lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8add8) _ _ _ _) => (eapply CONT1 with (r := sl); [eapply BUFS; [exact MULL | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1 HC; lia | clear - M1 M2 M3 HC EOME; lia] | clear - M1 M2 M3 M4 S1 S2 S3 S4 S5 S6 S7; lia | right; split; [exact LF0 | clear - M1 M3 M4; lia] | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
Qed.

Lemma n1_closeloop_ok : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  n1_ltail P OEND LLO LEND LOCV K -> n1_closeloop P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1. unfold n1_closeloop.
  intros m1 c8 c16 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl cur rsrc ome j va0 va1 va4 vr8 sh5 sh6 sn cidx dll dml dof x1 x5 x6 x7 x12 x17 x20 x23 x24 x27 x28 x29 x30 x31 INV LF MF EOME HC HRS HD HX1 HX2 HX3 HX4 HX5 HX6 HX7 HSN HS8 HCI HDL HDM HDO HRING.
  eapply (n1_closeloop_aux (Z.to_nat (ome - cur)) P OEND LLO LEND LOCV K ST HK CONT1); try eassumption. lia.
Qed.

End CANSEC1.
