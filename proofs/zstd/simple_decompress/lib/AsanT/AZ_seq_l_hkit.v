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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma areg_dctx_shadow : forall RNG (m1 : amem) D8 off, areg RNG m1 (8 * D8) DCTX_SIZEOF -> 0 <= off -> off + 8 <= DCTX_SIZEOF -> off mod 8 = 0 ->
  rdn bsegs m1 (wa (2147450880 + D8 + off / 8)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng RNG (2147450880 + D8 + off / 8) 1.
Proof.
  intros RNG m1 D8 off AR H0 H1 H2.
  destruct (AR ltac:(unfold DCTX_SIZEOF; clear; lia)) as (_ & U & R1 & R2).
  assert (Z0 : m1 (wa (shad (8 * D8 + off))) = Some (Z_to_bv 8 0)).
  { eapply (unp_shadow_zero m1 (8 * D8) DCTX_SIZEOF (8 * D8 + off)); [exact U | lia | ].
    Z.div_mod_to_equations. lia. }
  rewrite shad_div in Z0. unfold ASHOFF in Z0.
  replace ((8 * D8 + off) / 8) with (D8 + off / 8) in Z0 by (Z.div_mod_to_equations; lia).
  split.
  - cbn [rdn]. replace (2147450880 + D8 + off / 8) with (2147450880 + (D8 + off / 8)) by lia. rewrite Z0. reflexivity.
  - eapply rng_sub'; [exact R2 |]. unfold shspan. rewrite !shad_div. unfold ASHOFF, DCTX_SIZEOF in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sql_loc_shadow : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  rdn bsegs m1 (wa (2147450880 + l_D8 P + 3795)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rdn bsegs m1 (wa (2147450880 + l_D8 P + 3796)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng (l_RNG P) (2147450880 + l_D8 P + 3795) 1 /\ rng (l_RNG P) (2147450880 + l_D8 P + 3796) 1 /\
  l_DCTX P = 8 * l_D8 P /\ 512 <= l_D8 P <= 17592186032416.
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_D8 l_RNG l_DCTX] in *.
  sd_static_open ST.
  cbn [sql_astat] in S61. destruct S61 as (_ & _ & _ & _ & ED8 & _).
  assert (RD8 : 512 <= D8 <= 17592186032416) by (clear - ED8 S19 S20; lia).
  destruct AS as (AD & _). rewrite ED8 in AD.
  destruct (areg_dctx_shadow RNG m1 D8 30360 AD ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (Z5 & R5).
  destruct (areg_dctx_shadow RNG m1 D8 30368 AD ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (Z6 & R6).
  change (30360 / 8) with 3795 in Z5, R5. change (30368 / 8) with 3796 in Z6, R6.
  repeat (split; [assumption|]). exact RD8.
Qed.

(* [comment removed for export] *)
Lemma sql_tbl_k : forall P OEND LLO LEND LOCV K BND OP LP bc ptr sLL sOF sML nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
  sql_static P OEND LLO LEND LOCV -> sql_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML -> BND <= 100 + 100 * (l_nbSeq P - K) + 47 -> 1 <= K <= l_nbSeq P ->
  sql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML ->
  forall Q : Prop,
  (sql_next P nLL bLL nOF bOF nML bML ->
   0 <= nLL + 2^bLL <= 2^(st_log (l_tLL P)) -> 0 <= nOF + 2^bOF <= 2^(st_log (l_tOF P)) -> 0 <= nML + 2^bML <= 2^(st_log (l_tML P)) ->
   0 <= nLL <= 511 -> 0 <= nOF <= 511 -> 0 <= nML <= 511 -> 0 <= bLL <= 9 -> 0 <= bOF <= 9 -> 0 <= bML <= 9 ->
   0 <= aLL <= 16 -> 0 <= aOF <= 31 -> 0 <= aML <= 16 ->
   0 <= vLL <= 131072 -> 0 <= vML <= 131075 -> 0 <= vOF <= 4294967294 -> 0 <= vLL < 2^17 -> 0 <= vML + 2^aML < 2^18 -> 0 < 2^aML ->
   (aOF = 0 -> vOF = 0) -> (aOF = 1 -> vOF = 1) ->
   1 <= 2^(st_log (l_tLL P)) <= 512 -> 1 <= 2^(st_log (l_tOF P)) <= 512 -> 1 <= 2^(st_log (l_tML P)) <= 512 ->
   0 <= sLL <= 511 -> 0 <= sOF <= 511 -> 0 <= sML <= 511 -> 0 <= bc <= 9900000 -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV K BND OP LP bc ptr sLL sOF sML nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML ST LF HBND HK CF Q KQ.
  destruct CF as (NX & N1 & N2 & N3 & A1 & A2 & A3 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  destruct LF as (_ & _ & L3 & L4 & L5 & L6 & _).
  assert (OK3 : seq_table_ok K_LL (l_tLL P) /\ seq_table_ok K_OF (l_tOF P) /\ seq_table_ok K_ML (l_tML P) /\ 1 <= l_nbSeq P <= 98047).
  { clear - ST. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
    cbn [l_tLL l_tOF l_tML l_nbSeq] in *. sd_static_open ST. split; [exact OKLL|]. split; [exact OKOF|]. split; [exact OKML|]. exact S16. }
  destruct OK3 as (OKLL & OKOF & OKML & S16).
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  pose proof (Z.pow_pos_nonneg 2 aLL ltac:(lia) ltac:(lia)) as QA. pose proof (Z.pow_pos_nonneg 2 aML ltac:(lia) ltac:(lia)) as QM. pose proof (Z.pow_pos_nonneg 2 aOF ltac:(lia) ltac:(lia)) as QO.
  pose proof (Z.pow_nonneg 2 bLL ltac:(lia)) as QB1. pose proof (Z.pow_nonneg 2 bOF ltac:(lia)) as QB2. pose proof (Z.pow_nonneg 2 bML ltac:(lia)) as QB3.
  apply (KQ NX); first [assumption | (clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 N1 N2 N3 A1 A2 A3 V1 V2 V3 V4 V5 V6 L3 L4 L5 L6 HK HBND S16 PLL POF PML QA QM QO QB1 QB2 QB3; lia)].
Qed.

(* [comment removed for export] *)
Lemma sql_dec_k2 : forall P OEND LLO LEND LOCV K BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP jpad,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML -> BND <= 100 + 100 * (l_nbSeq P - K) + 47 -> 1 <= K <= l_nbSeq P ->
  rw_cells bsegs m1 (l_FF P) (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  forall Q : Prop,
  (forall L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
     l_LLT P = 8 * L8 -> l_OFT P = 8 * O8 -> l_MLT P = 8 * M8 ->
     512 <= L8 < 2^44 -> 512 <= O8 < 2^44 -> 512 <= M8 < 2^44 ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML)) ->
     rdn bsegs m1 (wa (2147450880 + L8 + sLL + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rdn bsegs m1 (wa (2147450880 + O8 + sOF + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rdn bsegs m1 (wa (2147450880 + M8 + sML + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rng (l_RNG P) (8 * L8 + 8 * sLL + 8) 8 -> rng (l_RNG P) (8 * O8 + 8 * sOF + 8) 8 -> rng (l_RNG P) (8 * M8 + 8 * sML + 8) 8 ->
     rng (l_RNG P) (2147450880 + L8 + sLL + 1) 1 -> rng (l_RNG P) (2147450880 + O8 + sOF + 1) 1 -> rng (l_RNG P) (2147450880 + M8 + sML + 1) 1 ->
     rw_cells bsegs m1 (l_FF P) (sql_ffr8 P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
     sql_next P nLL bLL nOF bOF nML bML ->
     0 <= nLL + 2^bLL <= 2^(st_log (l_tLL P)) -> 0 <= nOF + 2^bOF <= 2^(st_log (l_tOF P)) -> 0 <= nML + 2^bML <= 2^(st_log (l_tML P)) ->
     0 <= nLL <= 511 -> 0 <= nOF <= 511 -> 0 <= nML <= 511 -> 0 <= bLL <= 9 -> 0 <= bOF <= 9 -> 0 <= bML <= 9 ->
     0 <= aLL <= 16 -> 0 <= aOF <= 31 -> 0 <= aML <= 16 ->
     0 <= vLL <= 131072 -> 0 <= vML <= 131075 -> 0 <= vOF <= 4294967294 -> 0 <= vLL < 2^17 -> 0 <= vML + 2^aML < 2^18 -> 0 < 2^aML ->
     (aOF = 0 -> vOF = 0) -> (aOF = 1 -> vOF = 1) ->
     1 <= 2^(st_log (l_tLL P)) <= 512 -> 1 <= 2^(st_log (l_tOF P)) <= 512 -> 1 <= 2^(st_log (l_tML P)) <= 512 ->
     0 <= sLL <= 511 -> 0 <= sOF <= 511 -> 0 <= sML <= 511 -> 0 <= bc <= 9900000 ->
     sql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV K BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP jpad ST INV LF HBND HK FRF Q KQ.
  destruct (sql_dec_asan P OEND LLO LEND LOCV _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ST INV LF)
    as (L8 & O8 & M8 & E1 & E2 & E3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & R4 & R5 & R6).
  destruct (sql_linv_cells P OEND LLO LEND LOCV _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ST INV LF)
    as (nLL & aLL & bLL & vLL & nOF & aOF & bOF & vOF & nML & aML & bML & vML & (W1 & W2 & W3 & W4) & (W5 & W6 & W7 & W8) & (W9 & W10 & W11 & W12) & CF).
  rewrite E1 in W1, W2, W3, W4. rewrite E2 in W5, W6, W7, W8. rewrite E3 in W9, W10, W11, W12.
  pose proof CF as (NX & N1 & N2 & N3 & A1 & A2 & A3 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  destruct LF as (_ & _ & L3 & L4 & L5 & L6 & _).
  assert (OK3 : seq_table_ok K_LL (l_tLL P) /\ seq_table_ok K_OF (l_tOF P) /\ seq_table_ok K_ML (l_tML P) /\ 1 <= l_nbSeq P <= 98047 /\
                512 <= L8 < 2^44 /\ 512 <= O8 < 2^44 /\ 512 <= M8 < 2^44).
  { clear - ST E1 E2 E3. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
    cbn [l_tLL l_tOF l_tML l_nbSeq l_LLT l_OFT l_MLT] in *. sd_static_open ST. split; [exact OKLL|]. split; [exact OKOF|]. split; [exact OKML|]. split; [exact S16|].
    clear - S21 S22 S23 E1 E2 E3. lia. }
  destruct OK3 as (OKLL & OKOF & OKML & S16 & G1 & G2 & G3).
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  pose proof (Z.pow_pos_nonneg 2 aLL ltac:(lia) ltac:(lia)) as QA. pose proof (Z.pow_pos_nonneg 2 aML ltac:(lia) ltac:(lia)) as QM. pose proof (Z.pow_pos_nonneg 2 aOF ltac:(lia) ltac:(lia)) as QO.
  pose proof (Z.pow_nonneg 2 bLL ltac:(lia)) as QB1. pose proof (Z.pow_nonneg 2 bOF ltac:(lia)) as QB2. pose proof (Z.pow_nonneg 2 bML ltac:(lia)) as QB3.
  assert (FRF8 : rw_cells bsegs m1 (l_FF P) (sql_ffr8 P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad)).
  { rewrite <- (sql_ffr8_eq P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad E1 E2 E3). exact FRF. }
  apply (KQ L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML E1 E2 E3 G1 G2 G3 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 W12 Z1 Z2 Z3 R1 R2 R3 R4 R5 R6 FRF8 NX);
    first [exact CF | assumption | (clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 N1 N2 N3 A1 A2 A3 V1 V2 V3 V4 V5 V6 L3 L4 L5 L6 HK HBND S16 PLL POF PML QA QM QO QB1 QB2 QB3; lia)].
Qed.

End CANSEC1.
