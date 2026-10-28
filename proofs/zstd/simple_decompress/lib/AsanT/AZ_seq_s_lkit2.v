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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma ahull_sub : forall RNG (m : amem) A n A' n', ahull RNG m A n -> A <= A' -> A' + n' <= A + n -> ahull RNG m A' n'.
Proof.
  intros RNG m A n A' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) HA HB. exists RLO, RHI.
  split; [lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact W | exact R].
Qed.

(* [comment removed for export] *)
Lemma munch_focus : forall W (m m' : amem) A n, munch W m m' -> (forall x, A <= x < A + n -> outside W x) ->
  munch [(0, A); (A + n, 2^64)] m m'.
Proof.
  intros W m m' A n MU H x Hx. apply MU. apply H.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  cbn [outside] in Hx. lia.
Qed.

Lemma rw_cells_transport_pw : forall W (m m' : amem) A cs, rw_cells bsegs m A cs -> munch W m m' -> wmono bsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs m' A cs.
Proof.
  intros W m m' A cs RW MU WM H. eapply rw_cells_transport; [exact RW | exact (munch_focus W m m' A _ MU H) | exact WM |].
  cbn [disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma sqs_linv_step : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq D1 D2 CS, 0 <= CS <= 4304 ->
  munch [(D1, D2); (v_FRB P - CS, v_FRB P); (v_FRB P, v_FRB P + 280); (v_FF P, v_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  stk bsegs m2 (v_B0 P) (v_B1 P) -> stk bsegs m2 (v_lo P) (v_FRB P) -> v_DST P <= D1 -> D2 <= OEND ->
  rw_cells bsegs m2 (v_FRB P) (sqs_frame P OEND c0' c8' c152' c160' c168' c200' c208' c216' LP' jseq) ->
  rw_cells bsegs m2 (v_FF P) (sqs_ffr P cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  sqs_linv P OEND LLO LEND LOCV m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV
         m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq D1 D2 CS HCS MUL WML MI2 BUF2 STK2 HD1 HD2 FR FRF.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_FRB v_FF v_LLT v_OFT v_MLT v_SEQ v_sq v_tLL v_tOF v_tML v_DCTX v_ws v_B0 v_B1 v_lo v_DST] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  (* [comment removed for export] *)
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 S47 HCS LLL; lia| split; [clear - S28 S18 S47 HCS LLL; lia| split; [clear - S58 LLL; lia|exact I]]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 S47 HCS LOF; lia| split; [clear - S29 S18 S47 HCS LOF; lia| split; [clear - S59 LOF; lia|exact I]]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 S47 HCS LML; lia| split; [clear - S30 S18 S47 HCS LML; lia| split; [clear - S60 LML; lia|exact I]]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18 S47 HCS; lia| split; [clear - S25 S18 S47 HCS; lia| split; [clear - S56; lia|exact I]]]]]|].
  split.
  { destruct S12 as [(A1 & A2)|A].
    - eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2].
    - eapply rdbl_transport; [exact LIT | exact MUL |]. intros x Hx; left; cbn [outside].
      split; [clear - A S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia|]. split; [clear - S26 S18 S47 HCS Hx; lia|]. split; [clear - S26 S18 S47 HCS Hx; lia|]. split; [clear - S57 Hx; lia| exact I]. }
  split.
  { intros HL2. eapply rdbl_transport; [exact (XLIT HL2) | exact MUL |]. intros x Hx; left; cbn [outside].
    split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia|]. split; [clear - S27 S18 S47 HCS Hx; lia|]. split; [clear - S27 S18 S47 HCS Hx; lia|]. split; [clear - S54 Hx; lia| exact I]. }
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add h5_vcells]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S54; lia|exact I]]]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S54; lia|exact I]]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47 HCS; lia| split; [clear - S54; lia|exact I]]]]]|].
  split; [exact BUF2|].
  split; [exact STK2|].
  split; [eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S47 HCS; lia| split; [clear - S47 HCS; lia| split; [clear - S50 S18 S47 HCS; lia|exact I]]]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S1 S2 S3 S4 S5 S6 HD1 HD2 S47 S18; lia| split; [clear; lia| split; [clear; lia| split; [clear - S50 S18 S47 HCS; lia|exact I]]]]]|].
  split.
  { (* [comment removed for export] *)
    eapply rw_cells_transport_pw; [exact SHS | exact MUL | exact WML |]. cbn [cells_size csize Nat.add outside]. intros x Hx.
    split; [clear - S68 S69 S52 S53 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia|]. split; [clear - S53 S18 S47 HCS Hx; lia|]. split; [clear - S53 S18 S47 HCS Hx; lia|].
    split; [clear - S49 S52 S53 Hx; lia| exact I]. }
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx S47 S5 HD1 HD2 S18 HCS; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma sqs_linv_buf : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 D1 D2,
  munch [(D1, D2); (v_FRB P - 2224, v_FRB P)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  stk bsegs m2 (v_B0 P) (v_B1 P) -> stk bsegs m2 (v_lo P) (v_FRB P) -> v_DST P <= D1 -> D2 <= OEND ->
  sqs_linv P OEND LLO LEND LOCV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 D1 D2 MUL WML MI2 BUF2 STK2 HD1 HD2.
  pose proof INV as ((jpad & jseq & FR & FRF) & _).
  assert (MUL4 : munch [(D1, D2); (v_FRB P - 2224, v_FRB P); (v_FRB P, v_FRB P + 280); (v_FF P, v_FF P + 256)] m1 m2).
  { eapply munch_weaken; [|exact MUL]. unfold sub_fp; cbn [outside]. intros x Hx. tauto. }
  eapply (sqs_linv_step P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq D1 D2 2224 ltac:(lia) MUL4 WML MI2 BUF2 STK2 HD1 HD2).
  - eapply rw_cells_transport; [exact FR | exact MUL | exact WML |].
    clear - ST HD1 HD2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [sqs_frame v_FRB v_DST] in *. sd_static_open ST. unfold held in S24.
    cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S24 S18 S47 S1 S2 S3 S4 S5 S6 HD1 HD2; lia|]. split; [clear; lia| exact I].
  - eapply rw_cells_transport; [exact FRF | exact MUL | exact WML |].
    clear - ST HD1 HD2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [sqs_ffr v_FRB v_FF v_DST] in *. sd_static_open ST. unfold held in S55.
    cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S55 S1 S2 S3 S4 S5 S6 HD1 HD2; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

(* [comment removed for export] *)
Definition sqs_copy_post (P : ssq) (OEND LLO LEND LOCV : Z) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ sqs_linv P OEND LLO LEND LOCV m' c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP.

(* [comment removed for export] *)
Lemma sqs_copy_facts : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  stk bsegs m1 (v_B0 P) (v_B1 P) /\ rdbl bsegs m1 LLO (LEND + 32) /\ stk bsegs m1 (v_lo P) (v_FRB P) /\
  4096 <= v_B0 P /\ v_B0 P <= v_DST P /\ OEND <= v_B1 P /\ v_B1 P < 2^47 /\ 4096 <= LLO /\ LEND + 32 < 2^47.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & LIT & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_B0 v_B1 v_DST v_lo v_FRB] in *. sd_static_open ST.
  destruct XI as (_ & _ & BUF & STK & _). repeat (split; [first [assumption | lia]|]). lia.
Qed.

(* [comment removed for export] *)
Lemma sqs_copy_asan : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  art m1 /\ astk (v_RNG P) (v_lo P) (v_FRB P) /\
  (forall X n, 0 <= n -> ((LLO <= X /\ X + n <= LEND + 32) \/ (v_B0 P <= X /\ X + n <= v_B1 P /\ v_B0 P < v_B1 P)) ->
     app_blk X (X + n) /\ aro (v_RNG P) m1 X n /\ ahull (v_RNG P) m1 X n).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  pose proof (sqs_asan_now P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan sqs_astat v_RNG v_lo v_FRB v_B0 v_B1 v_DCTX] in *. sd_static_open ST. unfold held in S67.
  destruct AS as (ARD & AHD & _ & _ & _ & AOUT & ARL & AHL & _ & ARTC).
  destruct S61 as (AST & _).
  split; [exact ARTC|]. split; [eapply astk_sub; [exact AST | clear - S18 S47; lia]|].
  intros X n Hn [(X1 & X2)|(X1 & X2 & BB)].
  - unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF in *. destruct S67 as [(ELLO & ELEND)|(ELLO & ELEND)]; subst LLO LEND.
    + assert (AU : aregU RNG m1 X n) by (eapply aregU_sub; [exact ARL | clear - S10; lia | exact X1 | exact Hn | clear - X2; lia]).
      split; [eapply aregU_app_blk; [exact AU | exact Hn]|]. split; [apply aregU_aro; exact AU|].
      eapply ahull_sub; [exact AHL | exact X1 | clear - X2; lia].
    + assert (AU : aregU RNG m1 X n) by (eapply aregU_sub; [exact ARD | clear; lia | clear - X1; lia | exact Hn | clear - X2; lia]).
      split; [eapply aregU_app_blk; [exact AU | exact Hn]|]. split; [apply aregU_aro; exact AU|].
      eapply ahull_sub; [exact AHD | clear - X1; lia | clear - X2; lia].
  - destruct (AOUT BB) as (AO & AH).
    assert (AU : aregU RNG m1 X n) by (eapply aregU_sub; [exact AO | clear - BB; lia | exact X1 | exact Hn | clear - X2; lia]).
    split; [eapply aregU_app_blk; [exact AU | exact Hn]|]. split; [apply aregU_aro; exact AU|].
    eapply ahull_sub; [exact AH | exact X1 | clear - X2; lia].
Qed.

Lemma sqs_copy_spec : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP (D S n : Z)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= D -> 0 < n <= 2^40 -> D + n <= OEND ->
  ((LLO <= S /\ S + n <= LEND + 32) \/ (v_B0 P <= S /\ S + n <= v_B1 P)) ->
  evtF bsegs (v_RNG P) (sqs_copy_post P OEND LLO LEND LOCV c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D)
    (MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53ee0) fc None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP D S n ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HD Hn HDn SRC.
  pose proof (sqs_linv_buf P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  pose proof (sqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_copy_facts P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & LIT & STK & F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (sqs_copy_asan P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (ART & AST & AREG).
  (* [comment removed for export] *)
  assert (SF : zd_memmoveZ_stmtA /\ v_lo P <= v_FRB P - 2224 /\ v_FRB P < 2^47 /\ (v_B1 P <= v_lo P \/ v_FRB P <= v_B0 P) /\ (LEND + 32 <= v_lo P \/ v_FRB P <= LLO)).
  { clear - ST. destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [v_lo v_FRB v_B0 v_B1] in *. sd_static_open ST. unfold held in S24, S26. split; [exact S64|]. clear - S17 S18 S47 S24 S26. lia. }
  destruct SF as (MMV & G1 & G2 & G3 & G4).
  assert (BB : v_B0 P <= D /\ D + n <= v_B1 P /\ v_B0 P < v_B1 P) by (clear - HD Hn HDn F2 F3; lia).
  destruct (AREG D n ltac:(clear - Hn; lia) ltac:(right; exact BB)) as (ABD & AOD & AHD).
  assert (SRC' : (LLO <= S /\ S + n <= LEND + 32) \/ (v_B0 P <= S /\ S + n <= v_B1 P /\ v_B0 P < v_B1 P)) by (clear - SRC Hn BB; lia).
  destruct (AREG S n ltac:(clear - Hn; lia) SRC') as (ABS & AOS & AHS).
  assert (RDS : rdbl bsegs m1 S (S + n)).
  { destruct SRC as [(X1 & X2)|(X1 & X2)].
    - eapply rdbl_sub; [exact LIT | exact X1 | clear - X2; lia].
    - eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF | exact X1 | exact X2]. }
  unfold zd_memmoveZ_stmtA in MMV.
  eapply evtF_mono.
  - eapply (MMV (v_RNG P) D S n (v_FRB P) ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (v_lo P));
      [ eapply stk_sub; [exact BUF | clear - BB; lia | clear - Hn; lia | clear - BB; lia]
      | exact RDS | clear - Hn; lia | exact STK | exact G1 | exact G2
      | clear - SRC G1 G3 G4; lia | clear - BB G3; lia
      | exact ABS | exact AOS | exact AHS | exact ABD | exact AOD | exact AHD | exact ART | exact AST
      | exact MI | reflexivity | reflexivity | reflexivity ].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & BUFD).
    do 15 eexists. split; [reflexivity|].
    assert (MU2 : munch [(D, D + n); (v_FRB P - 2224, v_FRB P)] m1 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. tauto. }
    eapply STEP; [exact MU2 | exact WM | exact MI' | | exact STK' | exact HD | exact HDn].
    (* [comment removed for export] *)
    destruct (stk_split bsegs m1 (v_B0 P) D (v_B1 P) BUF ltac:(clear - BB Hn; lia)) as [BL BR0].
    destruct (stk_split bsegs m1 D (D + n) (v_B1 P) BR0 ltac:(clear - BB Hn; lia)) as [_ BR].
    apply (stk_merge bsegs m' (v_B0 P) D (v_B1 P)); [| | clear - BB Hn; lia].
    + eapply stk_transport; [exact BL | exact MU | exact WM |]. intros x Hx; left; cbn [outside].
      split; [clear - Hx G1 G3 BB Hn; lia|]. split; [clear - Hx Hn; lia| exact I].
    + apply (stk_merge bsegs m' D (D + n) (v_B1 P)); [exact BUFD | | clear - BB Hn; lia].
      eapply stk_transport; [exact BR | exact MU | exact WM |]. intros x Hx; left; cbn [outside].
      split; [clear - Hx G1 G3 BB Hn; lia|]. split; [clear - Hx Hn; lia| exact I].
Qed.

End CANSEC1.
