(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_dbs_post (P : ssq) (OEND LLO LEND LOCV : Z) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists (m2 : amem),
    (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
       ms' = MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m2 (seg_rom bsegs)) /\
    sqs_linv P OEND LLO LEND LOCV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP.

Lemma sqs_dbs_spec : forall P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  sqs_linv P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP -> 0 <= n -> LLO <= LP -> LP + n <= LEND -> OP + n <= OEND ->
  evtF bsegs (v_RNG P) (sqs_dbs_post P OEND LLO LEND LOCV c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 LP) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96540) fc None m0 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP n ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         ST HLOC INV HOP HN HLLO HLE HOE.
  pose proof (sqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof INV as ((jpad & jseq & FR & FRF) & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv sqs_asan sqs_astat v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (_ & _ & _ & _ & _ & AOUT & ARL & AHL & AZS & ART).
  destruct S61 as (ASTK & _).
  destruct (S71 HLOC) as (ELLO & ELEND & _).
  unfold zd_dbs_stmtA in S75.
  assert (RGS : 4096 <= B0 /\ B1 < 2^47 /\ B0 <= OP /\ OP + n <= B1 /\ 4096 <= LLO /\ LEND + 32 < 2^47 /\ LLO <= LP /\ LP + n <= LEND + 32 /\
                lo <= FRB - 2304 /\ 0 <= FRB < 2^47 /\ B0 <= LLO /\ LEND + 32 <= B1).
  { clear - S1 S2 S3 S4 S5 S6 S7 S9 S11 S17 S18 S42 S47 HOP HN HLLO HLE HOE HLOC. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  destruct (AOUT S68) as (ARB & AHB).
  eapply evtF_mono.
  - eapply (S75 RNG ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 FRB lo OP LP n B0 B1 LLO (LEND + 32));
      [ exact BUF | exact G1 | exact G2 | exact G3 | exact HN | exact G4
      | exact LIT | exact G5 | exact G6 | exact G7 | exact G8
      | right; clear - G11 G12; lia
      | exact STK | exact G9 | exact G10
      | unfold off_stack; clear - S24 S18 S47; lia | unfold off_stack; clear - S26 S18 S47; lia
      | exact S68 | exact ARB | exact AHB
      | rewrite ELLO, ELEND; unfold WILDCOPY_OVERLENGTH in ARL; replace (LBE + 32 - LITP) with (LBE + 32 - LITP) by reflexivity; exact ARL
      | rewrite ELLO, ELEND; unfold WILDCOPY_OVERLENGTH in AHL; exact AHL
      | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact MI
      | reflexivity | reflexivity | reflexivity ].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & STK' & BUF' & RD').
    exists m'. split; [do 15 eexists; reflexivity|].
    assert (MU4 : munch [(OP, OP + n); (FRB - 2304, FRB); (FRB, FRB + 280); (FF, FF + 256)] m0 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply (STEP m' c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq OP (OP + n) 2304);
      [ clear; lia | exact MU4 | exact WM | exact MI' | exact BUF' | exact STK' | exact HOP | exact HOE | | ].
    + eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from sqs_frame cells_size csize Nat.add].
      split; [clear - S24 S18 S47 G3 G4; lia|]. split; [clear; lia| exact I].
    + eapply rw_cells_transport; [exact FRF | exact MU | exact WM |].
      cbn [disjoint_from sqs_ffr cells_size csize Nat.add].
      split; [clear - S55 G3 G4; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

End CANSEC1.
