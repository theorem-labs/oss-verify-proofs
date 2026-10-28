(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_tbl_iface3 AF_huf_x2t_bgeo AF_huf_x2t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufStats ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bdok AF_huf_rstats_ok.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_bcomp AF_huf_x2t_bchain AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x2t_h.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs 0.
Hypothesis RSK : huf_rstats_stmtA AI rng_fs 1.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Theorem huf_rdt_x2_proofA : huf_rdt_stmtA2 AI rng_fs huf_dt_okA AHUF_RDT_X2.
Proof.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
         DT W S mtl flags pdt pw src jdt lo rstk AH NOF LBH HMTL HDT DTC HWB SRC SRCB SRCL S16 SRCA SDT SW ST BOT LO
         RCL RLO RHI RRLO SPT SP16 MI TP FLG HINV HBM CIBM RSTK RI RISH RFS RRS E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  rewrite <- (Z_to_bv_bv_unsigned sp).
  set (SPV := bv_unsigned sp) in *. clearbody SPV.
  eapply x2_openB with (AI := AI) (fflag := fflag) (rng_fs := rng_fs) (lo := lo) (pdt := pdt) (pw := pw) (jdt := jdt);
    try eassumption.
  intros FF m3 jA jB jC jT jD jE j3 hdw y5 y6 y7 y28 y29 y30 y31 FRM HHM HHR HDV C16 FRA FFH ZC.
  eapply x2_rsB with (AI := AI) (fflag := fflag) (rng_fs := rng_fs) (rstk := rstk) (pdt := pdt) (pw := pw) (jdt := jdt);
    try eassumption.
  intros m5 r tl nbs hw rank j0 z1 z5 z6 z7 z14 z15 z16 z17 z28 z29 z30 z31 OK.
  pose proof OK as (HY & UDT & UW & ART & HR & HM & HHR' & HDV' & STATS & NBSR & LHW & BHW & LRK & TLM & XB & _).
  destruct XB as (dt & rs0 & syb & rv & k0 & k8 & k16 & k24 & k32 & k40 & k48 & k56 & k64 & k72 & k80 & k88 & k96 & k104 & k112
                  & k120 & k136 & k144 & k152 & k160 & k192 & k224 & k232 & k240 & k248 & k256 & k264 & k272 & k280 & k288 & k296
                  & k304 & k312 & k320 & k328 & k336 & k344 & k360 & k368 & k376 & k384 & k392 & XB).
  eapply x2_chainB with (m5 := m5) (wksz := 8704) (SPA := SPB SPV) (nbs := nbs) (hw := hw) (rank := rank).
  all: try first [exact HY | exact UDT | exact UW | exact ART | exact HR | exact HM | exact HHR' | exact TP | exact AF_huf_x2t_h.x2hb_proof
                 | exact STATS | exact NBSR | exact LHW | exact BHW | exact LRK | exact TLM | exact XB].
  intros m2 dt2 rs2 rv2 syb2 q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q136 q144 q152 q160 q192 q208
         q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q360 q368 q376 q384 q392
         yra y5' y6' y7' y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28' y29' y30' y31' XB2 PRE Z0 Z1 Z2 Z3.
  eapply x2_kendB with (AI := AI) (fflag := fflag); eassumption.
Qed.
End Asm.
End CANSEC1.
