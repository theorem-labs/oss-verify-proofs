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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_mm_post (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz D n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMMOVE_STACK_A, SPz); (D, D + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz /\ stk bsegs m' D (D + n).

Lemma sql_mmove_spec : zd_memmoveZ_stmtA ->
  forall (RNG : footprint) (D S n SPz : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem) lo,
  stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) -> 0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMMOVE_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMMOVE_STACK_A \/ SPz <= S) -> (D + n <= lo \/ SPz <= D) ->
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk D (D + n) -> aro RNG m D n -> ahull RNG m D n ->
  art m -> astk RNG lo SPz -> mem_inv bsegs m ->
  evtF bsegs RNG (sql_mm_post RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz D n lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMMOVE) fc None m (seg_rom bsegs)).
Proof.
  intros MM RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         STD RDS Hn STK LO SPT SS SD ABS AOS AHS ABD AOD AHD ART AST MI.
  unfold zd_memmoveZ_stmtA in MM.
  eapply evtF_mono.
  - eapply (MM RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      [ exact STD | exact RDS | exact Hn | exact STK | exact LO | exact SPT | exact SS | exact SD
      | exact ABS | exact AOS | exact AHS | exact ABD | exact AOD | exact AHD | exact ART | exact AST | exact MI
      | reflexivity | reflexivity | reflexivity ].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DST').
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'| exact DST'].
Qed.

(* [comment removed for export] *)
Lemma sql_aregU_trF : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 < n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n (B & U & R1 & R2) MU X0 Hn Xn FB F0. split; [exact B|]. split; [| split; [exact R1 | exact R2]].
  eapply unp_tr; [exact U | exact MU |]. pose proof (shspan_bounds X n X0 Hn Xn) as (S1 & S2 & S3).
  cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div in *. unfold ASHOFF in *. clear - S1 S2 S3 FB F0 Xn X0 Hn. Z.div_mod_to_equations. lia.
Qed.
Lemma sql_aregU_trF0 : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 <= n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n A MU X0 Hn Xn FB F0. destruct (Z.eq_dec n 0) as [E|NZ].
  - subst n. destruct A as (B & U & R1 & R2). split; [exact B|]. split; [| split; [exact R1 | exact R2]].
    destruct U as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG. lia.
  - eapply sql_aregU_trF; [exact A | exact MU | exact X0 | clear - Hn NZ; lia | exact Xn | exact FB | exact F0].
Qed.
Lemma sql_ahull_tr : forall RNG (m m' : amem) X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R) WM. exists RLO, RHI.
  do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R].
Qed.
Lemma sql_art_trF : forall (m m' : amem) FF, art m -> munch [(FF, FF + 256)] m m' -> wmono bsegs m m' -> 6443008 <= FF -> art m'.
Proof.
  intros m m' FF (G1 & G2 & G3 & G4 & G5 & G6) MU WM HF.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from]; split; [clear - HA HF; lia | exact I]]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma sql_areg_trW : forall W RNG (m m' : amem) X n,
  areg RNG m X n -> munch W m m' -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X) -> areg RNG m' X n.
Proof.
  intros W RNG m m' X n A MU D Hn. destruct (A Hn) as (BK & U & R1 & R2).
  split; [exact BK|]. split; [eapply unp_tr; [exact U | exact MU | exact D]|]. split; [exact R1 | exact R2].
Qed.
Lemma sql_aregU_trW : forall W RNG (m m' : amem) X n,
  aregU RNG m X n -> munch W m m' -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X) -> aregU RNG m' X n.
Proof.
  intros W RNG m m' X n (BK & U & R1 & R2) MU D.
  split; [exact BK|]. split; [eapply unp_tr; [exact U | exact MU | exact D]|]. split; [exact R1 | exact R2].
Qed.
Lemma sql_art_trW : forall W (m m' : amem), art m -> munch W m m' -> wmono bsegs m m' ->
  (forall A cs, A + Z.of_nat (cells_size cs) <= 6443008 -> disjoint_from W A (Z.of_nat (cells_size cs))) -> art m'.
Proof.
  intros W m m' (G1 & G2 & G3 & G4 & G5 & G6) MU WM DJ.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU | exact WM | apply DJ; exact HA]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma sql_cells_tr : forall W (m1 m2 : amem) A cs,
  rw_cells bsegs m1 A cs -> munch W m1 m2 -> wmono bsegs m1 m2 -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m2 A cs.
Proof. intros W m1 m2 A cs H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM | exact D]. Qed.

(* [comment removed for export] *)
Lemma sql_aregU_of_areg : forall RNG m A n A' n', areg RNG m A n -> 0 < n -> A <= A' -> 0 <= n' -> A' + n' <= A + n -> aregU RNG m A' n'.
Proof. intros. eapply aregU_sub; eassumption. Qed.

End CANSEC1.
