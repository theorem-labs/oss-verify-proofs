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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqd_asan_transport0 : forall P (m1 : amem),
  sqd_ranges P -> sqd_side P -> sqd_sep P -> (w_nbSeq P <> 0 -> sqd_tables P) -> sqd_astat P -> sqd_pro P -> sqd_asan P (w_m P) ->
  (w_nbSeq P <> 0 -> w_LLT P + 4104 <= 2^47 /\ w_OFT P + 2056 <= 2^47 /\ w_MLT P + 4104 <= 2^47) ->
  munch (sqd_Wb P) (w_m P) m1 -> wmono bsegs (w_m P) m1 -> sqd_asan P m1.
Proof.
  intros P m1 RG SD SEP TBL AS PRO ASN TH3 MU WM.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_Wb sqd_asan sqd_astat sqd_ranges sqd_side sqd_sep sqd_tables sqd_pro w_m w_nbSeq w_LLT w_OFT w_MLT] in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
  destruct ASN as (ARD & AHD & ARS & ATB & ACL & AOUT & ARL & AHL & AZS & ARTC).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FBK).
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, apart, off_stack in *.
  pose proof atop_range as ATR. destruct AST as (AST1 & RSTK & RAI). unfold KHIGH in AST1.
  destruct (ARD ltac:(clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BDL.
  pose proof (ablk_lits _ _ FBK) as FBL.
  assert (FF8 : FF mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (FF0 : 0 <= FF) by (unfold AIMG_HI in FFa; clear - FFa; lia).
  assert (STK : 17594333495296 <= SPV - 4704) by (clear - AST1 R13; lia).
  assert (FFL : FF + 256 <= 2147450880 \/ 17594333495296 <= FF) by (clear - FBL; lia).
  assert (DCL : DCTX + 95992 <= 2147450880 \/ 17594333495296 <= DCTX) by (clear - BDL; lia).
  assert (FLO : FF + 256 <= lo) by (clear - FFb ATL; lia).
  (* [comment removed for export] *)
  assert (DJ : exists W, munch W m m1 /\ (forall X n, 0 <= X -> 0 < n -> X + n <= 2^47 -> (FF + 256 <= X \/ X + n <= FF) ->
                 disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)) /\
                 (forall A n, 0 <= A -> 0 <= n -> A + n <= 6443008 -> disjoint_from W A n)).
  { destruct (Z.eq_dec CAP 0) as [C0|C0].
    - subst CAP. exists [(DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
                         (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)].
      split; [exact (munch_drop_empty DST _ m m1 MU)|]. split.
      + intros X n H1 H2 H3 H4. exact (wb5_shadow_disj DCTX SPV FF SHF X n H1 H2 H3 FF0 FF8 ESHF H4 DCL STK FFL).
      + intros A n H1 H2 H3. unfold DCTX_entropy_rep, DCTX_fseEntropy, AIMG_HI in *. cbn [disjoint_from].
        split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 STK; lia|]. split; [clear - H3 FFa; lia|].
        split; [rewrite ESHF, shad_div; unfold ASHOFF; clear - H3 FF0; Z.div_mod_to_equations; lia| exact I].
    - exists [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
              (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)].
      split; [exact MU|].
      assert (BB : B0 < B1) by (clear - R6 R7 R8 C0; lia).
      destruct (AOUT BB) as (AO & _). destruct (AO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
      split.
      + intros X n H1 H2 H3 H4. exact (wb_shadow_disj DST CAP DCTX SPV FF SHF X n H1 H2 H3 FF0 FF8 ESHF H4 ltac:(clear - BOL R6 R7 R8; lia) DCL STK FFL).
      + intros A n H1 H2 H3. unfold DCTX_entropy_rep, DCTX_fseEntropy, AIMG_HI in *. cbn [disjoint_from].
        split; [clear - H3 BOL R6 R7 R8; lia|].
        split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 STK; lia|]. split; [clear - H3 FFa; lia|].
        split; [rewrite ESHF, shad_div; unfold ASHOFF; clear - H3 FF0; Z.div_mod_to_equations; lia| exact I]. }
  destruct DJ as (W & MUW & DJ & DJI).
  assert (TU : forall X n, unpoisoned m X (X + n) -> 0 <= X -> 0 < n -> X + n <= 2^47 -> (FF + 256 <= X \/ X + n <= FF) ->
                 unpoisoned m1 X (X + n)).
  { intros X n U H1 H2 H3 H4. eapply unp_tr; [exact U | exact MUW | exact (DJ X n H1 H2 H3 H4)]. }
  assert (TH : forall A n, ahull RNG m A n -> ahull RNG m1 A n).
  { intros A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R). exists RLO, RHI.
    do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R]. }
  assert (TA : forall X n, areg RNG m X n -> (0 < n -> 0 <= X /\ X + n <= 2^47 /\ (FF + 256 <= X \/ X + n <= FF)) -> areg RNG m1 X n).
  { intros X n A HX Hn. destruct (A Hn) as (B & U & Q1 & Q2). destruct (HX Hn) as (X1 & X2 & X3).
    split; [exact B|]. split; [exact (TU X n U X1 Hn X2 X3)|]. split; [exact Q1 | exact Q2]. }
  assert (TR : forall X n, aro RNG m X n -> (0 < n -> 0 <= X /\ X + n <= 2^47 /\ (FF + 256 <= X \/ X + n <= FF)) -> aro RNG m1 X n).
  { intros X n (U & Q1 & Q2) HX. split; [| split; [exact Q1 | exact Q2]].
    destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
    - destruct (HX Hn) as (X1 & X2 & X3). exact (TU X n U X1 Hn X2 X3).
    - destruct U as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. lia. }
  assert (TC : forall A cs, rw_cells bsegs m A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m1 A cs).
  { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MUW | exact WM | apply DJI; lia]. }
  split; [eapply TA; [exact ARD | intros _; clear - R1 R2 AFD; lia]|].
  split; [exact (TH _ _ AHD)|].
  split; [eapply TA; [exact ARS | intros Hn0; specialize (AFS Hn0); clear - R3 R4 AFS; lia]|].
  split.
  { intros HN. destruct (ATB HN) as (A1 & A2 & A3). destruct (AFT HN) as (F1 & F2 & F3). destruct (TH3 HN) as (U1 & U2 & U3).
    destruct (TBL HN) as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & _).
    pose proof (seq_pow_le _ _ OKLL) as P1. pose proof (seq_pow_le _ _ OKML) as P3.
    assert (P2 : 1 <= 2^(st_log tOF) <= 256).
    { destruct OKOF as ((O1 & O2) & _). cbn [kind_maxLog] in O2. split; [pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); lia|].
      change 256 with (2^8). apply Z.pow_le_mono_r; lia. }
    split; [eapply TR; [exact A1 | intros _; clear - T4 U1 F1 P1; lia]|].
    split; [eapply TR; [exact A2 | intros _; clear - T5 U2 F2 P2; lia]|].
    eapply TR; [exact A3 | intros _; clear - T6 U3 F3 P3; lia]. }
  split.
  { apply (aro_client_transport_gen RNG m m1 W WM ACL MUW). intros A n HIn.
    destruct (aclient_bounds A n HIn) as (B1' & B2' & B3'). apply DJ; try (clear - B1' B2' B3'; lia).
    right. unfold AIMG_HI in FFa. clear - B3' FFa. lia. }
  split.
  { intros BB. destruct (AOUT BB) as (AO & AH).
    destruct (AO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
    split; [eapply TA; [exact AO | intros _; specialize (AFO BB); clear - R9 BOL AFO BB; lia] | exact (TH _ _ AH)]. }
  split; [eapply TA; [exact ARL | intros _; clear - R10 R11 R12 AFL; lia]|].
  split; [exact (TH _ _ AHL)|].
  split.
  { destruct AZS as (RLO & RHI & U & HB & W0 & AB & R). exists RLO, RHI.
    split; [| split; [exact HB | split; [eapply wr_at_transport; [exact W0 | exact WM] | split; [exact AB | exact R]]]].
    replace SPV with (lo + (SPV - lo)) in U |- * by lia.
    apply TU; [exact U | clear - R15; lia | clear - R13; lia | clear - R14; lia | clear - FLO; lia]. }
  destruct ARTC as (G1 & G2 & G3 & G4 & G5 & G6). unfold art.
  split; [apply TC; [exact G1 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G2 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G4 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | clear; lia | cbn; clear; lia]|].
  apply TC; [exact G6 | clear; lia | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma stk_keep_empty : forall (m m' : amem) lo hi, stk bsegs m lo hi -> hi <= lo -> stk bsegs m' lo hi.
Proof. intros m m' lo hi (A & B & _) H. split; [exact A|]. split; [exact B|]. intros a Ha. exfalso. lia. Qed.

End CANSEC1.
