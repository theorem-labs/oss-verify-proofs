(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs D_libiface Lept_iface Lept_env LeptC_kit LeptL_kit
  Gq_numa Gq_gaps F_atof_kit F_atof_45 F_atof_75 F_atof_115 F_atof_185.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ATOF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma atof_lift : forall (bs : list Z) (d : Z),
  (forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo s : Z),
     bytes_at asegs m s (map (Z_to_bv 8) bs) -> io_ssp m -> mem_inv asegs m -> stk asegs m lo usp ->
     lo + ATOF_STACK <= usp -> usp <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo -> 0 < s -> s + Z.of_nat (length bs) <= lo ->
     evt asegs (atof_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc m usp lo d)
       (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 F_ATOF) fc None m (seg_rom asegs))) ->
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (s : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 s ->
  bytes_at asegs m s (map (Z_to_bv 8) bs) -> own_live (rt_live RT Σ) s (Z.of_nat (length bs)) ->
  io_ssp m -> ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_atof m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st_fa0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) m' ms
                     /\ rt_after RT Σ (bv_unsigned sp) lo m m'
                     /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).
Proof using AF.
  intros bs d LEAF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
    FDO MST -> -> TOK OWN SSP ART0 MI CO.
  destruct CO as (ST & LOW & LOR & SPT & SPA).
  destruct OWN as (p & k & PIN & PLO & PHI).
  pose proof (af_live_range RT AF Σ m p k ART0 PIN) as (P0 & PR & _).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  unfold entry_st, e_atof. rewrite ESP.
  unfold STACK_WIN, RT_STACK, USTACK_TOP in *.
  apply (cps_walk_lemma RT AF _ _ _ _ MST).
  eapply evt_cut.
  { apply (LEAF ra gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F (frm_clear fc) m usp lo s);
      first [ assumption | unfold ATOF_STACK; lia ]. }
  intros ms' PO. unfold atof_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & FA0 & MU & WM & MI' & ST').
  apply evt_done. apply cps_finish. intros c Hc.
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. exists m'.
  assert (ART' : ART RT Σ m').
  { apply (art_client_writes RT AF Σ m m' lo [(usp - ATOF_STACK, usp)] ART0 MU WM); [unfold STACK_WIN; lia|].
    cbn [ivls_client]. split; [| exact I]. intros z Hz. left. unfold ATOF_STACK in *. unfold USTACK_TOP. lia. }
  split.
  { unfold ret_st_fa0. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc.
    split; [ reflexivity | exact FA0 ]. }
  split.
  { unfold rt_after. split; [exact ART'|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
  intros a Ha. apply MU. cbn [outside]. split; [| exact I].
  destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [H|H]; unfold ATOF_STACK, STACK_WIN in *; lia.
Qed.

Theorem atof_ok : atof_contract RT.
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s k bs d
    FDO MST TP TOKIN A0 TOK OWN SSP ART0 MI CO.
  unfold TOKENS in TOKIN. cbn [In] in TOKIN.
  destruct TOKIN as [E|[E|[E|[E|[]]]]]; injection E as <- <- <-.
  - exact (atof_lift [52; 53; 0] _ atof_45_evt Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
             FDO MST TP A0 TOK OWN SSP ART0 MI CO).
  - exact (atof_lift [55; 53; 0] _ atof_75_evt Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
             FDO MST TP A0 TOK OWN SSP ART0 MI CO).
  - exact (atof_lift [49; 49; 53; 0] _ atof_115_evt Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
             FDO MST TP A0 TOK OWN SSP ART0 MI CO).
  - exact (atof_lift [49; 56; 53; 0] _ atof_185_evt Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
             FDO MST TP A0 TOK OWN SSP ART0 MI CO).
Qed.
End ATOF.
