(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit I_consts I_qck R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_acps Sj_hkit Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_os_xsputnA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export El_os_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition xsputnX_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS S N CAP q lo fO : Z) (kO : nat) (pb : word) (pp ep : Z) (dum bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  rw_cells asegs m OS (sb_cellsX pb (wz pp) (wz ep) dum) -> PUTINV OS pp ep -> bytes_at asegs m (shad OS) (repeat z8 36) ->
  bytes_at asegs m S bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> CAP <= 2^40 -> 0 < S -> S + CAP <= 2^47 -> acc asegs m S N -> (0 < N -> rng_class RT Σ S N) ->
  ((S + CAP <= lo /\ (S + CAP <= OS \/ OS + 288 <= S)) \/ q <= S) ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_XSPUTN_DEPTH <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (pb' : word) (pp' ep' : Z) (dum' : list byte),
     ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo q ->
     rw_cells asegs m' OS (sb_cellsX pb' (wz pp') (wz ep') dum') -> PUTINV OS pp' ep' -> bytes_at asegs m' (shad OS) (repeat z8 36) ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 40, OS + 128)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz N) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) (wz S) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz 0x10d178) fc None m (seg_rom asegs)).
End Stmt.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold EL_XSPUTN_DEPTH, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

Lemma rng_class_sub : forall Σ p n p' n', rng_class RT Σ p n -> p <= p' -> p' + n' <= p + n -> rng_class RT Σ p' n'.
Proof.
  intros Σ p n p' n' H H1 H2.
  destruct H as [(q & k & IN & A1 & A2) | [(f & k & IN & A1 & A2) | [(A1 & A2) | (A1 & A2)]]].
  - left. exists q, k. split; [exact IN| lia].
  - right; left. exists f, k. split; [exact IN| lia].
  - right; right; left. lia.
  - right; right; right. lia.
Qed.

Lemma chkr_of : forall Σ m p n, ART RT Σ m -> 0 < n <= 2^40 -> acc asegs m p n -> rng_class RT Σ p n -> chkr m p n.
Proof using AF_SHW.
  intros Σ m p n ART0 Hn AC RC. split; [exact AC|]. split.
  - intros i Hi. destruct (AF_SHW Σ m (p + i) 1 ART0 ltac:(lia) (rng_class_sub Σ p n (p + i) 1 RC ltac:(lia) ltac:(lia))) as (QW & _).
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & _). exists w1. exact W1.
  - destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (_ & RIM). split; [exact RIM| lia].
Qed.

Theorem xsputnX_aevt : xsputnX_cpsA RT PMc.
Proof using AF RIP AF_IC AF_SHW DCC FDO MST.
  unfold xsputnX_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SBF PI SHZ SRC LB RN CAP40 S0 SHI ACC CLS SEP ART0 MI ST LOW LOR SPT Q16 HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FHI'.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (LOC : os_locA OS).
  { split; [exact AL16|]. split; [ul|]. split; [ul|]. unfold SHADOW_LO. destruct FHI' as [H|H]; [left; lia| right; lia]. }
  assert (CKD : chkr m (OS + 64) 64).
  { apply (chkr_of Σ m (OS + 64) 64 ART0); [lia| |].
    - apply (acc_sub asegs m OS (8 * Z.of_nat 36) (OS + 64) 64); [| lia| lia].
      apply (acc_zero_run asegs m OS 36); [Z.div_mod_to_equations; lia| lia| exact SHZ].
    - right; left. exists fO, kO. split; [exact INF| lia]. }
  assert (CKS : 0 < N -> chkr m S N).
  { intros HC. apply (chkr_of Σ m S N ART0); [lia| exact ACC| exact (CLS HC)]. }
  pose proof (AF_IC Σ m ART0) as IC. pose proof (af_client_consts RT AF Σ m ART0) as CC. pose proof (DCC Σ m ART0) as DC.
  apply (aevt_evt RT AF PMc MST).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  eapply evt_mono.
  { eapply (os_xsputnX_proof RIP ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo OS S N CAP pp ep pb dum bs);
      rewrite ?EQ; first [exact ST| exact SBF| exact PI| exact LOC| exact SRC| exact LB| exact ACC| exact SEP| exact DC| exact CC| exact SHZ| exact CKS| exact CKD| exact IC| exact MI| ul | idtac].
    all: try ul. all: try (destruct SEP as [(A1 & A2)|A1]; [left; split; [exact A1| exact A2]| right; lia]). }
  cbv beta. intros ms' PO. unfold os_xsputnX_post in PO. rewrite !EQ in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & pb' & pp' & ep' & dum' & m' & -> & MU & WM & MI' & ST' & SBF' & PI').

  assert (ART' : ART RT Σ m').
  { apply (art_client_write RT AF Σ m m' (q - EL_XSPUTN_DEPTH) ART0 ltac:(ul)); [| exact WM].
    intros a Ha. apply MU. cbn [outside]. split; [| split; [| exact I]].
    - intros Hr. apply Ha. left. ul.
    - intros Hr. apply Ha. right; right; right; left. exists fO, kO. split; [exact INF| lia]. }
  apply (HK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' pb' pp' ep' dum' ART' MI' ST' SBF' PI').
  - apply (shz36_munch _ m m' OS SHZ MU); [lia| ul|]. intros x Hx. cbn [outside]. pose proof (os_locA_bounds OS LOC) as (B1 & B2 & B3).
    split; [ul|]. split; [ul| exact I].
  - intros a Ha Ho. apply MU. cbn [outside] in *. destruct Ho as (Ho & _). split; [| split; [exact Ho| exact I]].
    destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul.
Qed.
End Lift.
