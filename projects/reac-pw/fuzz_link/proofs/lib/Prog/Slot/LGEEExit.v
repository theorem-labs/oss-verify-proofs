(* LGlue's EXIT_OK: from the exit cut (0x1413c, ex_ms) to the caller's ra. The chain, each step a lemma:
     X1  0x1413c -> free (marks) at 0x173d4                  (LEX.le_EXa, cut_evt)
     F1  free (mk), ra 0x14144: mk leaves hb                 (LFrAl.lfr_free)
     X2  0x14144 -> free (m) at 0x173d4                      (LEX.le_EXb, cut_evt)
     F2  free (md), ra 0x1414c: md leaves hb                 (LFrAl.lfr_free)
     then the epilogue to the ret (LGEELib.ee_fin). What is left of hb is a permutation of hx g T: T itself
   when the driver call started with no kept block, else []; LGEELib.ee_case turns that into FIN's case. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrAl LFrLo LFrEn
  LGlue LEDefs LEX LGEEOp LGEELib.
Import ListNotations.
Local Open Scope Z_scope.

Section GEX.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* X1: mv a0, s7 ; jal free *)
Lemma ee_X1 : forall g md mk hb T c,
  CUT B API g L_EXIT hb T (ex_ms (lg_E g md mk) (lg_gp g)) c ->
  SR (ms_segs B) c (CUT B API g LLVM_FREE hb T (le_free1 (lg_S g) (lg_gp g) (lg_R g) md mk)).
Proof.
  intros g md mk hb T c HC.
  apply (ee_cut_wr B API FF) in HC.
  apply (cut_evt B API FF g L_EXIT hb T [] _ LLVM_FREE _ c HC).
  - intros t [].
  - intros ms (HX & HW).
    eapply evt_mono; [exact (le_EXa (lg_E g md mk) (lg_R g) (lg_gp g) ms eq_refl HW HX)|].
    intros ms' (H & Hfp). apply ee_eqv_intro. split; [exact H | exact (Hfp [])].
  - intros ms' H. exact (ee_free1_pc _ _ _ _ _ _ H).
Qed.

(* F1: free (marks) *)
Lemma ee_F1 : forall g md mk hb1 hb2 T c, ~ In (mk, MK_SIZE) T ->
  CUT B API g LLVM_FREE (hb1 ++ (mk, MK_SIZE) :: hb2) T (le_free1 (lg_S g) (lg_gp g) (lg_R g) md mk) c ->
  SR (ms_segs B) c (CUT B API g L_FREE1_RA (hb1 ++ hb2) T (le_free1r (lg_S g) (lg_gp g) (lg_R g) md)).
Proof.
  intros g md mk hb1 hb2 T c HnT HC.
  eapply SR_mono.
  - apply (lfr_free B API FF g hb1 mk MK_SIZE hb2 T L_FREE1_RA (le_free1 (lg_S g) (lg_gp g) (lg_R g) md mk)
             (eqv_cl (le_free1r (lg_S g) (lg_gp g) (lg_R g) md)) c HnT).
    + unfold L_FREE1_RA. lia.
    + reflexivity.
    + exact HC.
    + intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9
                 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & -> & _).
      repeat split.
    + intros R F fc m regs' m' HP RP C PM.
      destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9
                      & s10 & s11 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & EQ & FC & TM).
      destruct (ee_MS_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & EF & Efc & Em). subst R F0 fc0 m0.
      eapply ee_canon; [exact RP|].
      do 27 eexists. exists F, fc, m'. split; [reflexivity|]. split; [exact FC|].
      exact (ee_tail_carry B API FF g _ _ m m' TM C PM).
  - intros c' H. exact (ee_cut_collapse B API g _ _ _ _ c' H).
Qed.

(* X2: mv a0, s0 ; jal free *)
Lemma ee_X2 : forall g md hb T c,
  CUT B API g L_FREE1_RA hb T (le_free1r (lg_S g) (lg_gp g) (lg_R g) md) c ->
  SR (ms_segs B) c (CUT B API g LLVM_FREE hb T (le_free2 (lg_S g) (lg_gp g) (lg_R g) md)).
Proof.
  intros g md hb T c HC.
  apply (cut_evt B API FF g L_FREE1_RA hb T [] _ LLVM_FREE _ c HC).
  - intros t [].
  - intros ms H. eapply evt_mono; [exact (le_EXb (lg_S g) md (lg_R g) (lg_gp g) ms H)|].
    intros ms' (H' & Hfp). apply ee_eqv_intro. split; [exact H' | exact (Hfp [])].
  - intros ms' H. exact (ee_free2_pc _ _ _ _ _ H).
Qed.

(* F2: free (m) *)
Lemma ee_F2 : forall g md hb1 hb2 T c, ~ In (md, MD_SIZE) T ->
  CUT B API g LLVM_FREE (hb1 ++ (md, MD_SIZE) :: hb2) T (le_free2 (lg_S g) (lg_gp g) (lg_R g) md) c ->
  SR (ms_segs B) c (CUT B API g L_FREE2_RA (hb1 ++ hb2) T (le_free2r (lg_S g) (lg_gp g) (lg_R g))).
Proof.
  intros g md hb1 hb2 T c HnT HC.
  eapply SR_mono.
  - apply (lfr_free B API FF g hb1 md MD_SIZE hb2 T L_FREE2_RA (le_free2 (lg_S g) (lg_gp g) (lg_R g) md)
             (eqv_cl (le_free2r (lg_S g) (lg_gp g) (lg_R g))) c HnT).
    + unfold L_FREE2_RA. lia.
    + reflexivity.
    + exact HC.
    + intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & s8
                 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & -> & _).
      repeat split.
    + intros R F fc m regs' m' HP RP C PM.
      destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & s8
                      & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & EQ & FC & TM).
      destruct (ee_MS_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & EF & Efc & Em). subst R F0 fc0 m0.
      eapply ee_canon; [exact RP|].
      do 28 eexists. exists F, fc, m'. split; [reflexivity|]. split; [exact FC|].
      exact (ee_tail_carry B API FF g _ _ m m' TM C PM).
  - intros c' H. exact (ee_cut_collapse B API g _ _ _ _ c' H).
Qed.

Theorem glue_exit : EXIT_OK B API.
Proof.
  intros g c (md & mk & hb & T & HI & HC).
  pose proof (cut_T B API g _ _ _ _ c HC) as HT.
  destruct (hp_md_mk g (lg_E g md mk) hb T HI HT (md, MD_SIZE) ltac:(left; reflexivity)) as (_ & Hmd).
  destruct (hp_md_mk g (lg_E g md mk) hb T HI HT (mk, MK_SIZE) ltac:(right; left; reflexivity))
    as (Hin & Hmk).
  destruct (in_split _ _ Hin) as (hb1 & hb2 & Ehb).
  assert (P1 : Permutation (hb1 ++ hb2) ((md, MD_SIZE) :: hx g T)).
  { apply (Permutation_app_inv hb1 hb2 [(md, MD_SIZE)] (hx g T) (mk, MK_SIZE)). rewrite <- Ehb. exact HI. }
  destruct (in_split (md, MD_SIZE) (hb1 ++ hb2) (Permutation_in _ (Permutation_sym P1) (or_introl eq_refl)))
    as (hb3 & hb4 & Ehb').
  assert (P2 : Permutation (hb3 ++ hb4) (hx g T)).
  { apply (Permutation_app_inv hb3 hb4 [] (hx g T) (md, MD_SIZE)). rewrite <- Ehb'. exact P1. }
  eapply SR_bind; [exact (ee_X1 g md mk hb T c HC)|]. intros c1 H1. rewrite Ehb in H1.
  eapply SR_bind; [exact (ee_F1 g md mk hb1 hb2 T c1 Hmk H1)|]. intros c2 H2.
  eapply SR_bind; [exact (ee_X2 g md _ T c2 H2)|]. intros c3 H3. rewrite Ehb' in H3.
  eapply SR_bind; [exact (ee_F2 g md hb3 hb4 T c3 Hmd H3)|]. intros c4 H4.
  exact (ee_fin B API FF g _ T c4 (ee_case g _ T HT P2) H4).
Qed.

End GEX.

Print Assumptions glue_exit.
About glue_exit.
