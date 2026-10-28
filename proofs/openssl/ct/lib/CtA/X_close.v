(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Nodes RzCPS NodesA SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_cs X_open.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_aio_close : Z := 0x5255fc.

Lemma close_walkA : forall (sp fd : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z),
  stk ctasegs m lo sp -> SEGTOP_A <= lo -> lo + 128 <= sp -> sp < 2^64 -> 0 <= fd < 2^31 -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : word -> option byte) junk,
      ms' = MSsvc (mkR (Z_to_bv 64 0x5322e0) (Z_to_bv 64 (sp + -16)) gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 57) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x52c18c) (Z_to_bv 64 57) fc None m' (seg_rom ctasegs)
      /\ munch [(sp + -16, sp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ rw_cells ctasegs m' (sp + -16) [CB 8 junk; C8 ra]
      /\ stk ctasegs m' lo (sp + -16))
    (entry_st ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_close m).
Proof.
  intros until lo. intros ST LO0 LO UT Hfd MI.
  unfold entry_st, e_close. pose proof ST as (STa & STb & _). unfold SEGTOP_A in LO0.
  pose proof (munch_refl [(sp + -16, sp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 16%nat ST.
  do 11 step.
  do 9 step.
  step_ecall.
  do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FR| exact ST].
Qed.

Lemma close_walkB : forall (sp : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo : Z) junk,
  stk ctasegs m lo (sp + -16) -> SEGTOP_A <= lo -> lo + 128 <= sp -> sp < 2^64 ->
  rw_cells ctasegs m (sp + -16) [CB 8 junk; C8 ra] -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m (seg_rom ctasegs))
                 /\ stk ctasegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x5322e0) (Z_to_bv 64 (sp + -16)) gp tp t0 t1 t2 s0 s1
             (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 57) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52c190) fc None m (seg_rom ctasegs)).
Proof.
  intros until junk. intros ST LO0 LO UT FR MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in LO0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp + -16)) = sp + -16) by (apply unsigned_lit; lia).
  do 10 step. if_true.
  do 5 step.
  release_frame FR ST sp.
  apply evt_done. split; [| replace (sp + -16 + 16) with sp in ST by lia; exact ST].
  do 16 eexists. reflexivity.
Qed.

Section XClose.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem close_ok : close_contract RT.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd lo
    Ha0 Hfd HLK ST LO SPW HTP CAN ART0 MI0.
  subst a0.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  assert (SEG : SEGTOP_A <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below ctasegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (close_walkA usp fd ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST SEG LO ltac:(lia) ltac:(lia) MI0) as W1.
  lazymatch type of W1 with evt ctasegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x5322e0) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 57) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x52c18c) (Z_to_bv 64 57) fc None m1 (seg_rom ctasegs)) in *.
  unfold ASTA in Hc1'.
  apply (ast_close ctasegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun ms => nretA msA (eff0 (Z_to_bv 64 0)) = ms) (fun mo => ARTM RT Σ mo /\ PMfd (fd_remove F0 (Z_to_bv 64 fd)) fs0 mo) fd);
    [lia| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)| | | exact Hc1'|].
  - intros ms <-. split; [reflexivity|]. split; reflexivity.
  - intros mo (HAR & HF & HFS). rewrite HF. split; [exact HLK|].
    split; [apply (af_with_fds RT AF); exact HAR| split; [reflexivity| exact HFS]].
  - intros c2 Hc2.
    assert (EQ : nretA msA (eff0 (Z_to_bv 64 0)) = MS (mkR (Z_to_bv 64 0x5322e0) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                   (Z_to_bv 64 0) (Z_to_bv 64 57) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x52c190) fc None m1 (seg_rom ctasegs)).
    { unfold msA, eff0. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2.
    pose proof (close_walkB usp ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo junk ST1 SEG LO
                  ltac:(lia) FR1 MI1) as W2.
    lazymatch type of W2 with evt ctasegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes ctasegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (RS & ST2) & Hc3').
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 (usp - 128) ART0); [lia| | exact WM1].
      intros a Ha. rewrite (MU1 a); [reflexivity|]. cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I]. }
    exists m1. eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP; exact RS|].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact WM1|]. split; [exact ST2|].
    intros x Hx. apply MU1. cbn in Hx |- *. intuition lia.
Qed.

End XClose.
