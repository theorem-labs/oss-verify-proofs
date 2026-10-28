(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Nodes RzCPS NodesA SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_cs D_libiface D_clx D_trpro D_atiface X_atexit X_xdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section XAtreg.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem atexit_ok : atexit_contract RT XENVA XENVA1.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Ha0 ST LO SPW XE ART0 MI0.
  subst a0.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  destruct XE as ((f1 & a1v & XT) & I0).
  pose proof XT as (TID & (p1 & p2 & ATX) & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & _).
  assert (SEG : 0xbcb000 <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below ctasegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (atexit_reg_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AEF_GUARD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo p1 p2 cdt thr sec tm1 f1 a1v ST ATX ATA LIBC MI0 ltac:(fold usp; lia) SEG) as W1.
  unfold entry_st, e_atexit in Hc.
  lazymatch type of W1 with evt ctasegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO & Hc1'). unfold atexit_post in PO. fold usp in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & ATX1 & ATA1).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 128) ART0); [lia| | exact WM1].
    intros a Ha. apply MU1. cbn [outside].
    repeat (split; [intros Hin; apply Ha; first [left; ul | right; left; apply D_cs.client_static_intro; lia] |]). exact I. }
  exists m1. eapply ASTA_conseq; [exact Hc1'|]. intros ms <-.
  split; [exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc; reflexivity|].
  split.
  { split; [exact ART1|]. split; [exact MI1|]. split; [exact WM1|]. split; [exact ST1|].
    intros x Hx. apply MU1. unfold ATX_W in Hx. cbn [outside] in Hx |- *. intuition lia. }
  unfold XENVA1, AEF_CALLX, AEF_GUARDX.
  apply (XENVT_retab 1 f1 a1v 2 (Z_to_bv 64 0x51fbd8) (Z_to_bv 64 0x1f4074) m m1 XT).
  - intros a (lo0 & hi0 & Hin & Hx). apply MU1. cbn [outside]. cbn [In XENV_FPB] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat (split; [ul|]); exact I|]). destruct Hin.
  - exists p1, p2. exact ATX1.
  - exact ATA1.
Qed.

End XAtreg.
