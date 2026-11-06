(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the inner walk M02D.M02_inner
   (0x13ae0 .. calloc's entry at 0x16904) from its four pieces A (0x13ae0 .. 0x13b88), B (.. 0x13c00), C (.. 0x13c64)
   and D (.. the `jal calloc` at 0x13c98). m0 is an M02_inv successor of itself (M02K.m02_inv_refl); each piece
   ends in an M02_mid state (Exec.evt_cut), whose registers and memory are the next piece's start: sp, s0 = m,
   s8 = c, s10 = &m->n kept, fcsr's rounding mode 0, the memory an M02_inv successor of m0, and after B s6 = cap.
   Part of the proof of LLVMFuzzerTestOneInput: the composition of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment composition). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import M02D M02K.
Import ListNotations.
Open Scope Z_scope.

Theorem m02_compose : M02D.M02_A_stmt -> M02D.M02_B_stmt -> M02D.M02_C_stmt -> M02D.M02_D_stmt -> M02D.M02_inner.
Proof.
  intros PA PB PC PD. unfold M02_inner.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
    S c mm cap rc mc ret Esp Es0 Es8 Es10 Es4 HFC HMOD HM.
  pose proof (m02_inv_refl S c mm cap rc mc m0 HM) as HI.
  (* A: 0x13ae0 .. 0x13b88 *)
  eapply evt_cut.
  { eapply PA with (m0 := m0) (m := m0) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc)
      (ret := ret); eassumption. }
  intros ms1 (ra1 & u0 & u1 & u2 & us1 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & us2 & us3 & us4 & us5 &
              us6 & us7 & us9 & us11 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & HFC1 & HI1 & _).
  (* B: 0x13b88 .. 0x13c00 *)
  eapply evt_cut.
  { eapply PB with (m0 := m0) (m := m1) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc)
      (ret := ret); first [reflexivity | eassumption]. }
  intros ms2 (ra2 & q0 & q1 & q2 & qs1 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & qs2 & qs3 & qs4 & qs5 &
              qs6 & qs7 & qs9 & qs11 & q3 & q4 & q5 & q6 & F2 & fc2 & m2 & -> & HFC2 & HI2 & E6).
  cbv beta in E6. subst qs6.
  (* C: 0x13c00 .. 0x13c64 *)
  eapply evt_cut.
  { eapply PC with (m0 := m0) (m := m2) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc)
      (ret := ret); first [reflexivity | eassumption]. }
  intros ms3 (ra3 & y0 & y1 & y2 & ys1 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ys2 & ys3 & ys4 & ys5 &
              ys6 & ys7 & ys9 & ys11 & y3 & y4 & y5 & y6 & F3 & fc3 & m3 & -> & HFC3 & HI3 & E6').
  cbv beta in E6'. subst ys6.
  (* D: 0x13c64 .. calloc's entry *)
  eapply PD with (m0 := m0) (m := m3) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (ret := ret);
    first [reflexivity | eassumption].
Qed.
