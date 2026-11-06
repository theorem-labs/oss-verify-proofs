(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): the inner walk
   M02D.M02_inner (0x13c3c .. calloc's entry at 0x172a0) from its four pieces A (0x13c3c .. 0x13d04), B (.. 0x13dd0),
   C (.. 0x13e44) and D (.. the `jal calloc` at 0x13e7c). A starts on m0 itself; each piece ends in an M02_mid
   state (Exec.evt_cut), whose registers and memory are the next piece's start: sp, s2 = ~m, s11 = &m->n kept,
   fcsr's rounding mode 0, the memory an M02_inv successor of m0. The plain twin is lib/Prog/Seg/M02_I.v.
   Part of the proof of LLVMFuzzerTestOneInput: the composition of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment composition). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import M02D M02K.
Import ListNotations.
Open Scope Z_scope.

Theorem m02_compose : M02_A_stmt -> M02_B_stmt -> M02_C_stmt -> M02_D_stmt -> M02_inner.
Proof.
  intros PA PB PC PD. unfold M02_inner.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
    S c mm cap rc mc ret Esp Es2 Es11 Es4 HFC HMOD HM.
  (* A: 0x13c3c .. 0x13d04 *)
  eapply evt_cut.
  { eapply PA with (m0 := m0) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (ret := ret);
      eassumption. }
  intros ms1 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
              F1 & fc1 & m1 & -> & HFC1 & HI1).
  (* B: 0x13d04 .. 0x13dd0 *)
  eapply evt_cut.
  { eapply PB with (m0 := m0) (m := m1) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc)
      (ret := ret); first [reflexivity | eassumption]. }
  intros ms2 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
              F2 & fc2 & m2 & -> & HFC2 & HI2).
  (* C: 0x13dd0 .. 0x13e44 *)
  eapply evt_cut.
  { eapply PC with (m0 := m0) (m := m2) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc)
      (ret := ret); first [reflexivity | eassumption]. }
  intros ms3 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
              F3 & fc3 & m3 & -> & HFC3 & HI3).
  (* D: 0x13e44 .. calloc's entry *)
  eapply PD with (m0 := m0) (m := m3) (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (ret := ret);
    first [reflexivity | eassumption].
Qed.
