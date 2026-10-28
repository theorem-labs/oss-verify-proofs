(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_StateStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_ResvB LbB_WoR4 LbB_WoR5 LbB_WoVec.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Definition wps3 (ff : Z) (m : mem) (b1 b2 b3 : Z) : Prop :=
    wpst ff m (vtrip b1 500) (vtrip b2 100) (vtrip b3 100) /\ wblk m b1 500 /\ wblk m b2 100 /\ wblk m b3 100.

  Lemma munch_nil_eqF : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Definition wq1_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (ff + 2944)) s9 s10 s11 t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON4_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq1_post (e : went H) (ff : Z) (m : mem) (s2 s3 s4 s5 s6 s7 s9 s10 s11 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_ON5_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (ff + 2944)) s9 s10 s11 x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 (rv_entry RESV_W32)) (w_fc e) None m (seg_rom asegs).

  Lemma wq1 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wq1_post e ff m s2 s3 s4 s5 s6 s7 s9 s10 s11)
      (wq1_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wf1b (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 (w_F e) (w_fc e) m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqF m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.

  Definition wq2_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON5_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (ff + 2968)) s10 s11 t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON5_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq2_post (e : went H) (ff : Z) (m : mem) (s2 s3 s4 s5 s6 s7 s8 s10 s11 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_ON6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (ff + 2968)) s10 s11 x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 (rv_entry RESV_TYP)) (w_fc e) None m (seg_rom asegs).

  Lemma wq2 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wq2_post e ff m s2 s3 s4 s5 s6 s7 s8 s10 s11)
      (wq2_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wf2c (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 (w_F e) (w_fc e) m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqF m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.

  Definition wq3_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 (Z_to_bv 64 (ff + 2752)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON6_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq3_post (e : went H) (ff : Z) (m : mem) (s2 s3 s4 s5 s7 s8 s9 s10 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_MVA1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 2752)) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AST_MVA) (w_fc e) None m (seg_rom asegs).

  Lemma wq3 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wq3_post e ff m s2 s3 s4 s5 s7 s8 s9 s10)
      (wq3_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wf3c (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 (w_F e) (w_fc e) m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqF m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.

End WoF.
