(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_StateStmt LbB_ResvB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoR6.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma munch_nil_eqG : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Definition wv1_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN7_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 WO_AN7_RA) fc None m (seg_rom asegs).

  Definition wv1_post (e : went H) (ff : Z) (m : mem) (s2 s3 s4 s5 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_AN8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_W32)) fc None m (seg_rom asegs).

  Lemma wv1 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wv1_post e ff m s2 s3 s4 s5 s6 s8 s9 s10 s11 F fc)
      (wv1_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wg1b (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqG m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.

  Definition wv2_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (ff + 3272)) s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 WO_AN8_RA) fc None m (seg_rom asegs).

  Definition wv2_post (e : went H) (ff : Z) (m : mem) (s2 s3 s4 s5 s6 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_AN9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_TYP)) fc None m (seg_rom asegs).

  Lemma wv2 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wv2_post e ff m s2 s3 s4 s5 s6 s7 s8 s10 s11 F fc)
      (wv2_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wg2c (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqG m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.

  Definition wv3_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ff + 3056)) s3 s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 WO_AN9_RA) fc None m (seg_rom asegs).

  Definition wv3_post (e : went H) (ff : Z) (m : mem) (s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_MVA2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3056)) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3056)) s3 s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m (seg_rom asegs).

  Lemma wv3 : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    evt asegs (wv3_post e ff m s3 s4 s5 s7 s8 s9 s10 s11 F fc)
      (wv3_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc HP HI.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & _ & _ & FH0 & FL & _).
    assert (FH : ff + 3808 <= 2 ^ 47) by lia.
    eapply evt_cut.
    { exact (wg3c (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                  a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ff (w_lo e) (wSP e)
                  F0 FH (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & _ & _ & _).
    subst ms. pose proof (munch_nil_eqG m m1 MU) as EM. subst m1.
    apply evt_done. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31. reflexivity.
  Qed.
End WoG.
