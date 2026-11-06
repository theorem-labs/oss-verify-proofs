(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable Dispatch.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv LimArm LimGate LimTop LimArms1 LimArms2 LimArms3.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma spec_table_frame : Forall arm_frame_ok spec_table.
Proof.
  unfold spec_table.
  apply Forall_cons; [exact arm_17_frame |].
  apply Forall_cons; [exact arm_19_frame |].
  apply Forall_cons; [exact arm_20_frame |].
  apply Forall_cons; [exact arm_21_frame |].
  apply Forall_cons; [exact arm_22_frame |].
  apply Forall_cons; [exact arm_23_frame |].
  apply Forall_cons; [exact arm_24_frame |].
  apply Forall_cons; [exact arm_25_frame |].
  apply Forall_cons; [exact arm_29_frame |].
  apply Forall_cons; [exact arm_32_frame |].
  apply Forall_cons; [exact arm_35_frame |].
  apply Forall_cons; [exact arm_46_frame |].
  apply Forall_cons; [exact arm_48_frame |].
  apply Forall_cons; [exact arm_56_frame |].
  apply Forall_cons; [exact arm_57_frame |].
  apply Forall_cons; [exact arm_59_frame |].
  apply Forall_cons; [exact arm_61_frame |].
  apply Forall_cons; [exact arm_62_frame |].
  apply Forall_cons; [exact arm_63_frame |].
  apply Forall_cons; [exact arm_64_frame |].
  apply Forall_cons; [exact arm_65_frame |].
  apply Forall_cons; [exact arm_66_frame |].
  apply Forall_cons; [exact arm_67_frame |].
  apply Forall_cons; [exact arm_68_frame |].
  apply Forall_cons; [exact arm_72_frame |].
  apply Forall_cons; [exact arm_73_frame |].
  apply Forall_cons; [exact arm_78_frame |].
  apply Forall_cons; [exact arm_79_frame |].
  apply Forall_cons; [exact arm_80_frame |].
  apply Forall_cons; [exact arm_82_frame |].
  apply Forall_cons; [exact arm_83_frame |].
  apply Forall_cons; [exact arm_85_frame |].
  apply Forall_cons; [exact arm_93_frame |].
  apply Forall_cons; [exact arm_94_frame |].
  apply Forall_cons; [exact arm_96_frame |].
  apply Forall_cons; [exact arm_98_frame |].
  apply Forall_cons; [exact arm_101_frame |].
  apply Forall_cons; [exact arm_113_frame |].
  apply Forall_cons; [exact arm_119_frame |].
  apply Forall_cons; [exact arm_123_frame |].
  apply Forall_cons; [exact arm_124_frame |].
  apply Forall_cons; [exact arm_130_frame |].
  apply Forall_cons; [exact arm_131_frame |].
  apply Forall_cons; [exact arm_132_frame |].
  apply Forall_cons; [exact arm_134_frame |].
  apply Forall_cons; [exact arm_135_frame |].
  apply Forall_cons; [exact arm_144_frame |].
  apply Forall_cons; [exact arm_146_frame |].
  apply Forall_cons; [exact arm_147_frame |].
  apply Forall_cons; [exact arm_149_frame |].
  apply Forall_cons; [exact arm_157_frame |].
  apply Forall_cons; [exact arm_158_frame |].
  apply Forall_cons; [exact arm_159_frame |].
  apply Forall_cons; [exact arm_160_frame |].
  apply Forall_cons; [exact arm_167_frame |].
  apply Forall_cons; [exact arm_169_frame |].
  apply Forall_cons; [exact arm_172_frame |].
  apply Forall_cons; [exact arm_174_frame |].
  apply Forall_cons; [exact arm_175_frame |].
  apply Forall_cons; [exact arm_176_frame |].
  apply Forall_cons; [exact arm_177_frame |].
  apply Forall_cons; [exact arm_178_frame |].
  apply Forall_cons; [exact arm_198_frame |].
  apply Forall_cons; [exact arm_199_frame |].
  apply Forall_cons; [exact arm_200_frame |].
  apply Forall_cons; [exact arm_201_frame |].
  apply Forall_cons; [exact arm_202_frame |].
  apply Forall_cons; [exact arm_203_frame |].
  apply Forall_cons; [exact arm_204_frame |].
  apply Forall_cons; [exact arm_205_frame |].
  apply Forall_cons; [exact arm_206_frame |].
  apply Forall_cons; [exact arm_207_frame |].
  apply Forall_cons; [exact arm_208_frame |].
  apply Forall_cons; [exact arm_209_frame |].
  apply Forall_cons; [exact arm_210_frame |].
  apply Forall_cons; [exact arm_211_frame |].
  apply Forall_cons; [exact arm_212_frame |].
  apply Forall_cons; [exact arm_214_frame |].
  apply Forall_cons; [exact arm_215_frame |].
  apply Forall_cons; [exact arm_216_frame |].
  apply Forall_cons; [exact arm_220_frame |].
  apply Forall_cons; [exact arm_222_frame |].
  apply Forall_cons; [exact arm_226_frame |].
  apply Forall_cons; [exact arm_233_frame |].
  apply Forall_cons; [exact arm_242_frame |].
  apply Forall_cons; [exact arm_260_frame |].
  apply Forall_cons; [exact arm_261_frame |].
  apply Forall_cons; [exact arm_278_frame |].
  apply Forall_cons; [exact arm_435_frame |].
  apply Forall_cons; [exact arm_439_frame |].
  apply Forall_nil.
Qed.

Lemma spec_table_lpres : Forall arm_lpres_ok spec_table.
Proof.
  unfold spec_table.
  apply Forall_cons; [exact arm_17_lpres |].
  apply Forall_cons; [exact arm_19_lpres |].
  apply Forall_cons; [exact arm_20_lpres |].
  apply Forall_cons; [exact arm_21_lpres |].
  apply Forall_cons; [exact arm_22_lpres |].
  apply Forall_cons; [exact arm_23_lpres |].
  apply Forall_cons; [exact arm_24_lpres |].
  apply Forall_cons; [exact arm_25_lpres |].
  apply Forall_cons; [exact arm_29_lpres |].
  apply Forall_cons; [exact arm_32_lpres |].
  apply Forall_cons; [exact arm_35_lpres |].
  apply Forall_cons; [exact arm_46_lpres |].
  apply Forall_cons; [exact arm_48_lpres |].
  apply Forall_cons; [exact arm_56_lpres |].
  apply Forall_cons; [exact arm_57_lpres |].
  apply Forall_cons; [exact arm_59_lpres |].
  apply Forall_cons; [exact arm_61_lpres |].
  apply Forall_cons; [exact arm_62_lpres |].
  apply Forall_cons; [exact arm_63_lpres |].
  apply Forall_cons; [exact arm_64_lpres |].
  apply Forall_cons; [exact arm_65_lpres |].
  apply Forall_cons; [exact arm_66_lpres |].
  apply Forall_cons; [exact arm_67_lpres |].
  apply Forall_cons; [exact arm_68_lpres |].
  apply Forall_cons; [exact arm_72_lpres |].
  apply Forall_cons; [exact arm_73_lpres |].
  apply Forall_cons; [exact arm_78_lpres |].
  apply Forall_cons; [exact arm_79_lpres |].
  apply Forall_cons; [exact arm_80_lpres |].
  apply Forall_cons; [exact arm_82_lpres |].
  apply Forall_cons; [exact arm_83_lpres |].
  apply Forall_cons; [exact arm_85_lpres |].
  apply Forall_cons; [exact arm_93_lpres |].
  apply Forall_cons; [exact arm_94_lpres |].
  apply Forall_cons; [exact arm_96_lpres |].
  apply Forall_cons; [exact arm_98_lpres |].
  apply Forall_cons; [exact arm_101_lpres |].
  apply Forall_cons; [exact arm_113_lpres |].
  apply Forall_cons; [exact arm_119_lpres |].
  apply Forall_cons; [exact arm_123_lpres |].
  apply Forall_cons; [exact arm_124_lpres |].
  apply Forall_cons; [exact arm_130_lpres |].
  apply Forall_cons; [exact arm_131_lpres |].
  apply Forall_cons; [exact arm_132_lpres |].
  apply Forall_cons; [exact arm_134_lpres |].
  apply Forall_cons; [exact arm_135_lpres |].
  apply Forall_cons; [exact arm_144_lpres |].
  apply Forall_cons; [exact arm_146_lpres |].
  apply Forall_cons; [exact arm_147_lpres |].
  apply Forall_cons; [exact arm_149_lpres |].
  apply Forall_cons; [exact arm_157_lpres |].
  apply Forall_cons; [exact arm_158_lpres |].
  apply Forall_cons; [exact arm_159_lpres |].
  apply Forall_cons; [exact arm_160_lpres |].
  apply Forall_cons; [exact arm_167_lpres |].
  apply Forall_cons; [exact arm_169_lpres |].
  apply Forall_cons; [exact arm_172_lpres |].
  apply Forall_cons; [exact arm_174_lpres |].
  apply Forall_cons; [exact arm_175_lpres |].
  apply Forall_cons; [exact arm_176_lpres |].
  apply Forall_cons; [exact arm_177_lpres |].
  apply Forall_cons; [exact arm_178_lpres |].
  apply Forall_cons; [exact arm_198_lpres |].
  apply Forall_cons; [exact arm_199_lpres |].
  apply Forall_cons; [exact arm_200_lpres |].
  apply Forall_cons; [exact arm_201_lpres |].
  apply Forall_cons; [exact arm_202_lpres |].
  apply Forall_cons; [exact arm_203_lpres |].
  apply Forall_cons; [exact arm_204_lpres |].
  apply Forall_cons; [exact arm_205_lpres |].
  apply Forall_cons; [exact arm_206_lpres |].
  apply Forall_cons; [exact arm_207_lpres |].
  apply Forall_cons; [exact arm_208_lpres |].
  apply Forall_cons; [exact arm_209_lpres |].
  apply Forall_cons; [exact arm_210_lpres |].
  apply Forall_cons; [exact arm_211_lpres |].
  apply Forall_cons; [exact arm_212_lpres |].
  apply Forall_cons; [exact arm_214_lpres |].
  apply Forall_cons; [exact arm_215_lpres |].
  apply Forall_cons; [exact arm_216_lpres |].
  apply Forall_cons; [exact arm_220_lpres |].
  apply Forall_cons; [exact arm_222_lpres |].
  apply Forall_cons; [exact arm_226_lpres |].
  apply Forall_cons; [exact arm_233_lpres |].
  apply Forall_cons; [exact arm_242_lpres |].
  apply Forall_cons; [exact arm_260_lpres |].
  apply Forall_cons; [exact arm_261_lpres |].
  apply Forall_cons; [exact arm_278_lpres |].
  apply Forall_cons; [exact arm_435_lpres |].
  apply Forall_cons; [exact arm_439_lpres |].
  apply Forall_nil.
Qed.

Lemma spec_table_inv : Forall arm_inv_ok spec_table.
Proof.
  unfold spec_table.
  apply Forall_cons; [exact arm_17_inv |].
  apply Forall_cons; [exact arm_19_inv |].
  apply Forall_cons; [exact arm_20_inv |].
  apply Forall_cons; [exact arm_21_inv |].
  apply Forall_cons; [exact arm_22_inv |].
  apply Forall_cons; [exact arm_23_inv |].
  apply Forall_cons; [exact arm_24_inv |].
  apply Forall_cons; [exact arm_25_inv |].
  apply Forall_cons; [exact arm_29_inv |].
  apply Forall_cons; [exact arm_32_inv |].
  apply Forall_cons; [exact arm_35_inv |].
  apply Forall_cons; [exact arm_46_inv |].
  apply Forall_cons; [exact arm_48_inv |].
  apply Forall_cons; [exact arm_56_inv |].
  apply Forall_cons; [exact arm_57_inv |].
  apply Forall_cons; [exact arm_59_inv |].
  apply Forall_cons; [exact arm_61_inv |].
  apply Forall_cons; [exact arm_62_inv |].
  apply Forall_cons; [exact arm_63_inv |].
  apply Forall_cons; [exact arm_64_inv |].
  apply Forall_cons; [exact arm_65_inv |].
  apply Forall_cons; [exact arm_66_inv |].
  apply Forall_cons; [exact arm_67_inv |].
  apply Forall_cons; [exact arm_68_inv |].
  apply Forall_cons; [exact arm_72_inv |].
  apply Forall_cons; [exact arm_73_inv |].
  apply Forall_cons; [exact arm_78_inv |].
  apply Forall_cons; [exact arm_79_inv |].
  apply Forall_cons; [exact arm_80_inv |].
  apply Forall_cons; [exact arm_82_inv |].
  apply Forall_cons; [exact arm_83_inv |].
  apply Forall_cons; [exact arm_85_inv |].
  apply Forall_cons; [exact arm_93_inv |].
  apply Forall_cons; [exact arm_94_inv |].
  apply Forall_cons; [exact arm_96_inv |].
  apply Forall_cons; [exact arm_98_inv |].
  apply Forall_cons; [exact arm_101_inv |].
  apply Forall_cons; [exact arm_113_inv |].
  apply Forall_cons; [exact arm_119_inv |].
  apply Forall_cons; [exact arm_123_inv |].
  apply Forall_cons; [exact arm_124_inv |].
  apply Forall_cons; [exact arm_130_inv |].
  apply Forall_cons; [exact arm_131_inv |].
  apply Forall_cons; [exact arm_132_inv |].
  apply Forall_cons; [exact arm_134_inv |].
  apply Forall_cons; [exact arm_135_inv |].
  apply Forall_cons; [exact arm_144_inv |].
  apply Forall_cons; [exact arm_146_inv |].
  apply Forall_cons; [exact arm_147_inv |].
  apply Forall_cons; [exact arm_149_inv |].
  apply Forall_cons; [exact arm_157_inv |].
  apply Forall_cons; [exact arm_158_inv |].
  apply Forall_cons; [exact arm_159_inv |].
  apply Forall_cons; [exact arm_160_inv |].
  apply Forall_cons; [exact arm_167_inv |].
  apply Forall_cons; [exact arm_169_inv |].
  apply Forall_cons; [exact arm_172_inv |].
  apply Forall_cons; [exact arm_174_inv |].
  apply Forall_cons; [exact arm_175_inv |].
  apply Forall_cons; [exact arm_176_inv |].
  apply Forall_cons; [exact arm_177_inv |].
  apply Forall_cons; [exact arm_178_inv |].
  apply Forall_cons; [exact arm_198_inv |].
  apply Forall_cons; [exact arm_199_inv |].
  apply Forall_cons; [exact arm_200_inv |].
  apply Forall_cons; [exact arm_201_inv |].
  apply Forall_cons; [exact arm_202_inv |].
  apply Forall_cons; [exact arm_203_inv |].
  apply Forall_cons; [exact arm_204_inv |].
  apply Forall_cons; [exact arm_205_inv |].
  apply Forall_cons; [exact arm_206_inv |].
  apply Forall_cons; [exact arm_207_inv |].
  apply Forall_cons; [exact arm_208_inv |].
  apply Forall_cons; [exact arm_209_inv |].
  apply Forall_cons; [exact arm_210_inv |].
  apply Forall_cons; [exact arm_211_inv |].
  apply Forall_cons; [exact arm_212_inv |].
  apply Forall_cons; [exact arm_214_inv |].
  apply Forall_cons; [exact arm_215_inv |].
  apply Forall_cons; [exact arm_216_inv |].
  apply Forall_cons; [exact arm_220_inv |].
  apply Forall_cons; [exact arm_222_inv |].
  apply Forall_cons; [exact arm_226_inv |].
  apply Forall_cons; [exact arm_233_inv |].
  apply Forall_cons; [exact arm_242_inv |].
  apply Forall_cons; [exact arm_260_inv |].
  apply Forall_cons; [exact arm_261_inv |].
  apply Forall_cons; [exact arm_278_inv |].
  apply Forall_cons; [exact arm_435_inv |].
  apply Forall_cons; [exact arm_439_inv |].
  apply Forall_nil.
Qed.

Theorem spec_frame_facts_hold : spec_frame_facts.
Proof.
  constructor.
  - (* [comment removed for export] *)
    intros L i m o HI H G0 G1. unfold syscall_spec, dispatch in *.
    destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a |] eqn:E.
    + destruct (lookup_arm_sound _ _ _ E) as [Hin Hno].
      exact (proj1 (Forall_forall _ _) spec_table_frame a Hin L i m o (eq_sym Hno) HI H G0 G1).
    + exact (lrel_unmodeled L i m o H).
  - (* [comment removed for export] *)
    intros i m x m' evs H. unfold syscall_spec, dispatch in H.
    destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a |] eqn:E.
    + destruct (lookup_arm_sound _ _ _ E) as [Hin _].
      exact (proj1 (Forall_forall _ _) spec_table_lpres a Hin i m x m' evs H).
    + discriminate H.
  - (* [comment removed for export] *)
    intros L L' i m Hle H. exact (gate_mono L L' i m Hle H).
  - (* [comment removed for export] *)
    intros i m x m' evs H HI. unfold syscall_spec, dispatch in H.
    destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a |] eqn:E.
    + destruct (lookup_arm_sound _ _ _ E) as [Hin _].
      exact (proj1 (Forall_forall _ _) spec_table_inv a Hin i m x m' evs H HI).
    + discriminate H.
Qed.
