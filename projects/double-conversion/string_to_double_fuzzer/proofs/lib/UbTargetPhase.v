(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymPlan UbSymPlanSoundA UbTargetCover LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbTPB_g01 UbTPB_g02 UbTPB_g03 UbTPB_g04 UbTPB_g05 UbTPB_g06 UbTPB_g08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Definition classes_k0 : list tpc :=
  [TPC 0 0 tp_k0_0_0;
   TPC 1 12 tp_k0_1_12;
   TPC 13 28 tp_k0_13_28;
   TPC 29 44 tp_k0_29_44;
   TPC 45 60 tp_k0_45_60;
   TPC 61 76 tp_k0_61_76;
   TPC 77 92 tp_k0_77_92;
   TPC 93 108 tp_k0_93_108;
   TPC 109 124 tp_k0_109_124;
   TPC 125 140 tp_k0_125_140;
   TPC 141 156 tp_k0_141_156;
   TPC 157 188 tp_k0_157_188;
   TPC 189 236 tp_k0_189_236;
   TPC 237 284 tp_k0_237_284;
   TPC 285 316 tp_k0_285_316;
   TPC 317 396 tp_k0_317_396;
   TPC 397 492 tp_k0_397_492;
   TPC 493 572 tp_k0_493_572;
   TPC 573 668 tp_k0_573_668;
   TPC 669 796 tp_k0_669_796;
   TPC 797 1004 tp_k0_797_1004;
   TPC 1005 1148 tp_k0_1005_1148;
   TPC 1149 1340 tp_k0_1149_1340;
   TPC 1341 1628 tp_k0_1341_1628;
   TPC 1629 2028 tp_k0_1629_2028;
   TPC 2029 2332 tp_k0_2029_2332;
   TPC 2333 2716 tp_k0_2333_2716;
   TPC 2717 3260 tp_k0_2717_3260;
   TPC 3261 4076 tp_k0_3261_4076;
   TPC 4077 4668 tp_k0_4077_4668;
   TPC 4669 5436 tp_k0_4669_5436;
   TPC 5437 6540 tp_k0_5437_6540;
   TPC 6541 8172 tp_k0_6541_8172;
   TPC 8173 9340 tp_k0_8173_9340;
   TPC 9341 10908 tp_k0_9341_10908;
   TPC 10909 12268 tp_k0_10909_12268;
   TPC 12269 13084 tp_k0_12269_13084;
   TPC 13085 16364 tp_k0_13085_16364;
   TPC 16365 18700 tp_k0_16365_18700;
   TPC 18701 20460 tp_k0_18701_20460;
   TPC 20461 21820 tp_k0_20461_21820;
   TPC 21821 24556 tp_k0_21821_24556;
   TPC 24557 26188 tp_k0_24557_26188;
   TPC 26189 28652 tp_k0_26189_28652;
   TPC 28653 32748 tp_k0_28653_32748;
   TPC 32749 36844 tp_k0_32749_36844;
   TPC 36845 37436 tp_k0_36845_37436;
   TPC 37437 40940 tp_k0_37437_40940;
   TPC 40941 43676 tp_k0_40941_43676;
   TPC 43677 45036 tp_k0_43677_45036;
   TPC 45037 49132 tp_k0_45037_49132;
   TPC 49133 52412 tp_k0_49133_52412;
   TPC 52413 53228 tp_k0_52413_53228;
   TPC 53229 57324 tp_k0_53229_57324;
   TPC 57325 61420 tp_k0_57325_61420;
   TPC 61421 65516 tp_k0_61421_65516;
   TPC 65517 65529 tp_k0_65517_65529].

Lemma classes_k0_cover : covers (ivs0 classes_k0) 0 65529 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem target_phase : LibIface.lib_stmt_U ->
  forall (sp0 gm area brkv mas tid sec : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32904) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof.
  intros HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV SM.
  exact (tp0_dispatch classes_k0 0 65529 classes_k0_cover HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV SM
           (paylen_range0 sp0 gm area brkv mas tid sec content R M TP)).
Qed.
