(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymPlan UbSymPlanSoundA. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop.
Unset Nia Cache.  (* [comment removed for export] *) Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetAssembly. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTargetCover.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTPB_g01 UbTPB_g02 UbTPB_g03 UbTPB_g04.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithFP. Context {FP : PropExec.FPState}.
Section LIB.
Hypothesis LIB : lib_ok.

Definition classes_k0 : list tpc :=
  [TPC 0 0 (tp_k0_0_0 LIB);
   TPC 1 12 (tp_k0_1_12 LIB);
   TPC 13 28 (tp_k0_13_28 LIB);
   TPC 29 44 (tp_k0_29_44 LIB);
   TPC 45 60 (tp_k0_45_60 LIB);
   TPC 61 76 (tp_k0_61_76 LIB);
   TPC 77 92 (tp_k0_77_92 LIB);
   TPC 93 108 (tp_k0_93_108 LIB);
   TPC 109 124 (tp_k0_109_124 LIB);
   TPC 125 140 (tp_k0_125_140 LIB);
   TPC 141 156 (tp_k0_141_156 LIB);
   TPC 157 188 (tp_k0_157_188 LIB);
   TPC 189 236 (tp_k0_189_236 LIB);
   TPC 237 284 (tp_k0_237_284 LIB);
   TPC 285 316 (tp_k0_285_316 LIB);
   TPC 317 396 (tp_k0_317_396 LIB);
   TPC 397 492 (tp_k0_397_492 LIB);
   TPC 493 572 (tp_k0_493_572 LIB);
   TPC 573 668 (tp_k0_573_668 LIB);
   TPC 669 796 (tp_k0_669_796 LIB);
   TPC 797 1004 (tp_k0_797_1004 LIB);
   TPC 1005 1148 (tp_k0_1005_1148 LIB);
   TPC 1149 1340 (tp_k0_1149_1340 LIB);
   TPC 1341 1628 (tp_k0_1341_1628 LIB);
   TPC 1629 2028 (tp_k0_1629_2028 LIB);
   TPC 2029 2332 (tp_k0_2029_2332 LIB);
   TPC 2333 2716 (tp_k0_2333_2716 LIB);
   TPC 2717 3260 (tp_k0_2717_3260 LIB);
   TPC 3261 4076 (tp_k0_3261_4076 LIB);
   TPC 4077 4668 (tp_k0_4077_4668 LIB);
   TPC 4669 5436 (tp_k0_4669_5436 LIB);
   TPC 5437 6540 (tp_k0_5437_6540 LIB);
   TPC 6541 8172 (tp_k0_6541_8172 LIB);
   TPC 8173 9340 (tp_k0_8173_9340 LIB);
   TPC 9341 10908 (tp_k0_9341_10908 LIB);
   TPC 10909 12268 (tp_k0_10909_12268 LIB);
   TPC 12269 13084 (tp_k0_12269_13084 LIB);
   TPC 13085 16364 (tp_k0_13085_16364 LIB);
   TPC 16365 18700 (tp_k0_16365_18700 LIB);
   TPC 18701 20460 (tp_k0_18701_20460 LIB);
   TPC 20461 21820 (tp_k0_20461_21820 LIB);
   TPC 21821 24556 (tp_k0_21821_24556 LIB);
   TPC 24557 26188 (tp_k0_24557_26188 LIB);
   TPC 26189 28652 (tp_k0_26189_28652 LIB);
   TPC 28653 32748 (tp_k0_28653_32748 LIB);
   TPC 32749 36844 (tp_k0_32749_36844 LIB);
   TPC 36845 37436 (tp_k0_36845_37436 LIB);
   TPC 37437 40940 (tp_k0_37437_40940 LIB);
   TPC 40941 43676 (tp_k0_40941_43676 LIB);
   TPC 43677 45036 (tp_k0_43677_45036 LIB);
   TPC 45037 49132 (tp_k0_45037_49132 LIB);
   TPC 49133 52412 (tp_k0_49133_52412 LIB);
   TPC 52413 53228 (tp_k0_52413_53228 LIB);
   TPC 53229 57324 (tp_k0_53229_57324 LIB);
   TPC 57325 61420 (tp_k0_57325_61420 LIB);
   TPC 61421 65516 (tp_k0_61421_65516 LIB);
   TPC 65517 65529 (tp_k0_65517_65529 LIB)].

Lemma classes_k0_cover : covers (ivs0 classes_k0) 0 65529 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem target_phase :
  forall (sp0 gm area brkv mas tid sec cnr : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec cnr content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12db8) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof.
  intros sp0 gm area brkv mas tid sec cnr content R M VM model TP TV SM.
  exact (tp0_dispatch classes_k0 0 65529 classes_k0_cover sp0 gm area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_range0 sp0 gm area brkv mas tid sec cnr content R M TP)).
Qed.

End LIB.
End WithFP.
