(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Spec RefWorld RefTargetPre RefWorldK RefTargetPreK SymExec3 SymPlan SymPlanSoundA. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop.
Unset Nia Cache.  (* [comment removed for export] *) Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetAssembly. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetCover.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTPB_g01 RefTPB_g02 RefTPB_g03 RefTPB_g04.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithFP. Context {FP : PropExec.FPState}.
Section LIB.
Hypothesis LIB : lib_ok.

Definition classes_k1 : list (tpck 1) :=
  [TPCK 32763 36844 (tp_k1_32763_36844 LIB);
   TPCK 36845 37436 (tp_k1_36845_37436 LIB);
   TPCK 37437 40940 (tp_k1_37437_40940 LIB);
   TPCK 40941 43676 (tp_k1_40941_43676 LIB);
   TPCK 43677 45036 (tp_k1_43677_45036 LIB);
   TPCK 45037 49132 (tp_k1_45037_49132 LIB);
   TPCK 49133 52412 (tp_k1_49133_52412 LIB);
   TPCK 52413 53228 (tp_k1_52413_53228 LIB);
   TPCK 53229 57324 (tp_k1_53229_57324 LIB);
   TPCK 57325 61420 (tp_k1_57325_61420 LIB);
   TPCK 61421 65516 (tp_k1_61421_65516 LIB);
   TPCK 65517 69612 (tp_k1_65517_69612 LIB);
   TPCK 69613 73708 (tp_k1_69613_73708 LIB);
   TPCK 73709 74876 (tp_k1_73709_74876 LIB);
   TPCK 74877 77804 (tp_k1_74877_77804 LIB);
   TPCK 77805 81900 (tp_k1_77805_81900 LIB);
   TPCK 81901 85996 (tp_k1_81901_85996 LIB);
   TPCK 85997 87356 (tp_k1_85997_87356 LIB);
   TPCK 87357 90092 (tp_k1_87357_90092 LIB);
   TPCK 90093 94188 (tp_k1_90093_94188 LIB);
   TPCK 94189 98284 (tp_k1_94189_98284 LIB);
   TPCK 98285 102380 (tp_k1_98285_102380 LIB);
   TPCK 102381 104828 (tp_k1_102381_104828 LIB);
   TPCK 104829 106476 (tp_k1_104829_106476 LIB);
   TPCK 106477 110572 (tp_k1_106477_110572 LIB);
   TPCK 110573 114668 (tp_k1_110573_114668 LIB);
   TPCK 114669 118764 (tp_k1_114669_118764 LIB);
   TPCK 118765 122860 (tp_k1_118765_122860 LIB);
   TPCK 122861 126956 (tp_k1_122861_126956 LIB);
   TPCK 126957 131051 (tp_k1_126957_131051 LIB);
   TPCK 131052 131065 (tp_k1_131052_131065 LIB)].
Lemma classes_k1_cover : covers (ivsk classes_k1) 32763 131065 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k2 : list (tpck 2) :=
  [TPCK 98299 102380 (tp_k2_98299_102380 LIB);
   TPCK 102381 104828 (tp_k2_102381_104828 LIB);
   TPCK 104829 106476 (tp_k2_104829_106476 LIB);
   TPCK 106477 110572 (tp_k2_106477_110572 LIB);
   TPCK 110573 114668 (tp_k2_110573_114668 LIB);
   TPCK 114669 118764 (tp_k2_114669_118764 LIB);
   TPCK 118765 122860 (tp_k2_118765_122860 LIB);
   TPCK 122861 126956 (tp_k2_122861_126956 LIB);
   TPCK 126957 131051 (tp_k2_126957_131051 LIB);
   TPCK 131052 262137 (tp_k2_131052_262137 LIB)].
Lemma classes_k2_cover : covers (ivsk classes_k2) 98299 262137 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k3 : list (tpck 3) :=
  [TPCK 229371 524281 (tp_k3_229371_524281 LIB)].
Lemma classes_k3_cover : covers (ivsk classes_k3) 229371 524281 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k4 : list (tpck 4) :=
  [TPCK 491515 1048569 (tp_k4_491515_1048569 LIB)].
Lemma classes_k4_cover : covers (ivsk classes_k4) 491515 1048569 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k5 : list (tpck 5) :=
  [TPCK 1015803 2097145 (tp_k5_1015803_2097145 LIB)].
Lemma classes_k5_cover : covers (ivsk classes_k5) 1015803 2097145 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k6 : list (tpck 6) :=
  [TPCK 2064379 4194297 (tp_k6_2064379_4194297 LIB)].
Lemma classes_k6_cover : covers (ivsk classes_k6) 2064379 4194297 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k7 : list (tpck 7) :=
  [TPCK 4161531 8388601 (tp_k7_4161531_8388601 LIB)].
Lemma classes_k7_cover : covers (ivsk classes_k7) 4161531 8388601 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k8 : list (tpck 8) :=
  [TPCK 8355835 16777209 (tp_k8_8355835_16777209 LIB)].
Lemma classes_k8_cover : covers (ivsk classes_k8) 8355835 16777209 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k9 : list (tpck 9) :=
  [TPCK 16744443 33554425 (tp_k9_16744443_33554425 LIB)].
Lemma classes_k9_cover : covers (ivsk classes_k9) 16744443 33554425 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k10 : list (tpck 10) :=
  [TPCK 33521659 67108857 (tp_k10_33521659_67108857 LIB)].
Lemma classes_k10_cover : covers (ivsk classes_k10) 33521659 67108857 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem target_phase_k :
  forall k : Z, (1 <= k <= 10)%Z ->
  forall (sp0 B area brkv mas tid sec cnr : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec cnr content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12d58) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof.
  intros k Hk sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM.
  destruct (k_cases k Hk) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  - exact (tpk_dispatch 1 classes_k1 32763 131065 classes_k1_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 1 sp0 B area brkv mas tid sec cnr content R M 65536 131072 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 2 classes_k2 98299 262137 classes_k2_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 2 sp0 B area brkv mas tid sec cnr content R M 131072 262144 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 3 classes_k3 229371 524281 classes_k3_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 3 sp0 B area brkv mas tid sec cnr content R M 262144 524288 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 4 classes_k4 491515 1048569 classes_k4_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 4 sp0 B area brkv mas tid sec cnr content R M 524288 1048576 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 5 classes_k5 1015803 2097145 classes_k5_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 5 sp0 B area brkv mas tid sec cnr content R M 1048576 2097152 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 6 classes_k6 2064379 4194297 classes_k6_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 6 sp0 B area brkv mas tid sec cnr content R M 2097152 4194304 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 7 classes_k7 4161531 8388601 classes_k7_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 7 sp0 B area brkv mas tid sec cnr content R M 4194304 8388608 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 8 classes_k8 8355835 16777209 classes_k8_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 8 sp0 B area brkv mas tid sec cnr content R M 8388608 16777216 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 9 classes_k9 16744443 33554425 classes_k9_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 9 sp0 B area brkv mas tid sec cnr content R M 16777216 33554432 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 10 classes_k10 33521659 67108857 classes_k10_cover sp0 B area brkv mas tid sec cnr content R M VM model TP TV SM
           (paylen_rangek 10 sp0 B area brkv mas tid sec cnr content R M 33554432 67108864 TP eq_refl eq_refl)).
Qed.

End LIB.
End WithFP.
