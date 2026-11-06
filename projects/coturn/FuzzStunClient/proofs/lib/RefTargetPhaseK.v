(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import
  Spec TargetSpec TargetKDefs RefWorld RefTargetPre RefWorldK RefTargetPreK
  SymExec3 SymPlan SymPlanSoundA RefATB RefTargetEntry_defs RefTargetEntryK_defs
  TargetShape TargetShapeTop RefTargetAssembly RefTargetCover.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefTPB_g01 RefTPB_g02 RefTPB_g03 RefTPB_g04 RefTPB_g05 RefTPB_g06 RefTPB_g07 RefTPB_g08 RefTPB_g09 RefTPB_g10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Definition classes_k1 : list (tpck 1) :=
  [TPCK 32763 36844 tp_k1_32763_36844;
   TPCK 36845 37436 tp_k1_36845_37436;
   TPCK 37437 40940 tp_k1_37437_40940;
   TPCK 40941 43676 tp_k1_40941_43676;
   TPCK 43677 45036 tp_k1_43677_45036;
   TPCK 45037 49132 tp_k1_45037_49132;
   TPCK 49133 52412 tp_k1_49133_52412;
   TPCK 52413 53228 tp_k1_52413_53228;
   TPCK 53229 57324 tp_k1_53229_57324;
   TPCK 57325 61420 tp_k1_57325_61420;
   TPCK 61421 65516 tp_k1_61421_65516;
   TPCK 65517 69612 tp_k1_65517_69612;
   TPCK 69613 73708 tp_k1_69613_73708;
   TPCK 73709 74876 tp_k1_73709_74876;
   TPCK 74877 77804 tp_k1_74877_77804;
   TPCK 77805 81900 tp_k1_77805_81900;
   TPCK 81901 85996 tp_k1_81901_85996;
   TPCK 85997 87356 tp_k1_85997_87356;
   TPCK 87357 90092 tp_k1_87357_90092;
   TPCK 90093 94188 tp_k1_90093_94188;
   TPCK 94189 98284 tp_k1_94189_98284;
   TPCK 98285 102380 tp_k1_98285_102380;
   TPCK 102381 104828 tp_k1_102381_104828;
   TPCK 104829 106476 tp_k1_104829_106476;
   TPCK 106477 110572 tp_k1_106477_110572;
   TPCK 110573 114668 tp_k1_110573_114668;
   TPCK 114669 118764 tp_k1_114669_118764;
   TPCK 118765 122860 tp_k1_118765_122860;
   TPCK 122861 126956 tp_k1_122861_126956;
   TPCK 126957 131051 tp_k1_126957_131051;
   TPCK 131052 131065 tp_k1_131052_131065].
Lemma classes_k1_cover : covers (ivsk classes_k1) 32763 131065 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k2 : list (tpck 2) :=
  [TPCK 98299 102380 tp_k2_98299_102380;
   TPCK 102381 104828 tp_k2_102381_104828;
   TPCK 104829 106476 tp_k2_104829_106476;
   TPCK 106477 110572 tp_k2_106477_110572;
   TPCK 110573 114668 tp_k2_110573_114668;
   TPCK 114669 118764 tp_k2_114669_118764;
   TPCK 118765 122860 tp_k2_118765_122860;
   TPCK 122861 126956 tp_k2_122861_126956;
   TPCK 126957 131051 tp_k2_126957_131051;
   TPCK 131052 262137 tp_k2_131052_262137].
Lemma classes_k2_cover : covers (ivsk classes_k2) 98299 262137 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k3 : list (tpck 3) :=
  [TPCK 229371 524281 tp_k3_229371_524281].
Lemma classes_k3_cover : covers (ivsk classes_k3) 229371 524281 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k4 : list (tpck 4) :=
  [TPCK 491515 1048569 tp_k4_491515_1048569].
Lemma classes_k4_cover : covers (ivsk classes_k4) 491515 1048569 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k5 : list (tpck 5) :=
  [TPCK 1015803 2097145 tp_k5_1015803_2097145].
Lemma classes_k5_cover : covers (ivsk classes_k5) 1015803 2097145 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k6 : list (tpck 6) :=
  [TPCK 2064379 4194297 tp_k6_2064379_4194297].
Lemma classes_k6_cover : covers (ivsk classes_k6) 2064379 4194297 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k7 : list (tpck 7) :=
  [TPCK 4161531 8388601 tp_k7_4161531_8388601].
Lemma classes_k7_cover : covers (ivsk classes_k7) 4161531 8388601 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k8 : list (tpck 8) :=
  [TPCK 8355835 12566521 tp_k8_8355835_12566521;
   TPCK 12566522 16777209 tp_k8_12566522_16777209].
Lemma classes_k8_cover : covers (ivsk classes_k8) 8355835 16777209 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k9 : list (tpck 9) :=
  [TPCK 16744443 22347769 tp_k9_16744443_22347769;
   TPCK 22347770 27951096 tp_k9_22347770_27951096;
   TPCK 27951097 33554425 tp_k9_27951097_33554425].
Lemma classes_k9_cover : covers (ivsk classes_k9) 16744443 33554425 = true.
Proof. vm_compute. reflexivity. Qed.

Definition classes_k10 : list (tpck 10) :=
  [TPCK 33521659 40239097 tp_k10_33521659_40239097;
   TPCK 40239098 46956536 tp_k10_40239098_46956536;
   TPCK 46956537 53673975 tp_k10_46956537_53673975;
   TPCK 53673976 60391414 tp_k10_53673976_60391414;
   TPCK 60391415 67108857 tp_k10_60391415_67108857].
Lemma classes_k10_cover : covers (ivsk classes_k10) 33521659 67108857 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem target_phase_k :
  ref_tphase_hyps ->
  forall k : Z, (1 <= k <= 10)%Z ->
  forall (sp0 B area brkv mas tid : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).
Proof.
  intros RH k Hk sp0 B area brkv mas tid content R M VM model TP TV SM.
  destruct (k_cases k Hk) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  - exact (tpk_dispatch 1 classes_k1 32763 131065 classes_k1_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 1 sp0 B area brkv mas tid content R M 65536 131072 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 2 classes_k2 98299 262137 classes_k2_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 2 sp0 B area brkv mas tid content R M 131072 262144 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 3 classes_k3 229371 524281 classes_k3_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 3 sp0 B area brkv mas tid content R M 262144 524288 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 4 classes_k4 491515 1048569 classes_k4_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 4 sp0 B area brkv mas tid content R M 524288 1048576 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 5 classes_k5 1015803 2097145 classes_k5_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 5 sp0 B area brkv mas tid content R M 1048576 2097152 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 6 classes_k6 2064379 4194297 classes_k6_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 6 sp0 B area brkv mas tid content R M 2097152 4194304 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 7 classes_k7 4161531 8388601 classes_k7_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 7 sp0 B area brkv mas tid content R M 4194304 8388608 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 8 classes_k8 8355835 16777209 classes_k8_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 8 sp0 B area brkv mas tid content R M 8388608 16777216 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 9 classes_k9 16744443 33554425 classes_k9_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 9 sp0 B area brkv mas tid content R M 16777216 33554432 TP eq_refl eq_refl)).
  - exact (tpk_dispatch 10 classes_k10 33521659 67108857 classes_k10_cover RH sp0 B area brkv mas tid content R M VM model TP TV SM
           (paylen_rangek 10 sp0 B area brkv mas tid content R M 33554432 67108864 TP eq_refl eq_refl)).
Qed.
