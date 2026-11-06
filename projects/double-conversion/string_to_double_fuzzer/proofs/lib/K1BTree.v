(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth BK0TailAll K1BTpl K1BDx_10 K1BD0 K1BDx_2 K1BDx_3 K1BDx_4 K1BDx_5 K1BDx_6 K1BDx_7 K1BDx_8 K1BDx_9 K1BDx_1 K1BCertS0 K1BCertCx_0 K1BCertCx_1 K1BCertCx_2 K1BCertCx_3 K1BCertCx_4 K1BCertCx_5 K1BCertPx_0 K1BCertPx_1 K1BCertPx_2 K1BCertPx_3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Local Notation TT := TT_r5.
  Definition TSx_11 : mtree := MLeaf 2 xx.
  Lemma TSx_11_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 HS_hg11x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) TSx_11 = true.
  Proof. exact (payb_leaf KCm BFUELm FUELm BITm TT 2 2 HS_hg11x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) 2 _ eq_refl (k1xx_ok TT)). Qed.


  Definition PWx10_1_PEa : mtree := MEmpty 2.
  Lemma PWx10_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht10x) (((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, QMIN, 33521658)]) PWx10_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht10x) (((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, QMIN, 33521658)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx10_2_Phi10 : mtree := MClass C_hi10x T_hi10x.
  Lemma PWx10_2_Phi10_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht10x) ((((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) PWx10_2_Phi10 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht10x) ((((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) (C_hi10x) T_hi10x); [vm_compute; reflexivity | exact (T_hi10x_ok TT)]. Qed.
  Definition PWx10_3_PEb : mtree := MEmpty 2.
  Lemma PWx10_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht10x) ((((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) PWx10_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht10x) ((((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx10_4_PGb : mtree := MSplit QRoom 67108857 PWx10_2_Phi10 PWx10_3_PEb.
  Lemma PWx10_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht10x) (((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) PWx10_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht10x) (((root_class 5 ++ [(QFlen, 33554432, 67108863)])) ++ [(QRoom, 33521658 + 1, QMAX)]) QRoom (67108857) PWx10_2_Phi10 PWx10_3_PEb PWx10_2_Phi10_ok PWx10_3_PEb_ok). Qed.
  Definition PWx10_5_PGa : mtree := MSplit QRoom 33521658 PWx10_1_PEa PWx10_4_PGb.
  Lemma PWx10_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht10x) ((root_class 5 ++ [(QFlen, 33554432, 67108863)])) PWx10_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht10x) ((root_class 5 ++ [(QFlen, 33554432, 67108863)])) QRoom (33521658) PWx10_1_PEa PWx10_4_PGb PWx10_1_PEa_ok PWx10_4_PGb_ok). Qed.
  Definition TFx_10 : mtree := MPre 2 k1f10x [(199%nat, (2%nat, HS_ht10x))] [(199%nat, PWx10_5_PGa)].
  Lemma TFx_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr10x (root_class 5 ++ [(QFlen, 33554432, 67108863)]) TFx_10 = true.
  Proof. unfold TFx_10. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr10x (root_class 5 ++ [(QFlen, 33554432, 67108863)]) 2 k1f10x [(199%nat, (2%nat, HS_ht10x))] [(199%nat, PWx10_5_PGa)] eq_refl (k1f10x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(199%nat, (2%nat, HS_ht10x))] (root_class 5 ++ [(QFlen, 33554432, 67108863)]) 199%nat PWx10_5_PGa [] 2 HS_ht10x eq_refl eq_refl PWx10_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_10 : mtree := MPre 2 k1r10x [(135%nat, (2%nat, HS_hg11x))] [(135%nat, TSx_11)].
  Lemma TRx_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr10x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) TRx_10 = true.
  Proof. unfold TRx_10. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr10x (root_class 5 ++ [(QFlen, 67108864, QMAX)]) 2 k1r10x [(135%nat, (2%nat, HS_hg11x))] [(135%nat, TSx_11)] eq_refl (k1r10x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(135%nat, (2%nat, HS_hg11x))] (root_class 5 ++ [(QFlen, 67108864, QMAX)]) 135%nat TSx_11 [] 2 HS_hg11x eq_refl eq_refl TSx_11_ok). apply mforest_ok_nil. Qed.
  Definition TNx_10 : mtree := MSplit QFlen 67108863 (MClass (root_class 5 ++ [(QFlen, 33554432, 67108863)]) TFx_10) (MClass (root_class 5 ++ [(QFlen, 67108864, QMAX)]) TRx_10).
  Lemma TNx_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr10x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TNx_10 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_10_ok | exact TRx_10_ok]. Qed.
  Definition TSxa_10 : mtree := MPre 1 k1s10xa [(168%nat, (2%nat, HS_hr10x))] [(168%nat, TNx_10)].
  Lemma TSxa_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TSxa_10 = true.
  Proof. unfold TSxa_10. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 1 k1s10xa [(168%nat, (2%nat, HS_hr10x))] [(168%nat, TNx_10)] eq_refl (k1s10xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(168%nat, (2%nat, HS_hr10x))] (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 168%nat TNx_10 [] 2 HS_hr10x eq_refl eq_refl TNx_10_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_10 : mtree := MPre 1 k1s10xb [(168%nat, (2%nat, HS_hr10x))] [(168%nat, TNx_10)].
  Lemma TSxb_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TSxb_10 = true.
  Proof. unfold TSxb_10. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg10x e_r 4046) (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 1 k1s10xb [(168%nat, (2%nat, HS_hr10x))] [(168%nat, TNx_10)] eq_refl (k1s10xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(168%nat, (2%nat, HS_hr10x))] (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 168%nat TNx_10 [] 2 HS_hr10x eq_refl eq_refl TNx_10_ok). apply mforest_ok_nil. Qed.
  Definition TSx_10 : mtree := MCase e_r 4046 TSxa_10 TSxb_10.
  Lemma TSx_10_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg10x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TSx_10 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg10x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) e_r 4046 TSxa_10 TSxb_10 eq_refl TSxa_10_ok TSxb_10_ok). Qed.


  Definition PWx9_1_PEa : mtree := MEmpty 2.
  Lemma PWx9_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht9x) (((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, QMIN, 16744442)]) PWx9_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht9x) (((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, QMIN, 16744442)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx9_2_Phi9 : mtree := MClass C_hi9x T_hi9x.
  Lemma PWx9_2_Phi9_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht9x) ((((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) PWx9_2_Phi9 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht9x) ((((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) (C_hi9x) T_hi9x); [vm_compute; reflexivity | exact (T_hi9x_ok TT)]. Qed.
  Definition PWx9_3_PEb : mtree := MEmpty 2.
  Lemma PWx9_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht9x) ((((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) PWx9_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht9x) ((((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx9_4_PGb : mtree := MSplit QRoom 33554425 PWx9_2_Phi9 PWx9_3_PEb.
  Lemma PWx9_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht9x) (((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) PWx9_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht9x) (((root_class 5 ++ [(QFlen, 16777216, 33554431)])) ++ [(QRoom, 16744442 + 1, QMAX)]) QRoom (33554425) PWx9_2_Phi9 PWx9_3_PEb PWx9_2_Phi9_ok PWx9_3_PEb_ok). Qed.
  Definition PWx9_5_PGa : mtree := MSplit QRoom 16744442 PWx9_1_PEa PWx9_4_PGb.
  Lemma PWx9_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht9x) ((root_class 5 ++ [(QFlen, 16777216, 33554431)])) PWx9_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht9x) ((root_class 5 ++ [(QFlen, 16777216, 33554431)])) QRoom (16744442) PWx9_1_PEa PWx9_4_PGb PWx9_1_PEa_ok PWx9_4_PGb_ok). Qed.
  Definition TFx_9 : mtree := MPre 2 k1f9x [(196%nat, (2%nat, HS_ht9x))] [(196%nat, PWx9_5_PGa)].
  Lemma TFx_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr9x (root_class 5 ++ [(QFlen, 16777216, 33554431)]) TFx_9 = true.
  Proof. unfold TFx_9. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr9x (root_class 5 ++ [(QFlen, 16777216, 33554431)]) 2 k1f9x [(196%nat, (2%nat, HS_ht9x))] [(196%nat, PWx9_5_PGa)] eq_refl (k1f9x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(196%nat, (2%nat, HS_ht9x))] (root_class 5 ++ [(QFlen, 16777216, 33554431)]) 196%nat PWx9_5_PGa [] 2 HS_ht9x eq_refl eq_refl PWx9_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_9 : mtree := MPre 1 k1r9x [(132%nat, (1%nat, HS_hg10x))] [(132%nat, TSx_10)].
  Lemma TRx_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr9x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TRx_9 = true.
  Proof. unfold TRx_9. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr9x (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 1 k1r9x [(132%nat, (1%nat, HS_hg10x))] [(132%nat, TSx_10)] eq_refl (k1r9x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(132%nat, (1%nat, HS_hg10x))] (root_class 5 ++ [(QFlen, 33554432, QMAX)]) 132%nat TSx_10 [] 1 HS_hg10x eq_refl eq_refl TSx_10_ok). apply mforest_ok_nil. Qed.
  Definition TNx_9 : mtree := MSplit QFlen 33554431 (MClass (root_class 5 ++ [(QFlen, 16777216, 33554431)]) TFx_9) (MClass (root_class 5 ++ [(QFlen, 33554432, QMAX)]) TRx_9).
  Lemma TNx_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr9x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TNx_9 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_9_ok | exact TRx_9_ok]. Qed.
  Definition TSxa_9 : mtree := MPre 1 k1s9xa [(165%nat, (2%nat, HS_hr9x))] [(165%nat, TNx_9)].
  Lemma TSxa_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TSxa_9 = true.
  Proof. unfold TSxa_9. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 1 k1s9xa [(165%nat, (2%nat, HS_hr9x))] [(165%nat, TNx_9)] eq_refl (k1s9xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(165%nat, (2%nat, HS_hr9x))] (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 165%nat TNx_9 [] 2 HS_hr9x eq_refl eq_refl TNx_9_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_9 : mtree := MPre 1 k1s9xb [(165%nat, (2%nat, HS_hr9x))] [(165%nat, TNx_9)].
  Lemma TSxb_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TSxb_9 = true.
  Proof. unfold TSxb_9. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg9x e_r 4046) (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 1 k1s9xb [(165%nat, (2%nat, HS_hr9x))] [(165%nat, TNx_9)] eq_refl (k1s9xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(165%nat, (2%nat, HS_hr9x))] (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 165%nat TNx_9 [] 2 HS_hr9x eq_refl eq_refl TNx_9_ok). apply mforest_ok_nil. Qed.
  Definition TSx_9 : mtree := MCase e_r 4046 TSxa_9 TSxb_9.
  Lemma TSx_9_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg9x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TSx_9 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg9x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) e_r 4046 TSxa_9 TSxb_9 eq_refl TSxa_9_ok TSxb_9_ok). Qed.


  Definition PWx8_1_PEa : mtree := MEmpty 2.
  Lemma PWx8_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht8x) (((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, QMIN, 8355834)]) PWx8_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht8x) (((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, QMIN, 8355834)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx8_2_Phi8 : mtree := MClass C_hi8x T_hi8x.
  Lemma PWx8_2_Phi8_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht8x) ((((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) PWx8_2_Phi8 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht8x) ((((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) (C_hi8x) T_hi8x); [vm_compute; reflexivity | exact (T_hi8x_ok TT)]. Qed.
  Definition PWx8_3_PEb : mtree := MEmpty 2.
  Lemma PWx8_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht8x) ((((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) PWx8_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht8x) ((((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx8_4_PGb : mtree := MSplit QRoom 16777209 PWx8_2_Phi8 PWx8_3_PEb.
  Lemma PWx8_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht8x) (((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) PWx8_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht8x) (((root_class 5 ++ [(QFlen, 8388608, 16777215)])) ++ [(QRoom, 8355834 + 1, QMAX)]) QRoom (16777209) PWx8_2_Phi8 PWx8_3_PEb PWx8_2_Phi8_ok PWx8_3_PEb_ok). Qed.
  Definition PWx8_5_PGa : mtree := MSplit QRoom 8355834 PWx8_1_PEa PWx8_4_PGb.
  Lemma PWx8_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht8x) ((root_class 5 ++ [(QFlen, 8388608, 16777215)])) PWx8_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht8x) ((root_class 5 ++ [(QFlen, 8388608, 16777215)])) QRoom (8355834) PWx8_1_PEa PWx8_4_PGb PWx8_1_PEa_ok PWx8_4_PGb_ok). Qed.
  Definition TFx_8 : mtree := MPre 2 k1f8x [(193%nat, (2%nat, HS_ht8x))] [(193%nat, PWx8_5_PGa)].
  Lemma TFx_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr8x (root_class 5 ++ [(QFlen, 8388608, 16777215)]) TFx_8 = true.
  Proof. unfold TFx_8. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr8x (root_class 5 ++ [(QFlen, 8388608, 16777215)]) 2 k1f8x [(193%nat, (2%nat, HS_ht8x))] [(193%nat, PWx8_5_PGa)] eq_refl (k1f8x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(193%nat, (2%nat, HS_ht8x))] (root_class 5 ++ [(QFlen, 8388608, 16777215)]) 193%nat PWx8_5_PGa [] 2 HS_ht8x eq_refl eq_refl PWx8_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_8 : mtree := MPre 1 k1r8x [(129%nat, (1%nat, HS_hg9x))] [(129%nat, TSx_9)].
  Lemma TRx_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr8x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TRx_8 = true.
  Proof. unfold TRx_8. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr8x (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 1 k1r8x [(129%nat, (1%nat, HS_hg9x))] [(129%nat, TSx_9)] eq_refl (k1r8x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(129%nat, (1%nat, HS_hg9x))] (root_class 5 ++ [(QFlen, 16777216, QMAX)]) 129%nat TSx_9 [] 1 HS_hg9x eq_refl eq_refl TSx_9_ok). apply mforest_ok_nil. Qed.
  Definition TNx_8 : mtree := MSplit QFlen 16777215 (MClass (root_class 5 ++ [(QFlen, 8388608, 16777215)]) TFx_8) (MClass (root_class 5 ++ [(QFlen, 16777216, QMAX)]) TRx_8).
  Lemma TNx_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr8x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TNx_8 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_8_ok | exact TRx_8_ok]. Qed.
  Definition TSxa_8 : mtree := MPre 1 k1s8xa [(162%nat, (2%nat, HS_hr8x))] [(162%nat, TNx_8)].
  Lemma TSxa_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TSxa_8 = true.
  Proof. unfold TSxa_8. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 1 k1s8xa [(162%nat, (2%nat, HS_hr8x))] [(162%nat, TNx_8)] eq_refl (k1s8xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(162%nat, (2%nat, HS_hr8x))] (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 162%nat TNx_8 [] 2 HS_hr8x eq_refl eq_refl TNx_8_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_8 : mtree := MPre 1 k1s8xb [(162%nat, (2%nat, HS_hr8x))] [(162%nat, TNx_8)].
  Lemma TSxb_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TSxb_8 = true.
  Proof. unfold TSxb_8. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg8x e_r 4046) (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 1 k1s8xb [(162%nat, (2%nat, HS_hr8x))] [(162%nat, TNx_8)] eq_refl (k1s8xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(162%nat, (2%nat, HS_hr8x))] (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 162%nat TNx_8 [] 2 HS_hr8x eq_refl eq_refl TNx_8_ok). apply mforest_ok_nil. Qed.
  Definition TSx_8 : mtree := MCase e_r 4046 TSxa_8 TSxb_8.
  Lemma TSx_8_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg8x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TSx_8 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg8x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) e_r 4046 TSxa_8 TSxb_8 eq_refl TSxa_8_ok TSxb_8_ok). Qed.


  Definition PWx7_1_PEa : mtree := MEmpty 2.
  Lemma PWx7_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht7x) (((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, QMIN, 4161530)]) PWx7_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht7x) (((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, QMIN, 4161530)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx7_2_Phi7 : mtree := MClass C_hi7x T_hi7x.
  Lemma PWx7_2_Phi7_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht7x) ((((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) PWx7_2_Phi7 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht7x) ((((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) (C_hi7x) T_hi7x); [vm_compute; reflexivity | exact (T_hi7x_ok TT)]. Qed.
  Definition PWx7_3_PEb : mtree := MEmpty 2.
  Lemma PWx7_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht7x) ((((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) PWx7_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht7x) ((((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx7_4_PGb : mtree := MSplit QRoom 8388601 PWx7_2_Phi7 PWx7_3_PEb.
  Lemma PWx7_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht7x) (((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) PWx7_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht7x) (((root_class 5 ++ [(QFlen, 4194304, 8388607)])) ++ [(QRoom, 4161530 + 1, QMAX)]) QRoom (8388601) PWx7_2_Phi7 PWx7_3_PEb PWx7_2_Phi7_ok PWx7_3_PEb_ok). Qed.
  Definition PWx7_5_PGa : mtree := MSplit QRoom 4161530 PWx7_1_PEa PWx7_4_PGb.
  Lemma PWx7_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht7x) ((root_class 5 ++ [(QFlen, 4194304, 8388607)])) PWx7_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht7x) ((root_class 5 ++ [(QFlen, 4194304, 8388607)])) QRoom (4161530) PWx7_1_PEa PWx7_4_PGb PWx7_1_PEa_ok PWx7_4_PGb_ok). Qed.
  Definition TFx_7 : mtree := MPre 2 k1f7x [(190%nat, (2%nat, HS_ht7x))] [(190%nat, PWx7_5_PGa)].
  Lemma TFx_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr7x (root_class 5 ++ [(QFlen, 4194304, 8388607)]) TFx_7 = true.
  Proof. unfold TFx_7. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr7x (root_class 5 ++ [(QFlen, 4194304, 8388607)]) 2 k1f7x [(190%nat, (2%nat, HS_ht7x))] [(190%nat, PWx7_5_PGa)] eq_refl (k1f7x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(190%nat, (2%nat, HS_ht7x))] (root_class 5 ++ [(QFlen, 4194304, 8388607)]) 190%nat PWx7_5_PGa [] 2 HS_ht7x eq_refl eq_refl PWx7_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_7 : mtree := MPre 1 k1r7x [(126%nat, (1%nat, HS_hg8x))] [(126%nat, TSx_8)].
  Lemma TRx_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr7x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TRx_7 = true.
  Proof. unfold TRx_7. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr7x (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 1 k1r7x [(126%nat, (1%nat, HS_hg8x))] [(126%nat, TSx_8)] eq_refl (k1r7x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(126%nat, (1%nat, HS_hg8x))] (root_class 5 ++ [(QFlen, 8388608, QMAX)]) 126%nat TSx_8 [] 1 HS_hg8x eq_refl eq_refl TSx_8_ok). apply mforest_ok_nil. Qed.
  Definition TNx_7 : mtree := MSplit QFlen 8388607 (MClass (root_class 5 ++ [(QFlen, 4194304, 8388607)]) TFx_7) (MClass (root_class 5 ++ [(QFlen, 8388608, QMAX)]) TRx_7).
  Lemma TNx_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr7x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TNx_7 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_7_ok | exact TRx_7_ok]. Qed.
  Definition TSxa_7 : mtree := MPre 1 k1s7xa [(159%nat, (2%nat, HS_hr7x))] [(159%nat, TNx_7)].
  Lemma TSxa_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TSxa_7 = true.
  Proof. unfold TSxa_7. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 1 k1s7xa [(159%nat, (2%nat, HS_hr7x))] [(159%nat, TNx_7)] eq_refl (k1s7xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(159%nat, (2%nat, HS_hr7x))] (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 159%nat TNx_7 [] 2 HS_hr7x eq_refl eq_refl TNx_7_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_7 : mtree := MPre 1 k1s7xb [(159%nat, (2%nat, HS_hr7x))] [(159%nat, TNx_7)].
  Lemma TSxb_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TSxb_7 = true.
  Proof. unfold TSxb_7. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg7x e_r 4046) (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 1 k1s7xb [(159%nat, (2%nat, HS_hr7x))] [(159%nat, TNx_7)] eq_refl (k1s7xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(159%nat, (2%nat, HS_hr7x))] (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 159%nat TNx_7 [] 2 HS_hr7x eq_refl eq_refl TNx_7_ok). apply mforest_ok_nil. Qed.
  Definition TSx_7 : mtree := MCase e_r 4046 TSxa_7 TSxb_7.
  Lemma TSx_7_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg7x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TSx_7 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg7x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) e_r 4046 TSxa_7 TSxb_7 eq_refl TSxa_7_ok TSxb_7_ok). Qed.


  Definition PWx6_1_PEa : mtree := MEmpty 2.
  Lemma PWx6_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht6x) (((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, QMIN, 2064378)]) PWx6_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht6x) (((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, QMIN, 2064378)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx6_2_Phi6 : mtree := MClass C_hi6x T_hi6x.
  Lemma PWx6_2_Phi6_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht6x) ((((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) PWx6_2_Phi6 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht6x) ((((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) (C_hi6x) T_hi6x); [vm_compute; reflexivity | exact (T_hi6x_ok TT)]. Qed.
  Definition PWx6_3_PEb : mtree := MEmpty 2.
  Lemma PWx6_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht6x) ((((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) PWx6_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht6x) ((((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx6_4_PGb : mtree := MSplit QRoom 4194297 PWx6_2_Phi6 PWx6_3_PEb.
  Lemma PWx6_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht6x) (((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) PWx6_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht6x) (((root_class 5 ++ [(QFlen, 2097152, 4194303)])) ++ [(QRoom, 2064378 + 1, QMAX)]) QRoom (4194297) PWx6_2_Phi6 PWx6_3_PEb PWx6_2_Phi6_ok PWx6_3_PEb_ok). Qed.
  Definition PWx6_5_PGa : mtree := MSplit QRoom 2064378 PWx6_1_PEa PWx6_4_PGb.
  Lemma PWx6_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht6x) ((root_class 5 ++ [(QFlen, 2097152, 4194303)])) PWx6_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht6x) ((root_class 5 ++ [(QFlen, 2097152, 4194303)])) QRoom (2064378) PWx6_1_PEa PWx6_4_PGb PWx6_1_PEa_ok PWx6_4_PGb_ok). Qed.
  Definition TFx_6 : mtree := MPre 2 k1f6x [(187%nat, (2%nat, HS_ht6x))] [(187%nat, PWx6_5_PGa)].
  Lemma TFx_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr6x (root_class 5 ++ [(QFlen, 2097152, 4194303)]) TFx_6 = true.
  Proof. unfold TFx_6. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr6x (root_class 5 ++ [(QFlen, 2097152, 4194303)]) 2 k1f6x [(187%nat, (2%nat, HS_ht6x))] [(187%nat, PWx6_5_PGa)] eq_refl (k1f6x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(187%nat, (2%nat, HS_ht6x))] (root_class 5 ++ [(QFlen, 2097152, 4194303)]) 187%nat PWx6_5_PGa [] 2 HS_ht6x eq_refl eq_refl PWx6_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_6 : mtree := MPre 1 k1r6x [(123%nat, (1%nat, HS_hg7x))] [(123%nat, TSx_7)].
  Lemma TRx_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr6x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TRx_6 = true.
  Proof. unfold TRx_6. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr6x (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 1 k1r6x [(123%nat, (1%nat, HS_hg7x))] [(123%nat, TSx_7)] eq_refl (k1r6x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(123%nat, (1%nat, HS_hg7x))] (root_class 5 ++ [(QFlen, 4194304, QMAX)]) 123%nat TSx_7 [] 1 HS_hg7x eq_refl eq_refl TSx_7_ok). apply mforest_ok_nil. Qed.
  Definition TNx_6 : mtree := MSplit QFlen 4194303 (MClass (root_class 5 ++ [(QFlen, 2097152, 4194303)]) TFx_6) (MClass (root_class 5 ++ [(QFlen, 4194304, QMAX)]) TRx_6).
  Lemma TNx_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr6x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TNx_6 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_6_ok | exact TRx_6_ok]. Qed.
  Definition TSxa_6 : mtree := MPre 1 k1s6xa [(156%nat, (2%nat, HS_hr6x))] [(156%nat, TNx_6)].
  Lemma TSxa_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TSxa_6 = true.
  Proof. unfold TSxa_6. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 1 k1s6xa [(156%nat, (2%nat, HS_hr6x))] [(156%nat, TNx_6)] eq_refl (k1s6xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(156%nat, (2%nat, HS_hr6x))] (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 156%nat TNx_6 [] 2 HS_hr6x eq_refl eq_refl TNx_6_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_6 : mtree := MPre 1 k1s6xb [(156%nat, (2%nat, HS_hr6x))] [(156%nat, TNx_6)].
  Lemma TSxb_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TSxb_6 = true.
  Proof. unfold TSxb_6. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg6x e_r 4046) (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 1 k1s6xb [(156%nat, (2%nat, HS_hr6x))] [(156%nat, TNx_6)] eq_refl (k1s6xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(156%nat, (2%nat, HS_hr6x))] (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 156%nat TNx_6 [] 2 HS_hr6x eq_refl eq_refl TNx_6_ok). apply mforest_ok_nil. Qed.
  Definition TSx_6 : mtree := MCase e_r 4046 TSxa_6 TSxb_6.
  Lemma TSx_6_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg6x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TSx_6 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg6x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) e_r 4046 TSxa_6 TSxb_6 eq_refl TSxa_6_ok TSxb_6_ok). Qed.


  Definition PWx5_1_PEa : mtree := MEmpty 2.
  Lemma PWx5_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) (((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, QMIN, 1015802)]) PWx5_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) (((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, QMIN, 1015802)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx5_2_Phi5a : mtree := MClass C_hi5ax T_hi5ax.
  Lemma PWx5_2_Phi5a_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) (((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ++ [(QRoom, QMIN, 1040384)]) PWx5_2_Phi5a = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) (((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ++ [(QRoom, QMIN, 1040384)]) (C_hi5ax) T_hi5ax); [vm_compute; reflexivity | exact (T_hi5ax_ok TT)]. Qed.
  Definition PWx5_3_Phi5b : mtree := MClass C_hi5bx T_hi5bx.
  Lemma PWx5_3_Phi5b_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) (((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ++ [(QRoom, 1040384 + 1, QMAX)]) PWx5_3_Phi5b = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) (((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ++ [(QRoom, 1040384 + 1, QMAX)]) (C_hi5bx) T_hi5bx); [vm_compute; reflexivity | exact (T_hi5bx_ok TT)]. Qed.
  Definition PWx5_4_PShi5a : mtree := MSplit QRoom 1040384 PWx5_2_Phi5a PWx5_3_Phi5b.
  Lemma PWx5_4_PShi5a_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) ((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) PWx5_4_PShi5a = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) ((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) QRoom (1040384) PWx5_2_Phi5a PWx5_3_Phi5b PWx5_2_Phi5a_ok PWx5_3_Phi5b_ok). Qed.
  Definition PWx5_5_PEb : mtree := MEmpty 2.
  Lemma PWx5_5_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) ((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) PWx5_5_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) ((((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx5_6_PGb : mtree := MSplit QRoom 2097145 PWx5_4_PShi5a PWx5_5_PEb.
  Lemma PWx5_6_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) (((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) PWx5_6_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) (((root_class 5 ++ [(QFlen, 1048576, 2097151)])) ++ [(QRoom, 1015802 + 1, QMAX)]) QRoom (2097145) PWx5_4_PShi5a PWx5_5_PEb PWx5_4_PShi5a_ok PWx5_5_PEb_ok). Qed.
  Definition PWx5_7_PGa : mtree := MSplit QRoom 1015802 PWx5_1_PEa PWx5_6_PGb.
  Lemma PWx5_7_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht5x) ((root_class 5 ++ [(QFlen, 1048576, 2097151)])) PWx5_7_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht5x) ((root_class 5 ++ [(QFlen, 1048576, 2097151)])) QRoom (1015802) PWx5_1_PEa PWx5_6_PGb PWx5_1_PEa_ok PWx5_6_PGb_ok). Qed.
  Definition TFx_5 : mtree := MPre 2 k1f5x [(184%nat, (2%nat, HS_ht5x))] [(184%nat, PWx5_7_PGa)].
  Lemma TFx_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr5x (root_class 5 ++ [(QFlen, 1048576, 2097151)]) TFx_5 = true.
  Proof. unfold TFx_5. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr5x (root_class 5 ++ [(QFlen, 1048576, 2097151)]) 2 k1f5x [(184%nat, (2%nat, HS_ht5x))] [(184%nat, PWx5_7_PGa)] eq_refl (k1f5x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(184%nat, (2%nat, HS_ht5x))] (root_class 5 ++ [(QFlen, 1048576, 2097151)]) 184%nat PWx5_7_PGa [] 2 HS_ht5x eq_refl eq_refl PWx5_7_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_5 : mtree := MPre 1 k1r5x [(120%nat, (1%nat, HS_hg6x))] [(120%nat, TSx_6)].
  Lemma TRx_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr5x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TRx_5 = true.
  Proof. unfold TRx_5. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr5x (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 1 k1r5x [(120%nat, (1%nat, HS_hg6x))] [(120%nat, TSx_6)] eq_refl (k1r5x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(120%nat, (1%nat, HS_hg6x))] (root_class 5 ++ [(QFlen, 2097152, QMAX)]) 120%nat TSx_6 [] 1 HS_hg6x eq_refl eq_refl TSx_6_ok). apply mforest_ok_nil. Qed.
  Definition TNx_5 : mtree := MSplit QFlen 2097151 (MClass (root_class 5 ++ [(QFlen, 1048576, 2097151)]) TFx_5) (MClass (root_class 5 ++ [(QFlen, 2097152, QMAX)]) TRx_5).
  Lemma TNx_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr5x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TNx_5 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_5_ok | exact TRx_5_ok]. Qed.
  Definition TSxa_5 : mtree := MPre 1 k1s5xa [(153%nat, (2%nat, HS_hr5x))] [(153%nat, TNx_5)].
  Lemma TSxa_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TSxa_5 = true.
  Proof. unfold TSxa_5. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 1 k1s5xa [(153%nat, (2%nat, HS_hr5x))] [(153%nat, TNx_5)] eq_refl (k1s5xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(153%nat, (2%nat, HS_hr5x))] (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 153%nat TNx_5 [] 2 HS_hr5x eq_refl eq_refl TNx_5_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_5 : mtree := MPre 1 k1s5xb [(153%nat, (2%nat, HS_hr5x))] [(153%nat, TNx_5)].
  Lemma TSxb_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TSxb_5 = true.
  Proof. unfold TSxb_5. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg5x e_r 4046) (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 1 k1s5xb [(153%nat, (2%nat, HS_hr5x))] [(153%nat, TNx_5)] eq_refl (k1s5xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(153%nat, (2%nat, HS_hr5x))] (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 153%nat TNx_5 [] 2 HS_hr5x eq_refl eq_refl TNx_5_ok). apply mforest_ok_nil. Qed.
  Definition TSx_5 : mtree := MCase e_r 4046 TSxa_5 TSxb_5.
  Lemma TSx_5_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg5x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TSx_5 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg5x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) e_r 4046 TSxa_5 TSxb_5 eq_refl TSxa_5_ok TSxb_5_ok). Qed.


  Definition PWx4_1_PEa : mtree := MEmpty 2.
  Lemma PWx4_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht4x) (((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, QMIN, 491514)]) PWx4_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht4x) (((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, QMIN, 491514)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx4_2_Psec4 : mtree := MClass C_sec4x T_sec4x.
  Lemma PWx4_2_Psec4_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht4x) ((((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) PWx4_2_Psec4 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht4x) ((((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) (C_sec4x) T_sec4x); [vm_compute; reflexivity | exact (T_sec4x_ok TT)]. Qed.
  Definition PWx4_3_PEb : mtree := MEmpty 2.
  Lemma PWx4_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht4x) ((((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) PWx4_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht4x) ((((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx4_4_PGb : mtree := MSplit QRoom 1048569 PWx4_2_Psec4 PWx4_3_PEb.
  Lemma PWx4_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht4x) (((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) PWx4_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht4x) (((root_class 5 ++ [(QFlen, 524288, 1048575)])) ++ [(QRoom, 491514 + 1, QMAX)]) QRoom (1048569) PWx4_2_Psec4 PWx4_3_PEb PWx4_2_Psec4_ok PWx4_3_PEb_ok). Qed.
  Definition PWx4_5_PGa : mtree := MSplit QRoom 491514 PWx4_1_PEa PWx4_4_PGb.
  Lemma PWx4_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht4x) ((root_class 5 ++ [(QFlen, 524288, 1048575)])) PWx4_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht4x) ((root_class 5 ++ [(QFlen, 524288, 1048575)])) QRoom (491514) PWx4_1_PEa PWx4_4_PGb PWx4_1_PEa_ok PWx4_4_PGb_ok). Qed.
  Definition TFx_4 : mtree := MPre 2 k1f4x [(181%nat, (2%nat, HS_ht4x))] [(181%nat, PWx4_5_PGa)].
  Lemma TFx_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr4x (root_class 5 ++ [(QFlen, 524288, 1048575)]) TFx_4 = true.
  Proof. unfold TFx_4. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr4x (root_class 5 ++ [(QFlen, 524288, 1048575)]) 2 k1f4x [(181%nat, (2%nat, HS_ht4x))] [(181%nat, PWx4_5_PGa)] eq_refl (k1f4x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(181%nat, (2%nat, HS_ht4x))] (root_class 5 ++ [(QFlen, 524288, 1048575)]) 181%nat PWx4_5_PGa [] 2 HS_ht4x eq_refl eq_refl PWx4_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_4 : mtree := MPre 1 k1r4x [(117%nat, (1%nat, HS_hg5x))] [(117%nat, TSx_5)].
  Lemma TRx_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr4x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TRx_4 = true.
  Proof. unfold TRx_4. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr4x (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 1 k1r4x [(117%nat, (1%nat, HS_hg5x))] [(117%nat, TSx_5)] eq_refl (k1r4x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(117%nat, (1%nat, HS_hg5x))] (root_class 5 ++ [(QFlen, 1048576, QMAX)]) 117%nat TSx_5 [] 1 HS_hg5x eq_refl eq_refl TSx_5_ok). apply mforest_ok_nil. Qed.
  Definition TNx_4 : mtree := MSplit QFlen 1048575 (MClass (root_class 5 ++ [(QFlen, 524288, 1048575)]) TFx_4) (MClass (root_class 5 ++ [(QFlen, 1048576, QMAX)]) TRx_4).
  Lemma TNx_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr4x (root_class 5 ++ [(QFlen, 524288, QMAX)]) TNx_4 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_4_ok | exact TRx_4_ok]. Qed.
  Definition TSxa_4 : mtree := MPre 1 k1s4xa [(150%nat, (2%nat, HS_hr4x))] [(150%nat, TNx_4)].
  Lemma TSxa_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) TSxa_4 = true.
  Proof. unfold TSxa_4. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) 1 k1s4xa [(150%nat, (2%nat, HS_hr4x))] [(150%nat, TNx_4)] eq_refl (k1s4xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(150%nat, (2%nat, HS_hr4x))] (root_class 5 ++ [(QFlen, 524288, QMAX)]) 150%nat TNx_4 [] 2 HS_hr4x eq_refl eq_refl TNx_4_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_4 : mtree := MPre 1 k1s4xb [(150%nat, (2%nat, HS_hr4x))] [(150%nat, TNx_4)].
  Lemma TSxb_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) TSxb_4 = true.
  Proof. unfold TSxb_4. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg4x e_r 4046) (root_class 5 ++ [(QFlen, 524288, QMAX)]) 1 k1s4xb [(150%nat, (2%nat, HS_hr4x))] [(150%nat, TNx_4)] eq_refl (k1s4xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(150%nat, (2%nat, HS_hr4x))] (root_class 5 ++ [(QFlen, 524288, QMAX)]) 150%nat TNx_4 [] 2 HS_hr4x eq_refl eq_refl TNx_4_ok). apply mforest_ok_nil. Qed.
  Definition TSx_4 : mtree := MCase e_r 4046 TSxa_4 TSxb_4.
  Lemma TSx_4_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg4x (root_class 5 ++ [(QFlen, 524288, QMAX)]) TSx_4 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg4x (root_class 5 ++ [(QFlen, 524288, QMAX)]) e_r 4046 TSxa_4 TSxb_4 eq_refl TSxa_4_ok TSxb_4_ok). Qed.


  Definition PWx3_1_PEa : mtree := MEmpty 2.
  Lemma PWx3_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht3x) (((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, QMIN, 229370)]) PWx3_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht3x) (((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, QMIN, 229370)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx3_2_Psec3 : mtree := MClass C_sec3x T_sec3x.
  Lemma PWx3_2_Psec3_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht3x) ((((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) PWx3_2_Psec3 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht3x) ((((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) (C_sec3x) T_sec3x); [vm_compute; reflexivity | exact (T_sec3x_ok TT)]. Qed.
  Definition PWx3_3_PEb : mtree := MEmpty 2.
  Lemma PWx3_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht3x) ((((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) PWx3_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht3x) ((((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx3_4_PGb : mtree := MSplit QRoom 524281 PWx3_2_Psec3 PWx3_3_PEb.
  Lemma PWx3_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht3x) (((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) PWx3_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht3x) (((root_class 5 ++ [(QFlen, 262144, 524287)])) ++ [(QRoom, 229370 + 1, QMAX)]) QRoom (524281) PWx3_2_Psec3 PWx3_3_PEb PWx3_2_Psec3_ok PWx3_3_PEb_ok). Qed.
  Definition PWx3_5_PGa : mtree := MSplit QRoom 229370 PWx3_1_PEa PWx3_4_PGb.
  Lemma PWx3_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht3x) ((root_class 5 ++ [(QFlen, 262144, 524287)])) PWx3_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht3x) ((root_class 5 ++ [(QFlen, 262144, 524287)])) QRoom (229370) PWx3_1_PEa PWx3_4_PGb PWx3_1_PEa_ok PWx3_4_PGb_ok). Qed.
  Definition TFx_3 : mtree := MPre 2 k1f3x [(178%nat, (2%nat, HS_ht3x))] [(178%nat, PWx3_5_PGa)].
  Lemma TFx_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr3x (root_class 5 ++ [(QFlen, 262144, 524287)]) TFx_3 = true.
  Proof. unfold TFx_3. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr3x (root_class 5 ++ [(QFlen, 262144, 524287)]) 2 k1f3x [(178%nat, (2%nat, HS_ht3x))] [(178%nat, PWx3_5_PGa)] eq_refl (k1f3x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(178%nat, (2%nat, HS_ht3x))] (root_class 5 ++ [(QFlen, 262144, 524287)]) 178%nat PWx3_5_PGa [] 2 HS_ht3x eq_refl eq_refl PWx3_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_3 : mtree := MPre 1 k1r3x [(114%nat, (1%nat, HS_hg4x))] [(114%nat, TSx_4)].
  Lemma TRx_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr3x (root_class 5 ++ [(QFlen, 524288, QMAX)]) TRx_3 = true.
  Proof. unfold TRx_3. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr3x (root_class 5 ++ [(QFlen, 524288, QMAX)]) 1 k1r3x [(114%nat, (1%nat, HS_hg4x))] [(114%nat, TSx_4)] eq_refl (k1r3x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(114%nat, (1%nat, HS_hg4x))] (root_class 5 ++ [(QFlen, 524288, QMAX)]) 114%nat TSx_4 [] 1 HS_hg4x eq_refl eq_refl TSx_4_ok). apply mforest_ok_nil. Qed.
  Definition TNx_3 : mtree := MSplit QFlen 524287 (MClass (root_class 5 ++ [(QFlen, 262144, 524287)]) TFx_3) (MClass (root_class 5 ++ [(QFlen, 524288, QMAX)]) TRx_3).
  Lemma TNx_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr3x (root_class 5 ++ [(QFlen, 262144, QMAX)]) TNx_3 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_3_ok | exact TRx_3_ok]. Qed.
  Definition TSxa_3 : mtree := MPre 1 k1s3xa [(147%nat, (2%nat, HS_hr3x))] [(147%nat, TNx_3)].
  Lemma TSxa_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) TSxa_3 = true.
  Proof. unfold TSxa_3. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) 1 k1s3xa [(147%nat, (2%nat, HS_hr3x))] [(147%nat, TNx_3)] eq_refl (k1s3xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(147%nat, (2%nat, HS_hr3x))] (root_class 5 ++ [(QFlen, 262144, QMAX)]) 147%nat TNx_3 [] 2 HS_hr3x eq_refl eq_refl TNx_3_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_3 : mtree := MPre 1 k1s3xb [(147%nat, (2%nat, HS_hr3x))] [(147%nat, TNx_3)].
  Lemma TSxb_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) TSxb_3 = true.
  Proof. unfold TSxb_3. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg3x e_r 4046) (root_class 5 ++ [(QFlen, 262144, QMAX)]) 1 k1s3xb [(147%nat, (2%nat, HS_hr3x))] [(147%nat, TNx_3)] eq_refl (k1s3xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(147%nat, (2%nat, HS_hr3x))] (root_class 5 ++ [(QFlen, 262144, QMAX)]) 147%nat TNx_3 [] 2 HS_hr3x eq_refl eq_refl TNx_3_ok). apply mforest_ok_nil. Qed.
  Definition TSx_3 : mtree := MCase e_r 4046 TSxa_3 TSxb_3.
  Lemma TSx_3_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg3x (root_class 5 ++ [(QFlen, 262144, QMAX)]) TSx_3 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg3x (root_class 5 ++ [(QFlen, 262144, QMAX)]) e_r 4046 TSxa_3 TSxb_3 eq_refl TSxa_3_ok TSxb_3_ok). Qed.


  Definition PWx2_1_PEa : mtree := MEmpty 2.
  Lemma PWx2_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht2x) (((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, QMIN, 98298)]) PWx2_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht2x) (((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, QMIN, 98298)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx2_2_Psec2 : mtree := MClass C_sec2x T_sec2x.
  Lemma PWx2_2_Psec2_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht2x) ((((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) PWx2_2_Psec2 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht2x) ((((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) (C_sec2x) T_sec2x); [vm_compute; reflexivity | exact (T_sec2x_ok TT)]. Qed.
  Definition PWx2_3_PEb : mtree := MEmpty 2.
  Lemma PWx2_3_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht2x) ((((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) PWx2_3_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht2x) ((((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx2_4_PGb : mtree := MSplit QRoom 262137 PWx2_2_Psec2 PWx2_3_PEb.
  Lemma PWx2_4_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht2x) (((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) PWx2_4_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht2x) (((root_class 5 ++ [(QFlen, 131072, 262143)])) ++ [(QRoom, 98298 + 1, QMAX)]) QRoom (262137) PWx2_2_Psec2 PWx2_3_PEb PWx2_2_Psec2_ok PWx2_3_PEb_ok). Qed.
  Definition PWx2_5_PGa : mtree := MSplit QRoom 98298 PWx2_1_PEa PWx2_4_PGb.
  Lemma PWx2_5_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht2x) ((root_class 5 ++ [(QFlen, 131072, 262143)])) PWx2_5_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht2x) ((root_class 5 ++ [(QFlen, 131072, 262143)])) QRoom (98298) PWx2_1_PEa PWx2_4_PGb PWx2_1_PEa_ok PWx2_4_PGb_ok). Qed.
  Definition TFx_2 : mtree := MPre 2 k1f2x [(175%nat, (2%nat, HS_ht2x))] [(175%nat, PWx2_5_PGa)].
  Lemma TFx_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr2x (root_class 5 ++ [(QFlen, 131072, 262143)]) TFx_2 = true.
  Proof. unfold TFx_2. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr2x (root_class 5 ++ [(QFlen, 131072, 262143)]) 2 k1f2x [(175%nat, (2%nat, HS_ht2x))] [(175%nat, PWx2_5_PGa)] eq_refl (k1f2x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(175%nat, (2%nat, HS_ht2x))] (root_class 5 ++ [(QFlen, 131072, 262143)]) 175%nat PWx2_5_PGa [] 2 HS_ht2x eq_refl eq_refl PWx2_5_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_2 : mtree := MPre 1 k1r2x [(111%nat, (1%nat, HS_hg3x))] [(111%nat, TSx_3)].
  Lemma TRx_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr2x (root_class 5 ++ [(QFlen, 262144, QMAX)]) TRx_2 = true.
  Proof. unfold TRx_2. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr2x (root_class 5 ++ [(QFlen, 262144, QMAX)]) 1 k1r2x [(111%nat, (1%nat, HS_hg3x))] [(111%nat, TSx_3)] eq_refl (k1r2x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(111%nat, (1%nat, HS_hg3x))] (root_class 5 ++ [(QFlen, 262144, QMAX)]) 111%nat TSx_3 [] 1 HS_hg3x eq_refl eq_refl TSx_3_ok). apply mforest_ok_nil. Qed.
  Definition TNx_2 : mtree := MSplit QFlen 262143 (MClass (root_class 5 ++ [(QFlen, 131072, 262143)]) TFx_2) (MClass (root_class 5 ++ [(QFlen, 262144, QMAX)]) TRx_2).
  Lemma TNx_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr2x (root_class 5 ++ [(QFlen, 131072, QMAX)]) TNx_2 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_2_ok | exact TRx_2_ok]. Qed.
  Definition TSxa_2 : mtree := MPre 1 k1s2xa [(144%nat, (2%nat, HS_hr2x))] [(144%nat, TNx_2)].
  Lemma TSxa_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) TSxa_2 = true.
  Proof. unfold TSxa_2. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_lo HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) 1 k1s2xa [(144%nat, (2%nat, HS_hr2x))] [(144%nat, TNx_2)] eq_refl (k1s2xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(144%nat, (2%nat, HS_hr2x))] (root_class 5 ++ [(QFlen, 131072, QMAX)]) 144%nat TNx_2 [] 2 HS_hr2x eq_refl eq_refl TNx_2_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_2 : mtree := MPre 1 k1s2xb [(144%nat, (2%nat, HS_hr2x))] [(144%nat, TNx_2)].
  Lemma TSxb_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) TSxb_2 = true.
  Proof. unfold TSxb_2. apply (segb_tree KCm BFUELm FUELm BITm TT 1 1 (mcase_hi HS_hg2x e_r 4046) (root_class 5 ++ [(QFlen, 131072, QMAX)]) 1 k1s2xb [(144%nat, (2%nat, HS_hr2x))] [(144%nat, TNx_2)] eq_refl (k1s2xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(144%nat, (2%nat, HS_hr2x))] (root_class 5 ++ [(QFlen, 131072, QMAX)]) 144%nat TNx_2 [] 2 HS_hr2x eq_refl eq_refl TNx_2_ok). apply mforest_ok_nil. Qed.
  Definition TSx_2 : mtree := MCase e_r 4046 TSxa_2 TSxb_2.
  Lemma TSx_2_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 1 HS_hg2x (root_class 5 ++ [(QFlen, 131072, QMAX)]) TSx_2 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 1%nat 1%nat HS_hg2x (root_class 5 ++ [(QFlen, 131072, QMAX)]) e_r 4046 TSxa_2 TSxb_2 eq_refl TSxa_2_ok TSxb_2_ok). Qed.


  Definition PWx1_1_PEa : mtree := MEmpty 2.
  Lemma PWx1_1_PEa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) (((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, QMIN, 32762)]) PWx1_1_PEa = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) (((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, QMIN, 32762)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx1_2_Pp48 : mtree := MClass C_p48xa T_p48x.
  Lemma PWx1_2_Pp48_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) (((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, QMIN, 48128)]) PWx1_2_Pp48 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) (((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, QMIN, 48128)]) (C_p48xa) T_p48x); [vm_compute; reflexivity | exact (T_p48x_ok TT)]. Qed.
  Definition PWx1_3_Pp64 : mtree := MClass C_p64xa T_p64x.
  Lemma PWx1_3_Pp64_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) ((((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) PWx1_3_Pp64 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) ((((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) (C_p64xa) T_p64x); [vm_compute; reflexivity | exact (T_p64x_ok TT)]. Qed.
  Definition PWx1_4_Psec1 : mtree := MClass C_sec1x T_sec1x.
  Lemma PWx1_4_Psec1_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) ((((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) PWx1_4_Psec1 = true.
  Proof. apply (mtree_ok_class KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) ((((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) (C_sec1x) T_sec1x); [vm_compute; reflexivity | exact (T_sec1x_ok TT)]. Qed.
  Definition PWx1_5_PSp64 : mtree := MSplit QRoom 64512 PWx1_3_Pp64 PWx1_4_Psec1.
  Lemma PWx1_5_PSp64_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) (((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) PWx1_5_PSp64 = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) (((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ++ [(QRoom, 48128 + 1, QMAX)]) QRoom (64512) PWx1_3_Pp64 PWx1_4_Psec1 PWx1_3_Pp64_ok PWx1_4_Psec1_ok). Qed.
  Definition PWx1_6_PSp48 : mtree := MSplit QRoom 48128 PWx1_2_Pp48 PWx1_5_PSp64.
  Lemma PWx1_6_PSp48_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) ((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) PWx1_6_PSp48 = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) ((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) QRoom (48128) PWx1_2_Pp48 PWx1_5_PSp64 PWx1_2_Pp48_ok PWx1_5_PSp64_ok). Qed.
  Definition PWx1_7_PEb : mtree := MEmpty 2.
  Lemma PWx1_7_PEb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) ((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) PWx1_7_PEb = true.
  Proof. apply (mtree_ok_empty KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) ((((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
  Definition PWx1_8_PGb : mtree := MSplit QRoom 131065 PWx1_6_PSp48 PWx1_7_PEb.
  Lemma PWx1_8_PGb_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) (((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) PWx1_8_PGb = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) (((root_class 5 ++ [(QFlen, 65536, 131071)])) ++ [(QRoom, 32762 + 1, QMAX)]) QRoom (131065) PWx1_6_PSp48 PWx1_7_PEb PWx1_6_PSp48_ok PWx1_7_PEb_ok). Qed.
  Definition PWx1_9_PGa : mtree := MSplit QRoom 32762 PWx1_1_PEa PWx1_8_PGb.
  Lemma PWx1_9_PGa_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 (HS_ht1x) ((root_class 5 ++ [(QFlen, 65536, 131071)])) PWx1_9_PGa = true.
  Proof. exact (mtree_ok_split KCm BFUELm FUELm BITm TT 2%nat 2%nat (HS_ht1x) ((root_class 5 ++ [(QFlen, 65536, 131071)])) QRoom (32762) PWx1_1_PEa PWx1_8_PGb PWx1_1_PEa_ok PWx1_8_PGb_ok). Qed.
  Definition TFx_1 : mtree := MPre 2 k1f1x [(172%nat, (2%nat, HS_ht1x))] [(172%nat, PWx1_9_PGa)].
  Lemma TFx_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr1x (root_class 5 ++ [(QFlen, 65536, 131071)]) TFx_1 = true.
  Proof. unfold TFx_1. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr1x (root_class 5 ++ [(QFlen, 65536, 131071)]) 2 k1f1x [(172%nat, (2%nat, HS_ht1x))] [(172%nat, PWx1_9_PGa)] eq_refl (k1f1x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 [(172%nat, (2%nat, HS_ht1x))] (root_class 5 ++ [(QFlen, 65536, 131071)]) 172%nat PWx1_9_PGa [] 2 HS_ht1x eq_refl eq_refl PWx1_9_PGa_ok). apply mforest_ok_nil. Qed.
  Definition TRx_1 : mtree := MPre 1 k1r1x [(108%nat, (1%nat, HS_hg2x))] [(108%nat, TSx_2)].
  Lemma TRx_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr1x (root_class 5 ++ [(QFlen, 131072, QMAX)]) TRx_1 = true.
  Proof. unfold TRx_1. apply (segb_tree KCm BFUELm FUELm BITm TT 1 2 HS_hr1x (root_class 5 ++ [(QFlen, 131072, QMAX)]) 1 k1r1x [(108%nat, (1%nat, HS_hg2x))] [(108%nat, TSx_2)] eq_refl (k1r1x_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(108%nat, (1%nat, HS_hg2x))] (root_class 5 ++ [(QFlen, 131072, QMAX)]) 108%nat TSx_2 [] 1 HS_hg2x eq_refl eq_refl TSx_2_ok). apply mforest_ok_nil. Qed.
  Definition TNx_1 : mtree := MSplit QFlen 131071 (MClass (root_class 5 ++ [(QFlen, 65536, 131071)]) TFx_1) (MClass (root_class 5 ++ [(QFlen, 131072, QMAX)]) TRx_1).
  Lemma TNx_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 1 2 HS_hr1x (root_class 5 ++ [(QFlen, 65536, QMAX)]) TNx_1 = true.
  Proof. apply mtree_ok_split; (apply mtree_ok_class; [vm_compute; reflexivity|]); [exact TFx_1_ok | exact TRx_1_ok]. Qed.
  Definition TSxa_1 : mtree := MPre 1 k1s1xa [(141%nat, (2%nat, HS_hr1x))] [(141%nat, TNx_1)].
  Lemma TSxa_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 1 (mcase_lo HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) TSxa_1 = true.
  Proof. unfold TSxa_1. apply (segb_tree KCm BFUELm FUELm BITm TT 0 1 (mcase_lo HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) 1 k1s1xa [(141%nat, (2%nat, HS_hr1x))] [(141%nat, TNx_1)] eq_refl (k1s1xa_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(141%nat, (2%nat, HS_hr1x))] (root_class 5 ++ [(QFlen, 65536, QMAX)]) 141%nat TNx_1 [] 2 HS_hr1x eq_refl eq_refl TNx_1_ok). apply mforest_ok_nil. Qed.
  Definition TSxb_1 : mtree := MPre 1 k1s1xb [(141%nat, (2%nat, HS_hr1x))] [(141%nat, TNx_1)].
  Lemma TSxb_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 1 (mcase_hi HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) TSxb_1 = true.
  Proof. unfold TSxb_1. apply (segb_tree KCm BFUELm FUELm BITm TT 0 1 (mcase_hi HS_hg1x e_r 4046) (root_class 5 ++ [(QFlen, 65536, QMAX)]) 1 k1s1xb [(141%nat, (2%nat, HS_hr1x))] [(141%nat, TNx_1)] eq_refl (k1s1xb_ok TT) eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 1 [(141%nat, (2%nat, HS_hr1x))] (root_class 5 ++ [(QFlen, 65536, QMAX)]) 141%nat TNx_1 [] 2 HS_hr1x eq_refl eq_refl TNx_1_ok). apply mforest_ok_nil. Qed.
  Definition TSx_1 : mtree := MCase e_r 4046 TSxa_1 TSxb_1.
  Lemma TSx_1_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 1 HS_hg1x (root_class 5 ++ [(QFlen, 65536, QMAX)]) TSx_1 = true.
  Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT 0%nat 1%nat HS_hg1x (root_class 5 ++ [(QFlen, 65536, QMAX)]) e_r 4046 TSxa_1 TSxb_1 eq_refl TSxa_1_ok TSxb_1_ok). Qed.

  Definition T_K1 : mtree := MPre 0 k1s0x [(105%nat, (1%nat, HS_hg1x))] [(105%nat, TSx_1)].
  Lemma T_K1_ok : mtree_ok KCm BFUELm FUELm BITm TT 0 0 (HSA HS_main_both 0) (root_class 5 ++ [(QFlen, 65535 + 1, QMAX)]) T_K1 = true.
  Proof. unfold T_K1. apply (preb_tree HS_main_both KCm BFUELm FUELm BITm TT 0 0%nat (root_class 5 ++ [(QFlen, 65536, QMAX)]) 0 k1s0x [(105%nat, (1%nat, HS_hg1x))] [(105%nat, TSx_1)] eq_refl k1s0_ok eq_refl).
    apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 0 [(105%nat, (1%nat, HS_hg1x))] (root_class 5 ++ [(QFlen, 65536, QMAX)]) 105%nat TSx_1 [] 1 HS_hg1x eq_refl eq_refl TSx_1_ok).
    apply mforest_ok_nil. Qed.
End TTS.
