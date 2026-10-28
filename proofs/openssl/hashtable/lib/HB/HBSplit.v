(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBChain HBOpenDefs BC1HS BC2AStart.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition restrict6 (cs : acs) (lo hi : Z) : acs := set_kn cs (KRange (EVar 6) lo hi :: kn cs).
Definition c2a0_start : acs := restrict6 c2a_start0 0 5.
Definition c2a2_start : acs := restrict6 c2a_start0 6 6.
Definition c2a3_start : acs := restrict6 c2a_start0 7 10.
Definition c2a1_start : acs := c2a_start1.
Definition c2b0_start : acs := restrict6 c2b_start0 0 5.
Definition c2b2_start : acs := restrict6 c2b_start0 6 6.
Definition c2b3_start : acs := restrict6 c2b_start0 7 10.
Definition c2b1_start : acs := c2b_start1.

Section Split.
  Variable SV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable fs : Fs.Fs.
  #[local] Notation PIECE := (piece SV argH ISP fs).
  Lemma piece_split3 : forall cs T, knows_range (kn cs) 6%nat 0 10 = true ->
    PIECE (restrict6 cs 0 5) T -> PIECE (restrict6 cs 6 6) T -> PIECE (restrict6 cs 7 10) T -> PIECE cs T.
  Proof.
    intros cs T KR P0 P2 P3 E R FULL m HC.
    pose proof (knows_range_sound _ _ _ _ 6%nat 0 10 KR (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H6.
    assert (HX : forall lo hi, lo <= bv_unsigned (edenot E (EVar 6)) <= hi -> cs_ok HASEGS HAT AsanInit.LIMIT SV argH ISP fs E (restrict6 cs lo hi) R FULL m).
    { intros lo hi Hr. unfold restrict6. apply cs_ok_set_kn; [exact HC|]. constructor; [exact Hr | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
    destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 6))) 5) as [H5|H5]; [exact (P0 E R FULL m (HX 0 5 ltac:(lia)))|].
    destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 6))) 6) as [H7|H7]; [exact (P2 E R FULL m (HX 6 6 ltac:(lia))) | exact (P3 E R FULL m (HX 7 10 ltac:(lia)))].
  Qed.
End Split.
Lemma c2a_start0_kr : knows_range (kn c2a_start0) 6%nat 0 10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma c2b_start0_kr : knows_range (kn c2b_start0) 6%nat 0 10 = true. Proof. vm_compute. reflexivity. Qed.
