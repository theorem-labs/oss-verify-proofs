(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import EAsStartupHSA.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition UW_LONG : kentry := KRange (EVar 10) 0 5.
Definition UW_SHORT : kentry := KRange (EVar 10) 6 10.

Definition s6start0 : acs := set_kn HSA_easan_0 (UW_LONG :: kn HSA_easan_0).
Definition s6start1 : acs := set_kn HSA_easan_0 (UW_SHORT :: kn HSA_easan_0).
Definition s6start2 : acs := set_kn HSA_easan_1 (UW_LONG :: kn HSA_easan_1).
Definition s6start3 : acs := set_kn HSA_easan_1 (UW_SHORT :: kn HSA_easan_1).
Definition s6start4 : acs := HSA_easan_2.
Definition s6start5 : acs := HSA_easan_3.

Definition S6START_table : list (nat * acs) :=
  [(0%nat, s6start0); (1%nat, s6start1); (2%nat, s6start2); (3%nat, s6start3); (4%nat, s6start4); (5%nat, s6start5)].
Definition S6START (h : nat) : option acs := hs_lookup h S6START_table.

Lemma S6START_pc : forall h ch, S6START h = Some ch -> pc ch = pc HSA_easan_0.
Proof.
  intros h ch H. apply hs_lookup_cases in H. cbn [S6START_table fold_right fst snd] in H.
  repeat (destruct H as [[_ ->]|H]; [vm_compute; reflexivity|]). destruct H.
Qed.

Lemma erange_w_0 : erange (kn HSA_easan_0) (EVar 10) = Some (0, 10).
Proof. vm_compute. reflexivity. Qed.
Lemma erange_w_1 : erange (kn HSA_easan_1) (EVar 10) = Some (0, 10).
Proof. vm_compute. reflexivity. Qed.

Section Split.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

  (* [comment removed for export] *)
  Lemma s6_split : forall k ch E R FULL model,
    HSA_easan k = Some ch -> CSOK E ch R FULL model ->
    exists h ch', S6START h = Some ch' /\ pc ch' = pc ch /\ CSOK E ch' R FULL model.
  Proof.
    intros k ch E R FULL model Hk HC. apply hs_lookup_cases in Hk. cbn [HSA_easan_table fold_right fst snd] in Hk.
    destruct Hk as [[-> ->]|Hk].
    { destruct (split_sound SEGS A LIMIT SINV argH FS0 HSA_easan_0 (EVar 10) 5 0 10 E R FULL model HC erange_w_0) as [S1 S2].
      destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 10))) 5) as [Hle|Hgt].
      - exists 0%nat, s6start0. split; [reflexivity|]. split; [reflexivity|]. exact (S1 Hle).
      - exists 1%nat, s6start1. split; [reflexivity|]. split; [reflexivity|]. exact (S2 ltac:(lia)). }
    destruct Hk as [[-> ->]|Hk].
    { destruct (split_sound SEGS A LIMIT SINV argH FS0 HSA_easan_1 (EVar 10) 5 0 10 E R FULL model HC erange_w_1) as [S1 S2].
      destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 10))) 5) as [Hle|Hgt].
      - exists 2%nat, s6start2. split; [reflexivity|]. split; [reflexivity|]. exact (S1 Hle).
      - exists 3%nat, s6start3. split; [reflexivity|]. split; [reflexivity|]. exact (S2 ltac:(lia)). }
    destruct Hk as [[-> ->]|Hk]; [exists 4%nat, s6start4; split; [reflexivity|]; split; [reflexivity|]; exact HC|].
    destruct Hk as [[-> ->]|Hk]; [exists 5%nat, s6start5; split; [reflexivity|]; split; [reflexivity|]; exact HC|].
    destruct Hk.
  Qed.
End Split.
