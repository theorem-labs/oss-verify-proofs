(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout ACells LJ AFake AFakeRep AAllocCarve AInitReps.
Import ListNotations.
Open Scope Z_scope.

Definition fst0 : fstate := mkFST (fun _ => 0) [].

Lemma fst0_wf : fst_wf fst0.
Proof. unfold fst_wf, fst0. cbn [ft_live ft_hint length]. split; [constructor|]. split; [constructor|]. split; [lia|]. intros k _. lia. Qed.

Lemma map_const_seq : forall (b : byte) n s, map (fun _ : nat => b) (seq s n) = repeat b n.
Proof. induction n as [|n IH]; intros s; [reflexivity|]. cbn [seq map repeat]. f_equal. apply IH. Qed.

Section INIT.
Context {HC : HasCeiling}.
Variable fsb : Z.
Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                    /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).

#[using="HC FSB_OK"] Lemma RFAKE_B_init : forall (m : mem) js,
  rw_cells asegs m fsb [CB 88 (repeat zb 88)] ->
  rw_cells asegs m (fsb + 88) [C8 (wz 20)] ->
  rw_cells asegs m (fsb + 96) [CB (Z.to_nat (A0_FS_SIZE - 96)) (repeat zb (Z.to_nat (A0_FS_SIZE - 96)))] ->
  rw_cells asegs m (sh fsb) [CB (Z.to_nat A0_FS_SHSIZE) js] ->
  RFAKE_B fsb fst0 m.
Proof.
  intros m js H0 H88 HR HS. split; [exact fst0_wf|].
  pose proof (rw_zeros_cells m (fsb + 96) (Z.to_nat (A0_FS_SIZE - 96)) 0 [C1 zb] HR ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn [cells_size csize Nat.add]; lia)) as HGC.
  replace (fsb + 96 + Z.of_nat 0) with (fsb + 96) in HGC by lia.
  split.
  { unfold hint_cells, fst0. cbn [ft_hint].
    change [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 20); C1 zb]
      with ([C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ++ [C8 (wz 20)] ++ [C1 zb]).
    apply rw_cells_app. split.
    - eapply rw_cells_rebytes; [exact H0| cbn; tauto| reflexivity| reflexivity].
    - change (Z.of_nat (cells_size [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])) with 88.
      apply rw_cells_app. split; [exact H88|]. change (Z.of_nat (cells_size [C8 (wz 20)])) with 8. replace (fsb + 88 + 8) with (fsb + 96) by lia. exact HGC. }
  split.
  { pose proof (rw_zeros_sub m (fsb + 96) (Z.to_nat (A0_FS_SIZE - 96)) (Z.to_nat 4000) NFLAGS HR ltac:(unfold NFLAGS; lia)) as HF.
    replace (fsb + 96 + Z.of_nat (Z.to_nat 4000)) with (fsb + 4096) in HF by lia.
    unfold flag_list. replace (map (fun i : nat => fbyte fst0 (Z.of_nat i)) (seq 0 NFLAGS)) with (repeat zb NFLAGS); [exact HF|].
    symmetry. apply (map_const_seq zb NFLAGS 0%nat). }
  intros k pos Hk Hp _. destruct (slot_num fsb FSB_OK k pos Hk Hp) as (S1 & S2 & S3 & S4 & S5 & S6).
  split.
  - assert (LE : (Z.to_nat (fk_frame fsb k pos - (fsb + 96)) + Z.to_nat (FB_of k) <= Z.to_nat (A0_FS_SIZE - 96))%nat) by lia.
    destruct (cb_split3 m (fsb + 96) _ _ (Z.to_nat (fk_frame fsb k pos - (fsb + 96))) (Z.to_nat (FB_of k)) LE HR) as (_ & j2 & _ & _ & H2 & _).
    exists j2. replace (fsb + 96 + Z.of_nat (Z.to_nat (fk_frame fsb k pos - (fsb + 96)))) with (fk_frame fsb k pos) in H2 by lia. exact H2.
  - assert (LE : (Z.to_nat (sh (fk_frame fsb k pos) - sh fsb) + Z.to_nat (SB_of k) <= Z.to_nat A0_FS_SHSIZE)%nat) by lia.
    destruct (cb_split3 m (sh fsb) _ _ (Z.to_nat (sh (fk_frame fsb k pos) - sh fsb)) (Z.to_nat (SB_of k)) LE HS) as (_ & j2 & _ & _ & H2 & _).
    exists j2. replace (sh fsb + Z.of_nat (Z.to_nat (sh (fk_frame fsb k pos) - sh fsb))) with (sh (fk_frame fsb k pos)) in H2 by lia. exact H2.
Qed.
End INIT.
