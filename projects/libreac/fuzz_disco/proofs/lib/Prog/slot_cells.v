From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_preds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_chain.
Import ListNotations.
Open Scope Z_scope.


Lemma mem_inv_of_cj : forall m, MemNorm.mem_inv_cj rsegs m -> mem_inv rsegs m.
Proof. intros m H a b Hab. exact (proj1 (H a b Hab)). Qed.
Lemma junk8_sub : forall m A B n bs k, rw_cells rsegs m A [CB n bs] -> (k + 8 <= n)%nat -> B = A + Z.of_nat k ->
  junk8 m B.
Proof.
  intros m A B n bs k H Hk ->. apply (rw_c8 m _ (firstn 8 (skipn k bs))). exact (rw_cb_sub m A n bs k 8 Hk H).
Qed.

Lemma junkb_sub : forall m A B n bs k j, rw_cells rsegs m A [CB n bs] -> (k + j <= n)%nat -> B = A + Z.of_nat k ->
  junkb m B j.
Proof.
  intros m A B n bs k j H Hk ->. exists (firstn j (skipn k bs)). exact (rw_cb_sub m A n bs k j Hk H).
Qed.

Lemma junkb_of : forall m A n bs, rw_cells rsegs m A [CB n bs] -> junkb m A n.
Proof. intros m A n bs H. exists bs. exact H. Qed.

Lemma junk8_of : forall m A w, rw_cells rsegs m A [C8 w] -> junk8 m A.
Proof. intros m A w H. exists w. exact H. Qed.

Lemma spill_split : forall m X j0 j1 j2 j3 j4 h, rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 h) ->
  junkb m X 24 /\ rw_cells rsegs m (X + 24) [C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 INV9)] /\ junkb m (X + 40) 104 /\
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 h)] /\ junk8 m (X + 152) /\ junk8 m (X + 160) /\
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 MS_NS)] /\ rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 STALE_NS)] /\
  junk8 m (X + 184) /\ junk8 m (X + 192) /\ junk8 m (X + 200) /\
  rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 W0X0)] /\
  junk8 m (X + 216) /\ junk8 m (X + 224) /\ junkb m (X + 232) 4.
Proof.
  intros m X j0 j1 j2 j3 j4 h H.
  apply slot_ser_chain.spill_iff in H as (P0 & P24 & P32 & P40 & P144 & P152 & P168 & P176 & P184 & P208 & P216).
  split; [exact (junkb_of _ _ _ _ P0)|]. split; [exact P24|]. split; [exact P32|].
  split; [exact (junkb_of _ _ _ _ P40)|]. split; [exact P144|].
  split; [eapply (junk8_sub m _ _ 16 j2 0 P152); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 16 j2 8 P152); cbn; lia|].
  split; [exact P168|]. split; [exact P176|].
  split; [eapply (junk8_sub m _ _ 24 j3 0 P184); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 24 j3 8 P184); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 24 j3 16 P184); cbn; lia|].
  split; [exact P208|].
  split; [eapply (junk8_sub m _ _ 20 j4 0 P216); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 20 j4 8 P216); cbn; lia|].
  eapply (junkb_sub m _ _ 20 j4 16 4 P216); cbn; lia.
Qed.
