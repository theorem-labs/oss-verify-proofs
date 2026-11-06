From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_preds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require uslot_known.
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

Lemma rw_cons_at : forall m A B c cs, rw_cells rsegs m A (c :: cs) -> B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs.
Proof. intros m A B c cs H ->. exact (uslot_known.rw_cons_split m A c cs H). Qed.

Lemma spill_split : forall m X j0 j1 j2 j3 j4 j5 j6 h, rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 j5 j6 h X) ->
  junkb m X 32 /\ rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] /\ junkb m (X + 48) 72 /\
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 STALE1)] /\ rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] /\
  junk8 m (X + 136) /\ rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 MS_NS)] /\
  junk8 m (X + 152) /\ junk8 m (X + 160) /\ rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] /\
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] /\
  rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] /\
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] /\
  junk8 m (X + 208) /\ rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] /\
  junk8 m (X + 224) /\ junk8 m (X + 232) /\ junk8 m (X + 240) /\ junk8 m (X + 248) /\
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] /\ junkb m (X + 264) 4.
Proof.
  intros m X j0 j1 j2 j3 j4 j5 j6 h H0. unfold spill_cells in H0.
  destruct (rw_cons_at m _ (X + 32) _ _ H0 ltac:(cbn [csize]; lia)) as [P0 H1].
  destruct (rw_cons_at m _ (X + 40) _ _ H1 ltac:(cbn [csize]; lia)) as [P32 H2].
  destruct (rw_cons_at m _ (X + 48) _ _ H2 ltac:(cbn [csize]; lia)) as [P40 H3].
  destruct (rw_cons_at m _ (X + 120) _ _ H3 ltac:(cbn [csize]; lia)) as [P48 H4].
  destruct (rw_cons_at m _ (X + 128) _ _ H4 ltac:(cbn [csize]; lia)) as [P120 H5].
  destruct (rw_cons_at m _ (X + 136) _ _ H5 ltac:(cbn [csize]; lia)) as [P128 H6].
  destruct (rw_cons_at m _ (X + 144) _ _ H6 ltac:(cbn [csize]; lia)) as [P136 H7].
  destruct (rw_cons_at m _ (X + 152) _ _ H7 ltac:(cbn [csize]; lia)) as [P144 H8].
  destruct (rw_cons_at m _ (X + 168) _ _ H8 ltac:(cbn [csize]; lia)) as [P152 H9].
  destruct (rw_cons_at m _ (X + 176) _ _ H9 ltac:(cbn [csize]; lia)) as [P168 H10].
  destruct (rw_cons_at m _ (X + 184) _ _ H10 ltac:(cbn [csize]; lia)) as [P176 H11].
  destruct (rw_cons_at m _ (X + 192) _ _ H11 ltac:(cbn [csize]; lia)) as [P184 H12].
  destruct (rw_cons_at m _ (X + 200) _ _ H12 ltac:(cbn [csize]; lia)) as [P192 H13].
  destruct (rw_cons_at m _ (X + 208) _ _ H13 ltac:(cbn [csize]; lia)) as [P200 H14].
  destruct (rw_cons_at m _ (X + 216) _ _ H14 ltac:(cbn [csize]; lia)) as [P208 H15].
  destruct (rw_cons_at m _ (X + 224) _ _ H15 ltac:(cbn [csize]; lia)) as [P216 H16].
  destruct (rw_cons_at m _ (X + 256) _ _ H16 ltac:(cbn [csize]; lia)) as [P224 H17].
  destruct (rw_cons_at m _ (X + 264) _ _ H17 ltac:(cbn [csize]; lia)) as [P256 P264].
  split; [exact (junkb_of _ _ _ _ P0)|]. split; [exact P32|]. split; [exact P40|].
  split; [exact (junkb_of _ _ _ _ P48)|]. split; [exact P120|]. split; [exact P128|].
  split; [exact (rw_c8 _ _ _ P136)|]. split; [exact P144|].
  split; [eapply (junk8_sub m _ _ 16 j3 0 P152); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 16 j3 8 P152); cbn; lia|].
  split; [exact P168|]. split; [exact P176|]. split; [exact P184|]. split; [exact P192|]. split; [exact P200|].
  split; [exact (rw_c8 _ _ _ P208)|]. split; [exact P216|].
  split; [eapply (junk8_sub m _ _ 32 j5 0 P224); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 32 j5 8 P224); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 32 j5 16 P224); cbn; lia|].
  split; [eapply (junk8_sub m _ _ 32 j5 24 P224); cbn; lia|].
  split; [exact P256|]. exact (junkb_of _ _ _ _ P264).
Qed.
