From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PvNum.
Import ListNotations.
Open Scope Z_scope.

Lemma stk_C4 : forall m a, stk rsegs m a (a + 4) -> exists w, rw_cells rsegs m a [C4 w].
Proof.
  intros m a ST. destruct (stk_bytes rsegs m a (a + 4) ST ltac:(lia)) as (bs & L & Bb).
  replace (Z.to_nat (a + 4 - a)) with 4%nat in L by lia.
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4.
    rewrite unsigned_lit_wrap, (Z_to_le_bytes_mod 4 (bytes_le_to_Z bs) 64) by lia.
    rewrite <- L, pvn_le_back. exact Bb.
  - cbn [cells_size csize]. destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|].
    intros i Hi. apply (S3 (a + i)). lia.
Qed.

Lemma guard_wr : forall m i, 0 <= i < 8 ->
  writable_at rsegs m (0x23f98 + i) /\ writable_at rsegs m (0x555b8 + i).
Proof.
  intros m i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; split; unfold writable_at, wview;
    (destruct (m _); [discriminate|]); vm_compute; discriminate.
Qed.

Lemma errno_rd : forall m i, 0 <= i < 4 -> exists b, mrd rsegs m (wa (0x352a4 + i)) = Some b.
Proof.
  intros m i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]]; unfold mrd; (destruct (m _) as [b|]; [exists b; reflexivity|]);
    vm_compute; eexists; reflexivity.
Qed.

Lemma errno_C4 : forall m, (forall i, 0 <= i < 4 -> writable_at rsegs m (0x352a4 + i)) ->
  exists w, rw_cells rsegs m 0x352a4 [C4 w].
Proof.
  intros m HW. apply stk_C4. split; [lia|]. split; [lia|]. intros a Ha.
  split; [replace a with (0x352a4 + (a - 0x352a4)) by lia; apply HW; lia|].
  replace a with (0x352a4 + (a - 0x352a4)) by lia. apply errno_rd. lia.
Qed.
