From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_upd460 : forall m c cs (k : Z) bs,
  bytes_at rsegs m c cs -> length cs = 460%nat -> 0 <= k -> k + Z.of_nat (length bs) <= 460 ->
  bytes_at rsegs (write_to_mem m (wa (c + k)) bs) c (upd_bytes cs (Z.to_nat k) bs) /\
  length (upd_bytes cs (Z.to_nat k) bs) = 460%nat.
Proof.
  intros m c cs k bs HB HL Hk Hn. split.
  - apply bytes_at_write_inside; [exact HB | exact Hk | rewrite HL; lia].
  - rewrite upd_bytes_length; [exact HL | rewrite HL; lia].
Qed.

Lemma munch_upd460 : forall m0 m c (k : Z) bs,
  munch [(c, c + 460)] m0 m -> 0 <= c -> c + 460 <= 2^64 -> 0 <= k -> k + Z.of_nat (length bs) <= 460 ->
  munch [(c, c + 460)] m0 (write_to_mem m (wa (c + k)) bs).
Proof.
  intros m0 m c k bs MU Hc Hc' Hk Hn. apply munch_write; [exact MU | lia | lia |].
  cbn [inside]. left. lia.
Qed.

Ltac tx_len := rewrite ?length_le1, ?length_le4, ?length_le8; cbn; lia.

Ltac tx_store t k n :=
  lazymatch goal with
  | HW : wr_at rsegs ?m t 460, HB : bytes_at rsegs ?m t ?Tc, HL : length ?Tc = 460%nat,
    MU : munch [(t, t + 460)] ?m0 ?m, WM : wmono rsegs ?m0 ?m |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m (wa (t + k)) n = true) by (apply (wr_at_store_ok rsegs m t 460 k n HW); lia);
    zstep;
    change (Z_to_bv 64 (t + k)) with (wa (t + k));
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem m (wa (t + k)) ?bs) _) =>
      let HW' := fresh "HW" in let HB' := fresh "HB" in let HL' := fresh "HL" in
      pose proof (wr_at_write rsegs m t 460 (wa (t + k)) bs HW) as HW';
      destruct (bytes_at_upd460 m t Tc k bs HB HL ltac:(lia) ltac:(tx_len)) as [HB' HL'];
      apply (munch_upd460 m0 m t k bs) in MU; [ | lia | lia | lia | tx_len ];
      apply (wmono_write rsegs m0 m (wa (t + k)) bs) in WM;
      clear HS HW HB HL
    end
  end.
