From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memset_c asan_set_shadow_c.
Import ListNotations.
Open Scope bv_scope.

Lemma asan_cells_memset_reads : forall m, asan_cells m ->
  ov_read_bytes rsegs m (wa 0x9faf0) 8 = Some (le8 (wa 0xa1938)) /\
  ov_read_bytes rsegs m (wa 0xa1938) 8 = Some (le8 (wa 0x98010)).
Proof.
  intros m Hc. unfold asan_cells in Hc.
  destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRS & HG).
  unfold GOT_REAL_MEMSET, REAL_MEMSET, MUSL_MEMSET in *.
  split.
  - replace (wa 0x9faf0) with (wa (0x9faf0 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x9faf0 (le8 (wa 0xa1938)) 0 8 HG ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity.
  - replace (wa 0xa1938) with (wa (0xa1938 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0xa1938 (le8 (wa 0x98010)) 0 8 HRS ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity.
Qed.

Ltac set_shadow_proof HM :=
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk;
  cbv zeta; intros HSh Hrw Hc Hinv;
  let R1 := fresh "R1" in let R2 := fresh "R2" in
  destruct (asan_cells_memset_reads m Hc) as [R1 R2];
  step; step; step; step; step; step;
  eapply evt_mono;
  [ unfold memset_contract, MEMSET in HM; eapply HM; eassumption
  | let ms' := fresh "ms'" in let Hp := fresh "Hp" in intros ms' Hp; unfold memset_post in Hp;
    destruct Hp as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & RW);
    unfold asan_set_shadow_post;
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m';
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; exact RW ].

Theorem asan_set_shadow_00_holds : memset_contract -> asan_set_shadow_00_contract.
Proof.
  intros HM. unfold asan_set_shadow_00_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_00.
  set_shadow_proof HM.
Qed.

Theorem asan_set_shadow_f5_holds : memset_contract -> asan_set_shadow_f5_contract.
Proof.
  intros HM. unfold asan_set_shadow_f5_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_F5.
  set_shadow_proof HM.
Qed.

Theorem asan_set_shadow_f8_holds : memset_contract -> asan_set_shadow_f8_contract.
Proof.
  intros HM. unfold asan_set_shadow_f8_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_F8.
  set_shadow_proof HM.
Qed.
