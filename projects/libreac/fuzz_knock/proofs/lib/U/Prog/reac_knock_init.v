From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require Import reac_knock_init_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. vm_compute. reflexivity. Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma byte0_lit : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256) = Z_to_bv 8 0.
Proof. vm_compute. reflexivity. Qed.

Theorem reac_knock_init_holds : memset_contract -> reac_knock_init_contract.
Proof.
  intros MEMS. unfold reac_knock_init_contract, REAC_KNOCK_INIT, REAC_KNOCK_INIT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo junk NZ AL HK HMI ST LO DJ.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  assert (U40 : bv_unsigned (Z_to_bv 64 40) = 40) by reflexivity.
  carve_frame 32%nat ST.
  do 9 zstep.
  call MEMS; [exact HK | exact HMI | ].
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 40))) with 40%nat in *.
  zstep.
  if_cases T0; [exfalso; zify_cond T0; lia |].
  zstep. zstep.
  if_cases T1; [exfalso; zify_cond T1; rewrite land7_mod8 in T1; lia |].
  do 9 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  eapply rw_cells_rebytes; [eassumption | cbn; repeat split | ].
  unfold knock_cells, L_NS. cbn [cells_bytes cbytes].
  rewrite ?le4_zero, ?le8_zero, ?byte0_lit.
  cbn [repeat firstn skipn app].
  reflexivity.
Qed.
