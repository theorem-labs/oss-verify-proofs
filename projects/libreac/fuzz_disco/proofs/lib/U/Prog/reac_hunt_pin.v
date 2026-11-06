From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_pin_c.
Import ListNotations.
Open Scope Z_scope.

Lemma store_ok0 : forall m a n (j : nat), wr_at rsegs m a n -> Z.of_nat j <= n -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m a n j H Hj. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok rsegs m a n 0 j H); lia.
Qed.

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac zcu HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; try change (bv_wrap 64 7) with 7 in HC; rewrite ?land7 in HC;
  zify_bool HC; Z.div_mod_to_equations; lia.

Theorem reac_hunt_pin_holds : reac_hunt_pin_contract.
Proof.
  unfold reac_hunt_pin_contract, REAC_HUNT_PIN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m h E Hh H8 HW. subst a0.
  pose proof HW as (HWl & HWh & _).
  pose proof (store_ok0 m (h + 432) 8 4%nat HW ltac:(lia)) as ST.
  assert (ST2 : store_ok rsegs (write_to_mem m (Z_to_bv 64 (h + 432)) (le4 (Z_to_bv 64 1))) (wa (h + 436)) 4 = true).
  { change (Z_to_bv 64 (h + 432)) with (wa (h + 432)). replace (h + 436) with (h + 432 + 4) by lia.
    apply (wr_at_store_ok rsegs _ (h + 432) 8 4 4%nat); [apply wr_at_write; exact HW | lia | lia]. }
  step. if_cases HCa; [exfalso; zcu HCa | ]. step. step. if_cases HCb; [exfalso; zcu HCb | ].
  step. step. step. step.
  change (Z_to_bv 64 (h + 432)) with (wa (h + 432)). change (Z_to_bv 64 (h + 436)) with (wa (h + 436)).
  apply evt_done. cbv beta. do 2 eexists. split; [reflexivity |].
  split.
  { apply munch_write; [ | lia | rewrite length_le4; cbn; lia | cbn [inside]; rewrite length_le4; cbn; lia].
    apply munch_write; [apply munch_refl | lia | rewrite length_le4; cbn; lia | cbn [inside]; rewrite length_le4; cbn; lia]. }
  split; [apply wmono_write, wmono_write, wmono_refl |].
  split.
  - apply bytes_at_write_other; [ | lia | rewrite ?length_le4; cbn; lia | rewrite ?length_le4; cbn; lia].
    apply bytes_at_write_same; rewrite ?length_le4; cbn; lia.
  - apply bytes_at_write_same; rewrite ?length_le4; cbn; lia.
Qed.
