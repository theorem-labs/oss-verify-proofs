From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import RcLib RcLeafLib.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import reac_box_catalogue_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_box_catalogue_holds : reac_box_catalogue_contract.
Proof.
  unfold reac_box_catalogue_contract, REAC_BOX_CATALOGUE, BOX_CATALOGUE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c
    -> Hpre.
  destruct (Z.eqb_spec c 0) as [E|E].
  - subst c. step.
    rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb].
    step. step. step.
    apply evt_done. exists a1, m. split; reflexivity.
  - destruct Hpre as [|[H8 HW]]; [contradiction|].
    pose proof HW as (HWl & HWh & _).
    pose proof (rcl_store_ok rsegs m c 8 8%nat HW ltac:(lia)) as ST.
    step.
    rewrite (rcl_eqb c 0) by lia.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    step. step.
    rewrite (unsigned_lit c) by lia. rewrite rcl_land7. rewrite H8. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb negb].
    step. step. step. step. step.
    change (Z_to_bv 64 c) with (wa c).
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [apply bytes_at_write_same; rewrite ?length_le8; lia|].
    split; [apply munch_write; [apply munch_refl | lia | rewrite ?length_le8; lia | cbn [inside]; rewrite ?length_le8; lia]|].
    split; [apply wmono_write, wmono_refl|].
    intros MI. apply mem_inv_store; [exact MI | rewrite length_le8; exact ST].
Qed.
