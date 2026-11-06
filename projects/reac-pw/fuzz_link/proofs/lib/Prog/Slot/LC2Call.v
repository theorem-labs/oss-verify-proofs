(* Arm c2 (op_mark): 0x13da4 -> the call of mark_quietly. `mv a0, s7; mv a1, s2; jal 0x15d88` (0x13da4,
   0x13da8, 0x13dac; ra = 0x13db0): from model_mark's end (c2_13da4) to the SR cut c2_15d88. No memory
   is written. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

Lemma c2_call : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  c2_13da4 E i gp s ms -> evt rsegs (c2_post E (ms_mem ms) (c2_15d88 E i gp s)) ms.
Proof.
  intros E i gp s ms H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F & fc &
                 m & P & N & j0 & j1 & j2 & kbs & mbs & gbs & -> & HR).
  unfold wz.
  step. step. step.
  match goal with |- evt _ _ ?st => apply evt_done; unfold c2_post, eqv_cl; exists st end.
  split; [split|].
  - unfold c2_15d88.
    do 14 eexists. exists F, fc, m, P, N, j0, j1, j2, kbs, mbs, gbs.
    split; [reflexivity | exact HR].
  - exact (c2_seg_fp_refl _ _ m).
  - apply c2_ms_eqv_refl.
Qed.
