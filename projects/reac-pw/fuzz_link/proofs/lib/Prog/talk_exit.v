(* talk, PLAIN build: the epilogue fragment F_exit (lib/Prog/talk_defs.v), 0x1584c .. 0x15884:
   thirteen `ld` from the saved cells, `addi sp, sp, 0x90`, `ret`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Local Open Scope Z_scope.

Lemma F_exit_ok : F_exit_spec.
Proof.
  unfold F_exit_spec, saved_cells.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SP RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 -> HSP FR HQ.
  do 15 step.
  apply evt_done. exact HQ.
Qed.

Print Assumptions F_exit_ok.
