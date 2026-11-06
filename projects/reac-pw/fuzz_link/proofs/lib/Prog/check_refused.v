(* check_refused (fuzz_link.c:519-531), PLAIN build: the walk of its contract
   (lib/Prog/check_refused_c.v) on the plain image. Two instructions on the returning path:
   bne a1, a0, +8 (to the abort path at +0x08, not taken: the premise says a0 = a1); ret.
   No register is written and no memory is touched. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf hp_cka_kit check_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

Theorem check_refused_holds : check_refused_contract.
Proof.
  unfold check_refused_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ H. exact H.
  - unfold leaf_walk, CHECK_REFUSED.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HP MI ST LO SP.
    change (a0 = a1) in HP. subst a1.
    step. if_false. step.
    ret_unchanged MI ST.
Qed.

Print Assumptions check_refused_holds.
