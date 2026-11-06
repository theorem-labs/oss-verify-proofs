From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.

(* rp_fwd_class at 0x134ac (22 words). Each exit sets a0 to a literal; fin closes it by evaluating fwd_class_result
   with the branch facts the walk collected. *)

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

Local Ltac fin :=
  apply evt_done; unfold fwd_class_result, fwd_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts; do 3 eexists; reflexivity.

(* from 0x134e4: is_audio(f) *)
Local Ltac tail16 :=
  let H16 := fresh "H16" in let H17 := fresh "H17" in
  step; step; if_cases H16;
  [ zc H16; step; step; fin
  | zc H16; step; step; if_cases H17; [ zc H17; step; step; fin | zc H17; step; step; fin ] ].

Theorem rp_fwd_class_holds : rp_fwd_class_contract.
Proof.
  unfold rp_fwd_class_contract, RP_FWD_CLASS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs HB.
  step. step. if_cases HL.
  { zc HL. step. step. fin. }
  zc HL. destruct (HB HL) as [LEN BA].
  pose proof (rd1 m _ bs 0 BA ltac:(lia)) as R0. change (Z.of_nat 0) with 0 in R0.
  replace (wa (bv_unsigned a0 + 0)) with a0 in R0 by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
  pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
  pose proof (rd1 m _ bs 16 BA ltac:(lia)) as R16. change (Z.of_nat 16) with 16 in R16.
  pose proof (rd1 m _ bs 17 BA ltac:(lia)) as R17. change (Z.of_nat 17) with 17 in R17.
  remember (nth 0 bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  step. step. step. if_cases HC12.
  { zc HC12. step. step. fin. }
  zc HC12. step. step. step. if_cases HC13.
  { zc HC13. step. step. fin. }
  zc HC13. step. if_cases HZ.
  - zc HZ. tail16.
  - zc HZ. step. step. step. if_cases H0.
    + zc H0. tail16.
    + zc H0. step. step. fin.
Qed.
