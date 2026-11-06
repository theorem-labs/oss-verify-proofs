From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes is_tagged_reac_c.
Import ListNotations.
Open Scope Z_scope.

(* is_tagged_reac at 0x137e8 (24 words, UBSan build only). UBSan traps: the unimp at 0x13844, reached from 0x137e8
   (f = 0: refuted by the premise a0 <> 0), 0x137f0 (f >= 2^64 - 12), 0x13804 (f > 2^64 - 14), 0x13814 (f > 2^64 - 17)
   and 0x13828 (f > 2^64 - 18) (all four refuted by bytes_at with 18 <= length bs: f + 18 <= 2^64). *)

Lemma seqz_byte : forall b : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0).
Proof.
  intros b. unfold v_sltiu, zxb. rewrite zxb_u. pose proof (byte_range b) as X.
  destruct (Z.eq_dec (bv_unsigned b) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E).
    rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

Local Ltac fin :=
  apply evt_done; rewrite ?seqz_byte; unfold tagged_result, tag_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts;
  repeat match goal with |- context [Z.eqb ?x ?c] => destruct (Z.eqb x c) end;
  do 2 eexists; reflexivity.

Theorem is_tagged_reac_holds : is_tagged_reac_contract.
Proof.
  unfold is_tagged_reac_contract, IS_TAGGED_REAC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    NZ LEN BA.
  pose proof BA as (B0 & B1 & _).
  pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
  pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
  pose proof (rd1 m _ bs 16 BA ltac:(lia)) as R16. change (Z.of_nat 16) with 16 in R16.
  pose proof (rd1 m _ bs 17 BA ltac:(lia)) as R17. change (Z.of_nat 17) with 17 in R17.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  step. if_false. step. step. if_false.
  step. step. step. if_cases H81.
  { zc H81. step. step. fin. }
  zc H81. step. step. if_false. step. step. if_cases H13.
  { zc H13. step. step. fin. }
  zc H13. step. step. if_false. step. step. step. if_cases H16.
  { zc H16. step. step. fin. }
  zc H16. step. step. if_false. do 4 step. fin.
Qed.
