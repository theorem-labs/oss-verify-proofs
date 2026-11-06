(* check_forward walk, fuzz_wire ubsan 6e91fe0b5555 0x12f3c..0x12ff8 (fuzz_wire.c:50-70); new. rp_fwd_class is the
   named Section hypothesis HFC (its UBSan contract, U/Prog/rp_fwd_class_c.v), called first (0x12f5c) with f,
   n, bcast as check_forward got them. The harness's want (RP_FWD_DROP = 0 unless n >= 18 && f[12..13] == 88 19 &&
   (!bcast || f[0] == 0xff), then f[16..17] == 00 00 ? RP_FWD_AUDIO = 1 : RP_FWD_CTRL = 2; in a1 at 0x12f60..0x12fe8)
   is fwd_class_result n bcast bs on each of its paths, the value rp_fwd_class's post puts in a0, so the `bne a0, a1` at
   0x12fa4 falls through and the abort() call at 0x12ff0 is unreachable. bcast is tested as the whole register by both,
   so it needs no premise. UBSan traps: the unimp at 0x12ff4, reached from 0x12f6c (f >= 2^64 - 12), 0x12f80
   (f > 2^64 - 14), 0x12fc4 (f >= 2^64 - 16) and 0x12fd4 (f > 2^64 - 18), each refuted by bytes_at with n >= 18
   bytes: f + 18 <= 2^64. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes rp_fwd_class_c check_forward_c.
Import ListNotations.
Open Scope Z_scope.

(* Each test the model holds whose answer a path fixed. *)
Ltac eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.

Ltac fwd_eval :=
  cbv beta iota zeta delta [fwd_class_result fwd_byte];
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  eqb_facts; cbn [andb orb negb]; reflexivity.

Ltac byte_cond H := zify_cond H; rewrite ?zxb_u in H.

(* 0x12fa4 `bne a0, a1` .. 0x12fbc `ret`, with a1 = v, the want, and the model rewritten to it. *)
Ltac fwd_done v sp :=
  lazymatch goal with |- context [fwd_class_result ?n ?b ?bs] => replace (fwd_class_result n b bs) with v by fwd_eval end;
  step; first [if_true | if_false];
  do 6 step;
  apply evt_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  assumption.

(* 0x12fc0: is_audio(f) ? RP_FWD_AUDIO : RP_FWD_CTRL. *)
Ltac fwd_audio sp :=
  let H16 := fresh "H16" in let H17 := fresh "H17" in
  do 2 step; if_false; do 2 step; if_cases H16;
  [ byte_cond H16; do 2 step; fwd_done 2 sp
  | byte_cond H16; do 2 step; if_false; do 2 step; if_cases H17;
    [ byte_cond H17; do 2 step; fwd_done 1 sp | byte_cond H17; do 2 step; fwd_done 2 sp ] ].

Section C.
Hypothesis HFC : rp_fwd_class_contract.

Theorem check_forward_holds : check_forward_contract.
Proof.
  unfold check_forward_contract, CHECK_FORWARD, CHECK_FORWARD_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA NZ ST HLO DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof BA as (B0 & B1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 5 step.
  do 4 step.
  eapply evt_cut; [eapply HFC; intros ?; split; [ exact NZ | ]; split; [ | exact BA ]; lia |].
  intros ? (? & ? & ? & ->).
  replace (ret_pc (Z_to_bv 64 77664)) with (Z_to_bv 64 77664) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 2 step. if_cases HL.
  - (* n < 18: DROP *)
    zify_cond HL. step. fwd_done 0 sp.
  - zify_cond HL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 0 BA ltac:(lia)) as R0;
      pose proof (rd1 mm _ bs 12 BA ltac:(lia)) as R12; pose proof (rd1 mm _ bs 13 BA ltac:(lia)) as R13;
      pose proof (rd1 mm _ bs 16 BA ltac:(lia)) as R16; pose proof (rd1 mm _ bs 17 BA ltac:(lia)) as R17 end.
    change (Z.of_nat 0) with 0 in R0.
    replace (wa (bv_unsigned a0 + 0)) with a0 in R0 by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
    do 2 step. if_false. do 3 step. if_cases H12.
    { (* f[12] != 0x88: DROP *) byte_cond H12. step. fwd_done 0 sp. }
    byte_cond H12. do 2 step. if_false. do 3 step. if_cases H13.
    { (* f[13] != 0x19: DROP *) byte_cond H13. step. fwd_done 0 sp. }
    byte_cond H13. step. if_cases HB.
    + (* bcast == 0 *) byte_cond HB. fwd_audio sp.
    + byte_cond HB. do 3 step. if_cases H0.
      * (* f[0] == 0xff *) byte_cond H0. fwd_audio sp.
      * (* bcast and f[0] != 0xff: DROP *) byte_cond H0. step. fwd_done 0 sp.
Qed.

End C.
