(* check_ret walk, fuzz_wire ubsan 6e91fe0b5555 0x12ff8..0x1305c (fuzz_wire.c:72-84); new. rp_ret_accept is the named
   Section hypothesis HRA (its UBSan contract, U/Prog/rp_ret_accept_c.v). The harness's want (n >= 14 &&
   f[12] == 0x88 && f[13] == 0x19, in s0 at 0x13004..0x13038) is ret_accept_result n bs on each of its three paths, the
   value rp_ret_accept's post puts in a0, so the `bne a0, s0` at 0x13040 falls through and the abort() call at 0x13054
   is unreachable. UBSan traps: the unimp at 0x13058, reached from 0x13010 (f >= 2^64 - 12) and 0x13024
   (f > 2^64 - 14), both refuted by bytes_at with n >= 14 bytes: f + 14 <= 2^64. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes rp_ret_accept_c check_ret_c.
Import ListNotations.
Open Scope Z_scope.

(* `lbu a2, 13(a0); addi a2, a2, -25; seqz s0, a2` past f[12] == 0x88: s0 = ret_accept_result n bs. *)
Lemma chk_ret_seqz : forall (b13 : byte) (n : Z) (bs : list byte),
  14 <= n -> ret_byte bs 12 = 0x88 -> ret_byte bs 13 = bv_unsigned b13 ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b13) + -25)) 1 = Z_to_bv 64 (ret_accept_result n bs).
Proof.
  intros b13 n bs HL H12 H13.
  unfold v_sltiu, ret_accept_result, zxb. rewrite H12, H13, zxb_u, (proj2 (Z.ltb_ge _ _) HL).
  pose proof (byte_range b13) as X13.
  destruct (Z.eq_dec (bv_unsigned b13) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r.
    rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b13 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Section C.
Hypothesis HRA : rp_ret_accept_contract.

(* 0x1303c `jal rp_ret_accept` .. 0x13050 `ret`, with s0 = the want the harness computed. *)
Ltac ret_tail :=
  step;
  lazymatch goal with BA : bytes_at _ _ _ ?bs |- _ =>
    eapply evt_cut; [eapply HRA; intros ?; split; [ assumption | ]; split; [ | exact BA ]; lia |] end;
  intros ? (? & ? & ->);
  replace (ret_pc (Z_to_bv 64 77888)) with (Z_to_bv 64 77888) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

Ltac ret_done sp :=
  step; first [if_true | if_false];
  do 4 step;
  apply evt_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  assumption.

Theorem check_ret_holds : check_ret_contract.
Proof.
  unfold check_ret_contract, CHECK_RET, CHECK_RET_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA NZ ST HLO DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof BA as (B0 & B1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.
  do 2 step. if_cases HL.
  - (* n < 14: want = 0 *)
    zify_cond HL.
    assert (W : ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    step. ret_tail. rewrite W. ret_done sp.
  - zify_cond HL.
    do 2 step. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 12 BA ltac:(lia)) as R12; pose proof (rd1 mm _ bs 13 BA ltac:(lia)) as R13 end.
    change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    do 3 step. if_cases HC.
    + (* f[12] != 0x88: want = 0 *)
      zify_cond HC. rewrite zxb_u in HC.
      assert (W : ret_accept_result (bv_unsigned a1) bs = 0).
      { unfold ret_accept_result, ret_byte. rewrite <- E12.
        rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC). reflexivity. }
      step. ret_tail. rewrite W. ret_done sp.
    + (* f[12] == 0x88: want = (f[13] == 0x19) *)
      zify_cond HC. rewrite zxb_u in HC.
      do 2 step. if_false.
      do 4 step.
      rewrite (chk_ret_seqz b13 (bv_unsigned a1) bs HL)
        by (unfold ret_byte; rewrite <- ?E12, <- ?E13; first [exact HC | reflexivity]).
      ret_tail. ret_done sp.
Qed.

End C.
