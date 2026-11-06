(* check_downstream walk, fuzz_wire ubsan 6e91fe0b5555 0x1305c..0x1311c (fuzz_wire.c:86-98); new. rp_ds_accept is the
   named Section hypothesis HDA (its UBSan contract, U/Prog/rp_ds_accept_c.v). The harness's want (n >= 18 &&
   (w_is_reac(f, 12) || (w_is_tag(f) && w_is_reac(f, 16))), in s0 at 0x13068..0x130f4) is ds_accept_result n bs on each
   of its seven paths, the value rp_ds_accept's post puts in a0, so the `bne a0, s0` at 0x130fc falls through and the
   abort() call at 0x13114 is unreachable. UBSan traps: the unimp at 0x13110, reached from 0x13074 / 0x130a4 / 0x130f0
   (f >= 2^64 - 12), 0x13088 / 0x130b4 (f > 2^64 - 14), 0x130c4 (f >= 2^64 - 16) and 0x130d8 (f > 2^64 - 18), each
   refuted by bytes_at with n >= 18 bytes: f + 18 <= 2^64. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes rp_ds_accept_c check_downstream_c.
Import ListNotations.
Open Scope Z_scope.

(* `addi r, b, -c; seqz s, r` on a loaded byte b: s = (b == c). *)
Lemma chk_seqz_byte : forall (b : byte) c k, 0 <= c < 256 -> k = - c ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + k)) 1 = Z_to_bv 64 (if bv_unsigned b =? c then 1 else 0).
Proof.
  intros b c k Hc ->. pose proof (byte_range b) as Xb. unfold zxb. rewrite zxb_u.
  destruct (Z.eqb_spec (bv_unsigned b) c) as [E|E].
  - rewrite E. replace (c + - c) with 0 by lia. vm_compute. reflexivity.
  - unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + - c) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* Each byte test the model holds whose answer a path fixed. *)
Ltac eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.

Ltac ds_eval :=
  cbv beta iota zeta delta [ds_accept_result ds_byte];
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  eqb_facts; cbn [andb orb negb]; reflexivity.

Section C.
Hypothesis HDA : rp_ds_accept_contract.

(* 0x130f8 `jal rp_ds_accept` .. 0x1310c `ret`, with s0 = the want the harness computed, the model rewritten to it. *)
Ltac ds_tail v :=
  step;
  lazymatch goal with BA : bytes_at _ _ _ ?bs |- _ =>
    eapply evt_cut; [eapply HDA; intros ?; split; [ assumption | ]; split; [ | exact BA ]; lia |] end;
  intros ? (? & ? & ->);
  replace (ret_pc (Z_to_bv 64 78076)) with (Z_to_bv 64 78076) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
  lazymatch goal with |- context [ds_accept_result ?n ?bs] => replace (ds_accept_result n bs) with v by ds_eval end.

Ltac ds_done sp :=
  step; first [if_true | if_false];
  do 4 step;
  apply evt_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  assumption.

Ltac byte_cond H := zify_cond H; rewrite ?zxb_u in H.

Theorem check_downstream_holds : check_downstream_contract.
Proof.
  unfold check_downstream_contract, CHECK_DOWNSTREAM, CHECK_DOWNSTREAM_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA NZ ST HLO DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof BA as (B0 & B1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.
  do 2 step. if_cases HL.
  - (* n < 18 *)
    zify_cond HL. step. ds_tail 0. ds_done sp.
  - zify_cond HL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 12 BA ltac:(lia)) as R12; pose proof (rd1 mm _ bs 13 BA ltac:(lia)) as R13;
      pose proof (rd1 mm _ bs 16 BA ltac:(lia)) as R16; pose proof (rd1 mm _ bs 17 BA ltac:(lia)) as R17 end.
    change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
    change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
    do 2 step. if_false.
    do 3 step. if_cases H12.
    + (* f[12] != 0x88 *)
      byte_cond H12. do 2 step. if_false. do 2 step. if_cases H12b.
      * (* f[12] is neither 0x88 nor 0x81 *)
        byte_cond H12b. step. ds_tail 0. ds_done sp.
      * (* f[12] == 0x81: the tagged test *)
        byte_cond H12b. do 2 step. if_false. do 2 step. if_cases H13.
        -- (* f[13] != 0 *)
           byte_cond H13. step. ds_tail 0. ds_done sp.
        -- byte_cond H13. do 2 step. if_false. do 3 step. if_cases H16.
           ++ (* f[16] != 0x88 *)
              byte_cond H16. step. ds_tail 0. ds_done sp.
           ++ byte_cond H16. do 2 step. if_false. do 4 step.
              rewrite (chk_seqz_byte _ 25 (-25)) by lia.
              ds_tail (if bv_unsigned (nth 17 bs (Z_to_bv 8 0)) =? 25 then 1 else 0). ds_done sp.
    + (* f[12] == 0x88 *)
      byte_cond H12. do 2 step. if_false. do 3 step. if_cases H13.
      * (* f[13] != 0x19 *)
        byte_cond H13. do 2 step. if_false. step. ds_tail 0. ds_done sp.
      * byte_cond H13. do 2 step. ds_tail 1. ds_done sp.
Qed.

End C.
