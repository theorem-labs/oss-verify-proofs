(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section HeadArm.

  Lemma arm_HEAD_sq0 : forall s c r, REGS c r -> is_mode s = HEAD -> is_wrap s = 5 -> SQ (arm_HEAD ivar_ref (mkW s c r)).
  Proof.
    intros s c r HR E HWR. unfold arm_HEAD. arun3 gs_eq. regs_open HR.
    rewrite HWR. change (5 =? 0) with false. cbv iota.
    aflat.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply SQ_bind_run; [exact EQ|]. cbv beta iota.
      aflat. arun3 HOLD_eq. change (negb (Z.land 5 2 =? 0)) with false. cbn [andb].

      aflat. arun3 BITS_eq.
      assert (BADc : forall msg s1 c1 r', SQ (go_bad msg (mkW s1 c1 r'))).
      { intros msg s1 c1 r'. unfold go_bad. arun3 set_msg_eq. rewrite set_mode_eq. exact I. }
      acase3 Chk; [apply BADc|].
      aflat. arun3 BITS_eq.
      acase3 Ccm; [apply BADc|].
      aflat. arun3 DROPBITS_eq. aflat. arun3 BITS_eq. cbv zeta.
      (* zlib 1.4: the window-size check comes first, the wbits store after it *)
      aflat. arun3 gs_eq.
      acase3 Cws; [apply BADc|].
      aflat. apply SQ_bind_any.
      { lazymatch goal with |- SQ ((if ?cnd then _ else _) _) => destruct cnd end; [rewrite us_eq|rewrite aret_eq]; exact I. }
      intros u w1. destruct w1 as [s1 c1 r1']. aflat. arun3 aux_ref. aflat. arun3 us_eq. aflat. arun3 set_adler_check_eq. aflat. arun3 HOLD_eq. aflat. arun3 set_mode_eq.
      rewrite INITBITS_eq. exact I.
    - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. exact Hb1.
  Qed.

  Lemma arm_HEAD_sq : arm_sq HEAD (arm_HEAD ivar_ref).
  Proof. intros s c r HW [HWR _] E. winv_open2 HW E HC HR. exact (arm_HEAD_sq0 s c r HR E HWR). Qed.

End HeadArm.
