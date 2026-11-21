(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma arm_LIT_eq : forall s c r,
  arm_LIT (mkW s c r)
  = if ir_left r =? 0 then ALeave (mkW s c r)
    else ARun tt (mkW (iset_mode s LEN)
                      (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s))))
                      (irset_left (irset_put r (ir_put r + 1)) (wrap32 (ir_left r - 1)))).
Proof.
  intros s c r. unfold arm_LIT, abind, gr, gs, uc, ur, us, set_mode, aleave.
  cbn [w_s w_c w_r wset_s wset_c wset_r]. destruct (ir_left r =? 0); reflexivity.
Qed.

Section ArmLIT.

  Theorem arm_LIT_sim : arm_stmt LIT.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LIT) with arm_LIT. rewrite arm_LIT_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    change (arm6_pc LIT) with 0x1d12c.
    arm_begin C HM HRC HX HF HV HP.
    pose proof (is6_length _ _ _ _ Msc) as C92.
    destruct (Z.eq_dec (ir_left r) 0) as [E0|E0].
    -
      rewrite (proj2 (Z.eqb_eq _ _) E0).
      arm_symex ilS 6%nat [false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r [ir_ret r mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1d12c) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      exists R', M, pc6_leave. split; [by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
      split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl|].
      symex_reg HR' (9%bv : reg) as G8'.
      unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r].
      repeat match goal with |- _ /\ _ => split end;
        try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
      rewrite G8'. apply zw_neg_mod.
    -
      rewrite (proj2 (Z.eqb_neq _ _) E0).
      arm_symex ilS 30%nat [true; true] [RVal (EVar 45%nat); RVal (ELit (JT LEN))] (@nil (Z * expr)) [(45%nat, 256)] v r
        [is_length s mod 256] NoVals F0
        (mkst R (Z_to_bv 64 0x1d12c) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      { apply (code_read_op s6_segs M (cv_S v + 108) (is_length s)) in C92. rewrite code_op_eq in C92. exact C92. }
      set (M1 := wbytes M (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 (is_length s mod 256))) in Hms.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in Hms.
      exists R', M2, 0x1e3a0. split; [by_run Hms|].
      set (s' := iset_mode s LEN). set (c' := icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))).
      set (r' := irset_left (irset_put r (ir_put r + 1)) (wrap32 (ir_left r - 1))).
      pose proof (icset_outbuf_facts c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      assert (Hleft1 : wrap32 (ir_left r - 1) = ir_left r - 1) by (apply wrap32_pred; clear - E0 Rlf0 Rpt0 Rpl CP0; lia).
      assert (HM1 : LMEM v (mkW s c' r') M1).
      { subst M1 c'. apply (LMEM_store_out v C s c r r' M _ _ HM); [clear - E0 Rpt0 Rlf0 Rpl; lia | exact Col | reflexivity | | reflexivity ].
        rewrite wrap8_mod. reflexivity. }
      assert (HM2 : LMEM v (mkW s' c' r') M2).
      { subst M2 s'. apply (LMEM_store_scalar v C s c' r' _ M1 8 _ HM1); [lia | cbn; lia | cbn [r' ir_put irset_left irset_put]; clear - E0 Rpt0 Rlf0 Rpl; lia | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s LEN (lm_sc _ _ _ HM1)); [clear - CS; lia | unfold is6_SIZE; clear - CS; lia]. }
      cbn [arm_post]. split; [| split; [| split]].
      + subst s'. reflexivity.
      +
        split; [exact HM2|]. split.
        { subst M2 M1. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia].
          apply (RETC_other v C); [| clear - CP0 Rpt0; lia | clear - CP0 Rpt0 Rpl Rlf0 E0; cbn; lia | specialize (CfP ltac:(clear - Rpt0 Rpl Rlf0 E0; lia)); unfold sep in CfP; clear - CfP Rpt0 Rpl Rlf0 E0; cbn; lia].
          eapply RETC_regs; [exact HRC | reflexivity]. }
        split.
        *
          unfold LX; cbn [w_s w_c w_r]. subst s' c' r'. cbn [is_wrap is_wbits is_mode is_flags iset_mode ir_out ir_left ir_in ir_ret irset_left irset_put].
          rewrite F11. destruct s; cbn in *.
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj Xmsg Xhd))))))).
          -- unfold live_mode, LEN, FLAGS, HCRC, SYNC. lia.
          -- destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | exfalso]. rewrite Hmode in XM. unfold LIT, HEAD, BAD in XM. lia.
        *
          unfold LREG_arm. split; [| split].
          -- apply (LFIX_frame v R R' _ HF Hfr). reflexivity.
          -- symex_reg HR' (1%bv : reg) as G1'. symex_reg HR' (19%bv : reg) as G18'.
             unfold LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_left irset_put].
             repeat match goal with |- _ /\ _ => split end;
               try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
             ++ rewrite G18'. f_equal. lia.
             ++ rewrite G1', Hleft1. rewrite szwrap32_small by lia. reflexivity.
          -- symex_reg HR' (9%bv : reg) as G8'. intros _; exact G8'.
      +
        subst s'. split; [reflexivity | split; reflexivity].
      +
        subst M2. apply (MFRAME_store v (ir_put r) (ir_put r + 1) (ir_put r + 1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1) M M); [apply MFRAME_refl | lia | clear - CP0 Rpt0; lia | clear - CP0 Rpt0 Rpl Rlf0; cbn; lia |].
        right; right; right. cbn. clear; lia.
  Qed.
End ArmLIT.
End FXG.
