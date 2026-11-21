(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Segs6u Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflRod6 InflCtx6 InflLoop6 Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require IS6 InflArmLib6.

Module InflA_LIT.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

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
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    change (arm6_pc LIT) with 0x1f0f4.
    arm_begin C HM HRC HX HF HV HP.
    pose proof (is6_length _ _ _ _ Msc) as C92.
    destruct (Z.eq_dec (ir_left r) 0) as [E0|E0].
    -
      rewrite (proj2 (Z.eqb_eq _ _) E0).
      arm_symex ilS 10%nat [false] [RVal (EVar 39%nat); RVal (EVar 45%nat); RVal (EVar 35%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r
        [ir_ret r mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1f0f4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 0)) in Hms.
      assert (HM1 : LMEM v (mkW s c r) M1).
      { subst M1. rewrite <- E0. apply (LMEM_store_leftc v C s c r r M HM); [clear - Rpt0 Rpl Rlf0; lia | reflexivity | clear - Rlf0 Rpl Rpt0 PNO; lia | reflexivity]. }
      exists R', M1, pc6_leave. split; [by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split.
      2:{ subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia]. }
      split; [exact HM1|]. split; [exact HX|]. split; [apply same_blocks_refl|].
      symex_reg HR' (27%bv : reg) as G26'.
      unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r].
      repeat match goal with |- _ /\ _ => split end;
        try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
      rewrite G26'. apply zw_neg_mod.
    -
      rewrite (proj2 (Z.eqb_neq _ _) E0).
      arm_symex ilS 24%nat [true; true]
        [RVal (EVar 39%nat); RVal (EVar 45%nat); RVal (EVar 35%nat)]
        (@nil (Z * expr)) [(45%nat, 256)] v r
        [is_length s mod 256] NoVals F0
        (mkst R (Z_to_bv 64 0x1f0f4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      { apply (code_read_op s6u_segs M (cv_S v + 108) (is_length s)) in C92. rewrite code_op_eq in C92. exact C92. }
      assert (Hleft1 : wrap32 (ir_left r - 1) = ir_left r - 1) by (apply wrap32_pred; clear - E0 Rlf0 Rpt0 Rpl CP0; lia).
      set (s' := iset_mode s LEN). set (c' := icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))).
      set (r1 := irset_left r (wrap32 (ir_left r - 1))).
      set (r' := irset_left (irset_put r (ir_put r + 1)) (wrap32 (ir_left r - 1))).
      set (M1 := wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (szwrap 32 (ir_left r - 1)))) in Hms.
      set (M2 := wbytes M1 (zw (cv_P0 v + ir_put r)) (Z_to_le_bytes 1 (is_length s mod 256))) in Hms.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16200)) in Hms.
      pose proof (icset_outbuf_facts c (arr_set (ic_outbuf c) (ir_put r) (wrap8 (is_length s)))) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      assert (HM1 : LMEM v (mkW s c r1) M1).
      { subst M1. replace (szwrap 32 (ir_left r - 1)) with (ir_left r1) by (subst r1; cbn [ir_left irset_left]; rewrite Hleft1, szwrap32_small; [reflexivity | clear - E0 Rlf0 Rpt0 Rpl CP0; lia]).
        apply (LMEM_store_leftc v C s c r r1 M HM); [clear - Rpt0 Rpl Rlf0; lia | reflexivity | subst r1; cbn [ir_left irset_left]; rewrite Hleft1; clear - E0 Rlf0 Rpl Rpt0 PNO; lia | reflexivity]. }
      assert (HM2 : LMEM v (mkW s c' r') M2).
      { subst M2 c'. apply (LMEM_store_out v C s c r1 r' M1 _ _ HM1); [subst r1; cbn; clear - E0 Rpt0 Rlf0 Rpl; lia | exact Col | reflexivity | | reflexivity | reflexivity].
        rewrite wrap8_mod. reflexivity. }
      assert (HM3 : LMEM v (mkW s' c' r') M3).
      { subst M3 s'. apply (LMEM_store_scalar v C s c' r' _ M2 8 _ HM2); [lia | cbn; lia | cbn [r' ir_put irset_left irset_put]; clear - E0 Rpt0 Rlf0 Rpl; lia | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s LEN (lm_sc _ _ _ HM2)); [clear - CS; lia | unfold is6_SIZE; clear - CS; lia]. }
      arm_disp C HM3 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M3, (arm6_pc (is_mode s')). split; [eapply msteps_trans; [| exact Hms2]; by_run Hms|].
      cbn [arm_post]. split; [| split; [| split]].
      + reflexivity.
      +
        split; [exact HM3|]. split.
        { subst M3 M2 M1. retc_tower C HRC. }
        split.
        *
          unfold LX; cbn [w_s w_c w_r]. subst s' c' r'. cbn [is_wrap is_wbits is_mode is_flags iset_mode ir_out ir_left ir_in ir_ret irset_left irset_put].
          rewrite F11. destruct s; cbn in *.
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj Xmsg (conj Xhd _)))))))).
          -- unfold live_mode, LEN, FLAGS, HCRC, SYNC. lia.
          -- destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | exfalso]. rewrite Hmode in XM. unfold LIT, HEAD, BAD in XM. lia.
          -- bk_side.
        *
          unfold LREG_arm. split; [| split].
          -- lfix_close2 Hfr2 Hfr HR'.
          -- symex_reg HR' (9%bv : reg) as G9'.
             unfold LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_left irset_put].
             regs_via2 Hfr2 Hfr.
             rewrite G9'. f_equal. lia.
          -- intros _; exact G26'.
      +
        subst s'. split; [reflexivity | split; reflexivity].
      +
        subst M3. apply (MFRAME_store v (ir_put r) (ir_put r + 1) (ir_put r + 1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        subst M2. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + 1)); [| lia | clear - CP0 Rpt0; lia | clear - CP0 Rpt0 Rpl Rlf0; cbn; lia | right; right; right; cbn; clear; lia].
        subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End ArmLIT.
End FXG.
End InflA_LIT.

Module InflA_Term.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section ArmTerm.

  Lemma arm_dead_sim : forall m, (FLAGS <= m <= HCRC \/ m = SYNC) -> arm_stmt m.
  Proof.
    intros m Hm v w R M C Hmode HE HP. exfalso.
    destruct HE as (_ & _ & HX & _). destruct w as [s c r]. open_lx HX. cbn [w_s] in Hmode.
    rewrite Hmode in Xlive. unfold live_mode in Xlive. lia.
  Qed.


  Theorem arm_BAD_sim : arm_stmt BAD.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) BAD) with arm_BAD.
    unfold arm_BAD. rewrite abind_run, ur_eq, aleave_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    exists R, M, pc6_leave. split; [change (arm6_pc BAD) with pc6_leave; apply mst_refl|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [eapply LMEM_regs; [exact HM | reflexivity ..]|].
    split.
    { open_lx HX. unfold LX; cbn [w_s w_c w_r ir_out ir_left ir_in ir_ret irset_ret]. destruct r; cbn in *.
      refine (conj Xwrap (conj Xwbits (conj Xlive (conj Xflags (conj Xin (conj _ (conj Xmsg (conj Xhd _)))))))); [unfold Z_DATA_ERROR; lia | bk_side]. }
    split; [apply same_blocks_refl|].
    open_fix HF. open_vars HV. unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
    destruct r; cbn in *. repeat (split; [assumption|]). exact (G26 Hmode).
  Qed.

  Theorem arm_DONE_sim : arm_stmt DONE.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DONE) with arm_DONE.
    unfold arm_DONE. rewrite abind_run, ur_eq, aleave_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    change (arm6_pc DONE) with 0x214c4.
    arm_begin C HM HRC HX HF HV HP.
    arm_symex ilS 4%nat (@nil bool) NoReads (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x214c4) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    exists R', M, pc6_leave. split; [by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [eapply LMEM_regs; [exact HM | reflexivity ..]|].
    split.
    { unfold LX; cbn [w_s w_c w_r ir_out ir_left ir_in ir_ret irset_ret]. destruct r; cbn in *.
      refine (conj Xwrap (conj Xwbits (conj Xlive (conj Xflags (conj Xin (conj _ (conj Xmsg (conj Xhd _)))))))); [unfold Z_STREAM_END; lia | bk_side]. }
    split; [apply same_blocks_refl|].
    symex_reg HR' (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
    destruct r; cbn in *.
    repeat match goal with |- _ /\ _ => split end;
      try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
    exact G26'.
  Qed.

  Theorem arm_MEM_sim : arm_stmt MEM.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) MEM) with arm_MEM.
    unfold arm_MEM, areturn.
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    change (arm6_pc MEM) with 0x21650.
    arm_begin C HM HRC HX HF HV HP.
    arm_symex ilS 4%nat (@nil bool) NoReads (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x21650) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    exists R', M, pc6_ret. split; [by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
    split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl|].
    symex_reg HR' (10%bv : reg) as G10'.
    split; [| unfold Z_MEM_ERROR, Z_OK; lia].
    unfold LREG_ret, INF_FRAME.
    repeat match goal with |- _ /\ _ => split end;
      try (lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end).
    exact G10'.
  Qed.
End ArmTerm.
End FXG.
End InflA_Term.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Type2 InflA_Stored InflA_Head3 InflA_Check3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflArmLib6b InflArmLib6d InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Infl6B.   (* zlib 1.4: LMEM_store_total_in, for the NEED_DICT exit *)

Module InflA_Dict1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ilI : cfg := ilSx [0x1f1ec; 0x1f430] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section DictidLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition DJS (h0 n0 b0 : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 10 = zw (ir_have r) /\ getr R 16 = zw (cv_I0 v + ir_next r) /\ getr R 14 = zw (cv_I0 v + ir_next r)
    /\ getr R 17 = zw (ir_bits r)
    /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 19 = zw b0
    /\ ir_have r + ir_next r = h0 + n0 /\ ir_bits r = b0 + 8 * (ir_next r - n0) /\ 0 <= h0 < 2 ^ 31 /\ 0 <= b0 /\ 0 <= n0.
  Definition DJE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 12 = zw (cv_I0 v + ir_next r) /\ getr R 10 = zw (ir_have r).

  Ltac open_djs HJ :=
    let X := fresh in pose proof HJ as X; unfold DJS in X;
    destruct X as (HF & G9 & G22 & G10 & G16 & G14 & G17 & G24 & G25 & G18 & E1 & E2 & Hh0 & Hb0 & Hn00); open_fix HF.

  Definition djs_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (10, EVar 36%nat); (16, EAdd (EVar 43%nat) (EVar 44%nat)); (14, EAdd (EVar 43%nat) (EVar 44%nat)); (17, EVar 41%nat);
     (23, EVar 45%nat); (26, EAdd (EVar 43%nat) (EVar 46%nat)); (19, EVar 47%nat)].

  Ltac djs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00 :=
    let Q10 := fresh in let Q22 := fresh in let Q17 := fresh in let Q16 := fresh in let Q14 := fresh in let Q12 := fresh in
    symex_reg HR (10%bv : reg) as Q10; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (17%bv : reg) as Q17;
    symex_reg HR (16%bv : reg) as Q16; symex_reg HR (14%bv : reg) as Q14; symex_reg HR (12%bv : reg) as Q12;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold DJS, DJE, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIX _ _ => lfix_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q10; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q17; f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q14; f_equal; lia
          | rewrite Q12; f_equal; lia
          | clear - E1 E2 Hh0 Hb0 Hn00; lia
          | match goal with |- ?G => idtac "DJS LEFT" G end ].

  Lemma dictid_step_H : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> DJS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 32 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f1ec) M s6u_rom)
               /\ DJS h0 n0 b0 c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP djs_pins ilI 20%nat [true; true; true] [RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    djs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma dictid_step_E : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> DJS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> 32 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f430) M s6u_rom)
               /\ DJE c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hb8 Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP djs_pins ilI 20%nat [true; true; false] [RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    djs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma dictid_dry : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> DJS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HRC HJ RI CI Hb Hh. open_djs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP djs_pins ilI 14%nat [false] [RVal (EVar 48%nat); RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64)] v r
      [h0; n0; b0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f1ec) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | rewrite Q26; apply zw_neg_mod
            | rewrite Q24; f_equal; clear - Hh; lia
            | rewrite Q18; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption] end
            | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.

  Lemma dictid_A : forall s c r R M,
    LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 32 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f430) M s6u_rom) /\ DJE c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f1ec) M s6u_rom) /\ DJS (ir_have r) (ir_next r) (ir_bits r) c r R1.
  Proof.
    intros s c r R M HM HF HV RI.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - arm_symex ilI 8%nat [true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (10%bv : reg) as G10'.
      unfold DJE. split; [lfix_close Hfr HR1|]. regs_via Hfr; first [exact G12' | exact G10' | idtac].
    - arm_symex ilI 10%nat [false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (16%bv : reg) as G16'. symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (17%bv : reg) as G17'.
      unfold DJS. split; [lfix_close Hfr HR1|]. regs_via Hfr; first [exact G10' | exact G16' | exact G14' | exact G17' | idtac].
      + clear; lia.
      + clear; lia.
      + clear - Rhv0; lia.
      + clear - Rhv0 Rnh Rnx0 CI0; lia.
      + clear - Rbits; lia.
      + clear - Rnx0; lia.
  Qed.

  Lemma dictid_need : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    match NEEDBITS 32 (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f430) M s6u_rom)
        /\ DJE c r1 R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1 /\ 32 <= ir_bits r1
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f1d4) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1
    | ARet _ _ => False
    end.
  Proof.
    intros s c r R M HM HRC HF HV RI CI.
    pose proof RI as RI'. open_rinv RI'.
    destruct (dictid_A s c r R M HM HF HV RI) as (R1 & HA).
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - destruct HA as (Hms1 & DJE1). unfold NEEDBITS. rewrite NEEDBITS_k_done by (cbn; exact GE).
      exists r, R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact DJE1|]. split; [exact RI|]. split; [apply same5_refl | exact GE].
    - destruct HA as (Hms1 & DJS1).
      pose proof (need_loop v 32 0x1f1ec 0x1f430 (DJS (ir_have r) (ir_next r) (ir_bits r)) DJE C ltac:(lia)
                    (dictid_step_H _ _ _) (dictid_step_E _ _ _) (dictid_dry _ _ _)
                    8%nat s c r R1 M HM HRC DJS1 RI CI LT ltac:(cbn; clear - LT Rbits; lia)) as NL.
      change (NEEDBITS_k 8 32) with (NEEDBITS 32) in NL.
      destruct (NEEDBITS 32 (mkW s c r)) as [[] w1 | w1 | rc w1]; [| | exact NL].
      + destruct NL as (r1 & R2 & E & Hms2 & DJE & RI1 & S5 & Hb1 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact DJE|]. split; [exact RI1|]. split; [exact S5 | clear - Hb1; lia].
      + destruct NL as (r1 & R2 & E & Hms2 & HL & RI1 & S5 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL|]. split; [exact RI1 | exact S5].
  Qed.
End DictidLoop.
End FXG.
End InflA_Dict1.

Module InflA_Dict2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6d OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflNeed6 InflA_Dict1.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent ZSWAP32.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition restore_c (c : icall) (r : iregs) : icall :=
  icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r).

(* zlib 1.4 (inflate.c l.709-712): before it returns Z_NEED_DICT, inflate adds in - avail_in to strm->total_in *)
Definition dict_c (c : icall) (r : iregs) : icall :=
  icset_total_in (restore_c c r) (wrap64 (ic_total_in c + wrap32 (ir_in r - ir_have r))).

Lemma arm_DICT_run : forall iv flush s c r,
  is_havedict s = 0 ->
  arm_DICT iv flush (mkW s c r) = ARet Z_NEED_DICT (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (dict_c c r) r).
Proof.
  intros iv flush s c r Hhd. unfold arm_DICT. mstep1 (@gs_eq inflate_state). rewrite Hhd. cbn [Z.eqb].
  unfold amodify, abind, areturn, RESTORE, dict_c, restore_c. cbn [w_s w_c w_r]. reflexivity.
Qed.

Lemma arm_DICTID_run : forall iv flush s c r c1 r1,
  is_havedict s = 0 ->
  NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c1 r1) ->
  arm_DICTID iv flush (mkW s c r)
  = ARet Z_NEED_DICT (mkW (iset_bits (iset_hold (iset_mode (iset_check s (ZSWAP32 (ir_hold r1))) DICT) 0) 0)
                          (dict_c (icset_adler c1 (ZSWAP32 (ir_hold r1))) r1)
                          (irset_bits (irset_hold r1 0) 0)).
Proof.
  intros iv flush s c r c1 r1 Hhd HN. unfold arm_DICTID. rewrite abind_run, HN. mstep1 HOLD_eq.
  mstep1 set_adler_check_eq. mstep1 INITBITS_eq. mstep1 set_mode_eq.
  rewrite arm_DICT_run by (destruct s; exact Hhd). unfold dict_c, restore_c. irnorm. reflexivity.
Qed.


Definition dstops : list Z := [pc6_disp; pc6_ret; pc6_leave; pc6_mem; 0x21cb4; 0x225ec; 0x1af3c; 0x2a824; 0x21728] ++ arm6_pcs.
Definition ilR : cfg := CFG [] [] arm_rets dstops [].

Section DictBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dje HJ :=
    let X := fresh in pose proof HJ as X; unfold DJE in X;
    destruct X as (HF & G9 & G22 & G12 & G10); open_fix HF.
  Definition dje_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (12, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 36%nat)].

  Definition DREG (r : iregs) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - 256) /\ getr R 8 = zw (cv_S v) /\ getr R 13 = zw (cv_ZP v)
    /\ getr R 23 = zw (ir_have r) /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Definition dpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))].

  Lemma dict_core : forall s c r R M,
    is_havedict s = 0 -> live_mode (is_mode s) -> is_mode s <> HEAD -> is_mode s <> BAD ->
    LMEM v (mkW s c r) M -> LX v (mkW s c r) -> DREG r R ->
    RINV (cv_NI v) (cv_NO v) r -> 0 <= ic_total_in c < 2 ^ 64 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f484) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (ARet Z_NEED_DICT (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (dict_c c r) r)) R' M' pc'.
  Proof.
    intros s c r R M Hhd Hlive NH NB HM HX HD RI Cti.
    destruct HD as (P2 & P27 & P13 & P24 & P9 & P22 & P18 & P25 & P3 & P4).
    pose proof HM as HM0. pose proof RI as RI0.
    open_ictx C. open_lmem HM. open_frame Mfr. open_zs Mzs. open_lx HX. open_rinv RI.
    unfold mapped in *.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HinB : 0 <= cv_NI v - ir_have r < 2 ^ 31) by (clear - Rnx0 Rhv0 Rnh CI0; lia).
    pose proof (is6_havedict _ _ _ _ Msc) as C20. rewrite Hhd in C20.
    (* zlib 1.4: the NEED_DICT exit (0x213e8) restores avail_out, hold, bits, then next_in, avail_in, total_in
       (+= in - avail_in, in = the frame slot 72(sp)) and next_out *)
    arm_symexP (@nil (Z * expr)) ilR 24%nat [false] [RVal (ELit 0); RVal (EVar 39%nat); RVal (EVar 46%nat); RVal (EVar 45%nat)] dpins
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 64)] v r [cv_NI v; ic_total_in c] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f484) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTDC" G end.
    rewrite ?(Z.mod_small (cv_NI v - ir_have r) (2 ^ 32)) in Hms by (clear - HinB; lia).
    rewrite ?szwrap32_small in Hms by (clear - HinB; lia).
    rewrite ?(Z.mod_small (cv_NI v - ir_have r) (2 ^ 32)) in Hms by (clear - HinB; lia).
    rewrite <- ?(le8_wrap64 (ic_total_in c + _)) in Hms.
    set (tin := wrap64 (ic_total_in c + (cv_NI v - ir_have r))) in *.
    (* the restore in 1.4's store order *)
    pose proof (LMEM_store_avail_out v C s c r M (ir_left r) HM0 Hput) as H1.
    assert (H2' : LMEM v (mkW (iset_hold s (ir_hold r)) (icset_avail_out c (ir_left r)) r)
                    (wbytes (wbytes M (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r))) (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))).
    { apply (LMEM_store_scalar v C s _ r _ _ 96 _ H1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_hold _ (cv_S v) _ s (ir_hold r) (lm_sc _ _ _ H1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (H3 : LMEM v (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (icset_avail_out c (ir_left r)) r)
                    (wbytes (wbytes (wbytes M (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r))) (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))
                       (zw (cv_S v + 104)) (Z_to_le_bytes 4 (ir_bits r)))).
    { apply (LMEM_store_scalar v C _ _ r _ _ 104 _ H2'); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_bits _ (cv_S v) _ _ (ir_bits r) (lm_sc _ _ _ H2')); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (LMEM_store_next_in v C _ _ r _ (ir_next r) H3 Hput) as H4. rewrite (Z.add_0_r (cv_ZP v)) in H4.
    pose proof (LMEM_store_avail_in v C _ _ r _ (ir_have r) H4 Hput) as H5.
    pose proof (Infl6B.LMEM_store_total_in v C _ _ r _ tin H5 Hput) as H6.
    pose proof (LMEM_store_next_out v C _ _ r _ (ir_put r) H6 Hput) as H7.
    assert (Ec : icset_next_out (icset_total_in (icset_avail_in (icset_next_in (icset_avail_out c (ir_left r)) (ir_next r)) (ir_have r)) tin) (ir_put r)
                 = dict_c c r).
    { unfold dict_c, restore_c. subst tin. rewrite Rin. rewrite wrap32_id by (clear - HinB; lia). destruct c; reflexivity. }
    rewrite Ec in H7.
    match type of H7 with LMEM _ _ ?Mx => set (M4 := Mx) in * end.
    exists R', M4, pc6_ret. split; [subst M4; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split.
    - split; [exact H7|]. split.
      { apply (LX_step0 v s c r _ _ r HX NH NB); unfold dict_c, restore_c; try reflexivity; try (destruct s; reflexivity); [destruct s; exact Hlive | exact Xret | destruct c; cbn in *; exact Xmsg | bk_side]. }
      split; [split; [destruct s; reflexivity | split; destruct s; reflexivity]|].
      split; [| unfold Z_NEED_DICT, Z_OK; lia].
      symex_reg HR' (10%bv : reg) as G10'. unfold LREG_ret, INF_FRAME. regs_via Hfr; exact G10'.
    - subst M4.
      do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]).
      do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply MFRAME_refl.
  Qed.

  Lemma dictid_B_sim : forall s c r1 R M,
    is_mode s = DICTID -> is_havedict s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> DJE v c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f430) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M
           (ARet Z_NEED_DICT (mkW (iset_bits (iset_hold (iset_mode (iset_check s (ZSWAP32 (ir_hold r1))) DICT) 0) 0)
                                   (dict_c (icset_adler c (ZSWAP32 (ir_hold r1))) (irset_bits (irset_hold r1 0) 0))
                                   (irset_bits (irset_hold r1 0) 0))) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hhd HM HRC HX HJ RI CI Hb32. open_dje HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    rewrite <- (zswap_exec (ir_hold r1)).
    set (V := (Z.lor (Z.lor (ir_hold r1 * 2 ^ 24) (Z.land (ir_hold r1) 65280 * 2 ^ 8)) (Z.lor (Z.land (ir_hold r1 / 2 ^ 8) 65280) (ir_hold r1 mod 2 ^ 32 / 2 ^ 24))) mod 2 ^ 32).
    assert (HV : 0 <= V < 2 ^ 32) by (subst V; apply Z.mod_pos_bound; lia).
    arm_symexP dje_pins ilR 40%nat (@nil bool) (@nil (option expr))
      (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f430) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTD" G end.
    fold V in Hms1.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16190)) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 40)) (Z_to_le_bytes 8 V)) in *.
    set (M3 := wbytes M2 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 V)) in *.
    set (sB := iset_check (iset_mode s DICT) V). set (cB := icset_adler c V). set (r2 := irset_bits (irset_hold r1 0) 0).
    assert (HM1 : LMEM v (mkW (iset_mode s DICT) c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s DICT Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW sB c r1) M2).
    { apply (LMEM_store_scalar v C _ c r1 _ M1 40 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_check M1 (cv_S v) _ _ V (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW sB cB r2) M3).
    { apply (LMEM_regs v sB cB r1 cB r2); [exact (LMEM_store_adler v C sB c r1 M2 V HM2 Hput) | subst r2; reflexivity ..]. }
    pose proof (icset_adler_facts c V) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
    assert (HX3 : LX v (mkW sB cB r2)).
    { apply (LX_step0 v s c r1 _ cB r2 HX NH NB); subst sB cB r2; try reflexivity; [live_mode_tac | exact Xret | rewrite U9; exact Xmsg | bk_side]. }
    assert (HD3 : DREG r2 R1).
    { symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
      unfold DREG. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      regs_via Hfr1; first [exact Q22 | exact Q18 | exact Q25 | exact Q24 | match goal with |- ?G => idtac "DREG LEFT" G end]. }
    assert (RI2 : RINV (cv_NI v) (cv_NO v) r2) by (subst r2; unfold RINV in *; cbn; clear - RI; change (2 ^ 0) with 1; lia).
    destruct (dict_core sB cB r2 R1 M3 ltac:(subst sB; destruct s; exact Hhd) ltac:(subst sB; live_mode_tac)
                ltac:(subst sB; destruct s; cbv; discriminate) ltac:(subst sB; destruct s; cbv; discriminate) HM3 HX3 HD3 RI2
                ltac:(subst cB; exact Cti))
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
    replace (iset_bits (iset_hold (iset_mode (iset_check s V) DICT) 0) 0) with (iset_bits (iset_hold sB (ir_hold r2)) (ir_bits r2)) by (subst sB r2; destruct s; reflexivity).
    apply (arm_post_chain v (mkW s c r1) (mkW sB cB r2) M M3); [subst sB; split; [destruct s; reflexivity | split; destruct s; reflexivity] | | exact HPOST].
    cbn [w_r]. subst r2 M3 M2 M1. cbn [ir_put irset_bits irset_hold].
    apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End DictBody.

Lemma arm_DICTID_leave : forall iv flush s c r w1,
  NEEDBITS 32 (mkW s c r) = ALeave w1 -> arm_DICTID iv flush (mkW s c r) = ALeave w1.
Proof. intros iv flush s c r w1 HN. unfold arm_DICTID. rewrite abind_run, HN. reflexivity. Qed.

Theorem arm_DICT_sim : arm_stmt DICT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DICT) with (arm_DICT ivar_ref (cv_flush v)).
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  pose proof HX as HX'. open_lx HX'. pose proof HP as HP'. open_pinv HP'.
  rewrite (arm_DICT_run ivar_ref (cv_flush v) s c r Xhd).
  assert (HD : DREG v r R).
  { pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    unfold LFIX in HF. destruct HF as (_ & _ & _ & _ & _ & _ & G3 & G4).
    unfold DREG. repeat split; assumption. }
  exact (dict_core v C s c r R M Xhd Xlive ltac:(rewrite Hmode; cbv; discriminate) ltac:(rewrite Hmode; cbv; discriminate) HM HX HD RI
           ltac:(let X := fresh in pose proof CI as X; unfold CINV in X; destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X)).
Qed.

Theorem arm_DICTID_sim : arm_stmt DICTID.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DICTID) with (arm_DICTID ivar_ref (cv_flush v)).
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  arm_begin C HM HRC HX HF HV HP.
  pose proof (dictid_need v C s c r R M HM HRC HF HV RI CI) as HN.
  destruct (NEEDBITS 32 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct HN].
  - destruct HN as (r1 & R1 & -> & Hms1 & HJE & RI1 & S5 & Hb32).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_DICTID_run ivar_ref (cv_flush v) s c r c r1 Xhd EN).
    assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | exact Q2 | reflexivity]).
    assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | exact Q5]).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HX1 : LX v (mkW s c r1)).
    { apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]. }
    destruct (dictid_B_sim v C s c r1 R1 M Hmode Xhd HM1 HRC1 HX1 HJE RI1 CI Hb32) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
  - destruct HN as (r1 & R1 & -> & Hms1 & HL1 & RI1 & S5).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_DICTID_leave ivar_ref (cv_flush v) s c r _ EN).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    exists R1, M, pc6_leave. split; [exact Hms1|].
    cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
    split; [apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | exact Q2 | reflexivity]|].
    split; [| split; [apply same_blocks_refl | exact HL1]].
    apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
Qed.
End FXG.
End InflA_Dict2.

Module InflA_Length.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma arm_LENGTH_run : forall s c r,
  (is_wrap s = 5 \/ is_wrap s = 1) -> is_flags s = 0 ->
  arm_LENGTH (mkW s c r) = ALeave (mkW (iset_mode s DONE) c (irset_ret r Z_STREAM_END)).
Proof.
  intros s c r Hw Hf. unfold arm_LENGTH. mstep1 (@gs_eq inflate_state). rewrite (wrap15_eqb0 _ Hw), Hf. change (negb false && negb (0 =? 0)) with false.
  mstep1 (@aret_eq bool). mstep1 set_mode_eq. unfold arm_DONE. mstep1 ur_eq. rewrite aleave_eq. reflexivity.
Qed.

Theorem arm_LENGTH_sim : arm_stmt LENGTH.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) LENGTH) with arm_LENGTH.
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  arm_begin C HM HRC HX HF HV HP.
  assert (Hf : is_flags s = 0) by (destruct Xflags as [X0 | (_ & XM & _)]; [exact X0 | exfalso; rewrite Hmode in XM; destruct XM as [E|E]; cbv in E; discriminate]).
  rewrite (arm_LENGTH_run s c r Xwrap Hf).
  assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
  assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
  assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
  pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Xwrap) as Hwr. pose proof (wrap15_ne0 _ Xwrap) as Hw0.
  pose proof (is6_flags _ _ _ _ Msc) as C24. rewrite Hf in C24.
  change (arm6_pc LENGTH) with 0x204f8.
  arm_symex ilS 16%nat [false; true] [RVal (EVar 45%nat); RVal (ELit 0)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals F0
    (mkst R (Z_to_bv 64 0x204f8) M s6u_rom) R' HR' Hfr Hms.
  all: try arm_side.
  all: match goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFT" G end.
  set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16208)) in *.
  set (r' := irset_ret r Z_STREAM_END).
  assert (HM1 : LMEM v (mkW (iset_mode s DONE) c r') M1).
  { apply (LMEM_regs v (iset_mode s DONE) c r c r'); [| subst r'; reflexivity ..].
    apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
    apply (is6_upd_mode M (cv_S v) _ s DONE Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
  exists R', M1, pc6_leave. split; [subst M1; by_run Hms|].
  cbn [arm_post]. split; [reflexivity|]. split.
  2:{ subst M1 r'. cbn [ir_put irset_ret]. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
  split; [exact HM1|]. split.
  { apply (LX_step0 v s c r _ c r' HX NH NB); subst r'; try reflexivity; [live_mode_tac | cbn; unfold Z_STREAM_END; lia | exact Xmsg | bk_side]. }
  split; [apply same_blocks_mode|].
  unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret].
  repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | lazymatch goal with |- getr _ ?n = _ => let G := fresh "G" in symex_reg HR' n as G; rewrite G; first [reflexivity | assumption | f_equal; lia] end
          | match goal with |- ?G => idtac "LEAVE LEFT" G end ].
Qed.
End FXG.
End InflA_Length.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Match5 InflA_Distext3 InflA_Dist7 InflA_Lenext3 InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Cl2 InflA_Cl3 InflA_Ll.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InffastCtx IfSpec IfSpec6 InflA_LenF.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflRod6 InflCtx6 InflLoop6 Callee6i. Import InflA_LIT. Import InflA_Term. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Type2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Stored. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Stored.InflA_Copy. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Stored InflA_Head3 InflA_Check3. Import InflA_Dict2. Import InflA_Length. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Match5 InflA_Distext3 InflA_Dist7 InflA_Lenext3 InflA_Len7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Cl2 InflA_Cl3 InflA_Ll.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InffastCtx IfSpec IfSpec6 InflA_LenF.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma zrange32 : forall (P : Z -> Prop) (lo : Z),
  (forall i : nat, (i < 32)%nat -> P (lo + Z.of_nat i)) -> forall m, lo <= m <= lo + 31 -> P m.
Proof.
  intros P lo H m Hm. replace m with (lo + Z.of_nat (Z.to_nat (m - lo))) by lia. apply H. lia.
Qed.

Section Arms.
  Hypothesis MEMCPY : memcpy_run6u.
  Variable ROM : (word -> option byte) -> Prop.
  Hypothesis ROMok : forall M, rod6_clear M -> ROM M.
  Hypothesis ADLER : adler32_run6u ROM.
  Hypothesis ITABLE : itable_run6.
  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFOB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.
  Hypothesis CLPINV : InflA_Cl3.InflA_Codelens7.cl_pinv_stmt.

  Theorem arms6 : forall m, HEAD <= m <= SYNC -> arm_stmt m.
  Proof.
    apply (zrange32 arm_stmt HEAD). intros i Hi.
    do 32 (destruct i as [|i];
      [ first [ exact arm_HEAD_sim
              | apply arm_dead_sim; unfold HEAD, FLAGS, HCRC, SYNC; cbn; lia
              | exact arm_DICTID_sim | exact arm_DICT_sim | exact arm_TYPE_sim | exact arm_TYPEDO_sim
              | exact (arm_STORED_sim MEMCPY) | exact (arm_COPY__sim MEMCPY) | exact (arm_COPY_sim MEMCPY)
              | exact (arm_TABLE_sim (lenlens_core_ok ITABLE (codelens_core_ok ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV)))
              | exact (arm_LENLENS_sim ITABLE (codelens_core_ok ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV)) | exact (arm_CODELENS_sim ITABLE IFAST FFOK FASTOK GFOB FFRAME CLPINV)
              | exact (arm_LEN__sim IFAST FFOK FASTOK GFOB FFRAME) | exact (arm_LEN_sim IFAST FFOK FASTOK GFOB FFRAME) | exact arm_LENEXT_sim | exact arm_DIST_sim | exact arm_DISTEXT_sim
              | exact arm_MATCH_sim | exact arm_LIT_sim | exact (arm_CHECK_sim ROM ROMok ADLER) | exact arm_LENGTH_sim
              | exact arm_DONE_sim | exact arm_BAD_sim | exact arm_MEM_sim ]
      |]).
    cbn in Hi. lia.
  Qed.

  Theorem loop6 : loop_stmt.
  Proof. exact (inf_loop_sim arms6). Qed.
End Arms.
End FXG.
