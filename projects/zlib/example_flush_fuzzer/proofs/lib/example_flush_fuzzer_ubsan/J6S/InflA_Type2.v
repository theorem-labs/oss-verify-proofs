(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflA_Type.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section ArmTYPE2.

  Lemma typedo_core : forall v s c r R M,
    ictx v -> (is_mode s = TYPE \/ is_mode s = TYPEDO) ->
    ENTRY v (mkW s c r) R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d428) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_TYPEDO ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.
  Proof.
    intros v s c r R M C Hmode HE HP. pose proof HE as HE0. destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    arm_begin C HM HRC HX HF HV HP.
    assert (NH : is_mode s <> HEAD) by (clear - Hmode; destruct Hmode as [E|E]; rewrite E; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (clear - Hmode; destruct Hmode as [E|E]; rewrite E; cbv; discriminate).
    pose proof (is6_last _ _ _ _ Msc) as C12.
    assert (Hlr : - 2 ^ 31 <= is_last s < 2 ^ 31) by (destruct SR as (_ & H & _); exact H).
    destruct (Z.eq_dec (is_last s) 0) as [Hlast|Hlast].
    -
      destruct (typedo_A v s c r R M C HE0 HP Hlast) as (R1 & HA).
      destruct (NEEDBITS 3 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; [| | destruct HA].
      + destruct HA as (Hms1 & HJ & Hb3 & RI1 & Es & Ec & Eput & Eleft & Eout & Ein & Eret). cbn [w_s w_c w_r] in *. subst s1 c1.
        clear Rnx0 Rhv0 Rnh Rpt0 Rlf0 Rpl Rin Rout Routp Rbits Rhold Rhold64. open_rinv RI1.
        rewrite (arm_TYPEDO_run (cv_flush v) s c r s c r1 Hlast HN ltac:(clear - Hb3 Rbits; lia) Rhold).
        assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [assumption | symmetry; assumption | reflexivity]).
        assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | cbn [w_r]; exact Eret]).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Ein | rewrite Eret; exact Xret | exact Xmsg]).
        destruct (typedo_B_sim v s c r1 R1 M C HM1 HRC1 HX1 HJ RI1 CI Hmode Hb3) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Eput | exact HPOST].
      + destruct HA as (Hms1 & -> & HL1). rewrite (arm_TYPEDO_leave (cv_flush v) s c r _ Hlast HN).
        exists R1, M, pc6_leave. split; [exact Hms1|].
        cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
        split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl | exact HL1].
    -
      rewrite (arm_TYPEDO_last (cv_flush v) s c r Hlast).
      pose proof (szwrap32_of_mod32 (is_last s) Hlr) as Esz.
      assert (Hnz : szwrap 32 (is_last s mod 2 ^ 32) mod 2 ^ 64 <> 0).
      { rewrite Esz. apply mod64_nz; [exact Hlast | clear - Hlr; lia]. }
      arm_symex ilS 30%nat [true; true] [RVal (EVar 45%nat); RVal (ELit (JT CHECK))] (@nil (Z * expr)) [(45%nat, 2 ^ 32)] v r
        [is_last s mod 2 ^ 32] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d428) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7))).
      set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16206)).
      assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
      assert (E7 : Z.land (ir_bits r) 7 = ir_bits r mod 8) by apply land7_mod.
      assert (Hm8 : 0 <= ir_bits r mod 8 < 8) by (apply Z.mod_pos_bound; lia).
      assert (Hml : ir_bits r mod 8 <= ir_bits r) by (apply Z.mod_le; clear - Rbits; lia).
      assert (Ebits : wrap32 (ir_bits r - Z.land (ir_bits r) 7) = Z.land (ir_bits r) (-8)).
      { rewrite land_m8 by (clear - Rbits; lia). apply wrap32_id. rewrite E7. clear - Rbits Hm8 Hml. lia. }
      assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r c r' M HM); reflexivity).
      assert (HM1 : LMEM v (mkW (iset_mode s CHECK) c r') M1).
      { apply (LMEM_store_scalar v C s c r' _ M 8 _ HM0); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M (cv_S v) _ s CHECK Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R', M1, (arm6_pc CHECK). split; [subst M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [split; [reflexivity | split; reflexivity] |]].
      + split; [exact HM1|]. split; [subst M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r _ c r' HX NH NB); subst r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
        * symex_reg HR' (23%bv : reg) as G22'. symex_reg HR' (24%bv : reg) as G23'. symex_reg HR' (27%bv : reg) as G26'. symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [apply (LFIX_frame v R R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8'].
          regs_via Hfr.
          -- rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). rewrite shiftr_div by (clear - Hm8 E7; lia).
             rewrite E7. reflexivity.
          -- rewrite G23', Ebits. reflexivity.
      + subst M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Theorem arm_TYPEDO_sim : arm_stmt TYPEDO.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) TYPEDO) with (arm_TYPEDO ivar_ref (cv_flush v)).
    exact (typedo_core v s c r R M C (or_intror Hmode) HE HP).
  Qed.

  Theorem arm_TYPE_sim : arm_stmt TYPE.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) TYPE) with (arm_TYPE ivar_ref (cv_flush v)).
    unfold arm_TYPE. cbn [iv_flush_exits ivar_ref andb].
    pose proof HE as HE0. destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    arm_begin C HM HRC HX HF HV HP.
    replace ((cv_flush v =? Z_BLOCK) || (cv_flush v =? Z_TREES)) with false
      by (symmetry; apply orb_false_intro; apply Z.eqb_neq; unfold Z_BLOCK, Z_TREES; clear - Cflush; lia).
    open_frame Mfr.
    assert (Ef5 : (cv_flush v - 5) mod 2 ^ 64 = cv_flush v - 5 + 2 ^ 64) by (apply zmod64_neg; clear - Cflush; lia).
    arm_symex ilS 6%nat [true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r
      [(cv_flush v - 5) mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d418) M s6_rom) R1 HR1 Hfr Hms1.
    all: try arm_side.
    assert (HE1 : ENTRY v (mkW s c r) R1 M).
    { split; [exact HM|]. split; [exact HRC|]. split; [exact HX|].
      unfold LREG_arm, LVARS; cbn [w_r]. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|].
      split; [regs_via Hfr | intros Hb; rewrite (Hfr (9%bv : reg) eq_refl); exact (G8 Hb)]. }
    destruct (typedo_core v s c r R1 M C (or_introl Hmode) HE1 HP) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [| exact HPOST].
    eapply msteps_trans; [| exact Hms2]. by_run Hms1.
  Qed.
End ArmTYPE2.
End FXG.
