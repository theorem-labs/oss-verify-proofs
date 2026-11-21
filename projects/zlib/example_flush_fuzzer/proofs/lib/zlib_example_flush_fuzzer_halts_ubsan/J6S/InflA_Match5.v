(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b
     InflA_Match1 InflA_Match2 InflA_Match3 InflA_Match4.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section MatchCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Theorem match_core : forall s c r R M,
    is_mode s = MATCH ->
    ENTRY v (mkW s c r) R M -> match_facts v s c r ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e828) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_MATCH ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HE HP. pose proof HE as HE0. pose proof HP as HP0. destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    destruct HP as (Hsane & Hlen & Hoff & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hcp : 0 <= ir_out r - ir_left r <= ir_put r) by (clear - Rout Routp; lia).
    pose proof (is6_offset _ _ _ _ Msc) as C96. pose proof (is6_length _ _ _ _ Msc) as C92.
    pose proof (is6_whave _ _ _ _ Msc) as C64. pose proof (is6_wnext _ _ _ _ Msc) as C68. pose proof (is6_wsize _ _ _ _ Msc) as C60.
    pose proof (is6_window _ _ _ _ Msc) as C72. cbn [q_window] in C72.
    pose proof (is6_sane _ _ _ _ Msc) as C7144. rewrite Hsane in C7144.
    open_frame Mfr.
    destruct (Z.eq_dec (ir_left r) 0) as [L0'|L0'].
    2: destruct (Z_lt_le_dec (ir_out r - ir_left r) (is_offset s)) as [LT'|GE'].
    2: destruct (Z_lt_le_dec (is_whave s) (is_offset s - (ir_out r - ir_left r))) as [BW'|BW'].
    3: { destruct (Z_lt_le_dec (is_wnext s) (is_offset s - (ir_out r - ir_left r))) as [WR|NW].
         - exact (match_win_wrap v C s c r R M Hmode HE0 HP0 L0' LT' BW' WR).
         - exact (match_win_nowrap v C s c r R M Hmode HE0 HP0 L0' LT' BW' NW). }
    all: rewrite (arm_MATCH_eq s c r Hsane) by (first [clear - Hcp Hput CP0; lia | clear - Hoff; lia | clear - Hwn; lia | clear - Rlf0 Rpl Rpt0 CP0; lia | clear - Hlen; lia]).
    -
      replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact L0').
      arm_symex ilMS 6%nat [true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r [ir_ret r mod 2 ^ 64] NoVals F0
        (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      exists R', M, pc6_leave. split; [by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
      split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl|].
      symex_reg HR' (9%bv : reg) as G8'. unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr. rewrite G8'. apply zw_neg_mod.
    -
      replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0'). rename L0' into L0.
      unfold msel. destruct (Z.ltb_spec (ir_out r - ir_left r) (is_offset s)) as [LT|GE]; [| exfalso; clear - LT' GE; lia].
      set (cw := is_offset s - (ir_out r - ir_left r)) in *.
      assert (Hcw : 1 <= cw <= 32768) by (subst cw; clear - LT Hcp Hoff; lia).
      destruct (Z.ltb_spec (is_whave s) cw) as [BW|BW]; [| exfalso; clear - BW BW'; lia].
        arm_symex ilMS 40%nat [false; false; false; false; true]
          [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (ELit 1); RVal (ELit (JT BAD))]
          (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 32769); (47%nat, 2 ^ 63)] v r
          [is_offset s; is_whave s; cv_S v + 7160] NoVals F0 (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R' HR' Hfr Hms.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTB" G end.
        set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66260)) in *.
        set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
        set (c' := icset_msg c MSG_invalid_distance_too_far_back).
        assert (HM1 : LMEM v (mkW s c' r) M1) by (exact (LMEM_store_msg v C s c r M MSG_invalid_distance_too_far_back HM Hput)).
        assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r) M2).
        { apply (LMEM_store_scalar v C s c' r _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        pose proof (icset_msg_facts c MSG_invalid_distance_too_far_back) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
        exists R', M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms|].
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
        + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
          * apply (LX_step0 v s c r _ c' r HX NH NB); subst c'; try reflexivity; [live_mode_tac | exact Xret | rewrite E11; unfold MSG_invalid_distance_too_far_back; lia].
          * symex_reg HR' (9%bv : reg) as G8'.
            unfold LREG_arm, LVARS; cbn [w_r]. split; [apply (LFIX_frame v R R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8']. regs_via Hfr.
        + subst M2 M1.
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    -
      replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0'). rename L0' into L0.
      unfold msel. destruct (Z.ltb_spec (ir_out r - ir_left r) (is_offset s)) as [LT|GE]; [exfalso; clear - LT GE'; lia|].
        set (cpy := mclamp r (is_length s)).
        assert (Hcpy : 1 <= cpy <= is_length s /\ cpy <= ir_left r) by (subst cpy; unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
        assert (PRE : exists R1,
          msteps s6_segs (mkst R (Z_to_bv 64 0x1e828) M s6_rom)
                 (mkst R1 (Z_to_bv 64 0x1e8d8) (wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - cpy))) s6_rom)
          /\ (forall rg, reg_in rg [12; 13; 14]%bv = false -> getr R1 rg = getr R rg)
          /\ getr R1 13 = zw (cv_P0 v + (ir_put r - is_offset s)) /\ getr R1 12 = zw cpy /\ getr R1 14 = zw (cv_P0 v + (ir_put r - is_offset s) + cpy)).
        { destruct (Z_lt_le_dec (is_length s) (ir_left r)) as [CL|CL].
          - assert (Ecpy : cpy = is_length s) by (subst cpy; unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia). rewrite Ecpy.
            arm_symex ilMS 30%nat [false; true; true] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 259)] v r
              [is_offset s; is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
            all: try arm_side.
            all: match goal with |- ?G => idtac "LEFTO1" G end.
            exists R1. split; [replace (is_length s - is_length s) with 0 by lia; by_run Hms1|]. split; [exact Hfr1|].
            symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
            split; [rewrite G13; f_equal; lia|]. split; [rewrite G12; f_equal; lia | rewrite G14; rewrite ?Z.mod_small by (clear - Hlen; lia); f_equal; lia].
          - assert (Ecpy : cpy = ir_left r) by (subst cpy; unfold mclamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia). rewrite Ecpy.
            arm_symex ilMS 30%nat [false; true; false] [RVal (EVar 45%nat); RVal (EVar 42%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 32769); (46%nat, 259)] v r
              [is_offset s; is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1e828) M s6_rom) R1 HR1 Hfr1 Hms1.
            all: try arm_side.
            all: match goal with |- ?G => idtac "LEFTO2" G end.
            exists R1. split; [rewrite <- (le4_szwrap (is_length s - ir_left r)); by_run Hms1|]. split; [exact Hfr1|].
            symex_reg HR1 (13%bv : reg) as G13. symex_reg HR1 (12%bv : reg) as G12. symex_reg HR1 (14%bv : reg) as G14.
            split; [rewrite G13; f_equal; lia|]. split; [rewrite G12; f_equal; lia | rewrite G14; rewrite ?Z.mod_small by (clear - L0 Rlf0 Rpl Rpt0 CP0; lia); f_equal; lia]. }
        destruct PRE as (R1 & Hms1 & Hfr1 & G13 & G12 & G14).
        pose proof (match_tail v C s c r R M R1 (FOut (ir_put r - is_offset s)) cpy Hmode (proj1 Hcpy) (proj2 Hcpy) (proj2 Hlen) HM HRC HX HF HV RI CI Hwl Hwb
                      ltac:(cbn; clear - GE Hcp Hoff; lia) ltac:(fr_weak Hfr1) G13 G12 G14) as T.
        cbv zeta in T. destruct (match_copy (is_window s) (ic_outbuf c, ir_put r, FOut (ir_put r - is_offset s), cpy)) as [[[ob put'] fr'] c'].
        destruct T as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HPOST].
  Qed.
End MatchCore.

Theorem arm_MATCH_sim : arm_stmt MATCH.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) MATCH) with (arm_MATCH ivar_ref).
  exact (match_core v C s c r R M Hmode HE (match_facts_of_pinv v s c r Hmode HP)).
Qed.
End FXG.
