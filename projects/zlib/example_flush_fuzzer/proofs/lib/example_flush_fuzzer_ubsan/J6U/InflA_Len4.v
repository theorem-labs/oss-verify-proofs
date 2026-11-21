(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6 InflA_Dist3. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Lenext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Lenext3.InflA_Lenext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Lenext3 InflA_Len3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section LenFin2.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).
  Ltac open_lfreg HR :=
    destruct HR as (HF & G9 & G22 & G11 & G12 & G14 & G7 & G28 & G19 & G29); open_fixc HF;
    let XF := fresh in pose proof HF as XF; unfold LFIXc, INF_FRAME in XF; destruct XF as (P2 & P27 & P8 & _);
    pose proof G9 as P9; pose proof G22 as P22; pose proof G11 as P11; pose proof G12 as P12; pose proof G14 as P14.

  Lemma len_fin : forall s c r R M here BK maxb,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    term_ok LENS maxb here = true -> maxb <= 15 -> code_bits here <= ir_bits r -> 0 <= BK <= 15 ->
    LMEM v (mkW (iset_back s BK) c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFREG v s r here BK R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20c78) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW (iset_back s BK) c r) M (len_res here BK s c r) R' M' pc'.
  Proof.
    intros s c r R M here BK maxb Hmode HD RI TE Hmaxb Hhb HBK HM HRC HX HR.
    pose proof (code_op_range here) as Hop.
    destruct (Z_le_gt_dec 16 (code_op here)) as [O16|Olt]; [destruct (Z_lt_le_dec (code_op here) 32) as [O32|O32]|].
    { exact (len_fin_base v C s c r R M here BK maxb Hmode HD RI TE Hmaxb Hhb (conj O16 O32) HBK HM HRC HX HR). }
    all: pose proof HD as HD0; open_lfacts HD; open_lfreg HR.
    all: open_ictx C; open_lmem HM; open_retc HRC; open_lx HX; pose proof RI as RI0; open_rinv RI; pose proof CI as CI'; open_cinv CI; open_frame Mfr; unfold mapped in *.
    all: assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    all: assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    all: assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    all: destruct (term_ok_LENS _ _ TE) as (Bh & CL).
    all: pose proof (code_val_range here) as Hval; pose proof (code_bits_range here) as Hcb; pose proof (cent_range here) as Hcent; pose proof (cent_shr8_range here) as Hc8.
    all: pose proof (is6_back _ _ _ _ Msc) as C7148; cbn [is_back iset_back] in C7148.
    all: pose proof (land192_cent here ltac:(clear - Hhb Rbits; lia)) as L192.
    all: pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI0 ltac:(clear - Hhb Bh; lia)) as [EW RI'].
    all: unfold len_res, rdrop; rewrite EW; rewrite (swrap32_smallv (BK + code_bits here)) by (clear - HBK Bh Hcb Hmaxb; lia).
    all: set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) in *.
    all: assert (HV' : forall R1, getr R1 23 = zw (ir_have r) -> getr R1 9 = zw (cv_P0 v + ir_put r) ->
              getr R1 25 = zw (zalu ALU_SRL (ir_hold r) (cent here / 2 ^ 8)) -> getr R1 19 = zw (szwrap 32 (ir_bits r - (cent here / 2 ^ 8) mod 2 ^ 6)) ->
              getr R1 26 = zw (cv_I0 v + ir_next r) -> forall sx cx, LVARS v (mkW sx cx r') R1)
      by (intros R1 Q24 Q9 Q22 Q18 Q25 sx cx; unfold LVARS; cbn [w_r]; subst r'; cbn;
          rewrite srl_cent in Q22 by (first [exact Rhold64 | clear - Hhb Rbits; lia]);
          rewrite cent_bits6 in Q18 by (clear - Hhb Rbits; lia); rewrite szwrap32_small in Q18 by (clear - Hhb Bh Rbits; lia);
          rewrite Z.shiftr_div_pow2 by (clear - Bh; lia); repeat split; assumption).
    all: set (s1 := iset_back s (BK + code_bits here)) in *; set (s2 := iset_length s1 (code_val here)) in *.
    all: assert (HM1 : LMEM v (mkW s1 c r) (wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))))
      by (subst s1; rewrite <- (iset_back_back s BK);
          apply (LMEM_store_scalar v C (iset_back s BK) c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity];
          apply (is6_upd_back M (cv_S v) _ (iset_back s BK) _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]).
    all: assert (HM2 : LMEM v (mkW s2 c r) (wbytes (wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))))
      by (apply (LMEM_store_scalar v C s1 c r _ _ 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity];
          apply (is6_upd_length _ (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]).
    -
      destruct CL as [(O0 & _) | [(O & _) | (I64 & I16)]]; [exfalso; clear - O0 O32; lia | exfalso; clear - O O32; lia |].
      replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; clear - O32; lia).
      assert (NZ : code_op here <> 0) by (clear - O32; lia).
      destruct (Z.eq_dec (Z.land (code_op here) 32) 0) as [E32|N32].
      +
        rewrite E32. replace (negb (Z.land (code_op here) 64 =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact I64). cbn [Z.eqb negb].
        arm_symexP (@nil (Z * expr)) ilS 28%nat [false; false; false; true] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 35%nat)] lfpins lfvb v r
          [BK; cent here / 2 ^ 8; cent here; code_op here] NoVals F0
          (mkst R (Z_to_bv 64 0x20c78) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLF_BAD" G end.
        rewrite ?cent_val in Hms1. rewrite ?cent_bits6 in Hms1 by (clear - Hhb Rbits; lia).
        set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) in *.
        set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
        set (M3 := wbytes M2 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66780)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
        set (c' := icset_msg c MSG_invalid_literal_length_code) in *.
        assert (HM3 : LMEM v (mkW s2 c' r) M3) by (exact (LMEM_store_msg v C s2 c r M2 MSG_invalid_literal_length_code HM2 Hput)).
        assert (HM4' : LMEM v (mkW (iset_mode s2 BAD) c' r) M4).
        { apply (LMEM_store_scalar v C s2 c' r _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M3 (cv_S v) _ s2 BAD (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW (iset_mode s2 BAD) c' r') M4) by (apply (LMEM_regs v (iset_mode s2 BAD) c' r c' r' M4 HM4'); subst r'; reflexivity).
        pose proof (icset_msg_facts c MSG_invalid_literal_length_code) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
        arm_disp C HM4 Hfr1 R2 Hms2 G26' Hfr2.
        exists R2, M4, (arm6_pc (is_mode (iset_mode s2 BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s2 s1; split; [reflexivity | split; reflexivity] |]].
        * split; [exact HM4|]. split; [subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
          -- apply (LX_step0 v s c r _ c' r' HX NH NB); subst s2 s1 c' r'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_literal_length_code; lia | bk_side].
          -- symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25.
             unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| intros _; exact G26'].
             refine (HV' R2 _ _ _ _ _ (iset_mode s2 BAD) c'); rewrite Hfr2 by reflexivity; first [exact Q24 | exact Q22 | exact Q18 | exact Q25 | rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9].
        * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
          do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
          apply MFRAME_refl.
      +
        replace (negb (Z.land (code_op here) 32 =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact N32).
        arm_symexP (@nil (Z * expr)) ilS 28%nat [false; false; true] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 35%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] lfpins lfvb v r
          [BK; cent here / 2 ^ 8; cent here; code_op here] NoVals F0
          (mkst R (Z_to_bv 64 0x20c78) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTLF_TYPE" G end.
        rewrite ?cent_val in Hms1. rewrite ?cent_bits6 in Hms1 by (clear - Hhb Rbits; lia).
        rewrite (le4_eqm (2 ^ 64 - 1) (-1) eq_refl) in Hms1 || rewrite (le4_eqm 18446744073709551615 (-1) eq_refl) in Hms1 || idtac.
        set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) in *.
        set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
        set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16191)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (-1))) in *.
        set (s4 := iset_back (iset_mode s2 TYPE) (-1)) in *.
        assert (Es4 : iset_mode (iset_back s2 (-1)) TYPE = s4) by (subst s4 s2 s1; destruct s; reflexivity). rewrite Es4.
        assert (HM3 : LMEM v (mkW (iset_mode s2 TYPE) c r) M3).
        { apply (LMEM_store_scalar v C s2 c r _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M2 (cv_S v) _ s2 TYPE (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4' : LMEM v (mkW s4 c r) M4).
        { apply (LMEM_store_scalar v C (iset_mode s2 TYPE) c r _ M3 7164 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_back M3 (cv_S v) _ (iset_mode s2 TYPE) _ (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW s4 c r') M4) by (apply (LMEM_regs v s4 c r c r' M4 HM4'); subst r'; reflexivity).
        arm_disp C HM4 Hfr1 R2 Hms2 G26' Hfr2.
        exists R2, M4, (arm6_pc (is_mode s4)). split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s4 s2 s1; split; [reflexivity | split; reflexivity] |]].
        * split; [exact HM4|]. split; [subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
          -- apply (LX_step0 v s c r _ c r' HX NH NB); subst s4 s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
          -- symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25.
             unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| subst s4 s2 s1; cbn; intros Hb; exfalso; cbv in Hb; discriminate].
             refine (HV' R2 _ _ _ _ _ s4 c); rewrite Hfr2 by reflexivity; first [exact Q24 | exact Q22 | exact Q18 | exact Q25 | rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9].
        * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
          do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
          apply MFRAME_refl.
    -
      destruct CL as [(O0 & V256) | [(O & _) | (I64 & I16)]]; [| exfalso; clear - O Olt; lia | exfalso; apply I64; assert (E : code_op here = 0 \/ 1 <= code_op here <= 15) by (clear - Olt Hop; lia); destruct E as [E|E]; [rewrite E; reflexivity | exact (proj1 (proj2 (op_link_tests _ E)))]].
      rewrite O0. cbn [Z.eqb].
      arm_symexP (@nil (Z * expr)) ilS 22%nat [false; true] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 35%nat)] lfpins lfvb v r
        [BK; cent here / 2 ^ 8; cent here; code_op here] NoVals F0
        (mkst R (Z_to_bv 64 0x20c78) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: try (rewrite O0; reflexivity).
      all: match goal with |- ?G => idtac "LEFTLF_LIT" G end.
      rewrite ?cent_val in Hms1. rewrite ?cent_bits6 in Hms1 by (clear - Hhb Rbits; lia).
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16205)) in *.
      assert (HM3' : LMEM v (mkW (iset_mode s2 LIT) c r) M3).
      { apply (LMEM_store_scalar v C s2 c r _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s2 LIT (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW (iset_mode s2 LIT) c r') M3) by (apply (LMEM_regs v (iset_mode s2 LIT) c r c r' M3 HM3'); subst r'; reflexivity).
      arm_disp C HM3 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M3, (arm6_pc (is_mode (iset_mode s2 LIT))). split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s2 s1; split; [reflexivity | split; reflexivity] |]].
      * split; [exact HM3|]. split; [subst M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
        -- apply (LX_step0 v s c r _ c r' HX NH NB); subst s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        -- symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25.
           unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| subst s2 s1; cbn; intros Hb; exfalso; cbv in Hb; discriminate].
           refine (HV' R2 _ _ _ _ _ (iset_mode s2 LIT) c); rewrite Hfr2 by reflexivity; first [exact Q24 | exact Q22 | exact Q18 | exact Q25 | rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9].
      * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M3 M2 M1.
        do 3 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
        apply MFRAME_refl.
  Qed.
End LenFin2.
End FXG.
