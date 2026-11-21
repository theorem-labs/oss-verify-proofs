(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7 InflA_Lenext2 InflA_Lenext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflA_Len3.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section LenFin2.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Lemma len_fin : forall s c r R M here BK maxb,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    term_ok LENS maxb here = true -> code_bits here <= ir_bits r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFREG v s r here BK R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e590) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (len_res here BK s c r) R' M' pc'.
  Proof.
    intros s c r R M here BK maxb Hmode HD RI TE Hhb HM HRC HX HR.
    pose proof (code_op_range here) as Hop.
    destruct (Z_le_gt_dec 16 (code_op here)) as [O16|Olt]; [destruct (Z_lt_le_dec (code_op here) 32) as [O32|O32]|].
    { exact (len_fin_base v C s c r R M here BK maxb Hmode HD RI TE Hhb (conj O16 O32) HM HRC HX HR). }
    all: pose proof HD as HD0; open_lfacts HD.
    all: destruct HR as (HF & G18 & G1 & G22 & G13 & G12 & G27 & G9 & G16 & G14 & G7 & G17); open_fix HF.
    all: open_ictx C; open_lmem HM; open_retc HRC; open_lx HX; pose proof RI as RI0; open_rinv RI; pose proof CI as CI'; open_cinv CI; open_frame Mfr; unfold mapped in *.
    all: assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    all: assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    all: assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    all: destruct (term_ok_LENS _ _ TE) as (Bh & CL).
    all: pose proof (code_val_range here) as Hval; pose proof (code_bits_range here) as Hcb.
    all: assert (HBKm : 0 <= BK mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    all: rewrite <- (zw_mod BK) in G16.
    all: pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI0 ltac:(clear - Hhb Bh; lia)) as [EW RI'].
    all: pose proof (swrap32_range (BK + code_bits here)) as Hbk'.
    all: unfold len_res, rdrop; rewrite EW.
    all: set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) in *.
    all: assert (HV' : forall R1, getr R1 18 = zw (ir_have r) -> getr R1 19 = zw (cv_P0 v + ir_put r) -> getr R1 1 = zw (ir_left r) ->
              getr R1 23 = zw (zalu ALU_SRL (ir_hold r) (code_bits here)) -> getr R1 24 = zw (szwrap 32 (ir_bits r - code_bits here)) ->
              getr R1 27 = zw (cv_I0 v + ir_next r) -> forall sx cx, LVARS v (mkW sx cx r') R1)
      by (intros R1 Q24 Q19 Q18 Q23 Q8 Q26 sx cx; unfold LVARS; cbn [w_r]; subst r'; cbn;
          rewrite zalu_srl_small in Q23 by (clear - Rhold64 Hhb Bh Rbits; lia); rewrite szwrap32_small in Q8 by (clear - Hhb Bh Rbits; lia);
          rewrite Z.shiftr_div_pow2 by (clear - Bh; lia); repeat split; assumption).
    all: set (s1 := iset_back s (swrap32 (BK + code_bits here))) in *; set (s2 := iset_length s1 (code_val here)) in *.
    -
      destruct CL as [(O0 & _) | [(O & _) | (I64 & I16)]]; [exfalso; clear - O0 O32; lia | exfalso; clear - O O32; lia |].
      replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; clear - O32; lia).
      destruct (Z.eq_dec (Z.land (code_op here) 32) 0) as [E32|N32].
      +
        rewrite E32. replace (negb (Z.land (code_op here) 64 =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact I64). cbn [Z.eqb negb].
        arm_symexP (@nil (Z * expr)) ilS 30%nat [false; false; true; true] [RVal (ELit (JT BAD))] lfpins lfvb v r
          [BK mod 2 ^ 64; code_bits here; code_op here; code_val here] NoVals F0
          (mkst R (Z_to_bv 64 0x1e590) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        rewrite le4_BK in Hms1.
        set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (BK + code_bits here)))) in *.
        set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
        assert (HM1 : LMEM v (mkW s1 c r) M1).
        { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM2 : LMEM v (mkW s2 c r) M2).
        { apply (LMEM_store_scalar v C s1 c r _ M1 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_length M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (9%bv : reg) as Q9.
        assert (HF' : LFIX v R1) by (apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity).
        pose proof (HV' R1 Q24 ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) ltac:(rewrite (Hfr1 (1%bv : reg) eq_refl); exact G1) Q23 Q8 Q26) as HVx.
        set (M3 := wbytes M2 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66780)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
        set (c' := icset_msg c MSG_invalid_literal_length_code) in *.
        assert (HM3 : LMEM v (mkW s2 c' r) M3) by (exact (LMEM_store_msg v C s2 c r M2 MSG_invalid_literal_length_code HM2 Hput)).
        assert (HM4' : LMEM v (mkW (iset_mode s2 BAD) c' r) M4).
        { apply (LMEM_store_scalar v C s2 c' r _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M3 (cv_S v) _ s2 BAD (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW (iset_mode s2 BAD) c' r') M4) by (apply (LMEM_regs v (iset_mode s2 BAD) c' r c' r' M4 HM4'); subst r'; reflexivity).
        pose proof (icset_msg_facts c MSG_invalid_literal_length_code) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
        exists R1, M4, (arm6_pc BAD). split; [subst M4 M3 M2 M1; by_run Hms1|].
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s2 s1; split; [reflexivity | split; reflexivity] |]].
        * split; [exact HM4|]. split; [subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
          -- apply (LX_step0 v s c r _ c' r' HX NH NB); subst s2 s1 c' r'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_literal_length_code; lia].
          -- unfold LREG_arm. split; [exact HF'|]. split; [exact (HVx (iset_mode s2 BAD) c') | intros _; exact Q9].
        * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
          do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
          apply MFRAME_refl.
      +
        replace (negb (Z.land (code_op here) 32 =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact N32).
        arm_symexP (@nil (Z * expr)) ilS 30%nat [false; true; true] [RVal (ELit (JT TYPE))] lfpins lfvb v r
          [BK mod 2 ^ 64; code_bits here; code_op here; code_val here] NoVals F0
          (mkst R (Z_to_bv 64 0x1e590) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        rewrite le4_BK in Hms1.
        set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (BK + code_bits here)))) in *.
        set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
        assert (HM1 : LMEM v (mkW s1 c r) M1).
        { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM2 : LMEM v (mkW s2 c r) M2).
        { apply (LMEM_store_scalar v C s1 c r _ M1 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_length M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (9%bv : reg) as Q9.
        assert (HF' : LFIX v R1) by (apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity).
        pose proof (HV' R1 Q24 ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) ltac:(rewrite (Hfr1 (1%bv : reg) eq_refl); exact G1) Q23 Q8 Q26) as HVx.
        set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16191)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (-1))) in *.
        set (s3 := iset_mode s2 TYPE) in *. set (s4 := iset_back s3 (-1)) in *.
        assert (Es4 : iset_mode (iset_back s2 (-1)) TYPE = s4) by (subst s4 s3 s2 s1; destruct s; reflexivity). rewrite Es4.
        assert (HM3 : LMEM v (mkW s3 c r) M3).
        { apply (LMEM_store_scalar v C s2 c r _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M2 (cv_S v) _ s2 TYPE (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4' : LMEM v (mkW s4 c r) M4).
        { apply (LMEM_store_scalar v C s3 c r _ M3 7164 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_back M3 (cv_S v) _ s3 _ (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW s4 c r') M4) by (apply (LMEM_regs v s4 c r c r' M4 HM4'); subst r'; reflexivity).
        exists R1, M4, (arm6_pc TYPE). split; [subst M4 M3 M2 M1; by_run Hms1|].
        cbn [arm_post]. split; [subst s4 s3 s2 s1; reflexivity|]. split; [| split; [subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] |]].
        * split; [exact HM4|]. split; [subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
          -- apply (LX_step0 v s c r _ c r' HX NH NB); subst s4 s3 s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
          -- unfold LREG_arm. split; [exact HF'|]. split; [exact (HVx s4 c) | subst s4 s3 s2 s1; cbn; intros Hb; exfalso; cbv in Hb; discriminate].
        * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
          do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
          apply MFRAME_refl.
    -
      destruct CL as [(O0 & V256) | [(O & _) | (I64 & I16)]]; [| exfalso; clear - O Olt; lia | exfalso; apply I64; assert (E : code_op here = 0 \/ 1 <= code_op here <= 15) by (clear - Olt Hop; lia); destruct E as [E|E]; [rewrite E; reflexivity | exact (proj1 (proj2 (op_link_tests _ E)))]].
      rewrite O0. cbn [Z.eqb].
      arm_symexP (@nil (Z * expr)) ilS 30%nat [true; true] [RVal (ELit (JT LIT))] lfpins lfvb v r
        [BK mod 2 ^ 64; code_bits here; code_op here; code_val here] NoVals F0
        (mkst R (Z_to_bv 64 0x1e590) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      rewrite le4_BK in Hms1.
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (BK + code_bits here)))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r) M2).
      { apply (LMEM_store_scalar v C s1 c r _ M1 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_length M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (9%bv : reg) as Q9.
      assert (HF' : LFIX v R1) by (apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity).
      pose proof (HV' R1 Q24 ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) ltac:(rewrite (Hfr1 (1%bv : reg) eq_refl); exact G1) Q23 Q8 Q26) as HVx.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16205)) in *.
      assert (HM3' : LMEM v (mkW (iset_mode s2 LIT) c r) M3).
      { apply (LMEM_store_scalar v C s2 c r _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s2 LIT (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW (iset_mode s2 LIT) c r') M3) by (apply (LMEM_regs v (iset_mode s2 LIT) c r c r' M3 HM3'); subst r'; reflexivity).
      exists R1, M3, (arm6_pc LIT). split; [subst M3 M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s2 s1; split; [reflexivity | split; reflexivity] |]].
      * split; [exact HM3|]. split; [subst M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
        -- apply (LX_step0 v s c r _ c r' HX NH NB); subst s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
        -- unfold LREG_arm. split; [exact HF'|]. split; [exact (HVx (iset_mode s2 LIT) c) | subst s2 s1; cbn; intros Hb; exfalso; cbv in Hb; discriminate].
      * cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M3 M2 M1.
        do 3 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
        apply MFRAME_refl.
  Qed.
End LenFin2.
End FXG.
