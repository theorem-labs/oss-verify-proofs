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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Match3 InflA_Match5 InflA_Distext1 InflA_Distext2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilXE : cfg := CFG [] [] arm_rets (0x1e784 :: arm_stops) [].

Section DistextCore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_df HD :=
    destruct HD as (Hsane & Hlen & Hoff & Hex & Hoe & Hback & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).

  Lemma distext_core : forall s c r R M,
    is_mode s = DISTEXT -> distext_facts v s c r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    getr R 13 = zw (is_extra s) ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e784) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_DISTEXT ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD HM HRC HX HF HV G13. pose proof HD as HD0. open_df HD.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    rewrite Z.shiftl_1_l in Hoe.
    destruct (Z.eq_dec (is_extra s) 0) as [E0|E0].
    -
      rewrite (arm_DISTEXT_zero s c r E0). rewrite E0 in G13.
      arm_symex ilXA 6%nat [true] (@nil (option expr)) [(13, ELit 0)] (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1e784) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16204)) in *.
      assert (HM1 : LMEM v (mkW (iset_mode s MATCH) c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M (cv_S v) _ s MATCH Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HE1 : ENTRY v (mkW (iset_mode s MATCH) c r) R1 M1).
      { split; [exact HM1|]. split; [subst M1; retc_tower C HRC|]. split.
        - apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
        - unfold LREG_arm. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. split; [unfold LVARS; cbn [w_r]; regs_via Hfr1 | cbn; intros Hb; exfalso; cbv in Hb; discriminate]. }
      assert (MF1 : match_facts v (iset_mode s MATCH) c r).
      { unfold match_facts. cbn. rewrite E0 in Hoe. refine (conj Hsane (conj _ (conj _ (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj RI CI))))))))); [clear - Hlen; lia | clear - Hoff Hoe; cbn in Hoe; lia]. }
      destruct (match_core v C (iset_mode s MATCH) c r R1 M1 ltac:(reflexivity) HE1 MF1) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r) (mkW (iset_mode s MATCH) c r) M M1); [apply same_blocks_mode | | exact HPOST].
      cbn [w_r]. subst M1. apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      assert (Hex1 : 1 <= is_extra s <= 15) by (clear - Hex E0; lia).
      assert (P2e : 0 < 2 ^ is_extra s) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z_le_gt_dec (is_extra s) (ir_bits r)) as [GE|LT].
      +
        assert (HN : NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c r)) by (unfold NEEDBITS; apply NEEDBITS_k_done; cbn; exact GE).
        rewrite (arm_DISTEXT_run s c r c r ltac:(lia) ltac:(lia) ltac:(clear - Hoe P2e Hoff; lia) HN ltac:(clear - GE Rbits; lia) Rhold).
        arm_symex ilXA 8%nat [false; true] (@nil (option expr)) [(13, EVar 45%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
          (mkst R (Z_to_bv 64 0x1e784) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        assert (HJ : XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
        { symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (15%bv : reg) as Q15.
          unfold XJE, XK. repeat match goal with |- _ /\ _ => split end;
            first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                  | exact Q14 | exact Q12 | exact Q15 ]. }
        destruct (distext_body v C s c r R1 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD0 E0 GE HM HRC HX HJ) as (R' & M' & pc' & Hms2 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
      +
        arm_symex ilXA 8%nat [false; false] (@nil (option expr)) [(13, EVar 45%nat)] [(45%nat, 16)] v r [is_extra s] NoVals F0
          (mkst R (Z_to_bv 64 0x1e784) M s6_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        assert (HJ : XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s) c r R1).
        { symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (12%bv : reg) as Q12. symex_reg HR1 (16%bv : reg) as Q16.
          unfold XJS, XK. repeat match goal with |- _ /\ _ => split end;
            first [ apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity
                  | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr1 n eq_refl); assumption end
                  | exact Q14 | exact Q12 | exact Q16 | clear; lia | clear - Rbits; lia ]. }
        pose proof (need_loop v (is_extra s) 0x1e798 0x1e7e4 (XJS v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) (XJE v (ir_bits r) (ir_have r) (ir_next r) (is_extra s)) C ltac:(lia)
                      (distext_step_H v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      (distext_step_E v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      (distext_dry v C (ir_bits r) (ir_have r) (ir_next r) (is_extra s) Hex1 (proj1 Rbits) Rnx0)
                      8%nat s c r R1 M HM HRC HJ RI CI ltac:(lia) ltac:(cbn; clear - LT Rbits Hex1; lia)) as NL.
        change (NEEDBITS_k 8 (is_extra s)) with (NEEDBITS (is_extra s)) in NL.
        destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct NL].
        * destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
          destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
          pose proof RI1 as X. unfold RINV in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
          rewrite (arm_DISTEXT_run s c r c r1 ltac:(lia) ltac:(lia) ltac:(clear - Hoe P2e Hoff; lia) EN ltac:(clear - Hb1 Rb1; lia) Rh1).
          assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
          assert (HD1 : distext_facts v s c r1) by (unfold distext_facts; rewrite Z.shiftl_1_l; exact (conj Hsane (conj Hlen (conj Hoff (conj Hex (conj Hoe (conj Hback (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj RI1 CI))))))))))))).
          destruct (distext_body v C s c r1 R2 M (ir_bits r) (ir_have r) (ir_next r) Hmode HD1 E0 ltac:(clear - Hb1; lia) HM1 HRC1 HX1 HJE) as (R' & M' & pc' & Hms3 & HPOST).
          exists R', M', pc'. split; [eapply msteps_trans; [| eapply msteps_trans; [exact Hms2 | exact Hms3]]; by_run Hms1|].
          apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
        * destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
          destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
          rewrite (arm_DISTEXT_leave s c r _ E0 EN).
          exists R2, M, pc6_leave. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1|].
          cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
          split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
          apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End DistextCore.

Theorem arm_DISTEXT_sim : arm_stmt DISTEXT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DISTEXT) with (arm_DISTEXT ivar_ref).
  pose proof (distext_facts_of_pinv v s c r Hmode HP) as HD.
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  pose proof HM as HM0. pose proof HX as HX0. pose proof HF as HF0. pose proof HV as HV0.
  arm_begin C HM HRC HX HF HV HP.
  pose proof (is6_extra _ _ _ _ Msc) as C100.
  pose proof HD as HD'. destruct HD' as (_ & _ & _ & Hex & _).
  change (arm6_pc DISTEXT) with 0x1d198.
  arm_symex ilXE 4%nat (@nil bool) [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 16)] v r [is_extra s] NoVals F0
    (mkst R (Z_to_bv 64 0x1d198) M s6_rom) R1 HR1 Hfr1 Hms1.
  all: try arm_side.
  symex_reg HR1 (13%bv : reg) as G13.
  destruct (distext_core v C s c r R1 M Hmode HD HM0 HRC HX0 (LFIX_frame v R R1 _ HF0 Hfr1 eq_refl)
              ltac:(unfold LVARS; cbn [w_r]; regs_via Hfr1) G13) as (R' & M' & pc' & Hms2 & HPOST).
  exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
Qed.
End FXG.
