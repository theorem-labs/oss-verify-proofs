(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Head1 InflA_Head2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac wrap_brc Hw :=
  lazymatch goal with
  | |- _ mod _ <> _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ <> _ mod _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ mod _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  | |- _ / _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section HeadBody2.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_hje HJ :=
    let X := fresh in pose proof HJ as X; unfold HJE, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G12 & G26 & G27); open_fix HF.
  Ltac reload_regs HR Q1 Q10 Q11 Q29 Q30 Q31 :=
    symex_reg HR (1%bv : reg) as Q1; symex_reg HR (10%bv : reg) as Q10; symex_reg HR (11%bv : reg) as Q11;
    symex_reg HR (29%bv : reg) as Q29; symex_reg HR (25%bv : reg) as Q30; symex_reg HR (31%bv : reg) as Q31;
    change 75024 with A6_JTAB in Q30;
    change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31; rewrite zw_neg_mod in Q31.
  Ltac regs_via2 Hfr Hfr1 :=
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ =>
              rewrite (Hfr n eq_refl); first [assumption | rewrite (Hfr1 n eq_refl); assumption] end
          | match goal with |- ?G => idtac "REGS2 LEFT" G end ].


  Lemma head_B_sim : forall s c r1 R M,
    is_mode s = HEAD -> (is_wrap s = 5 \/ is_wrap s = 1) -> is_wbits s = 15 -> is_head s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> HJE v (is_wrap s) c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 16 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1da84) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (head_B (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16. open_hje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_head _ _ _ _ Msc) as C48. rewrite Hhd in C48.
    pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Hwb in C56.
    pose proof (mod31_cell M Mrod : cell s6_segs M (0 + 67208) 8 595056260442243601) as Crod.
    unfold head_B. cbn [w_s w_c w_r].
    assert (Hhx : 0 <= hx (ir_hold r1) < 2 ^ 57).
    { unfold hx. pose proof (Z.mod_pos_bound (ir_hold r1) (2 ^ 8) ltac:(lia)).
      assert (0 <= ir_hold r1 / 2 ^ 8 < 2 ^ 56) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    assert (Hq4 : 0 <= ir_hold r1 / 2 ^ 4 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm4 : 0 <= (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (Hm4' : 0 <= ir_hold r1 mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (XflagsB : forall rr, is_flags s = 0 \/ is_flags s = -1 /\ (BAD = HEAD \/ BAD = BAD) /\ ir_out rr = ir_left rr -> True) by (intros; exact I).
    pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_and2 _ Hw) as Hw2. pose proof (wrap15_and1 _ Hw) as Hw1.
    rewrite <- mod31_magic by (clear - Hhx; lia).
    rewrite <- (hx_exec (ir_hold r1)) by exact Rhold64. rewrite <- inv31_exec. unfold INV31X, MOD31_MAGIC.
    destruct (Z.ltb_spec ((((ir_hold r1 * 2 ^ 56) mod 2 ^ 64 / 2 ^ 48 + ir_hold r1 / 2 ^ 8) * -38083600668303590433) mod 2 ^ 64) 595056260442243601) as [DV|NDV]; cbn [negb].
    2:{
      arm_symexP j1011_pins ilS 50%nat [true; true; false; false; true] [RVal (ELit 0); RVal (ELit 595056260442243601); RVal (ELit (JT BAD))]
        [(12, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1da84) M s6_rom) R' HR' Hfr Hms.
      all: try wrap_brc Hw.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT1" G end.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66808)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_incorrect_header_check).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_incorrect_header_check HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_incorrect_header_check) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      exists R', M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c'. rewrite E11. replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ Xhd))))))); [live_mode_tac | | unfold MSG_incorrect_header_check; lia].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. split; [apply (LFIX_frame v R R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8']. regs_via Hfr.
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec (ir_hold r1 mod 2 ^ 4) 8) as [M8|M8]; cbn [negb].
    2:{
      arm_symexP j1011_pins ilD 50%nat [true; true; false; true; true]
        [RVal (ELit 0); RVal (ELit 595056260442243601); RVal (EVar 34%nat); RVal (ELit 16209); RVal (EVar 35%nat); RVal (ELit 18446744073709535436)]
        [(12, EVar 46%nat)] [(45%nat, 2 ^ 63); (46%nat, 8)] v r1 [cv_S v + 168; is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1da84) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try wrap_brc Hw.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT2" G end.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66987)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_unknown_compression_method).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_unknown_compression_method HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (lm_rod _ _ _ HM2) as Mrod2. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM2)) as C8'. cbn [w_s] in C8'.
      replace (is_mode (iset_mode s BAD)) with BAD in C8' by (destruct s; reflexivity).
      reload_regs HR1 Q1 Q10 Q11 Q29 Q30 Q31.
      j1011_symex ilS 12%nat [true] [RVal (ELit 16209); RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
        (mkst R1 (Z_to_bv 64 pc6_disp) M2 s6_rom) R' HR' Hfr Hms.
      all: try (lazymatch goal with |- getr _ ?n = zw _ => rewrite (Hfr1 n eq_refl); assumption end).
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT2b" G end.
      pose proof (icset_msg_facts c MSG_unknown_compression_method) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      exists R', M2, (arm6_pc BAD). split; [eapply msteps_trans; [| subst M2 M1; by_run Hms]; subst M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c'. rewrite E11. replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ Xhd))))))); [live_mode_tac | | unfold MSG_unknown_compression_method; lia].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. split; [| split; [| intros _; exact G8']].
          -- unfold LFIX, INF_FRAME, A6_JTAB. regs_via2 Hfr Hfr1.
          -- regs_via2 Hfr Hfr1.
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    set (len := (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8) in *.
    set (r2 := irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ 4)) (ir_bits r1 - 4)) in *.
    destruct (Z.ltb_spec 15 len) as [BW|BW].
    {
      assert (BW' : 7 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4) by (clear - BW; lia).
      (* 1.4 order (smodel14-r1's HEAD row): the len > 15 test comes before the wbits load *)
      arm_symexP j1011_pins ilD 60%nat [true; true; false; true; false; true]
        [RVal (ELit 0); RVal (ELit 595056260442243601); RVal (EVar 34%nat); RVal (ELit 16209); RVal (EVar 35%nat); RVal (ELit 18446744073709535436)]
        [(12, EVar 46%nat)] [(45%nat, 2 ^ 63); (46%nat, 8)] v r1 [cv_S v + 168; is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1da84) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try wrap_brc Hw.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66704)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_invalid_window_size).
      assert (HM1 : LMEM v (mkW s c' r2) M1) by (apply (LMEM_regs v s c' r1 c' r2); [exact (LMEM_store_msg v C s c r1 M MSG_invalid_window_size HM Hput) | subst r2; reflexivity ..]).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r2) M2).
      { apply (LMEM_store_scalar v C s c' r2 _ M1 8 _ HM1); [lia | cbn; lia | subst r2; exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (lm_rod _ _ _ HM2) as Mrod2. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM2)) as C8'. cbn [w_s] in C8'.
      replace (is_mode (iset_mode s BAD)) with BAD in C8' by (destruct s; reflexivity).
      reload_regs HR1 Q1 Q10 Q11 Q29 Q30 Q31.
      symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. rewrite ?szwrap32_small in Q8 by (clear - Rbits Hb16; lia).
      j1011_symex ilS 12%nat [true] [RVal (ELit 16209); RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v
        (mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) (ir_hold r1 / 2 ^ 4) (ir_bits r1 - 4) (ir_in r1) (ir_out r1) (ir_ret r1))
        (@nil Z) NoVals F0
        (mkst R1 (Z_to_bv 64 pc6_disp) M2 s6_rom) R' HR' Hfr Hms.
      all: cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      all: try (lazymatch goal with |- getr _ ?n = zw _ => first [rewrite (Hfr1 n eq_refl); assumption | rewrite Q23; f_equal; lia | rewrite Q8; f_equal; lia] end).
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT3b" G end.
      pose proof (icset_msg_facts c MSG_invalid_window_size) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      exists R', M2, (arm6_pc BAD). split; [eapply msteps_trans; [| subst M2 M1; by_run Hms]; subst M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | subst r2; reflexivity]|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c' r2. rewrite E11. cbn [ir_in ir_ret irset_bits irset_hold].
          replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ Xhd))))))); [live_mode_tac | | unfold MSG_invalid_window_size; lia].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (9%bv : reg) as G8'. symex_reg HR' (23%bv : reg) as G22'. symex_reg HR' (24%bv : reg) as G23'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [| split; [| intros _; exact G8']].
          -- unfold LFIX, INF_FRAME, A6_JTAB. regs_via2 Hfr Hfr1.
          -- regs_via2 Hfr Hfr1; first [exact G22' | exact G23'].
      + subst M2 M1 r2. cbn [ir_put irset_bits irset_hold].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    exact (head_ok v C s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16 DV M8 ltac:(subst len; clear - BW; lia)).
  Qed.
End HeadBody2.

Lemma sr_head : forall s, SRNGq s -> is_head s = 0.
Proof. intros s H. do 30 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Theorem arm_HEAD_sim : arm_stmt HEAD.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) HEAD) with (arm_HEAD ivar_ref).
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  arm_begin C HM HRC HX HF HV HP.
  pose proof (sr_head s SR) as Hhd.
  pose proof (head_need v C s c r R M Xwrap HM HRC HF HV RI CI) as HN.
  destruct (NEEDBITS 16 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct HN].
  - destruct HN as (r1 & R1 & -> & Hms1 & HJE & RI1 & S5 & Hb16).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof RI1 as RI1'. unfold RINV in RI1'. destruct RI1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
    rewrite (arm_HEAD_run s c r s c r1 Xwrap Xwbits EN eq_refl ltac:(clear - Hb16 Rb1; lia) Rh1).
    assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]).
    assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | exact Q5]).
    assert (HX1 : LX v (mkW s c r1)).
    { apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
      destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [exact XM|]. rewrite Q2, Q4. exact XO. }
    destruct (head_B_sim v C s c r1 R1 M Hmode Xwrap Xwbits Hhd HM1 HRC1 HX1 HJE RI1 CI Hb16) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
  - destruct HN as (r1 & R1 & -> & Hms1 & HL1 & RI1 & S5).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_HEAD_leave s c r _ Xwrap EN).
    exists R1, M, pc6_leave. split; [exact Hms1|].
    cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
    split; [apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]|].
    split; [| split; [apply same_blocks_refl | exact HL1]].
    apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
    destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [exact XM|]. rewrite Q2, Q4. exact XO.
Qed.
End FXG.
