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


Definition r_drop3 (r : iregs) : iregs := irset_bits (irset_hold r (ir_hold r / 2 ^ 3)) (ir_bits r - 3).

Definition typedo_B (flush : Z) (w : iw) : ares unit :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  let v := ir_hold r mod 2 ^ 1 in
  let t := (ir_hold r / 2 ^ 1) mod 2 ^ 2 in
  let s1 := iset_last s v in
  if t =? 0 then ARun tt (mkW (iset_mode s1 STORED) c (r_drop3 r))
  else if t =? 1 then
    (if flush =? Z_TREES then ALeave (mkW (iset_mode (fixedtables s1) LEN_) c (r_drop3 r))
     else ARun tt (mkW (iset_mode (fixedtables s1) LEN_) c (r_drop3 r)))
  else if t =? 2 then ARun tt (mkW (iset_mode s1 TABLE) c (r_drop3 r))
  else ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_block_type) (r_drop3 r)).

Lemma arm_TYPEDO_run : forall flush s c r s1 c1 r1,
  is_last s = 0 ->
  NEEDBITS 3 (mkW s c r) = ARun tt (mkW s1 c1 r1) ->
  3 <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_TYPEDO ivar_ref flush (mkW s c r) = typedo_B flush (mkW s1 c1 r1).
Proof.
  intros flush s c r s1 c1 r1 Hlast HN Hb Hh.
  assert (E1 : wrap32 (ir_bits r1 - 1) = ir_bits r1 - 1) by (apply wrap32_id; lia).
  assert (E2 : wrap32 (ir_bits r1 - 1 - 2) = ir_bits r1 - 3) by (rewrite wrap32_id by lia; lia).
  assert (E3 : Z.shiftr (ir_hold r1 / 2 ^ 1) 2 = ir_hold r1 / 2 ^ 3).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. reflexivity. }
  assert (E4 : Z.shiftr (ir_hold r1) 1 = ir_hold r1 / 2 ^ 1) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (B1 : BITSv (ir_hold r1) 1 = ir_hold r1 mod 2 ^ 1) by (rewrite BITSv_land, Z.land_ones by lia; reflexivity).
  assert (B2 : BITSv (ir_hold r1 / 2 ^ 1) 2 = (ir_hold r1 / 2 ^ 1) mod 2 ^ 2) by (rewrite BITSv_land, Z.land_ones by (first [apply Z.div_pos; lia | lia]); reflexivity).
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite Hlast. cbn [Z.eqb negb].
  rewrite abind_run, HN.
  mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. irnorm. rewrite E1, E4. mstep1 BITS_eq. irnorm. rewrite B1, B2.
  unfold typedo_B, r_drop3. irnorm.
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 0) eqn:T0.
  { rewrite abind_run. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 1) eqn:T1.
  { rewrite abind_run. rewrite abind_run. rewrite us_eq. cbv beta iota. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. cbn [iv_flush_exits ivar_ref andb].
    destruct (flush =? Z_TREES).
    - rewrite abind_run, DROPBITS_eq. cbv beta iota. rewrite aleave_eq. irnorm. rewrite E3, E2. reflexivity.
    - rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  destruct ((ir_hold r1 / 2 ^ 1) mod 2 ^ 2 =? 2) eqn:T2.
  { rewrite abind_run. rewrite abind_run. rewrite set_mode_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity. }
  rewrite abind_run. rewrite abind_run. rewrite go_bad_eq. cbv beta iota. rewrite aret_eq. rewrite DROPBITS_eq. irnorm. rewrite E3, E2. reflexivity.
Qed.

Lemma arm_TYPEDO_leave : forall flush s c r w1,
  is_last s = 0 -> NEEDBITS 3 (mkW s c r) = ALeave w1 ->
  arm_TYPEDO ivar_ref flush (mkW s c r) = ALeave w1.
Proof.
  intros flush s c r w1 Hlast HN.
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite Hlast. cbn [Z.eqb negb].
  rewrite abind_run, HN. reflexivity.
Qed.

Lemma arm_TYPEDO_last : forall flush s c r,
  is_last s <> 0 ->
  arm_TYPEDO ivar_ref flush (mkW s c r)
  = ARun tt (mkW (iset_mode s CHECK) c
                 (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)))).
Proof.
  intros flush s c r Hlast.
  unfold arm_TYPEDO. mstep1 (@gs_eq inflate_state). rewrite (proj2 (Z.eqb_neq _ _) Hlast). cbn [negb].
  mstep1 BYTEBITS_eq. rewrite set_mode_eq. reflexivity.
Qed.

Lemma NEEDBITS3_eq : forall s c r,
  0 <= ir_bits r < 64 ->
  NEEDBITS 3 (mkW s c r)
  = if ir_bits r <? 3 then
      (if ir_have r =? 0 then ALeave (mkW s c r) else ARun tt (mkW s c (pullr c r)))
    else ARun tt (mkW s c r).
Proof.
  intros s c r Hb. unfold NEEDBITS. rewrite NEEDBITS_k_S.
  destruct (ir_bits r <? 3) eqn:E; [|reflexivity]. destruct (ir_have r =? 0); [reflexivity|].
  apply NEEDBITS_k_done. unfold pullr. cbn [ir_bits]. apply Z.ltb_lt in E. rewrite wrap32_id by lia. lia.
Qed.


Definition ilT : cfg := ilSx [0x1d460] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].
(* 1.4: TYPE's fixed-table case walks to the dispatch first (as HEAD's adler path does) *)
Definition ilDT : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].

Section ArmTYPE.

  (* register facts across two walks (Head2's regs_via2) *)
  Ltac regs_via2T Hfr Hfr1 :=
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ =>
              rewrite (Hfr n eq_refl); first [assumption | rewrite (Hfr1 n eq_refl); assumption] end
          | match goal with |- ?G => idtac "REGS2 LEFT" G end ].

  Definition JREG (v : icv) (w : iw) (R : bvmap 5 word) : Prop :=
    let r := w_r w in
    LFIX v R /\ getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Lemma typedo_A : forall v s c r R M,
    ictx v -> ENTRY v (mkW s c r) R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_last s = 0 ->
    exists R1,
      match NEEDBITS 3 (mkW s c r) with
      | ARun _ w1 =>
          msteps s6_segs (mkst R (Z_to_bv 64 0x1d428) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom)
          /\ JREG v w1 R1 /\ 3 <= ir_bits (w_r w1) /\ RINV (cv_NI v) (cv_NO v) (w_r w1)
          /\ w_s w1 = s /\ w_c w1 = c /\ ir_put (w_r w1) = ir_put r /\ ir_left (w_r w1) = ir_left r
          /\ ir_out (w_r w1) = ir_out r /\ ir_in (w_r w1) = ir_in r /\ ir_ret (w_r w1) = ir_ret r
      | ALeave w1 =>
          msteps s6_segs (mkst R (Z_to_bv 64 0x1d428) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
          /\ w1 = mkW s c r /\ LREG_leave v (mkW s c r) R1
      | ARet _ _ => False
      end.
  Proof.
    intros v s c r R M C HE HP Hlast. destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    arm_begin C HM HRC HX HF HV HP.
    pose proof (is6_last _ _ _ _ Msc) as C12. rewrite Hlast in C12.
    rewrite NEEDBITS3_eq by exact Rbits.
    destruct (Z.ltb_spec (ir_bits r) 3) as [Hb3|Hb3].
    - destruct (Z.eq_dec (ir_have r) 0) as [Hh0|Hh0].
      +
        rewrite (proj2 (Z.eqb_eq _ _) Hh0).
        arm_symex ilT 8%nat [false; false; false] [RVal (ELit 0); RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r [ir_ret r mod 2 ^ 64] NoVals F0
          (mkst R (Z_to_bv 64 0x1d428) M s6_rom) R1 HR1 Hfr Hms.
        all: try arm_side.
        exists R1. split; [by_run Hms|]. split; [reflexivity|].
        symex_reg HR1 (9%bv : reg) as G8'.
        unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr. rewrite G8'. apply zw_neg_mod.
      +
        rewrite (proj2 (Z.eqb_neq _ _) Hh0).
        assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh0 Rnx0 Rhv0 Rnh; lia).
        pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
        pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
        arm_symex ilT 12%nat [false; false; true] [RVal (ELit 0)] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals
          (famA c s)
          (mkst R (Z_to_bv 64 0x1d428) M s6_rom) R1 HR1 Hfr Hms.
        all: try arm_side.
        assert (Hh32 : 0 < ir_have r < 2 ^ 32) by (clear - Hh0 Rnx0 Rhv0 Rnh CI0; lia).
        rewrite (pullr_small' c r Hh32 ltac:(clear - Rbits Hb3; lia) Rhold Hby).
        exists R1. split; [by_run Hms|].
        symex_reg HR1 (26%bv : reg) as G27'. symex_reg HR1 (23%bv : reg) as G22'. symex_reg HR1 (18%bv : reg) as G9'. symex_reg HR1 (24%bv : reg) as G23'.
        cbn [famA] in G22'. rewrite bmod_get in G22' by exact Hby.
        rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22';
          [| clear - Hby; lia | clear - Rbits Hb3; lia | clear - Hby Rbits Hb3; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia].
        split.
        { unfold JREG; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
          split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr.
          - rewrite G9'. rewrite szwrap32_small by (clear - Hh32 CI0 Rnh Rnx0; lia). reflexivity.
          - rewrite G22'. f_equal. lia.
          - rewrite G23'. rewrite lor8_small by (clear - Rbits Hb3; lia). reflexivity.
          - rewrite G27'. f_equal. lia. }
        cbn [w_s w_c w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_in ir_ret].
        split; [clear - Rbits Hb3; lia|].
        split.
        { pose proof (pull_hold_lt _ _ _ Rhold ltac:(clear - Rbits; lia) Hby) as HH.
          unfold RINV; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
          clear - HH Hh32 Rnx0 Rhv0 Rnh Rpt0 Rlf0 Rpl Rin Rout Routp Rbits Hb3. repeat (split; [lia|]). exact (proj2 HH). }
        repeat (split; [reflexivity|]). reflexivity.
    -
      arm_symex ilT 8%nat [false; true] [RVal (ELit 0)] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1d428) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      split.
      { unfold JREG; cbn [w_r]. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr.
        symex_reg HR1 (26%bv : reg) as G27'. exact G27'. }
      cbn [w_s w_c w_r]. split; [exact Hb3|]. split; [exact RI|]. repeat (split; [reflexivity|]). reflexivity.
  Qed.

  Lemma typedo_B_sim : forall v s c r1 R1 M,
    ictx v -> LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> JREG v (mkW s c r1) R1 ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c ->
    (is_mode s = TYPE \/ is_mode s = TYPEDO) -> 3 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (typedo_B (cv_flush v) (mkW s c r1)) R' M' pc'.
  Proof.
    intros v s c r1 R1 M C HM HRC HX HJ RI CI Hmode Hb3.
    destruct HJ as (HF & G9 & G18 & G1 & G22 & G23 & G27).
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_rinv RI. open_cinv CI.
    pose proof Rhold as Hh1.
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (clear - Hmode; destruct Hmode as [E|E]; rewrite E; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (clear - Hmode; destruct Hmode as [E|E]; rewrite E; cbv; discriminate).
    unfold typedo_B. cbn [w_s w_c w_r].
    set (t := (ir_hold r1 / 2 ^ 1) mod 2 ^ 2). set (lastv := ir_hold r1 mod 2 ^ 1).
    assert (Ht : 0 <= t < 4) by (subst t; apply Z.mod_pos_bound; lia).
    assert (Hlastv : 0 <= lastv < 2) by (subst lastv; apply Z.mod_pos_bound; lia).
    assert (Et : (ir_hold r1 mod 2 ^ 3) / 2 ^ 1 = t).
    { subst t. clear - Hh1. rewrite <- (Z.mod_small ((ir_hold r1 mod 2 ^ 3) / 2 ^ 1) (2 ^ 2)).
      2:{ split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 1 * 2 ^ 2) with (2 ^ 3). apply Z.mod_pos_bound; lia. }
      rewrite <- !Z.shiftr_div_pow2 by lia. rewrite <- !Z.land_ones by lia.
      apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec, Z.land_spec by lia.
      destruct (Z_lt_le_dec n 2).
      - rewrite !Z.ones_spec_low by lia. rewrite !andb_true_r. reflexivity.
      - rewrite (Z.ones_spec_high 2 n) by lia. rewrite !andb_false_r. reflexivity. }
    assert (El : ir_hold r1 mod 2 ^ 1 = lastv) by reflexivity.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    set (r' := r_drop3 r1).
    assert (HM0 : LMEM v (mkW s c r') M) by (apply (LMEM_regs v s c r1 c r' M HM); reflexivity).
    set (s1 := iset_last s lastv).
    set (M1 := wbytes M (zw (cv_S v + 12)) (Z_to_le_bytes 4 lastv)).
    assert (HM1 : LMEM v (mkW s1 c r') M1).
    { apply (LMEM_store_scalar v C s c r' s1 M 12 _ HM0); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_last M (cv_S v) _ s lastv Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    destruct (Z.eqb_spec t 2) as [T2|T2].
    {
      replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      j11_symex ilS 30%nat [true; false; true] [RVal (ELit (JT TABLE))] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16196)).
      assert (HM2 : LMEM v (mkW (iset_mode s1 TABLE) c r') M2).
      { apply (LMEM_store_scalar v C s1 c r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s1 TABLE (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R', M2, (arm6_pc TABLE). split; [subst M2 M1; rewrite El in Hms; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
      - split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
        + symex_reg HR' (23%bv : reg) as G22'. symex_reg HR' (24%bv : reg) as G23'. symex_reg HR' (27%bv : reg) as G26'. symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [apply (LFIX_frame v R1 R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8'].
          regs_via Hfr.
          * exact G22'.
          * rewrite G23'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
          * exact G26'.
      - subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec t 0) as [T0|T0].
    {
      replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      j11_symex ilS 30%nat [false; false; true] [RVal (ELit (JT STORED))] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16193)).
      assert (HM2 : LMEM v (mkW (iset_mode s1 STORED) c r') M2).
      { apply (LMEM_store_scalar v C s1 c r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s1 STORED (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R', M2, (arm6_pc STORED). split; [subst M2 M1; rewrite El in Hms; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
      - split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
        + symex_reg HR' (23%bv : reg) as G22'. symex_reg HR' (24%bv : reg) as G23'. symex_reg HR' (27%bv : reg) as G26'. symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [apply (LFIX_frame v R1 R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8'].
          regs_via Hfr.
          * exact G22'.
          * rewrite G23'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
          * exact G26'.
      - subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec t 1) as [T1|T1].
    {
      replace (cv_flush v =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; clear - Cflush; lia).
      (* 1.4: the fixed tables come from a call to inflate_fixed (0x1f834, a leaf, walked inline); after it the arm
         reloads t6 (sp + 88), flush (sp + 104) and strm (sp + 96) from the frame *)
      (* Two walks, as HEAD's adler path: to the dispatch (t6 comes back from the frame as the unsigned word, so the
         jump-table address is only computed after t6 is re-pinned as -16180), then the dispatch to LEN_. *)
      open_frame Mfr. unfold mapped in *.
      j11_symex ilDT 60%nat [false; true; true]
        [RVal (ELit 18446744073709535436); RVal (EVar 35%nat); RVal (EVar 34%nat)]
        (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom) R2 HR2 Hfr2 Hms2.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTT1" G end.
      set (M2 := wbytes M1 (zw (cv_S v + 120)) (Z_to_le_bytes 8 75438)).
      set (M3 := wbytes M2 (zw (cv_S v + 128)) (Z_to_le_bytes 8 77486)).
      set (M4 := wbytes M3 (zw (cv_S v + 136)) (Z_to_le_bytes 8 21474836489)).
      set (M5 := wbytes M4 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16199)).
      assert (HM2 : LMEM v (mkW (iset_lencode s1 CLenfix) c r') M2).
      { apply (LMEM_store_scalar v C _ c r' _ M1 120 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_lencode M1 (cv_S v) _ _ CLenfix (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW (iset_distcode (iset_lencode s1 CLenfix) CDistfix) c r') M3).
      { apply (LMEM_store_scalar v C _ c r' _ M2 128 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_distcode M2 (cv_S v) _ _ CDistfix (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4 : LMEM v (mkW (iset_distbits (iset_lenbits (iset_distcode (iset_lencode s1 CLenfix) CDistfix) 9) 5) c r') M4).
      { apply (LMEM_store_scalar v C _ c r' _ M3 136 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        subst M4. rewrite (wbytes_sd_split M3 (cv_S v + 136) 21474836489).
        replace (cv_S v + 136 + 4) with (cv_S v + 140) by lia. change (Z.shiftr 21474836489 32) with 5.
        apply (is6_upd_distbits _ (cv_S v) _ _ 5); [| clear - CS; lia | clear - CS; unfold is6_SIZE; lia].
        rewrite (le4_eqm 21474836489 9) by reflexivity.
        apply (is6_upd_lenbits M3 (cv_S v) _ _ 9 (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (Efx : iset_distbits (iset_lenbits (iset_distcode (iset_lencode s1 CLenfix) CDistfix) 9) 5 = fixedtables s1) by (clear; unfold fixedtables; destruct s1; reflexivity).
      rewrite Efx in HM4.
      assert (HM5 : LMEM v (mkW (iset_mode (fixedtables s1) LEN_) c r') M5).
      { apply (LMEM_store_scalar v C _ c r' _ M4 8 _ HM4); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M4 (cv_S v) _ _ LEN_ (lm_sc _ _ _ HM4)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (lm_rod _ _ _ HM5) as Mrod5. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM5)) as C8'. cbn [w_s] in C8'.
      replace (is_mode (iset_mode (fixedtables s1) LEN_)) with LEN_ in C8' by (destruct (fixedtables s1); reflexivity).
      symex_reg HR2 (1%bv : reg) as Q1. symex_reg HR2 (10%bv : reg) as Q10. symex_reg HR2 (11%bv : reg) as Q11.
      symex_reg HR2 (29%bv : reg) as Q29. symex_reg HR2 (31%bv : reg) as Q31.
      change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31. rewrite zw_neg_mod in Q31.
      symex_reg HR2 (23%bv : reg) as Q23. symex_reg HR2 (24%bv : reg) as Q24.
      rewrite ?szwrap32_small in Q24 by (clear - Hb3 Rbits; lia).
      clear HR2.
      j11_symex ilS 12%nat [true] [RVal (ELit 16199); RVal (ELit (JT LEN_))] (@nil (Z * expr)) (@nil (nat * Z)) v r' (@nil Z) NoVals F0
        (mkst R2 (Z_to_bv 64 pc6_disp) M5 s6_rom) R' HR' Hfr Hms.
      all: unfold r'; cbn [r_drop3 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret irset_bits irset_hold].
      all: try (lazymatch goal with |- getr _ ?n = zw _ =>
                  first [assumption | rewrite (Hfr2 n eq_refl); assumption | rewrite Q23; f_equal; lia | rewrite Q24; f_equal; lia] end).
      all: try arm_side.
      all: try (assert (0 <= ir_hold r1 / 2 ^ 3 <= ir_hold r1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia).
      all: match goal with |- ?G => idtac "LEFTT2" G end.
      exists R', M5, (arm6_pc LEN_). split.
      { apply (msteps_trans _ _ (mkst R2 (Z_to_bv 64 pc6_disp) M5 s6_rom)); [| by_run Hms].
        subst M5 M4 M3 M2 M1; rewrite El in Hms2; by_run Hms2. }
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; clear; split; [| split]; unfold fixedtables; destruct s; reflexivity |]].
      - split; [exact HM5|]. split; [subst M5 M4 M3 M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; try (clear; unfold fixedtables; destruct s; reflexivity); [live_mode_tac | exact Xret | exact Xmsg].
        + symex_reg HR' (27%bv : reg) as G26'. symex_reg HR' (9%bv : reg) as G8'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'.
          cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold] in *.
          split; [unfold LFIX, INF_FRAME, A6_JTAB; regs_via2T Hfr Hfr2|]. split; [| intros _; exact G8'].
          regs_via2T Hfr Hfr2.
      - subst M5 M4 M3 M2 M1.
        do 5 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
        apply MFRAME_refl. }
    assert (T3 : t = 3) by lia.
    j11_symex ilS 40%nat [true; true; true] [RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
      (mkst R1 (Z_to_bv 64 0x1d460) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66674)).
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)).
    set (c' := icset_msg c MSG_invalid_block_type).
    assert (HM2 : LMEM v (mkW s1 c' r') M2) by (exact (LMEM_store_msg v C s1 c r' M1 MSG_invalid_block_type HM1 Hput)).
    assert (HM3 : LMEM v (mkW (iset_mode s1 BAD) c' r') M3).
    { apply (LMEM_store_scalar v C s1 c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s1 BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (icset_msg_facts c MSG_invalid_block_type) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    exists R', M3, (arm6_pc BAD). split; [subst M3 M2 M1; rewrite El in Hms; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
    - split; [exact HM3|]. split; [subst M3 M2 M1; retc_tower C HRC|]. split.
      + apply (LX_step0 v s c r1 _ c' r' HX NH NB); subst s1 r' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; unfold MSG_invalid_block_type; lia].
      + symex_reg HR' (23%bv : reg) as G22'. symex_reg HR' (24%bv : reg) as G23'. symex_reg HR' (27%bv : reg) as G26'. symex_reg HR' (9%bv : reg) as G8'.
        unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
        split; [apply (LFIX_frame v R1 R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8'].
        regs_via Hfr.
        * exact G22'.
        * rewrite G23'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
        * exact G26'.
    - subst M3 M2 M1.
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End ArmTYPE.
End FXG.
