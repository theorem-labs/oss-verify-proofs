(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6.

Module InflA_Type.
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


Definition ilT : cfg := ilSx [0x1f530] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section ArmTYPE.

  Definition JREG (v : icv) (w : iw) (R : bvmap 5 word) : Prop :=
    let r := w_r w in
    LFIX v R /\ getr R 23 = zw (ir_have r) /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r)
    /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Lemma typedo_A : forall v s c r R M,
    ictx v -> ENTRY v (mkW s c r) R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_last s = 0 ->
    exists R1,
      match NEEDBITS 3 (mkW s c r) with
      | ARun _ w1 =>
          msteps s6u_segs (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom)
          /\ JREG v w1 R1 /\ 3 <= ir_bits (w_r w1) /\ RINV (cv_NI v) (cv_NO v) (w_r w1)
          /\ w_s w1 = s /\ w_c w1 = c /\ ir_put (w_r w1) = ir_put r /\ ir_left (w_r w1) = ir_left r
          /\ ir_out (w_r w1) = ir_out r /\ ir_in (w_r w1) = ir_in r /\ ir_ret (w_r w1) = ir_ret r
      | ALeave w1 =>
          msteps s6u_segs (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
          /\ w1 = mkW s c r /\ LREG_leave v (mkW s c r) R1
      | ARet _ _ => False
      end.
  Proof.
    intros v s c r R M C HE HP Hlast. destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    arm_begin C HM HRC HX HF HV HP.
    pose proof (is6_last _ _ _ _ Msc) as C12. rewrite Hlast in C12.
    rewrite NEEDBITS3_eq by exact Rbits.
    destruct (Z.ltb_spec (ir_bits r) 3) as [Hb3|Hb3].
    - destruct (Z.eq_dec (ir_have r) 0) as [Hh0|Hh0].
      +
        rewrite (proj2 (Z.eqb_eq _ _) Hh0).
        arm_symex ilT 12%nat [true; false; false] [RVal (ELit 0); RVal (EVar 45%nat); RVal (EVar 35%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r [ir_ret r mod 2 ^ 64] NoVals F0
          (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) R1 HR1 Hfr Hms.
        all: try arm_side.
        exists R1. split; [by_run Hms|]. split; [reflexivity|].
        symex_reg HR1 (27%bv : reg) as G26'.
        unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr. rewrite G26'. apply zw_neg_mod.
      +
        rewrite (proj2 (Z.eqb_neq _ _) Hh0).
        assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh0 Rnx0 Rhv0 Rnh; lia).
        pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
        pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
        arm_symex ilT 20%nat [true; false; true; true] [RVal (ELit 0); RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals
          (famA c s)
          (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) R1 HR1 Hfr Hms.
        all: try arm_side.
        assert (Hh32 : 0 < ir_have r < 2 ^ 32) by (clear - Hh0 Rnx0 Rhv0 Rnh CI0; lia).
        rewrite (pullr_small' c r Hh32 ltac:(clear - Rbits Hb3; lia) Rhold Hby).
        exists R1. split; [by_run Hms|].
        symex_reg HR1 (26%bv : reg) as G25'. symex_reg HR1 (25%bv : reg) as G22'. symex_reg HR1 (23%bv : reg) as G24'. symex_reg HR1 (19%bv : reg) as G18'.
        cbn [famA] in G22'. rewrite bmod_get in G22' by exact Hby.
        rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22';
          [| clear - Hby; lia | clear - Rbits Hb3; lia | clear - Hby Rbits Hb3; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby); assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia].
        split.
        { unfold JREG; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
          split; [lfix_close Hfr HR1|]. regs_via Hfr.
          - rewrite G24'. rewrite szwrap32_small by (clear - Hh32 CI0 Rnh Rnx0; lia). reflexivity.
          - rewrite G22'. f_equal. lia.
          - rewrite G18'. rewrite lor8_small by (clear - Rbits Hb3; lia). reflexivity.
          - rewrite G25'. f_equal. lia. }
        cbn [w_s w_c w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_in ir_ret].
        split; [clear - Rbits Hb3; lia|].
        split.
        { pose proof (pull_hold_lt _ _ _ Rhold ltac:(clear - Rbits; lia) Hby) as HH.
          unfold RINV; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
          clear - HH Hh32 Rnx0 Rhv0 Rnh Rpt0 Rlf0 Rpl Rin Rout Routp Rbits Hb3. repeat (split; [lia|]). exact (proj2 HH). }
        repeat (split; [reflexivity|]). reflexivity.
    -
      arm_symex ilT 8%nat [true; true] [RVal (ELit 0)] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
        (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      split.
      { unfold JREG; cbn [w_r]. split; [lfix_close Hfr HR1|]. regs_via Hfr. }
      cbn [w_s w_c w_r]. split; [exact Hb3|]. split; [exact RI|]. repeat (split; [reflexivity|]). reflexivity.
  Qed.

  Lemma typedo_B_sim : forall v s c r1 R1 M,
    ictx v -> LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> JREG v (mkW s c r1) R1 ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c ->
    (is_mode s = TYPE \/ is_mode s = TYPEDO) -> 3 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M (typedo_B (cv_flush v) (mkW s c r1)) R' M' pc'.
  Proof.
    intros v s c r1 R1 M C HM HRC HX HJ RI CI Hmode Hb3.
    destruct HJ as (HF & G24 & G9 & G22 & G18 & G25).
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_lx HX. open_fix HF. open_rinv RI. open_cinv CI.
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
      arm_symex ilS 30%nat [true; false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16196)).
      assert (HM2 : LMEM v (mkW (iset_mode s1 TABLE) c r') M2).
      { apply (LMEM_store_scalar v C s1 c r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s1 TABLE (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s1 TABLE))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; rewrite El in Hms; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
      - split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        + symex_reg HR' (25%bv : reg) as G22'. symex_reg HR' (19%bv : reg) as G18'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr.
          * exact G22'.
          * rewrite G18'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
      - subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec t 0) as [T0|T0].
    {
      replace (t =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 30%nat [false; false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16193)).
      assert (HM2 : LMEM v (mkW (iset_mode s1 STORED) c r') M2).
      { apply (LMEM_store_scalar v C s1 c r' _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s1 STORED (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s1 STORED))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; rewrite El in Hms; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
      - split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        + symex_reg HR' (25%bv : reg) as G22'. symex_reg HR' (19%bv : reg) as G18'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr.
          * exact G22'.
          * rewrite G18'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
      - subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec t 1) as [T1|T1].
    {
      replace (cv_flush v =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; clear - Cflush; lia).
      (* zlib 1.4: the fixed tables are set by a CALL, inflate_fixed(state) at 0x22550 (UBSan null and 8-alignment checks
         on state, then the three stores of 1.3.1's inlined fixedtables); after it, ra and flush are re-read from the frame *)
      assert (CS8 : cv_S v mod 8 = 0).
      { clear - CS. destruct CS as (_ & _ & H16). apply Z.mod_divide in H16; [|lia]. destruct H16 as [k Hk]. rewrite Hk.
        replace (k * 16) with ((k * 2) * 8) by lia. apply Z.mod_mul. lia. }
      assert (HS7 : Z.land (cv_S v) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact CS8).
      arm_symex ilS 40%nat [false; true; false; false; true] [RVal (ELit 16209); RVal (EVar 35%nat)] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: try (rewrite HS7; reflexivity).
      all: lazymatch goal with |- exists _ _ _, _ => idtac | |- ?G => idtac "LEFTT2" G end.
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
      arm_disp C HM5 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M5, (arm6_pc (is_mode (iset_mode (fixedtables s1) LEN_))). split; [eapply msteps_trans; [| exact Hms2]; subst M5 M4 M3 M2 M1; rewrite El in Hms; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; clear; split; [| split]; unfold fixedtables; destruct s; reflexivity |]].
      - split; [exact HM5|]. split; [subst M5 M4 M3 M2 M1; retc_tower C HRC|]. split.
        + apply (LX_step0 v s c r1 _ c r' HX NH NB); subst s1 r'; try reflexivity; try (clear; unfold fixedtables; destruct s; reflexivity); [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        + symex_reg HR' (25%bv : reg) as G22'. symex_reg HR' (19%bv : reg) as G18'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr.
          * exact G22'.
          * rewrite G18'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
      - subst M5 M4 M3 M2 M1.
        do 5 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
        apply MFRAME_refl. }
    assert (T3 : t = 3) by lia.
    arm_symex ilS 40%nat [true; true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
      (mkst R1 (Z_to_bv 64 0x1f530) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66674)).
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)).
    set (c' := icset_msg c MSG_invalid_block_type).
    assert (HM2 : LMEM v (mkW s1 c' r') M2) by (exact (LMEM_store_msg v C s1 c r' M1 MSG_invalid_block_type HM1 Hput)).
    assert (HM3 : LMEM v (mkW (iset_mode s1 BAD) c' r') M3).
    { apply (LMEM_store_scalar v C s1 c' r' _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s1 BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (icset_msg_facts c MSG_invalid_block_type) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    arm_disp C HM3 Hfr R2 Hms2 G26' Hfr2.
    exists R2, M3, (arm6_pc (is_mode (iset_mode s1 BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; rewrite El in Hms; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
    - split; [exact HM3|]. split; [subst M3 M2 M1; retc_tower C HRC|]. split.
      + apply (LX_step0 v s c r1 _ c' r' HX NH NB); subst s1 r' c'; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; unfold MSG_invalid_block_type; lia | bk_side].
      + symex_reg HR' (25%bv : reg) as G22'. symex_reg HR' (19%bv : reg) as G18'.
        unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [r_drop3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
        split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
        regs_via2 Hfr2 Hfr.
        * exact G22'.
        * rewrite G18'. rewrite szwrap32_small by (clear - Hb3 Rbits; lia). reflexivity.
    - subst M3 M2 M1.
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End ArmTYPE.
End FXG.
End InflA_Type.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6. Import InflA_Type.
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
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_TYPEDO ivar_ref (cv_flush v) (mkW s c r)) R' M' pc'.
  Proof.
    intros v s c r R M C Hmode HE HP. pose proof HE as HE0. destruct HE as (HM & HRC & HX & (HF & HV & G26)).
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
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Ein | rewrite Eret; exact Xret | exact Xmsg | bk_side]).
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
      arm_symex ilS 12%nat [false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 32)] v r
        [is_last s mod 2 ^ 32] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f4d0) M s6u_rom) R' HR' Hfr Hms.
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
      arm_disp C HM1 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M1, (arm6_pc (is_mode (iset_mode s CHECK))). split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [split; [reflexivity | split; reflexivity] |]].
      + split; [exact HM1|]. split; [subst M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r _ c r' HX NH NB); subst r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
        * symex_reg HR' (25%bv : reg) as G22'. symex_reg HR' (19%bv : reg) as G18'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr.
          -- rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). rewrite shiftr_div by (clear - Hm8 E7; lia).
             rewrite E7. reflexivity.
          -- rewrite G18', Ebits. reflexivity.
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
    pose proof HE as HE0. destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    arm_begin C HM HRC HX HF HV HP.
    replace ((cv_flush v =? Z_BLOCK) || (cv_flush v =? Z_TREES)) with false
      by (symmetry; apply orb_false_intro; apply Z.eqb_neq; unfold Z_BLOCK, Z_TREES; clear - Cflush; lia).
    assert (Ef5 : (cv_flush v - 5) mod 2 ^ 64 = cv_flush v - 5 + 2 ^ 64) by (apply zmod64_neg; clear - Cflush; lia).
    arm_symex ilS 6%nat [true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 2 ^ 64)] v r
      [(cv_flush v - 5) mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f4c0) M s6u_rom) R1 HR1 Hfr Hms1.
    all: try arm_side.
    assert (HE1 : ENTRY v (mkW s c r) R1 M).
    { split; [exact HM|]. split; [exact HRC|]. split; [exact HX|].
      unfold LREG_arm, LVARS; cbn [w_r]. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|].
      split; [regs_via Hfr | intros Hb; rewrite (Hfr (27%bv : reg) eq_refl); exact (G26 Hb)]. }
    destruct (typedo_core v s c r R1 M C (or_introl Hmode) HE1 HP) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [| exact HPOST].
    eapply msteps_trans; [| exact Hms2]. by_run Hms1.
  Qed.
End ArmTYPE2.
End FXG.
