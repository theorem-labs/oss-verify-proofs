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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b
     InflNeed6 InflA_Copy.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Definition r_bb (r : iregs) : iregs :=
  irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)).

Definition stored_B (w1 : iw) : ares unit :=
  let s := w_s w1 in let c := w_c w1 in let r := w_r w1 in
  let hold := ir_hold r in
  if negb (Z.land hold 65535 =? Z.lxor (Z.shiftr hold 16) 65535)
  then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_stored_block_lengths) r)
  else arm_COPY (mkW (iset_mode (iset_mode (iset_length s (Z.land (wrap32 hold) 65535)) COPY_) COPY) c
                      (irset_bits (irset_hold r 0) 0)).

Lemma arm_STORED_run : forall flush s c r s1 c1 r1,
  flush <> Z_TREES ->
  NEEDBITS 32 (mkW s c (r_bb r)) = ARun tt (mkW s1 c1 r1) ->
  arm_STORED ivar_ref flush (mkW s c r) = stored_B (mkW s1 c1 r1).
Proof.
  intros flush s c r s1 c1 r1 Hf HN.
  unfold arm_STORED. mstep1 BYTEBITS_eq. change (irset_bits _ _) with (r_bb r). rewrite abind_run, HN.
  mstep1 HOLD_eq. unfold stored_B. cbn [w_s w_c w_r].
  destruct (negb (Z.land (ir_hold r1) 65535 =? Z.lxor (Z.shiftr (ir_hold r1) 16) 65535)); [rewrite go_bad_eq; reflexivity|].
  mstep1 us_eq. mstep1 INITBITS_eq. mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb].
  replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  unfold arm_COPY_. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_STORED_leave : forall flush s c r w1,
  NEEDBITS 32 (mkW s c (r_bb r)) = ALeave w1 -> arm_STORED ivar_ref flush (mkW s c r) = ALeave w1.
Proof.
  intros flush s c r w1 HN. unfold arm_STORED. mstep1 BYTEBITS_eq. change (irset_bits _ _) with (r_bb r). rewrite abind_run, HN. reflexivity.
Qed.

Lemma r_bb_small : forall r, 0 <= ir_bits r < 64 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  r_bb r = mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                (ir_in r) (ir_out r) (ir_ret r)
  /\ 0 <= ir_hold r / 2 ^ (ir_bits r mod 8) < 2 ^ (ir_bits r - ir_bits r mod 8)
  /\ 0 <= ir_bits r mod 8 < 8 /\ ir_bits r mod 8 <= ir_bits r.
Proof.
  intros r Hb Hh. pose proof (land7_mod (ir_bits r)) as E7.
  assert (Hm8 : 0 <= ir_bits r mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hml : ir_bits r mod 8 <= ir_bits r) by (apply Z.mod_le; lia).
  pose proof (hold_drop (ir_hold r) (ir_bits r) (ir_bits r mod 8) ltac:(lia) Hh) as HD.
  split; [| split; [exact HD | split; [exact Hm8 | exact Hml]]].
  unfold r_bb. destruct r; cbn in *. rewrite E7. rewrite shiftr_div by lia. rewrite wrap32_id by lia. reflexivity.
Qed.


Definition ilN : cfg := ilSx [0x1d20c; 0x1d4a0] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section ArmSTORED.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis MEMCPY : memcpy_run6.

  Definition JS (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 13 = zw (ir_bits r) /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 27 = zw (cv_I0 v + ir_next r).
  Definition JE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 27 = zw (cv_I0 v + ir_next r).

  Ltac open_js HJ :=
    let X := fresh in pose proof HJ as X; unfold JS, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G13 & G14 & G26); open_fix HF.

  Ltac js_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let G9 := fresh in let G22 := fresh in let G23 := fresh in let G13 := fresh in let G14 := fresh in let G26 := fresh in let G27 := fresh in
    symex_reg HR (18%bv : reg) as G9; symex_reg HR (23%bv : reg) as G22; symex_reg HR (24%bv : reg) as G23;
    symex_reg HR (13%bv : reg) as G13; symex_reg HR (14%bv : reg) as G14; symex_reg HR (27%bv : reg) as G26;
    cbn [famA] in G22; rewrite bmod_get in G22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold JS, JE, LVR, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G9; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite G22; f_equal; lia
          | rewrite G23; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G13; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G14; f_equal; lia
          | rewrite G26; f_equal; lia
          | match goal with |- ?G => idtac "JS LEFT" G end ].

  Lemma stored_step_H : forall s c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 32 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d20c) M s6_rom)
               /\ JS c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilN 14%nat [true; true] (@nil (option expr)) [(13, EVar 41%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat))] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0.
  Qed.

  Lemma stored_step_E : forall s c r R M,
    LMEM v (mkW s c r) M -> JS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> 32 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d4a0) M s6_rom)
               /\ JE c (pull1 c r) R1.
  Proof.
    intros s c r R M HM HJ RI CI Hb Hb8 Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilN 14%nat [true; false] (@nil (option expr)) [(13, EVar 41%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat))] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma stored_dry : forall s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros s c r R M HM HRC HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    arm_symex ilN 8%nat [false] [RVal (EVar 45%nat)] [(13, EVar 41%nat); (14, EAdd (EVar 43%nat) (EVar 44%nat))] [(45%nat, 2 ^ 64)] v r
      [ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d20c) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'. symex_reg HR1 (27%bv : reg) as G26'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [rewrite G26'; f_equal; lia | rewrite G8'; apply zw_neg_mod].
  Qed.

  Ltac open_je HJ :=
    let X := fresh in pose proof HJ as X; unfold JE, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G26); open_fix HF.

  Lemma stored_chk : forall h, 0 <= h ->
    (Z.land h 65535 =? Z.lxor (Z.shiftr h 16) 65535) = (Z.lxor (h / 2 ^ 16) (h mod 2 ^ 16) =? 65535).
  Proof.
    intros h Hh.
    change 65535 with (Z.ones 16) at 1. rewrite Z.land_ones by lia. change (Z.ones 16) with 65535.
    rewrite Z.shiftr_div_pow2 by lia.
    set (hi := h / 2 ^ 16). set (lo := h mod 2 ^ 16).
    destruct (Z.eqb_spec lo (Z.lxor hi 65535)) as [E|N]; destruct (Z.eqb_spec (Z.lxor hi lo) 65535) as [E'|N']; try reflexivity; exfalso.
    - apply N'. rewrite E. rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l. reflexivity.
    - apply N. rewrite <- E'. rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l. reflexivity.
  Qed.
  Lemma stored_len : forall h, 0 <= h -> Z.land (wrap32 h) 65535 = h mod 2 ^ 16.
  Proof.
    intros h Hh. rewrite wrap32_mod. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    apply mod_pow2_le. lia.
  Qed.

  Lemma stored_B_sim : forall s c r1 R M,
    is_mode s = STORED ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> JE c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d4a0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (stored_B (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode HM HRC HX HJ RI CI Hb32. open_je HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    unfold stored_B. cbn [w_s w_c w_r]. rewrite stored_chk by (clear - Rhold; lia). rewrite stored_len by (clear - Rhold; lia).
    assert (Hlo : 0 <= ir_hold r1 mod 2 ^ 16 < 65536) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eqb_spec (Z.lxor (ir_hold r1 / 2 ^ 16) (ir_hold r1 mod 2 ^ 16)) 65535) as [EQ|NE]; cbn [negb].
    -
      arm_symex ilS 16%nat [false; true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d4a0) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (L := ir_hold r1 mod 2 ^ 16) in *.
      set (M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 L)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16194)) in *.
      set (s2 := iset_mode (iset_length s L) COPY_) in *.
      set (r2 := irset_bits (irset_hold r1 0) 0) in *.
      assert (HM1 : LMEM v (mkW (iset_length s L) c r1) M1).
      { apply (LMEM_store_scalar v C s c r1 _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_length M (cv_S v) _ s L Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2' : LMEM v (mkW s2 c r1) M2).
      { apply (LMEM_store_scalar v C _ c r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ _ COPY_ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r2) M2) by (apply (LMEM_regs v s2 c r1 c r2 M2 HM2'); subst r2; reflexivity).
      assert (HRC2 : RETC v (mkW s2 c r2) M2) by (subst M2 M1; retc_tower C HRC).
      assert (HX2 : LX v (mkW s2 c r2)).
      { apply (LX_step0 v s c r1 _ c r2 HX NH NB); subst s2 r2; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
      assert (HJ2 : CREG v (mkW s2 c r2) R1).
      { split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|].
        symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8.
        unfold LVARS; cbn [w_r]. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
        regs_via Hfr1; first [exact Q23 | exact Q8 | exact G26]. }
      assert (RI2 : RINV (cv_NI v) (cv_NO v) r2).
      { subst r2. unfold RINV in *. cbn. clear - RI. change (2 ^ 0) with 1. lia. }
      destruct (copy__core MEMCPY v s2 c r2 R1 M2 C ltac:(subst s2; destruct s; reflexivity)
                  ltac:(subst s2; replace (is_length _) with L by (destruct s; reflexivity); clear - Hlo; lia)
                  HM2 HRC2 HX2 HJ2 RI2 CI) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r1) (mkW s2 c r2) M M2); [subst s2; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r2. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      arm_symex ilS 30%nat [true; true] [RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d4a0) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66326)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_invalid_stored_block_lengths).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_invalid_stored_block_lengths HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_stored_block_lengths) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      exists R', M2, (arm6_pc BAD). split; [subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r1 _ c' r1 HX NH NB); subst c'; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; unfold MSG_invalid_stored_block_lengths; lia].
        * symex_reg HR' (9%bv : reg) as G8'. symex_reg HR' (27%bv : reg) as G26'.
          unfold LREG_arm, LVARS; cbn [w_r].
          split; [apply (LFIX_frame v R R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8'].
          regs_via Hfr.
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
  Qed.

  Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - b mod 8.
  Proof.
    intros b Hb.
    assert (H: forall k, 0 <= k < 32 -> Z.land k 24 = k - k mod 8).
    { intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
       \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst k; reflexivity. }
    apply H. exact Hb.
  Qed.

  Lemma stored_A : forall s c r R M,
    LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    let rb := mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                   (ir_in r) (ir_out r) (ir_ret r) in
    exists R1,
      if 32 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d1f0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d4a0) M s6_rom) /\ JE c rb R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d1f0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d20c) M s6_rom) /\ JS c rb R1.
  Proof.
    intros s c r R M HF HV RI. cbv zeta.
    open_ictx C. open_fix HF. open_vars HV. open_rinv RI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    pose proof (land7_mod (ir_bits r)) as E7.
    assert (Hm8 : 0 <= ir_bits r mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hml : ir_bits r mod 8 <= ir_bits r) by (apply Z.mod_le; clear - Rbits; lia).
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - arm_symex ilN 8%nat [true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d1f0) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (23%bv : reg) as G22'. symex_reg HR1 (24%bv : reg) as G23'.
      unfold JE, LVR; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr.
      + rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). reflexivity.
      + rewrite G23'. match goal with |- ?G => idtac "G23" G end. rewrite land_m8 by (clear - Rbits; lia). rewrite E7. reflexivity.
    - arm_symex ilN 8%nat [false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d1f0) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (23%bv : reg) as G22'. symex_reg HR1 (24%bv : reg) as G23'. symex_reg HR1 (13%bv : reg) as G13'. symex_reg HR1 (14%bv : reg) as G14'.
      unfold JS, LVR; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr.
      + rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). reflexivity.
      + rewrite G23'. match goal with |- ?G => idtac "G23" G end. rewrite land24 by (clear - Rbits LT; lia). reflexivity.
      + rewrite G13'. rewrite land24 by (clear - Rbits LT; lia). reflexivity.
      + exact G14'.
  Qed.

  Theorem arm_STORED_sim0 : forall w R M,
    is_mode (w_s w) = STORED -> ENTRY v w R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 (arm6_pc STORED)) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v w M (dispatch ivar_ref (cv_flush v) w) R' M' pc'.
  Proof.
    intros w R M Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) STORED) with (arm_STORED ivar_ref (cv_flush v)).
    destruct HE as (HM & HRC & HX & (HF & HV & G8)).
    arm_begin C HM HRC HX HF HV HP.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hf6 : cv_flush v <> Z_TREES) by (unfold Z_TREES; clear - Cflush; lia).
    destruct (r_bb_small r Rbits Rhold) as (Ebb & Hhb & Hm8 & Hml).
    set (rb := mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                    (ir_in r) (ir_out r) (ir_ret r)) in *.
    assert (RIb : RINV (cv_NI v) (cv_NO v) rb) by (subst rb; unfold RINV in *; cbn; clear - RI Hhb Hm8 Hml; lia).
    assert (HMb : LMEM v (mkW s c rb) M) by (apply (LMEM_regs v s c r c rb M HM); reflexivity).
    assert (HRCb : RETC v (mkW s c rb) M) by (eapply RETC_regs; [exact HRC | reflexivity]).
    assert (HXb : LX v (mkW s c rb)) by (apply (LX_step0 v s c r s c rb HX NH NB); try reflexivity; [exact Xlive | exact Xret | exact Xmsg]).
    destruct (stored_A s c r R M HF HV RI) as (R1 & HA).
    change (arm6_pc STORED) with 0x1d1f0.
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    -
      destruct HA as (Hms1 & HJE).
      assert (Hb32 : 32 <= ir_bits r - ir_bits r mod 8).
      { pose proof (Z.div_mod (ir_bits r) 8 ltac:(lia)) as E. clear - GE Hm8 E. lia. }
      assert (HN : NEEDBITS 32 (mkW s c (r_bb r)) = ARun tt (mkW s c rb)).
      { rewrite Ebb. unfold NEEDBITS. apply NEEDBITS_k_done. cbn. exact Hb32. }
      rewrite (arm_STORED_run (cv_flush v) s c r s c rb Hf6 HN).
      destruct (stored_B_sim s c rb R1 M Hmode HMb HRCb HXb HJE RIb CI ltac:(subst rb; cbn; exact Hb32)) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      apply (arm_post_rebase v s c r c rb); [reflexivity | exact HPOST].
    -
      destruct HA as (Hms1 & HJS).
      pose proof (need_loop v 32 0x1d20c 0x1d4a0 JS JE C ltac:(lia) stored_step_H stored_step_E stored_dry
                    8%nat s c rb R1 M HMb HRCb HJS RIb CI ltac:(subst rb; cbn; clear - LT Hm8; lia) ltac:(subst rb; cbn; clear - LT Hm8 Hml; lia)) as NL.
      change (NEEDBITS_k 8 32) with (NEEDBITS 32) in NL.
      destruct (NEEDBITS 32 (mkW s c rb)) as [[] w1 | w1 | rc w1] eqn:HN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). subst rb. cbn in Q1, Q2, Q3, Q4, Q5.
        rewrite <- Ebb in HN. rewrite (arm_STORED_run (cv_flush v) s c r s c r1 Hf6 HN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]).
        destruct (stored_B_sim s c r1 R2 M Hmode HM1 HRC1 HX1 HJE RI1 CI ltac:(clear - Hb1; lia)) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). subst rb. cbn in Q1, Q2, Q3, Q4, Q5.
        rewrite <- Ebb in HN. rewrite (arm_STORED_leave (cv_flush v) s c r _ HN).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
  Qed.
End ArmSTORED.

Section ArmSTORED2.
  Hypothesis MEMCPY : memcpy_run6.
  Theorem arm_STORED_sim : arm_stmt STORED.
  Proof. intros v w R M C Hmode HE HP. exact (arm_STORED_sim0 v C MEMCPY w R M Hmode HE HP). Qed.
End ArmSTORED2.
End FXG.
