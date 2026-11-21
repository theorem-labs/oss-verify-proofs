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
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition lx_len (s : inflate_state) (r1 : iregs) : Z := is_length s + ir_hold r1 mod 2 ^ is_extra s.
Definition lx_s (s : inflate_state) (r1 : iregs) : inflate_state :=
  iset_mode (iset_was (iset_back (iset_length s (lx_len s r1)) (swrap32 (is_back s + is_extra s))) (lx_len s r1)) DIST.
Definition lx_r (s : inflate_state) (r1 : iregs) : iregs :=
  irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ is_extra s)) (ir_bits r1 - is_extra s).

Lemma arm_LENEXT_run : forall s c r c1 r1,
  0 < is_extra s <= 15 -> 0 <= is_length s -> is_length s + 2 ^ is_extra s <= 2 ^ 32 ->
  NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c1 r1) ->
  is_extra s <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_LENEXT ivar_ref (mkW s c r) = arm_DIST ivar_ref (mkW (lx_s s r1) c1 (lx_r s r1)).
Proof.
  intros s c r c1 r1 Hex Hlen Hle HN Hb Hh.
  assert (Hv : 0 <= ir_hold r1 mod 2 ^ is_extra s < 2 ^ is_extra s) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. rewrite add_back_eq. cbv beta iota.
  rewrite abind_run. unfold aux. cbn [iv_aux ivar_ref bkv]. rewrite us_eq. cbv beta iota.
  mstep1 set_mode_eq. unfold lx_s, lx_r, lx_len. cbn [iv_aux ivar_ref]. irnorm.
  rewrite (BITSv_land (ir_hold r1) (is_extra s)), Z.land_ones by lia.
  rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap32_id by lia.
  destruct s; reflexivity.
Qed.

Lemma arm_LENEXT_zero : forall s c r,
  is_extra s = 0 -> arm_LENEXT ivar_ref (mkW s c r) = arm_DIST ivar_ref (mkW (iset_mode (iset_was s (is_length s)) DIST) c r).
Proof.
  intros s c r H0. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). rewrite H0. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). rewrite abind_run. unfold aux. cbn [iv_aux ivar_ref]. rewrite us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LENEXT_leave : forall s c r w1,
  is_extra s <> 0 -> NEEDBITS (is_extra s) (mkW s c r) = ALeave w1 -> arm_LENEXT ivar_ref (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 H0 HN. unfold arm_LENEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. reflexivity.
Qed.

Definition lenext_facts (v : icv) (s : inflate_state) (c : icall) : Prop :=
  3 <= is_length s /\ 0 <= is_extra s <= 15 /\ is_length s + Z.shiftl 1 (is_extra s) - 1 <= 258 /\ dist_facts v s c.

Lemma sinv_lenext : forall s, sinv s -> is_mode s = LENEXT ->
  3 <= is_length s /\ 0 <= is_extra s <= 15 /\ is_length s + Z.shiftl 1 (is_extra s) - 1 <= 258.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.

Lemma lenext_facts_of_pinv : forall v s c r,
  is_mode s = LENEXT -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> lenext_facts v s c.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_lenext s PS Hmode) as (Hlen & Hex & Hle). pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof (sr_back s SR) as Hback.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof (dist_tab s PS ltac:(rewrite Hmode; reflexivity)) as DT.
  pose proof (sr_dofs s SR) as Hofs.
  unfold lenext_facts, dist_facts. rewrite Z.shiftl_1_l in Hle.
  assert (Hlen' : 3 <= is_length s <= 258) by (pose proof (Z.pow_pos_nonneg 2 (is_extra s) ltac:(lia) ltac:(lia)); lia).
  rewrite Z.shiftl_1_l. repeat (split; [assumption|]). exact Hofs.
Qed.

Lemma dist_facts_lx : forall v s c L bk W,
  dist_facts v s c -> 3 <= L <= 258 ->
  dist_facts v (iset_mode (iset_was (iset_back (iset_length s L) (swrap32 bk)) W) DIST) c.
Proof.
  intros v s c L bk W HD HL. destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & DT & Hofs).
  unfold dist_facts. destruct s; cbn in *. pose proof (swrap32_range bk). repeat (split; [assumption || exact DT|]). exact Hofs.
Qed.
Lemma dist_facts_lz : forall v s c W,
  dist_facts v s c -> dist_facts v (iset_mode (iset_was s W) DIST) c.
Proof.
  intros v s c W HD. destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & DT & Hofs).
  unfold dist_facts. destruct s; cbn in *. repeat (split; [assumption || exact DT|]). exact Hofs.
Qed.


Section LenextBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lf HD :=
    destruct HD as (Hlen3 & Hex & Hle & HDD); pose proof HDD as HDD0;
    destruct HDD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Lemma lenext_body : forall s c r1 R M b0 h0 n0,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r1 -> is_extra s <> 0 -> is_extra s <= ir_bits r1 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> XJE v b0 h0 n0 (is_extra s) c r1 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d9e8) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (arm_DIST ivar_ref (mkW (lx_s s r1) c (lx_r s r1))) R' M' pc'.
  Proof.
    intros s c r1 R M b0 h0 n0 Hmode HD RI Hex0 Hbx HM HRC HX HJ. open_lf HD.
    destruct HJ as ((HF & G18 & G1 & G13 & G23 & G9 & G26) & G22 & G14 & G12 & G15). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_length _ _ _ _ Msc) as C92. pose proof (is6_back _ _ _ _ Msc) as C7148.
    assert (Hbm : 0 <= is_back s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (P2e : 0 < 2 ^ is_extra s <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.shiftl_1_l in Hle.
    set (ex := is_extra s) in *.
    arm_symexP (@nil (Z * expr)) ilS 24%nat (@nil bool) [RVal (EVar 46%nat); RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 47%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
       (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
       (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
       (14, EVar 41%nat); (12, EVar 36%nat); (15, EAdd (EVar 43%nat) (EVar 44%nat)); (13, EVar 45%nat)]
      [(45%nat, 16); (46%nat, 512); (47%nat, 2 ^ 32)] v r1
      [ex; is_length s; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x1d9e8) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    rewrite (mask_exec (ir_hold r1) ex Rhold64 ltac:(lia)) in Hms1.
    rewrite (szwrap32_of_mod32 (is_back s) Hback) in Hms1.
    rewrite <- (le4_swrap32 (is_back s + ex)) in Hms1.
    set (v1 := ir_hold r1 mod 2 ^ ex) in *.
    assert (Hv1 : 0 <= v1 < 2 ^ ex) by (subst v1; apply Z.mod_pos_bound; lia).
    set (L' := is_length s + v1) in *.
    set (M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 L')) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (is_back s + ex)))) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16202)) in *.
    set (M4 := wbytes M3 (zw (cv_S v + 7168)) (Z_to_le_bytes 4 L')) in *.
    set (s1 := iset_length s L'). set (s2 := iset_back s1 (swrap32 (is_back s + ex))). set (s3 := iset_mode s2 DIST). set (s4 := iset_was s3 L').
    assert (Es4 : lx_s s r1 = s4) by (subst s4 s3 s2 s1 L' v1 ex; unfold lx_s, lx_len; destruct s; reflexivity).
    assert (HM1 : LMEM v (mkW s1 c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r1) M2).
    { apply (LMEM_store_scalar v C s1 c r1 _ M1 7164 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW s3 c r1) M3).
    { apply (LMEM_store_scalar v C s2 c r1 _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s2 DIST (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM4' : LMEM v (mkW s4 c r1) M4).
    { apply (LMEM_store_scalar v C s3 c r1 _ M3 7168 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_was M3 (cv_S v) _ s3 _ (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    rewrite <- Es4 in HM4'.
    assert (HM4 : LMEM v (mkW (lx_s s r1) c (lx_r s r1)) M4) by (apply (LMEM_regs v (lx_s s r1) c r1 c (lx_r s r1) M4 HM4'); reflexivity).
    assert (HRC4 : RETC v (mkW (lx_s s r1) c (lx_r s r1)) M4).
    { subst M4 M3 M2 M1. apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]. }
    assert (HX4 : LX v (mkW (lx_s s r1) c (lx_r s r1))).
    { rewrite Es4. apply (LX_step0 v s c r1 s4 c (lx_r s r1) HX NH NB); subst s4 s3 s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
    pose proof (hold_drop (ir_hold r1) (ir_bits r1) ex ltac:(lia) Rhold) as HD'.
    assert (RI4 : RINV (cv_NI v) (cv_NO v) (lx_r s r1)).
    { unfold lx_r, RINV in *. cbn. clear - RI HD' Hbx Hex Hex0. subst ex. lia. }
    symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26.
    assert (HF4 : LFIX v R1) by (unfold LFIX, INF_FRAME, A6_JTAB; regs_via Hfr1).
    assert (HV4 : LVARS v (mkW (lx_s s r1) c (lx_r s r1)) R1).
    { unfold LVARS; cbn [w_r]. unfold lx_r. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      regs_via Hfr1; first [exact Q24 | rewrite Q23; rewrite zalu_srl_small by (clear - Rhold64 Hex; lia); reflexivity
                           | rewrite Q8; rewrite szwrap32_small by (clear - Rbits Hbx Hex; lia); reflexivity | exact Q26
                           | match goal with |- ?G => idtac "LV LEFT" G end]. }
    assert (HD4 : dist_facts v (lx_s s r1) c).
    { unfold lx_s. apply dist_facts_lx; [exact HDD0|]. unfold lx_len. subst ex v1. clear - Hlen3 Hle Hv1. lia. }
    destruct (dist_core v C (lx_s s r1) c (lx_r s r1) R1 M4 ltac:(rewrite Es4; reflexivity) HD4 RI4 HM4 HRC4 HX4 HF4 HV4)
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r1) (mkW (lx_s s r1) c (lx_r s r1)) M M4); [rewrite Es4; subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. unfold lx_r. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
    do 4 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.

  Lemma lenext_ztail : forall s c r R M,
    is_mode s = LENEXT -> lenext_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIX v R -> LVARS v (mkW s c r) R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e5d8) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_DIST ivar_ref (mkW (iset_mode (iset_was s (is_length s)) DIST) c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HD RI HM HRC HX HF HV. open_lf HD. open_fix HF. open_vars HV.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_length _ _ _ _ Msc) as C92.
    arm_symex ilS 10%nat (@nil bool) [RVal (EVar 45%nat); RVal (EAdd (EVar 33%nat) (ELit 7160))] (@nil (Z * expr))
      [(45%nat, 512)] v r [is_length s] NoVals F0
      (mkst R (Z_to_bv 64 0x1e5d8) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTLZ" G end.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16202)) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7168)) (Z_to_le_bytes 4 (is_length s))) in *.
    set (s1 := iset_mode s DIST). set (s2 := iset_was s1 (is_length s)).
    assert (Es2 : iset_mode (iset_was s (is_length s)) DIST = s2) by (subst s2 s1; destruct s; reflexivity).
    rewrite Es2.
    assert (HM1 : LMEM v (mkW s1 c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s DIST Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r) M2).
    { apply (LMEM_store_scalar v C s1 c r _ M1 7168 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_was M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC2 : RETC v (mkW s2 c r) M2) by (subst M2 M1; retc_tower C HRC).
    assert (HX2 : LX v (mkW s2 c r)).
    { apply (LX_step0 v s c r s2 c r HX NH NB); subst s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
    assert (HF2 : LFIX v R1) by (apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity).
    assert (HV2 : LVARS v (mkW s2 c r) R1) by (unfold LVARS; cbn [w_r]; regs_via Hfr1).
    assert (HD2 : dist_facts v s2 c).
    { subst s2 s1. replace (iset_was (iset_mode s DIST) (is_length s)) with (iset_mode (iset_was s (is_length s)) DIST) by (destruct s; reflexivity).
      apply dist_facts_lz. exact HDD0. }
    destruct (dist_core v C s2 c r R1 M2 ltac:(subst s2 s1; destruct s; reflexivity) HD2 RI0 HM2 HRC2 HX2 HF2 HV2)
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW s2 c r) M M2); [subst s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. subst M2 M1.
    do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End LenextBody.
End FXG.
