(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Match3 InflA_Match5 InflA_Distext1.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition dx_s (s : inflate_state) (r1 : iregs) : inflate_state :=
  iset_mode (iset_back (iset_offset s (is_offset s + ir_hold r1 mod 2 ^ is_extra s)) (swrap32 (is_back s + is_extra s))) MATCH.
Definition dx_r (s : inflate_state) (r1 : iregs) : iregs :=
  irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ is_extra s)) (ir_bits r1 - is_extra s).

Lemma arm_DISTEXT_run : forall s c r c1 r1,
  0 < is_extra s <= 15 -> 0 <= is_offset s -> is_offset s + 2 ^ is_extra s <= 2 ^ 32 ->
  NEEDBITS (is_extra s) (mkW s c r) = ARun tt (mkW s c1 r1) ->
  is_extra s <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_DISTEXT ivar_ref (mkW s c r) = arm_MATCH ivar_ref (mkW (dx_s s r1) c1 (dx_r s r1)).
Proof.
  intros s c r c1 r1 Hex Hoff Hoe HN Hb Hh.
  assert (Hv : 0 <= ir_hold r1 mod 2 ^ is_extra s < 2 ^ is_extra s) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. mstep1 BITS_eq. mstep1 us_eq. mstep1 DROPBITS_eq. rewrite add_back_eq. cbv beta iota.
  mstep1 set_mode_eq. unfold dx_s, dx_r, bkv. cbn [iv_aux ivar_ref]. irnorm.
  rewrite (BITSv_land (ir_hold r1) (is_extra s)), Z.land_ones by lia.
  rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap32_id by lia.
  reflexivity.
Qed.

Lemma arm_DISTEXT_zero : forall s c r,
  is_extra s = 0 -> arm_DISTEXT ivar_ref (mkW s c r) = arm_MATCH ivar_ref (mkW (iset_mode s MATCH) c r).
Proof.
  intros s c r H0. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). rewrite H0. cbn [Z.eqb negb].
  mstep1 (@aret_eq unit). mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_DISTEXT_leave : forall s c r w1,
  is_extra s <> 0 -> NEEDBITS (is_extra s) (mkW s c r) = ALeave w1 -> arm_DISTEXT ivar_ref (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 H0 HN. unfold arm_DISTEXT. mstep1 (@gs_eq inflate_state). replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite abind_run. rewrite abind_run, HN. reflexivity.
Qed.



Lemma testbit_high64 : forall h m, 0 <= h < 2 ^ 64 -> 64 <= m -> Z.testbit h m = false.
Proof.
  intros h m Hh Hm. destruct (Z.eq_dec h 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [| lia]. apply (proj1 (Z.log2_lt_pow2 h 64 ltac:(lia))). lia.
Qed.
Lemma mask_exec : forall h e, 0 <= h < 2 ^ 64 -> 0 <= e < 32 ->
  Z.land h (Z.lxor (zaluw ALU_SLL (-1) e) (-1)) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zaluw_sll_m1 by lia.
  replace (2 ^ 64 - 2 ^ e) with (Z.ldiff (Z.ones 64) (Z.ones e)).
  2:{ rewrite <- Z.sub_nocarry_ldiff.
      - unfold Z.ones. rewrite !Z.shiftl_1_l. lia.
      - apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.bits_0.
        destruct (Z_lt_le_dec m e); [| rewrite (Z.ones_spec_high e m) by lia; reflexivity].
        rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. reflexivity. }
  rewrite Z.lxor_m1_r. rewrite <- Z.ldiff_land.
  rewrite <- (Z.land_ones h e) by lia.
  apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.ldiff_spec, Z.land_spec.
  destruct (Z_lt_le_dec m e).
  - rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high e m) by lia. destruct (Z_lt_le_dec m 64).
    + rewrite (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_false_r. reflexivity.
    + rewrite (Z.ones_spec_high 64 m) by lia. rewrite (testbit_high64 h m) by lia. reflexivity.
Qed.

Lemma le4_swrap32 : forall x, Z_to_le_bytes 4 (swrap32 x) = Z_to_le_bytes 4 x.
Proof. intros x. apply le4_eqm. unfold swrap32, two31. rewrite wrap32_mod. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

Definition distext_facts (v : icv) (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  is_sane s = 1 /\ 3 <= is_length s <= 258 /\ 1 <= is_offset s /\ 0 <= is_extra s <= 15
  /\ is_offset s + Z.shiftl 1 (is_extra s) - 1 <= 32768 /\ - 2 ^ 31 <= is_back s < 2 ^ 31
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ RINV (cv_NI v) (cv_NO v) r /\ CINV (cv_NI v) (cv_NO v) c.

Lemma sinv_distext : forall s, sinv s -> is_mode s = DISTEXT ->
  3 <= is_length s <= 258 /\ 1 <= is_offset s /\ 0 <= is_extra s <= 15 /\ is_offset s + Z.shiftl 1 (is_extra s) - 1 <= 32768.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.
Lemma sr_back : forall s, SRNGq s -> - 2 ^ 31 <= is_back s < 2 ^ 31.
Proof. intros s H. do 28 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Lemma distext_facts_of_pinv : forall v s c r,
  is_mode s = DISTEXT -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> distext_facts v s c r.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_distext s PS Hmode) as (Hlen & Hoff & Hex & Hoe). pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof (sr_back s SR) as Hback.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  unfold distext_facts. repeat (split; [assumption|]). exact CI.
Qed.


Definition ilXA : cfg := CFG [] [] arm_rets (0x1e798 :: 0x1e7e4 :: arm_stops) [].

Section DistextBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_df HD :=
    destruct HD as (Hsane & Hlen & Hoff & Hex & Hoe & Hback & Hwh & Hwn & Hwl & Hws & Hwb & RI & CI).

  Lemma distext_body : forall s c r1 R M b0 h0 n0,
    is_mode s = DISTEXT -> distext_facts v s c r1 -> is_extra s <> 0 -> is_extra s <= ir_bits r1 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> XJE v b0 h0 n0 (is_extra s) c r1 R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e7e4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (arm_MATCH ivar_ref (mkW (dx_s s r1) c (dx_r s r1))) R' M' pc'.
  Proof.
    intros s c r1 R M b0 h0 n0 Hmode HD Hex0 Hbx HM HRC HX HJ. open_df HD.
    destruct HJ as ((HF & G18 & G1 & G13 & G23 & G9 & G26) & G22 & G14 & G12 & G15). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_offset _ _ _ _ Msc) as C96. pose proof (is6_back _ _ _ _ Msc) as C7148.
    replace (cv_S v + 7164) with (cv_S v + 7160 + 4) in C7148 by lia.
    assert (Hbm : 0 <= is_back s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (P2e : 0 < 2 ^ is_extra s <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    rewrite Z.shiftl_1_l in Hoe.
    set (ex := is_extra s) in *.
    arm_symexP (@nil (Z * expr)) ilS 20%nat (@nil bool) [RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
       (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
       (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
       (14, EVar 41%nat); (12, EVar 36%nat); (15, EAdd (EVar 43%nat) (EVar 44%nat)); (13, EVar 45%nat)]
      [(45%nat, 16); (46%nat, 32769); (47%nat, 2 ^ 63); (48%nat, 2 ^ 32)] v r1
      [ex; is_offset s; cv_S v + 7160; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x1e7e4) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    rewrite (mask_exec (ir_hold r1) ex Rhold64 ltac:(lia)) in Hms1.
    rewrite (szwrap32_of_mod32 (is_back s) Hback) in Hms1.
    rewrite <- (le4_swrap32 (is_back s + ex)) in Hms1.
    replace (cv_S v + 7160 + 4) with (cv_S v + 7164) in Hms1 by lia.
    set (v1 := ir_hold r1 mod 2 ^ ex) in *.
    assert (Hv1 : 0 <= v1 < 2 ^ ex) by (subst v1; apply Z.mod_pos_bound; lia).
    set (M1 := wbytes M (zw (cv_S v + 112)) (Z_to_le_bytes 4 (is_offset s + v1))) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (is_back s + ex)))) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16204)) in *.
    set (s1 := iset_offset s (is_offset s + v1)). set (s2 := iset_back s1 (swrap32 (is_back s + ex))). set (s3 := iset_mode s2 MATCH).
    assert (Es3 : dx_s s r1 = s3) by (subst s3 s2 s1 v1 ex; reflexivity).
    assert (HM1 : LMEM v (mkW s1 c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 112 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_offset M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW s2 c r1) M2).
    { apply (LMEM_store_scalar v C s1 c r1 _ M1 7164 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_back M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3' : LMEM v (mkW s3 c r1) M3).
    { apply (LMEM_store_scalar v C s2 c r1 _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M2 (cv_S v) _ s2 MATCH (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW (dx_s s r1) c (dx_r s r1)) M3).
    { rewrite Es3. apply (LMEM_regs v s3 c r1 c (dx_r s r1) M3 HM3'); reflexivity. }
    assert (HRC3 : RETC v (mkW (dx_s s r1) c (dx_r s r1)) M3).
    { subst M3 M2 M1. apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]. }
    assert (HX3 : LX v (mkW (dx_s s r1) c (dx_r s r1))).
    { rewrite Es3. apply (LX_step0 v s c r1 s3 c (dx_r s r1) HX NH NB); subst s3 s2 s1; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
    pose proof (hold_drop (ir_hold r1) (ir_bits r1) ex ltac:(lia) Rhold) as HD'.
    assert (HE3 : ENTRY v (mkW (dx_s s r1) c (dx_r s r1)) R1 M3).
    { split; [exact HM3|]. split; [exact HRC3|]. split; [exact HX3|].
      symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26.
      unfold LREG_arm, LVARS; cbn [w_r w_s]. unfold dx_r. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      split; [| split; [| rewrite Es3; subst s3; cbn; intros Hb; exfalso; cbv in Hb; discriminate]].
      - unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr1.
      - regs_via Hfr1; first [exact Q24 | rewrite Q23; rewrite zalu_srl_small by (clear - Rhold64 Hex; lia); reflexivity
                             | rewrite Q8; rewrite szwrap32_small by (clear - Rbits Hbx Hex; lia); reflexivity | exact Q26]. }
    assert (MF3 : match_facts v (dx_s s r1) c (dx_r s r1)).
    { rewrite Es3. unfold match_facts. subst s3 s2 s1. cbn. unfold dx_r. unfold RINV in *. cbn.
      refine (conj Hsane (conj _ (conj _ (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj _ CI)))))))));
        [clear - Hlen; lia | clear - Hoff Hoe Hv1; subst ex v1; lia | clear - RI HD' Hbx Hex; subst ex; lia]. }
    destruct (match_core v C (dx_s s r1) c (dx_r s r1) R1 M3 ltac:(rewrite Es3; reflexivity) HE3 MF3) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r1) (mkW (dx_s s r1) c (dx_r s r1)) M M3); [rewrite Es3; subst s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
    cbn [w_r]. unfold dx_r. cbn [ir_put irset_bits irset_hold]. subst M3 M2 M1.
    do 3 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End DistextBody.
End FXG.
