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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Match2 InflA_Match5. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require InflA_Distext3. Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflA_Distext3.InflA_Distext2. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflDec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition rdrop (r : iregs) (n : Z) : iregs := irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n)).

Definition dist_res (here BK : Z) (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  let r' := rdrop r (code_bits here) in
  let s1 := iset_back s (swrap32 (BK + code_bits here)) in
  if negb (Z.land (code_op here) 64 =? 0)
  then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_distance_code) r')
  else arm_DISTEXT ivar_ref (mkW (iset_mode (iset_extra (iset_offset s1 (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c r').

Lemma swrap32_add_l : forall a b, swrap32 (swrap32 a + b) = swrap32 (a + b).
Proof.
  intros a b. unfold swrap32, two31. rewrite !wrap32_mod.
  f_equal. replace ((a + 2147483648) mod 2 ^ 32 - 2147483648 + b + 2147483648) with ((a + 2147483648) mod 2 ^ 32 + b) by lia.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma iset_back_back : forall s a b, iset_back (iset_back s a) b = iset_back s b.
Proof. intros s a b. destruct s; reflexivity. Qed.




Lemma op_lt16_240 : forall op, 0 <= op < 256 -> (op <? 16) = (Z.land op 240 =? 0).
Proof.
  intros op Hop.
  destruct (Z.ltb_spec op 16) as [L|L].
  - symmetry. apply Z.eqb_eq.
    assert (E : op = 0 \/ 1 <= op <= 15) by lia. destruct E as [->|E]; [reflexivity|].
    exact (proj1 (proj2 (proj2 (op_link_tests op E)))).
  - symmetry. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.land op 240) (Z.log2 op) = false) by (rewrite Z0; apply Z.bits_0).
    rewrite Z.land_spec, Z.bit_log2 in T by lia.
    assert (4 <= Z.log2 op <= 7).
    { split; [apply Z.log2_le_pow2; lia|]. apply Z.lt_succ_r. apply Z.log2_lt_pow2; cbn; lia. }
    assert (E : Z.log2 op = 4 \/ Z.log2 op = 5 \/ Z.log2 op = 6 \/ Z.log2 op = 7) by lia.
    destruct E as [E|[E|[E|E]]]; rewrite E in T; cbv in T; discriminate T.
Qed.


Definition dist_facts (v : icv) (s : inflate_state) (c : icall) : Prop :=
  is_sane s = 1 /\ 3 <= is_length s <= 258 /\ - 2 ^ 31 <= is_back s < 2 ^ 31
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ CINV (cv_NI v) (cv_NO v) c
  /\ (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ ext <= cext (is_distcode s))
  /\ cofs_ok (is_distcode s).

Lemma sinv_dist_len : forall s, sinv s -> is_mode s = DIST -> 3 <= is_length s <= 258.
Proof. intros s H Hm. destruct H as (_ & _ & _ & _ & _ & _ & _ & Q & _). exact (Q Hm). Qed.
Lemma sr_dofs : forall s, SRNGq s -> cofs_ok (is_distcode s).
Proof. intros s H. do 18 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Lemma dist_facts_of_pinv : forall v s c r,
  is_mode s = DIST -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> dist_facts v s c.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_dist_len s PS Hmode) as Hlen. pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof (sr_back s SR) as Hback.
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof (dist_tab s PS ltac:(rewrite Hmode; reflexivity)) as DT.
  pose proof (sr_dofs s SR) as Hofs.
  unfold dist_facts. repeat (split; [assumption|]). exact Hofs.
Qed.

Lemma mod16_base : forall op, 16 <= op < 32 -> op mod 2 ^ 4 = op - 16.
Proof. intros op H. symmetry. apply (Z.mod_unique_pos op (2 ^ 4) 1 (op - 16)); lia. Qed.
Lemma swrap32_mod32 : forall x, swrap32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold swrap32, two31. rewrite wrap32_mod.
  rewrite <- Zminus_mod_idemp_l. change (2^32) with 4294967296. rewrite Z.mod_mod by lia.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma mod64_mod32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma le4_BK : forall BK n, Z_to_le_bytes 4 (BK mod 2 ^ 64 + n) = Z_to_le_bytes 4 (swrap32 (BK + n)).
Proof.
  intros BK n. apply le4_eqm. rewrite swrap32_mod32. rewrite <- Zplus_mod_idemp_l, mod64_mod32, Zplus_mod_idemp_l. reflexivity.
Qed.


Lemma swrap32_smallv : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> swrap32 x = x.
Proof. intros x Hx. apply swrap32_id. exact Hx. Qed.
Lemma iset_back_self : forall s, iset_back s (is_back s) = s.
Proof. intros s. destruct s; reflexivity. Qed.

Definition ilDF : cfg := CFG [] [] arm_rets (0x20f54 :: arm_stops) [].

Section DistFin.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition FREG (s : inflate_state) (r : iregs) (here : Z) (R : bvmap 5 word) : Prop :=
    LFIXc v R /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 14 = zw (ir_bits r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 22 = zw (cent here / 2 ^ 8) /\ getr R 21 = zw (code_bits here) /\ getr R 29 = zw (code_op here) /\ getr R 30 = zw (cent here).

  Definition fpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (25, EVar 40%nat); (14, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (22, EVar 45%nat); (21, EVar 46%nat); (29, EVar 47%nat); (30, EVar 48%nat)].
  Definition fvb : list (nat * Z) := [(45%nat, 2 ^ 24); (46%nat, 256); (47%nat, 256); (48%nat, 2 ^ 32); (49%nat, 2 ^ 32)].

  Lemma dist_fin : forall s c r R M here BK maxb,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    term_ok DISTS maxb here = true -> code_bits here <= ir_bits r -> 0 <= BK <= 143 ->
    LMEM v (mkW (iset_back s BK) c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> FREG s r here R ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x20f04) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW (iset_back s BK) c r) M (dist_res here BK s c r) R' M' pc'.
  Proof.
    intros s c r R M here BK maxb Hmode HD RI TE Hhb HBK HM HRC HX HR. pose proof HD as HD0. open_dfacts HD.
    destruct HR as (HF & G9 & G22 & G14 & G12 & G25 & G21 & G20 & G29 & G30). open_fixc HF.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G9 as P9. pose proof G22 as P22. pose proof G14 as P14. pose proof G12 as P12. pose proof G25 as P25.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    destruct (term_ok_DISTS _ _ TE) as (Bh & CL).
    pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval. pose proof (code_bits_range here) as Hcb.
    pose proof (cent_range here) as Hcent. pose proof (cent_shr8_range here) as Hc8.
    assert (HBKm : BK mod 2 ^ 32 = BK) by (apply Z.mod_small; lia).
    pose proof (is6_back _ _ _ _ Msc) as C7148. cbn [is_back iset_back] in C7148.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI ltac:(clear - Hhb Bh; lia)) as [EW RI'].
    unfold dist_res, rdrop. rewrite EW.
    rewrite (swrap32_smallv (BK + code_bits here)) by (clear - HBK Bh Hcb; lia).
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) in *.
    set (s1 := iset_back s (BK + code_bits here)) in *.
    assert (HV' : forall R1, getr R1 23 = zw (ir_have r) -> getr R1 9 = zw (cv_P0 v + ir_put r) ->
              getr R1 25 = zw (zalu ALU_SRL (ir_hold r) (cent here / 2 ^ 8)) -> getr R1 19 = zw (szwrap 32 (ir_bits r - code_bits here)) ->
              getr R1 26 = zw (cv_I0 v + ir_next r) -> forall sx, LVARS v (mkW sx c r') R1).
    { intros R1 Q24 Q9 Q22 Q18 Q25 sx. unfold LVARS. cbn [w_r]. subst r'. cbn.
      rewrite srl_cent in Q22 by (first [exact Rhold64 | clear - Hhb Rbits; lia]). rewrite szwrap32_small in Q18 by (clear - Hhb Bh Rbits; lia).
      rewrite Z.shiftr_div_pow2 by (clear - Bh; lia). repeat split; assumption. }
    pose proof (land192_cent here ltac:(clear - Hhb Rbits; lia)) as L192.
    destruct CL as [(O16 & V1 & VE & O29) | (I64 & I16 & I32)].
    -
      destruct (op_base_tests (code_op here) O16) as (_ & E64 & _ & _ & E15 & _). rewrite E64, E15. cbn [Z.eqb negb].
      arm_symexP (@nil (Z * expr)) ilDF 22%nat [false; false; false] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 49%nat); RVal (EVar 35%nat)] fpins fvb v r
        [cent here / 2 ^ 8; code_bits here; code_op here; cent here; BK mod 2 ^ 32] NoVals F0
        (mkst R (Z_to_bv 64 0x20f04) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTDF1" G end.
      rewrite ?HBKm, ?(szwrap32_small BK) in Hms1 by (clear - HBK; lia).
      rewrite (mod16_base (code_op here) O16), ?cent_val in Hms1.
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 112)) (Z_to_le_bytes 4 (code_val here))) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 116)) (Z_to_le_bytes 4 (code_op here - 16))) in *.
      set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16203)) in *.
      set (s2 := iset_offset s1 (code_val here)). set (s3 := iset_extra s2 (code_op here - 16)). set (s4 := iset_mode s3 DISTEXT).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst s1. rewrite <- (iset_back_back s BK).
        apply (LMEM_store_scalar v C (iset_back s BK) c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_back M (cv_S v) _ (iset_back s BK) _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r) M2).
      { apply (LMEM_store_scalar v C s1 c r _ M1 112 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_offset M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW s3 c r) M3).
      { apply (LMEM_store_scalar v C s2 c r _ M2 116 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_extra M2 (cv_S v) _ s2 _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4' : LMEM v (mkW s4 c r) M4).
      { apply (LMEM_store_scalar v C s3 c r _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M3 (cv_S v) _ s3 DISTEXT (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4 : LMEM v (mkW s4 c r') M4) by (apply (LMEM_regs v s4 c r c r' M4 HM4'); subst r'; reflexivity).
      assert (HRC4 : RETC v (mkW s4 c r') M4) by (subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]).
      assert (HX4 : LX v (mkW s4 c r')).
      { apply (LX_step0 v s c r s4 c r' HX NH NB); subst s4 s3 s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]. }
      symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (14%bv : reg) as Q14. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (11%bv : reg) as Q11.
      assert (HF4 : LFIX v R1) by (unfold LFIX, INF_FRAME; regs_via Hfr1; first [exact Q13 | exact Q11]).
      pose proof (HV' R1) as HV4.
      assert (HVX : LVX v (mkW s4 c r') R1).
      { unfold LVX. cbn [w_r]. subst r'. cbn.
        rewrite srl_cent in Q22 by (first [exact Rhold64 | clear - Hhb Rbits; lia]). rewrite szwrap32_small in Q18 by (clear - Hhb Bh Rbits; lia).
        rewrite Z.shiftr_div_pow2 by (clear - Bh; lia). regs_via Hfr1; first [exact Q22 | exact Q18]. }
      assert (HD4 : distext_facts v s4 c r').
      { unfold distext_facts. subst s4 s3 s2 s1. cbn. rewrite Z.shiftl_1_l. rewrite Z.shiftl_1_l in VE.
        refine (conj Hsane (conj Hlen (conj V1 (conj _ (conj _ (conj _ (conj Hwh (conj Hwn (conj Hwl (conj Hws (conj Hwb (conj RI' CI'))))))))))));
          clear - O16 O29 VE HBK Bh Hcb; lia. }
      destruct (distext_core v C s4 c r' R1 M4 ltac:(reflexivity) HD4 HM4 HRC4 HX4 HF4 HVX ltac:(rewrite Q14, (mod16_base (code_op here) O16); subst s4 s3 s2 s1; destruct s; reflexivity) ltac:(rewrite (Hfr1 (12%bv : reg) eq_refl); exact G12))
        as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
      apply (arm_post_chain v (mkW (iset_back s BK) c r) (mkW s4 c r') M M4); [subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
      do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
    -
      replace (negb (Z.land (code_op here) 64 =? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact I64).
      arm_symexP (@nil (Z * expr)) ilDF 22%nat [false; false; true] [RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 49%nat); RVal (EVar 35%nat)] fpins fvb v r
        [cent here / 2 ^ 8; code_bits here; code_op here; cent here; BK mod 2 ^ 32] NoVals F0
        (mkst R (Z_to_bv 64 0x20f04) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTDF2" G end.
      rewrite ?HBKm, ?(szwrap32_small BK) in Hms1 by (clear - HBK; lia).
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (BK + code_bits here))) in *.
      set (M2 := wbytes M1 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66385)) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_invalid_distance_code) in *.
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { subst s1. rewrite <- (iset_back_back s BK).
        apply (LMEM_store_scalar v C (iset_back s BK) c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_back M (cv_S v) _ (iset_back s BK) _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s1 c' r) M2) by (exact (LMEM_store_msg v C s1 c r M1 MSG_invalid_distance_code HM1 Hput)).
      assert (HM3' : LMEM v (mkW (iset_mode s1 BAD) c' r) M3).
      { apply (LMEM_store_scalar v C s1 c' r _ M2 8 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M2 (cv_S v) _ s1 BAD (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW (iset_mode s1 BAD) c' r') M3).
      { apply (LMEM_regs v (iset_mode s1 BAD) c' r c' r' M3 HM3'); subst r'; reflexivity. }
      pose proof (icset_msg_facts c MSG_invalid_distance_code) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
      arm_disp C HM3 Hfr1 R2 Hms2 G26' Hfr2.
      exists R2, M3, (arm6_pc (is_mode (iset_mode s1 BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [subst s1; split; [reflexivity | split; reflexivity] |]].
      + split; [exact HM3|]. split; [subst M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]|]. split.
        * apply (LX_step0 v s c r _ c' r' HX NH NB); subst s1 c' r'; try reflexivity; [live_mode_tac | exact Xret | rewrite K11; unfold MSG_invalid_distance_code; lia | bk_side].
        * symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (13%bv : reg) as Q13. symex_reg HR1 (11%bv : reg) as Q11.
          unfold LREG_arm. split; [lfix_close2 Hfr2 Hfr1 HR1|]. split; [| intros _; exact G26'].
          refine (HV' R2 _ _ _ _ _ (iset_mode s1 BAD)); rewrite Hfr2 by reflexivity; first [exact Q24 | exact Q22 | exact Q18 | rewrite (Hfr1 (9%bv : reg) eq_refl); exact G9 | rewrite (Hfr1 (26%bv : reg) eq_refl); exact G25].
      + cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M3 M2 M1.
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.
End DistFin.
End FXG.
