(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext1 InflA_Distext2 InflDec6 InflA_Dist3 InflA_Dist7 InflA_Lenext2 InflA_Lenext3.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition len_res (here BK : Z) (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  let r' := rdrop r (code_bits here) in
  let s1 := iset_length (iset_back s (swrap32 (BK + code_bits here))) (code_val here) in
  if code_op here =? 0 then ARun tt (mkW (iset_mode s1 LIT) c r')
  else if negb (Z.land (code_op here) 32 =? 0) then ARun tt (mkW (iset_mode (iset_back s1 (-1)) TYPE) c r')
  else if negb (Z.land (code_op here) 64 =? 0) then ARun tt (mkW (iset_mode s1 BAD) (icset_msg c MSG_invalid_literal_length_code) r')
  else arm_LENEXT ivar_ref (mkW (iset_mode (iset_extra s1 (Z.land (code_op here) 15)) LENEXT) c r').

Definition len_after1 (s0 : inflate_state) (last : Z) : AM unit :=
  (do here <- (if negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0) then
                 let last' := last in
                 do here <- DECODE2 (is_lencode s0) last' ;
                 DROPBITS (code_bits last') ;; add_back ivar_ref (code_bits last') ;; aret here
               else aret last) ;
   DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
   us (fun s => iset_length s (code_val here)) ;;
   if code_op here =? 0 then set_mode LIT
   else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
   else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
   else us (fun s => iset_extra s (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am.


Lemma len_tail_eq : forall s c r here,
  (DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
   us (fun s => iset_length s (code_val here)) ;;
   if code_op here =? 0 then set_mode LIT
   else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
   else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
   else us (fun s => iset_extra s (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am (mkW s c r)
  = len_res here (is_back s) s c r.
Proof.
  intros s c r here. mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv]. mstep1 us_eq.
  unfold len_res, rdrop.
  destruct (code_op here =? 0); [rewrite set_mode_eq; irnorm; reflexivity|].
  destruct (negb (Z.land (code_op here) 32 =? 0)); [rewrite abind_run, set_back_eq; cbn [iv_aux ivar_ref sbv]; rewrite set_mode_eq; irnorm; reflexivity|].
  destruct (negb (Z.land (code_op here) 64 =? 0)); [rewrite go_bad_eq; irnorm; reflexivity|].
  mstep1 us_eq. mstep1 set_mode_eq. irnorm. reflexivity.
Qed.

Lemma len_after1_term : forall s last c r,
  (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) = false -> len_after1 s last (mkW s c r) = len_res last (is_back s) s c r.
Proof. intros s last c r E. unfold len_after1. rewrite E. mstep1 (@aret_eq Z). apply len_tail_eq. Qed.

Lemma len_after1_link : forall s last c r here r2,
  (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) = true ->
  DECODE2 (is_lencode s) last (mkW s c r) = ARun here (mkW s c r2) ->
  len_after1 s last (mkW s c r) = len_res here (is_back s + code_bits last) s c (rdrop r2 (code_bits last)).
Proof.
  intros s last c r here r2 E HD2. unfold len_after1. rewrite E. rewrite abind_run. rewrite abind_run, HD2.
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv]. rewrite aret_eq.
  rewrite len_tail_eq. cbn [is_back iset_back]. unfold len_res, rdrop. irnorm.
  replace (iset_back (iset_back s (swrap32 (is_back s + code_bits last))) (swrap32 (swrap32 (is_back s + code_bits last) + code_bits here)))
    with (iset_back s (swrap32 (is_back s + code_bits last + code_bits here))) by (rewrite iset_back_back, swrap32_add_l; reflexivity).
  reflexivity.
Qed.

Lemma len_after1_leave2 : forall s last c r w2,
  (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) = true ->
  DECODE2 (is_lencode s) last (mkW s c r) = ALeave w2 -> len_after1 s last (mkW s c r) = ALeave w2.
Proof. intros s last c r w2 E HD2. unfold len_after1. rewrite E. rewrite abind_run. rewrite abind_run, HD2. reflexivity. Qed.



Definition len_facts (v : icv) (s : inflate_state) (c : icall) : Prop :=
  is_sane s = 1
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ arr_len (is_window s) = cv_WN v /\ (is_wsize s = 0 \/ is_wsize s = cv_WN v)
  /\ (forall i, 0 <= i < cv_WN v -> 0 <= arr_get (is_window s) i < 256)
  /\ CINV (cv_NI v) (cv_NO v) c
  /\ (exists ext, tab_ok LENS (cat (is_codes s) (is_lencode s)) (is_lenbits s) ext = true /\ ext <= cext (is_lencode s))
  /\ cofs_ok (is_lencode s)
  /\ (exists ext, tab_ok DISTS (cat (is_codes s) (is_distcode s)) (is_distbits s) ext = true /\ ext <= cext (is_distcode s))
  /\ cofs_ok (is_distcode s).

Lemma sr_lofs : forall s, SRNGq s -> cofs_ok (is_lencode s).
Proof. intros s H. do 17 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Lemma len_facts_of_pinv : forall v s c r,
  is_mode s = LEN -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> len_facts v s c.
Proof.
  intros v s c r Hmode HP. open_pinv HP.
  pose proof (sr_sane s SR) as Hsane. pose proof (sinv_wcur s PS) as [Hwh Hwn].
  pose proof WI as WI'. unfold WINV in WI'. cbn [w_s] in WI'. destruct WI' as (Hwl & _ & _ & Hws).
  pose proof (sr_winb s SR) as Hwb. rewrite Hwl in Hwb.
  pose proof (len_tab s PS ltac:(rewrite Hmode; reflexivity)) as LT.
  pose proof (dist_tab s PS ltac:(rewrite Hmode; reflexivity)) as DT.
  pose proof (sr_lofs s SR) as Hlofs. pose proof (sr_dofs s SR) as Hdofs.
  unfold len_facts. repeat (split; [assumption|]). exact Hdofs.
Qed.

Lemma len_facts_back : forall v s c bk, len_facts v s c -> len_facts v (iset_back s bk) c.
Proof.
  intros v s c bk HD. destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & LT & Hlofs & DT & Hdofs).
  unfold len_facts. destruct s; cbn in *. repeat (split; [assumption || exact LT || exact DT|]). exact Hdofs.
Qed.

Lemma lenext_facts_len : forall v s c bk here,
  len_facts v s c -> 16 <= code_op here < 32 -> 3 <= code_val here -> code_val here + Z.shiftl 1 (code_op here - 16) - 1 <= 258 ->
  lenext_facts v (iset_mode (iset_extra (iset_length (iset_back s (swrap32 bk)) (code_val here)) (code_op here - 16)) LENEXT) c.
Proof.
  intros v s c bk here HD Hop Hv3 Hvle. destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & LT & Hlofs & DT & Hdofs).
  pose proof (swrap32_range bk). rewrite Z.shiftl_1_l in Hvle.
  assert (P : 1 <= 2 ^ (code_op here - 16)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  unfold lenext_facts, dist_facts. destruct s; cbn in *. rewrite Z.shiftl_1_l.
  repeat (split; [first [assumption | exact DT | lia] |]). exact Hdofs.
Qed.


Section LenFin.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Definition LFREG (s : inflate_state) (r : iregs) (here BK : Z) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 13 = zw (ir_bits r) /\ getr R 12 = zw (ir_have r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 27 = zw (cv_S v + 7160) /\ getr R 16 = zw BK
    /\ getr R 14 = zw (code_bits here) /\ getr R 7 = zw (code_op here) /\ getr R 17 = zw (code_val here).

  Definition lfpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (13, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EAdd (EVar 33%nat) (ELit 7160));
     (16, EVar 45%nat); (14, EVar 46%nat); (7, EVar 47%nat); (17, EVar 48%nat)].
  Definition lfvb : list (nat * Z) := [(45%nat, 2 ^ 64); (46%nat, 256); (47%nat, 256); (48%nat, 65536)].

  Lemma len_fin_base : forall s c r R M here BK maxb,
    is_mode s = LEN -> len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    term_ok LENS maxb here = true -> code_bits here <= ir_bits r -> 16 <= code_op here < 32 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFREG s r here BK R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e590) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (len_res here BK s c r) R' M' pc'.
  Proof.
    intros s c r R M here BK maxb Hmode HD RI TE Hhb O16 HM HRC HX HR. pose proof HD as HD0. open_lfacts HD.
    destruct HR as (HF & G18 & G1 & G22 & G13 & G12 & G27 & G9 & G16 & G14 & G7 & G17). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    destruct (term_ok_LENS _ _ TE) as (Bh & CL).
    pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval. pose proof (code_bits_range here) as Hcb.
    assert (HBKm : 0 <= BK mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    rewrite <- (zw_mod BK) in G16.
    pose proof (RINV_drop (cv_NI v) (cv_NO v) ltac:(clear - CI0; lia) ltac:(clear - CP0; lia) r (code_bits here) RI0 ltac:(clear - Hhb Bh; lia)) as [EW RI'].
    pose proof (swrap32_range (BK + code_bits here)) as Hbk'.
    destruct CL as [(O0 & _) | [(_ & V3 & VE & O21) | (I64 & I16)]]; [exfalso; clear - O0 O16; lia | | exfalso; destruct (op_base_tests (code_op here) O16) as (_ & E64 & _); exact (I64 E64)].
    destruct (op_base_tests (code_op here) O16) as (_ & E64 & E32 & _ & E15 & NZ).
    unfold len_res, rdrop. rewrite EW.
    replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). rewrite E64, E32, E15. cbn [Z.eqb negb].
    set (r' := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)) in *.
    assert (HV' : forall R1, getr R1 18 = zw (ir_have r) -> getr R1 19 = zw (cv_P0 v + ir_put r) -> getr R1 1 = zw (ir_left r) ->
              getr R1 23 = zw (zalu ALU_SRL (ir_hold r) (code_bits here)) -> getr R1 24 = zw (szwrap 32 (ir_bits r - code_bits here)) ->
              getr R1 27 = zw (cv_I0 v + ir_next r) -> forall sx, LVARS v (mkW sx c r') R1).
    { intros R1 Q24 Q19 Q18 Q23 Q8 Q26 sx. unfold LVARS. cbn [w_r]. subst r'. cbn.
      rewrite zalu_srl_small in Q23 by (clear - Rhold64 Hhb Bh Rbits; lia). rewrite szwrap32_small in Q8 by (clear - Hhb Bh Rbits; lia).
      rewrite Z.shiftr_div_pow2 by (clear - Bh; lia). repeat split; assumption. }
    destruct (Z.eq_dec (code_op here) 16) as [E16|N16].
    -
      arm_symexP (@nil (Z * expr)) ilS 20%nat [false; false; false; true] (@nil (option expr)) lfpins lfvb v r
        [BK mod 2 ^ 64; code_bits here; code_op here; code_val here] NoVals F0
        (mkst R (Z_to_bv 64 0x1e590) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: try (rewrite E16; reflexivity).
      rewrite le4_BK, (mod16_base (code_op here) O16) in Hms1.
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (BK + code_bits here)))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 116)) (Z_to_le_bytes 4 (code_op here - 16))) in *.
      set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16201)) in *.
      set (s1 := iset_back s (swrap32 (BK + code_bits here))). set (s2 := iset_length s1 (code_val here)).
      set (s3 := iset_extra s2 (code_op here - 16)). set (s4 := iset_mode s3 LENEXT).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r) M2).
      { apply (LMEM_store_scalar v C s1 c r _ M1 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_length M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW s3 c r) M3).
      { apply (LMEM_store_scalar v C s2 c r _ M2 116 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_extra M2 (cv_S v) _ s2 _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4' : LMEM v (mkW s4 c r) M4).
      { apply (LMEM_store_scalar v C s3 c r _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M3 (cv_S v) _ s3 LENEXT (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4 : LMEM v (mkW s4 c r') M4) by (apply (LMEM_regs v s4 c r c r' M4 HM4'); subst r'; reflexivity).
      assert (HRC4 : RETC v (mkW s4 c r') M4) by (subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]).
      assert (HX4 : LX v (mkW s4 c r')).
      { apply (LX_step0 v s c r s4 c r' HX NH NB); subst s4 s3 s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
      symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26.
      assert (HF4 : LFIX v R1) by (unfold LFIX, INF_FRAME, A6_JTAB; regs_via Hfr1).
      pose proof (HV' R1 Q24 ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) ltac:(rewrite (Hfr1 (1%bv : reg) eq_refl); exact G1) Q23 Q8 Q26 s4) as HV4.
      assert (HD4 : lenext_facts v s4 c) by (subst s4 s3 s2 s1; apply (lenext_facts_len v s c _ here HD0 O16 V3 VE)).
      rewrite (arm_LENEXT_zero s4 c r') by (subst s4 s3 s2 s1; cbn; clear - E16; lia).
      destruct (lenext_ztail v C s4 c r' R1 M4 ltac:(reflexivity) HD4 RI' HM4 HRC4 HX4 HF4 HV4) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r) (mkW s4 c r') M M4); [subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
      do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
    -
      assert (NE16 : code_op here mod 2 ^ 4 <> 0) by (rewrite (mod16_base (code_op here) O16); clear - N16 O16; lia).
      arm_symexP (@nil (Z * expr)) ilS 20%nat [false; false; false; false] (@nil (option expr)) lfpins lfvb v r
        [BK mod 2 ^ 64; code_bits here; code_op here; code_val here] NoVals F0
        (mkst R (Z_to_bv 64 0x1e590) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTLF2" G end.
      rewrite le4_BK, (mod16_base (code_op here) O16) in Hms1.
      set (M1 := wbytes M (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (swrap32 (BK + code_bits here)))) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (code_val here))) in *.
      set (M3 := wbytes M2 (zw (cv_S v + 116)) (Z_to_le_bytes 4 (code_op here - 16))) in *.
      set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16201)) in *.
      set (s1 := iset_back s (swrap32 (BK + code_bits here))). set (s2 := iset_length s1 (code_val here)).
      set (s3 := iset_extra s2 (code_op here - 16)). set (s4 := iset_mode s3 LENEXT).
      assert (HM1 : LMEM v (mkW s1 c r) M1).
      { apply (LMEM_store_scalar v C s c r _ M 7164 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_back M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r) M2).
      { apply (LMEM_store_scalar v C s1 c r _ M1 108 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_length M1 (cv_S v) _ s1 _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM3 : LMEM v (mkW s3 c r) M3).
      { apply (LMEM_store_scalar v C s2 c r _ M2 116 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_extra M2 (cv_S v) _ s2 _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4' : LMEM v (mkW s4 c r) M4).
      { apply (LMEM_store_scalar v C s3 c r _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M3 (cv_S v) _ s3 LENEXT (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM4 : LMEM v (mkW s4 c r') M4) by (apply (LMEM_regs v s4 c r c r' M4 HM4'); subst r'; reflexivity).
      assert (HRC4 : RETC v (mkW s4 c r') M4) by (subst M4 M3 M2 M1; apply (RETC_regs v (mkW s c r)); [retc_tower C HRC | subst r'; reflexivity]).
      assert (HX4 : LX v (mkW s4 c r')).
      { apply (LX_step0 v s c r s4 c r' HX NH NB); subst s4 s3 s2 s1 r'; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
      symex_reg HR1 (18%bv : reg) as Q24. symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26.
      symex_reg HR1 (13%bv : reg) as Q13. rewrite (mod16_base (code_op here) O16) in Q13.
      assert (HF4 : LFIX v R1) by (unfold LFIX, INF_FRAME, A6_JTAB; regs_via Hfr1).
      pose proof (HV' R1 Q24 ltac:(rewrite (Hfr1 (19%bv : reg) eq_refl); exact G18) ltac:(rewrite (Hfr1 (1%bv : reg) eq_refl); exact G1) Q23 Q8 Q26 s4) as HV4.
      assert (HD4 : lenext_facts v s4 c) by (subst s4 s3 s2 s1; apply (lenext_facts_len v s c _ here HD0 O16 V3 VE)).
      destruct (lenext_nz v C s4 c r' R1 M4 ltac:(reflexivity) HD4 RI' ltac:(subst s4 s3 s2 s1; cbn; clear - N16 O16; lia) HM4 HRC4 HX4 HF4 HV4
                  ltac:(rewrite Q13; subst s4 s3 s2 s1; reflexivity)) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M4 M3 M2 M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r) (mkW s4 c r') M M4); [subst s4 s3 s2 s1; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r'. cbn [ir_put irset_bits irset_hold]. subst M4 M3 M2 M1.
      do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
  Qed.
End LenFin.
End FXG.
