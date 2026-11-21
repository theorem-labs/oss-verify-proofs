(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_adler32 Zh_kit Zg_adler32_iface Zg_infl_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface ZChkAdl AdlerModel InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateArms RefInflateSafeS2 RefInflateSafeOK3 RefInflate_runA. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LV_WIN : Z := 0x1ee00.
Definition PC_LV_TAIL : Z := 0x1ee60.

Definition lv_w (w : iw) : iw :=
  mkW (fst (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w)))
      (snd (lv_pre (s_rest (w_s w) (w_r w)) (c_rest (w_c w) (w_r w)) (w_r w))) (w_r w).

Definition IMEMLW (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  iframeL X (w_r w) m
  /\ stk psegs m (ix_lo X) (bv_unsigned (ix_sp X) + -240)
  /\ IREP m (ix_L X) (w_s w) (w_c w)
  /\ iin m X
  /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv psegs m /\ munch W (ix_m0 X) m /\ wmono psegs (ix_m0 X) m.
Lemma IMEMLW_of_IMEML : forall X w m, IMEML X w m -> IMEMLW (ix_W X) X w m.
Proof. intros X w m H. exact H. Qed.

Definition ix_WF (X : ictx) : list ivl := ix_W X ++ [(il_Aw (ix_L X), il_Aw (ix_L X) + 32768)].

Definition ILVT (W : list ivl) (X : ictx) (w : iw) (pc : Z) (x10 x12 x15 x19 x25 : word) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x9 x13 x14 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -240)) (ix_gp X) (ix_tp X) x5 x6 x7 x25
                 x9 x10 (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_ret (w_r w))) (wz (ir_left (w_r w))) x19 x21 (wz 16209) (wz (ir_out (w_r w))) x24 (wz (ir_have (w_r w))) x26 x27 x28 x29 x30 x31)
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMLW W X w m.

Lemma ILVT_intro : forall W X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -240) -> x3 = ix_gp X -> x4 = ix_tp X -> x11 = wz (ix_flush X) ->
  x18 = wz (ir_ret (w_r w)) -> x19 = wz (ir_left (w_r w)) -> x22 = wz 16209 -> x23 = wz (ir_out (w_r w)) -> x25 = wz (ir_have (w_r w)) ->
  F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  ILVT W X w pc x10 x12 x15 x20 x8 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILVT. do 18 eexists. split; [reflexivity| assumption]. Qed.

Definition IMEMF (W : list ivl) (X : ictx) (w : iw) (m : mem) : Prop :=
  stk psegs m (ix_lo X) (bv_unsigned (ix_sp X))
  /\ IREP m (ix_L X) (w_s w) (w_c w) /\ iin m X /\ iout m (ix_L X) (ix_rest0 X) (w_c w) (ir_put (w_r w))
  /\ mem_inv psegs m /\ munch W (ix_m0 X) m /\ wmono psegs (ix_m0 X) m.

Definition IFIN (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
    ms = MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz rc) a1 a2 a3 a4 a5 a6 a7
                 (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
            (ix_F X) (ret_pc (ix_ra X)) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMF W X w m.

Definition IRETW (W : list ivl) (X : ictx) (rc : Z) (w : iw) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    ms = MS (mkR x21 (wz (bv_unsigned (ix_sp X) + -240)) (ix_gp X) (ix_tp X) x5 x6 x7 x25 x23 x10 x11 x12 x13 x14 x15 x16 x17
                 x8 x1 x18 (wz rc) x19 x30 x22 x9 x27 x26 x28 x29 x24 x31)
            (ix_F X) (wz PC_EPILOGUE) (ix_fc X) None m (seg_rom psegs)
    /\ IMEMLW W X w m.
Lemma IRETW_of_IRET : forall X rc w ms, IRET X rc w ms -> IRETW (ix_W X) X rc w ms.
Proof.
  intros X rc w ms (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & E & HM & _).
  unfold IRETW. do 28 eexists. split; [exact E| exact HM].
Qed.
Lemma IRETW_intro : forall W X rc w x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -240) -> x3 = ix_gp X -> x4 = ix_tp X -> x20 = wz rc -> F = ix_F X -> fc = ix_fc X ->
  IMEMLW W X w m ->
  IRETW W X rc w (MS (mkR x21 x2 x3 x4 x5 x6 x7 x25 x23 x10 x11 x12 x13 x14 x15 x16 x17 x8 x1 x18 x20 x19 x30 x22 x9 x27 x26 x28 x29 x24 x31)
                  F (wz PC_EPILOGUE) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold IRETW. do 28 eexists. split; [reflexivity| assumption]. Qed.

Lemma epilogue_gen : forall W X rc w ms, IRETW W X rc w ms -> ix_ok X -> evt psegs (IFIN W X rc w) ms.
Proof.
  intros W X rc [s c r] ms HL XO.
  destruct HL as (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m
                  & -> & (retw & jf0 & jf1 & jf & FRM) & STK & HREP & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM. cbn [w_s w_c w_r] in *. ix_open XO.
  unfold PC_EPILOGUE. do 15 zs.
  release_frame FRM STK (bv_unsigned (ix_sp X)).
  zs.
  apply evt_done. unfold IFIN. do 15 eexists. split; [reflexivity|].
  unfold IMEMF. cbn [w_s w_c w_r]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma epilogue_spec : forall X rc w ms, IRET X rc w ms -> ix_ok X -> evt psegs (IFIN (ix_W X) X rc w) ms.
Proof. intros X rc w ms H XO. exact (epilogue_gen _ X rc w ms (IRETW_of_IRET _ _ _ _ H) XO). Qed.

Lemma leave_tail : forall W X w x12 x15 x19 ms,
  adler32_stmt ->
  ILVT W X w PC_LV_TAIL (wz (il_S (ix_L X))) x12 x15 x19 (wz (il_As (ix_L X))) ms -> ix_ok X -> (W = ix_W X \/ W = ix_WF X) ->
  0 <= ix_flush X <= 4 -> 0 <= ir_have (w_r w) <= ir_in (w_r w) -> ir_in (w_r w) < 2^31 ->
  0 <= ir_left (w_r w) <= ir_out (w_r w) -> ir_out (w_r w) < 2^32 -> ir_out (w_r w) - ir_left (w_r w) <= ir_put (w_r w) ->
  ir_put (w_r w) < 2^31 -> ir_put (w_r w) <= Z.of_nat (length (ix_rest0 X)) -> - 2^31 <= ir_ret (w_r w) < 2^31 ->
  ic_avail_in (w_c w) = ir_have (w_r w) -> ic_avail_out (w_c w) = ir_left (w_r w) -> ic_next_out (w_c w) = ir_put (w_r w) ->
  is_wrap (w_s w) = 5 -> (is_window_blk (w_s w) <> None -> ix_hasw X = true) ->
  (ir_left (w_r w) < ir_out (w_r w) -> is_flags (w_s w) = 0 /\ adler_canon (is_check (w_s w))) ->
  (forall i, 0 <= i < ir_put (w_r w) -> 0 <= arr_get (ic_outbuf (w_c w)) i < 256) ->
  evt psegs (IFIN W X (ret_model (ix_flush X) (wrap32 (ir_in (w_r w) - ir_have (w_r w))) (wrap32 (ir_out (w_r w) - ir_left (w_r w))) (w_r w))
                  (mkW (fst (lv_pre (w_s w) (w_c w) (w_r w))) (snd (lv_pre (w_s w) (w_c w) (w_r w))) (w_r w))) ms.
Proof.
  intros W X [s c r] x12 x15 x19 ms ADL HL XO HW RF RIH RIN ROL ROUT ROP RPT RPL RR EAI EAO ENO Pw PWIN HCK POB.
  cbn [w_s w_c w_r] in *.
  eapply evt_cut; [| intros ms1 H1; exact (epilogue_gen W X _ _ ms1 H1 XO)].
  assert (HSUB : sub_fp (ix_WfS X) W).
  { destruct HW as [-> | ->]; unfold sub_fp, ix_WfS, ix_Wf, ix_WF, ix_W; intros a Ha; cbn [outside app] in *; repeat split; lia. }
  set (RC := ret_model (ix_flush X) (wrap32 (ir_in r - ir_have r)) (wrap32 (ir_out r - ir_left r)) r).
  rewrite lv_pre_shape. cbv zeta. rewrite EAO, EAI, ENO, Pw.
  rewrite (wrap32_id (ir_out r - ir_left r)) by lia. rewrite (wrap32_id (ir_in r - ir_have r)) by lia.
  change (Z.land 5 4 =? 0) with false. cbn [negb andb fst snd].
  destruct HL as (x1 & x5 & x6 & x7 & x9 & x13 & x14 & x16 & x17 & x21 & x24 & x26 & x27 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  destruct HMEM as ((retw & jf0 & jf1 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (BY : bytes_at psegs m (il_NO (ix_L X) + (ir_put r - (ir_out r - ir_left r)))
                        (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r)))).
  { pose proof (iout_prefix_bytes m (ix_L X) (ix_rest0 X) c (ir_put r) OUT ltac:(lia)) as HB.
    rewrite <- (av8_sub (ic_outbuf c) (ir_put r) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r)) by lia.
    rewrite <- (firstn_skipn (Z.to_nat (ir_put r - (ir_out r - ir_left r))) (av8 (ic_outbuf c) (ir_put r))) in HB.
    apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite length_firstn, av8_length, Nat.min_l in HB by lia.
    rewrite <- (firstn_skipn (Z.to_nat (ir_out r - ir_left r)) (skipn _ _)) in HB. apply bytes_at_app in HB. destruct HB as [HB _].
    replace (il_NO (ix_L X) + (ir_put r - (ir_out r - ir_left r)))
      with (il_NO (ix_L X) + Z.of_nat (Z.to_nat (ir_put r - (ir_out r - ir_left r)))) by lia.
    exact HB. }
  assert (LSL : Z.of_nat (length (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r))))
                = ir_out r - ir_left r).
  { rewrite length_map. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
  assert (BZ8 : forall l, (forall k, (k < length l)%nat -> 0 <= nth k l 0 < 256) -> bZ (map (Z_to_bv 8) l) = l).
  { intros l. induction l as [|x l IH]; intros H; [reflexivity|].
    cbn [map bZ]. unfold bZ in IH |- *. cbn [map]. f_equal.
    - apply bv8_small. apply (H 0%nat). cbn. lia.
    - apply IH. intros k Hk. apply (H (S k)). cbn. lia. }
  unfold iout in OUT.
  pose proof (conj MU WM) as MW0. clear MU.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (E240 : bv_unsigned (wz (bv_unsigned (ix_sp X) + -240)) = bv_unsigned (ix_sp X) + -240) by (apply unsigned_lit; lia).
  unfold PC_LV_TAIL.
  do 7 zs. rewrite !land_u32_small by lia.
  do 3 zs. rewrite !land_u32_small by lia.
  do 4 zs.
  rd_sub GA 16%nat 0%nat 1%nat. zs. clear RD. rewrite Pw.
  do 2 zs. change (Z.land (bv_unsigned (zx8 (wz 5))) 4) with 4.
  zs. zs. br_false.
  zs. br_cases K.
  - assert (EO0 : ir_out r - ir_left r = 0) by lia.
    rewrite EO0. cbn [Z.eqb negb].
    do 31 zs.
    rewrite bufrule_clang by lia.
    unfold RC, ret_model. change Z_FINISH with 4. change Z_OK with 0.
    destruct ((((wrap32 (ir_in r - ir_have r) =? 0) && (wrap32 (ir_out r - ir_left r) =? 0)) || (ix_flush X =? 4)) && (ir_ret r =? 0))%bool; cbn [Z.b2z].
    + zs. br_false. do 2 zs.
      itr_groups MUf WMf.
      apply evt_done. eapply IRETW_intro; try reflexivity.
      unfold IMEMLW. cbn [w_s w_c w_r].
      split; [exists retw, jf0, jf1, jf; unfold iframe_cells; exact FRM|].
      split; [exact STK|].
      split. { split.
               - eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. rewrite ?wz_wrap64. close_cells ZS.
               - constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]. }
      split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|].
      split; [eassumption|].
      split; [destruct MW0 as [MU0 _]; eapply munch_trans; [exact MU0| exact (munch_weaken _ _ _ _ HSUB MUf)]| exact WM].
    + zs. br_true. zs.
      itr_groups MUf WMf.
      apply evt_done. eapply IRETW_intro; try reflexivity.
      unfold IMEMLW. cbn [w_s w_c w_r].
      split; [exists retw, jf0, jf1, jf; unfold iframe_cells; exact FRM|].
      split; [exact STK|].
      split. { split.
               - eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. rewrite ?wz_wrap64. close_cells ZS.
               - constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]. }
      split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|].
      split; [eassumption|].
      split; [destruct MW0 as [MU0 _]; eapply munch_trans; [exact MU0| exact (munch_weaken _ _ _ _ HSUB MUf)]| exact WM].
  - assert (EO1 : 0 < ir_out r - ir_left r) by lia.
    destruct (HCK ltac:(lia)) as (Pf0 & HCKc). pose proof HCKc as (CK1 & CK2 & CK3).
    replace (ir_out r - ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    assert (EV : UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r))
                 = adler32_z_spec (is_check s) (il_NO (ix_L X) + (ir_put r - (ir_out r - ir_left r)))
                                  (map (Z_to_bv 8) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r)))).
    { unfold UPDATE_CHECK_bytes. rewrite Pf0. cbn [Z.eqb negb]. unfold iadler32_upd.
      rewrite (adler32_z_spec_any (is_check s) _ _ HCKc) by lia.
      rewrite BZ8; [reflexivity|].
      intros k Hk. unfold arr_slice in *. rewrite arr_slice_nat_length in Hk. rewrite arr_slice_nat_nth by exact Hk. apply POB. lia. }
    rewrite EV.
    assert (ACALL : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                           (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B len lo : Z) (d : list byte),
        0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
        bytes_at psegs m B d -> mem_inv psegs m ->
        stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
        len = Z.of_nat (length d) ->
        evt psegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz Z_ADLER32) fc None m (seg_rom psegs))).
    { intros. subst. apply ADL; assumption. }
    do 2 zs. rewrite Pf0. do 2 zs. rewrite ENO.
    zs. br_true.
    replace (il_NO (ix_L X) + ir_put r + - (ir_out r - ir_left r)) with (il_NO (ix_L X) + (ir_put r - (ir_out r - ir_left r))) by lia.
    zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply ACALL; [lia| lia| rewrite LSL; lia| rewrite LSL; lia| exact BY| eassumption| rewrite E240; exact STK| rewrite E240; lia| rewrite E240; lia
                      | rewrite LSL; lia| rewrite LSL; reflexivity]
      | cbv beta; unfold adler32_postS; rewrite ?E240; post_call psegs mm ] end.
    try clear STK. match goal with H : stk psegs _ (ix_lo X) _ |- _ => rename H into STK end.
    do 5 zs.
    do 31 zs.
    rewrite bufrule_clang by lia.
    unfold RC, ret_model. change Z_FINISH with 4. change Z_OK with 0.
    destruct ((((wrap32 (ir_in r - ir_have r) =? 0) && (wrap32 (ir_out r - ir_left r) =? 0)) || (ix_flush X =? 4)) && (ir_ret r =? 0))%bool; cbn [Z.b2z].
    + zs. br_false. do 2 zs.
      itr_groups MUf WMf.
      apply evt_done. eapply IRETW_intro; try reflexivity.
      unfold IMEMLW. cbn [w_s w_c w_r].
      split; [exists retw, jf0, jf1, jf; unfold iframe_cells; exact FRM|].
      split; [exact STK|].
      split. { split.
               - eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. rewrite ?wz_wrap64. close_cells ZS.
               - constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]. }
      split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|].
      split; [eassumption|].
      split; [destruct MW0 as [MU0 _]; eapply munch_trans; [exact MU0| exact (munch_weaken _ _ _ _ HSUB MUf)]| exact WM].
    + zs. br_true. zs.
      itr_groups MUf WMf.
      apply evt_done. eapply IRETW_intro; try reflexivity.
      unfold IMEMLW. cbn [w_s w_c w_r].
      split; [exists retw, jf0, jf1, jf; unfold iframe_cells; exact FRM|].
      split; [exact STK|].
      split. { split.
               - eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app]. inorm. rewrite ?wz_wrap64. close_cells ZS.
               - constructor; inorm; [unfold isA, isA_cells; inorm; rewrite ?wz_wrap64; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]. }
      split; [exact IN|]. split; [unfold iout; rewrite (iout_bytes_ext _ _ c) by reflexivity; exact OUT|].
      split; [eassumption|].
      split; [destruct MW0 as [MU0 _]; eapply munch_trans; [exact MU0| exact (munch_weaken _ _ _ _ HSUB MUf)]| exact WM].
Qed.
