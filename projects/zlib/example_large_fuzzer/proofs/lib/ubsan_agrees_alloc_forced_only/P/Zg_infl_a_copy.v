(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_dview Z_dkit Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Z_infl_pure3 Z_updwin_pure Zh_kit Zg_infl_pure Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateA_STORED RefInflateA_COPY DeflateLz RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac close_mem jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma sx32_u : forall L, 0 <= L < 2 ^ 32 -> bv_unsigned (sx32 (wz L)) = if L <? 2 ^ 31 then L else L + 18446744069414584320.
Proof.
  intros L HL. unfold sx32. rewrite (unsigned_lit L) by lia.
  destruct (Z.ltb_spec L (2 ^ 31)) as [H|H].
  - rewrite bv_swrap32_id by lia. apply unsigned_lit. lia.
  - replace (bv_swrap 32 L) with (L - 4294967296).
    + apply Z_to_bv_unsigned_neg64 || (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; change (2 ^ 64) with 18446744073709551616; change (2 ^ 31) with 2147483648 in H; change (2 ^ 32) with 4294967296 in HL; Z.div_mod_to_equations; lia).
    + unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648.
      change (2 ^ 31) with 2147483648 in H. change (2 ^ 32) with 4294967296 in HL. Z.div_mod_to_equations. lia.
Qed.

Lemma len_sub_cell : forall L n, 0 < n <= L -> L < 2 ^ 32 ->
  le4 (wz (bv_swrap 32 (bv_unsigned (sx32 (wz L)) - n))) = le4 (wz (wrap32 (L - n))).
Proof.
  intros L n Hn HL. apply le4_wz_mod. rewrite sx32_u by lia. rewrite wrap32_id by lia.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648.
  destruct (Z.ltb_spec L 2147483648); Z.div_mod_to_equations; lia.
Qed.

Lemma blit_bytes : forall (dst src : arr) put so n,
  0 <= put -> 0 <= n -> put + n <= arr_len dst -> 0 <= so ->
  (forall i, 0 <= i < put -> 0 <= arr_get dst i < 256) -> (forall j, 0 <= arr_get src j < 256) ->
  forall i, 0 <= i < put + n -> 0 <= arr_get (arr_blit dst put src so n) i < 256.
Proof.
  intros dst src put so n Hp Hn Hle Hso Hd Hs i Hi. rewrite arr_get_blit. unfold arr_inb.
  destruct ((put <=? i) && (i <? put + Z.max 0 n) && ((0 <=? i) && (i <? arr_len dst))) eqn:E; [apply Hs|].
  apply Hd. apply Bool.andb_false_iff in E. destruct E as [E|E].
  - apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E; lia| apply Z.ltb_ge in E; lia].
  - apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E; lia| apply Z.ltb_ge in E; lia].
Qed.

Definition PC_COPY_T : Z := 0x1d814.  (* 1.4: the equal run 0x1d6b0..0x1d6c4 -> 0x1d7b4..0x1d7c8 (pcmap HAND) *)
Definition ICT (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (x8 x12 : word) : machine_state -> Prop :=
  fun ms => exists x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x30 m,
    ms = MS (mkR (wz (ir_left r)) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) x5 x6 x7 (wz (il_As (ix_L X)))
                 x8 (wz (il_S (ix_L X))) (wz (ix_flush X)) x12 x13 x14 x15 x16 x17
                 (wz (ir_have r)) (wz (il_NO (ix_L X) + ir_put r)) (wz n) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold r)) (wz (ir_bits r)) (wz 75072)
                 x27 (wz (il_NI (ix_L X) + ir_next r)) x28 (wz 30) x30 (wz (-16180)))
            (ix_F X) (wz PC_COPY_T) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X (mkW s c r) m.

Lemma ICT_intro : forall X s c r n x8 x12 x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc pc m,
  x1 = wz (ir_left r) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have r) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put r) -> x19 = wz n -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold r) -> x23 = wz (ir_bits r) -> x24 = wz 75072 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next r) -> x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X -> pc = wz PC_COPY_T ->
  IMEM X (mkW s c r) m ->
  ICT X s c r n x8 x12 (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31) F pc fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ICT. do 12 eexists. split; [reflexivity| assumption]. Qed.

Lemma copy_tail : forall X s c r n x8 x12 ms,
  ICT X s c r n x8 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> is_mode s = COPY -> is_flags s = 0 ->
  0 < n -> n <= ir_have r -> n <= ir_left r -> n <= is_length s -> is_length s < 2^32 -> ir_out r = arr_len (ic_outbuf c) ->
  evt psegs (fun ms' => IPOST X (ARun tt (mkW (iset_length s (wrap32 (is_length s - n))) (cpy_c c r n) (cpy_r r n))) ms'
                        /\ PATG X (mkW (iset_length s (wrap32 (is_length s - n))) (cpy_c c r n) (cpy_r r n))) ms.
Proof.
  intros X s c r n x8 x12 ms (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM) XO HREGS HP HM Pf0 Hn0 Hnh Hnl HnL RLEN HOUT.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (HISR : ISR s) by (split; assumption).
  assert (HAV : ir_have r < 2^31 /\ ir_left r < 2^31) by (rewrite Pin in Rnh; rewrite Pout in Rpl; lia).
  assert (ELEN : arr_len (ix_input X) = ir_next r + ir_have r) by (rewrite <- Pin; lia).
  assert (ELEN2 : Z.of_nat (length (ix_rest0 X)) = ir_put r + ir_left r) by (rewrite <- Pout; lia).

  assert (HP' : PATG X (mkW (iset_length s (wrap32 (is_length s - n))) (cpy_c c r n) (cpy_r r n))).
  { destruct POB as (POB1 & POW & POL & _ & PHW). unfold PATG, OBYT, cpy_c, cpy_r. ired. rewrite arr_len_blit, HM.
    split; [exact Pw|]. split; [exact Pwb|]. split; [exact Phd|]. split; [left; exact Pf0|]. split; [unfold COPY, FLAGS, HCRC; lia|].
    split; [exact Pwin|]. split; [exact Pin|]. split; [exact Pin1|]. split; [exact Pout|]. split; [exact Pout1|]. split; [exact HISR|].
    split; [apply blit_bytes; try lia; [exact POB1| exact Rin]|].
    split; [exact POW|]. split; [rewrite HOUT, wrap32_id by lia; lia|]. split; [reflexivity| exact PHW]. }
  clear Pfl PL PHD.
  pose proof HMEM as ((jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM). unfold iframe_cells in FRM. unfold iin, u8ro in IN. unfold iout in OUT. unfold ix_W in MU. cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_COPY_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA.
  do 2 zs. rewrite (zx32_small n) by lia. do 5 zs.

  assert (SRC : bytes_at psegs m (il_NI (ix_L X) + ir_next r) (map (Z_to_bv 8) (arr_slice (ix_input X) (ir_next r) n))).
  { rewrite <- (av8_sub (ix_input X) (arr_len (ix_input X)) (ir_next r) n) by lia.
    pose proof IN as IN2. rewrite <- (firstn_skipn (Z.to_nat (ir_next r)) (av8 (ix_input X) (arr_len (ix_input X)))) in IN2.
    apply bytes_at_app in IN2. destruct IN2 as [_ IN2]. rewrite length_firstn, av8_length, Nat.min_l in IN2 by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn _ _)) in IN2. apply bytes_at_app in IN2. destruct IN2 as [IN2 _].
    replace (il_NI (ix_L X) + ir_next r) with (il_NI (ix_L X) + Z.of_nat (Z.to_nat (ir_next r))) by lia. exact IN2. }
  destruct (u8arr_split3 _ (il_NO (ix_L X)) (iout_bytes (ix_rest0 X) c (ir_put r)) (Z.to_nat (ir_put r)) (Z.to_nat n) OUT ltac:(lia)) as (O1 & O2 & O3).
  replace (il_NO (ix_L X) + Z.of_nat (Z.to_nat (ir_put r))) with (il_NO (ix_L X) + ir_put r) in O2, O3 by lia.
  clear OUT.
  eapply evt_cut.
  { eapply (memcpy_Z (il_NO (ix_L X) + ir_put r) (il_NI (ix_L X) + ir_next r) n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m
              (map (Z_to_bv 8) (arr_slice (ix_input X) (ir_next r) n)));
      [exact SRC| unfold arr_slice; rewrite length_map, arr_slice_nat_length; lia| exact O2| pose proof (xo_io _ XO) as SEPIO; unfold apart in SEPIO; rewrite <- Pin in *; lia| exact MI| lia| lia| lia]. }
  intros ms' PO. destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & PC & SRC').
  clear SRC SRC' O2.
  pose proof (f_equal Z.of_nat (firstn_length_le (iout_bytes (ix_rest0 X) c (ir_put r)) (n := Z.to_nat (ir_put r)) ltac:(lia))) as LO1.
  apply (fun H => u8arr_transport psegs _ m m' _ _ H MUc WMc) in O1; [| cbn [disjoint_from]; rewrite LO1; lia].
  itr_groups MUc WMc.
  transport_after_call psegs m m' MUc WMc.
  pose proof (u8arr_join3 m' (il_NO (ix_L X)) _ _ _ (Z.to_nat n) O1 ltac:(rewrite length_firstn, iout_bytes_length, Nat.min_l by lia; replace (il_NO (ix_L X) + Z.of_nat (Z.to_nat (ir_put r))) with (il_NO (ix_L X) + ir_put r) by lia; exact PC)
                ltac:(rewrite length_firstn, iout_bytes_length, Nat.min_l by lia; replace (il_NO (ix_L X) + Z.of_nat (Z.to_nat (ir_put r)) + Z.of_nat (Z.to_nat n)) with (il_NO (ix_L X) + ir_put r + Z.of_nat (Z.to_nat n)) by lia; exact O3)) as OUT.
  rewrite <- Pin in OUT. rewrite <- (iout_bytes_blit (ix_rest0 X) c (ic_input c) (ir_next r) (ir_put r) n) in OUT by lia.
  change (icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) n)) with (cpy_c c r n) in OUT.
  replace (Z.to_nat (ir_put r) + Z.to_nat n)%nat with (Z.to_nat (ir_put r + n)) in OUT by lia.
  clear O1 O3 PC. clear MUc WMc. ifine m'.
  pose proof (iout_bytes_length (ix_rest0 X) (cpy_c c r n) (ir_put r + n) ltac:(unfold cpy_c; cbn [ic_outbuf icset_outbuf]; lia)) as LOB2. apply (f_equal Z.of_nat) in LOB2.
  assert (RMODE : 0 <= is_mode s < 2 ^ 31) by (rewrite HM; unfold COPY; lia).
  replace (ret_pc (wz 120880)) with (wz 120880) by (symmetry; apply ret_pc_even; [lia| reflexivity]).  (* 1.4: memcpy returns to 0x1d7d0 *)
  do 17 zs.
  itr_groups MUf WMf.
  apply evt_done. split; [|exact HP'].
  cbn [IPOST]. eexists. eapply ILOOP_intro; unfold cpy_r; ired; [ireg .. |].
  apply IMEM_intro; inorm.
  - exists jf. exact FRM.
  - exact STK.
  - exact ZS.
  - constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA; apply len_sub_cell; lia| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| unfold cpy_c; unfold iarrs in *; inorm; rewrite ?arr_len_blit; exact ARRS| exact LAY].
  - exact IN.
  - unfold iout. exact OUT.
  - eassumption.
  - exact MU.
  - exact WM.
Qed.

Lemma copy_core : forall X w x8 x12 ms,
  ILOOP X w PC_COPY x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = COPY ->
  evt psegs (fun ms' => IPOST X (arm_COPY w) ms' /\ PATG X (wof (arm_COPY w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as HREGS0.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  assert (HAV : ir_have r < 2^31 /\ ir_left r < 2^31) by (rewrite Pin in Rnh; rewrite Pout in Rpl; lia).
  assert (HISR : ISR s) by (split; assumption).
  assert (RLEN : 0 <= is_length s < 2^32) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H); exact H).
  assert (RMODE : 0 <= is_mode s < 2 ^ 31) by (rewrite HM; unfold COPY; lia).
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF.
  clear RH HCORE HMF HWB Pfl PL PHD HW.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM0).
  pose proof HMEM0 as ((jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (sx32_u _ RLEN) as ESX.
  unfold PC_COPY. do 2 zs. br_cases K0; rewrite ESX in K0.
  -
    assert (EL0 : is_length s = 0) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
    rewrite (arm_COPY_zero s c r EL0).
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [| cbn [wof]; eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity..|]; exact HISR].
    cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm.
    + exists jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (NL0 : is_length s <> 0) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
    itr_groups MUf WMf.
    zs. br_cases K1; rewrite ?ESX in K1.
    +
      assert (K1' : is_length s < ir_have r /\ is_length s < 2^31) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
      zs. br_cases K2; rewrite ?ESX in K2.
      *
        assert (K2' : is_length s < ir_left r) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
        assert (ECN : cpy_n s r = is_length s)
          by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
        zs. br_true.
      rewrite (arm_COPY_run s c r NL0 ltac:(rewrite ECN; lia)), ECN.
      eapply copy_tail; [ eapply ICT_intro; ired; [ireg .. | reflexivity | exact HMEM0] | exact XO | exact HREGS0 | exact HP | exact HM | exact Pf0 | lia | lia | lia | lia | lia | exact HWF ].
      *
        assert (K2' : ir_left r <= is_length s) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
        zs. zs. br_cases K3.
        -- assert (ECN : cpy_n s r = ir_left r)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_run s c r NL0 ltac:(rewrite ECN; lia)), ECN.
           eapply copy_tail; [ eapply ICT_intro; ired; [ireg .. | reflexivity | exact HMEM0] | exact XO | exact HREGS0 | exact HP | exact HM | exact Pf0 | lia | lia | lia | lia | lia | exact HWF ].
        --
           assert (ECN : cpy_n s r = 0)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_leave s c r NL0 ECN).
           do 2 zs.
           apply evt_done. split; [|exact HP].
           cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
           apply IMEML_intro; inorm.
           ++ exists (wz (ir_ret r)), jf. exact FRM.
           ++ exact STK.
           ++ exact ZS.
           ++ constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
           ++ exact IN.
           ++ unfold iout. exact OUT.
           ++ eassumption.
           ++ exact MU.
           ++ exact WM.
    +
      assert (K1' : ir_have r <= is_length s) by (destruct (Z.ltb_spec (is_length s) (2 ^ 31)); lia).
      zs. zs. br_cases K2.
      *
        zs. zs. br_cases K3.
        -- assert (ECN : cpy_n s r = ir_left r)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_run s c r NL0 ltac:(rewrite ECN; lia)), ECN.
           eapply copy_tail; [ eapply ICT_intro; ired; [ireg .. | reflexivity | exact HMEM0] | exact XO | exact HREGS0 | exact HP | exact HM | exact Pf0 | lia | lia | lia | lia | lia | exact HWF ].
        -- assert (ECN : cpy_n s r = 0)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_leave s c r NL0 ECN).
           do 2 zs.
           apply evt_done. split; [|exact HP].
           cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
           apply IMEML_intro; inorm.
           ++ exists (wz (ir_ret r)), jf. exact FRM.
           ++ exact STK.
           ++ exact ZS.
           ++ constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
           ++ exact IN.
           ++ unfold iout. exact OUT.
           ++ eassumption.
           ++ exact MU.
           ++ exact WM.
      *
        zs. br_cases K3.
        -- assert (ECN : cpy_n s r = ir_have r)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_run s c r NL0 ltac:(rewrite ECN; lia)), ECN.
           eapply copy_tail; [ eapply ICT_intro; ired; [ireg .. | reflexivity | exact HMEM0] | exact XO | exact HREGS0 | exact HP | exact HM | exact Pf0 | lia | lia | lia | lia | lia | exact HWF ].
        -- assert (ECN : cpy_n s r = 0)
             by (unfold cpy_n; cbv zeta; destruct (Z.ltb_spec (ir_have r) (is_length s)); destruct (Z.ltb_spec (ir_left r) (ir_have r)); destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
           rewrite (arm_COPY_leave s c r NL0 ECN).
           do 2 zs.
           apply evt_done. split; [|exact HP].
           cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
           apply IMEML_intro; inorm.
           ++ exists (wz (ir_ret r)), jf. exact FRM.
           ++ exact STK.
           ++ exact ZS.
           ++ constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
           ++ exact IN.
           ++ unfold iout. exact OUT.
           ++ eassumption.
           ++ exact MU.
           ++ exact WM.
Qed.

Lemma arm_COPY_ok : forall flush, arm_stmtg flush COPY PC_COPY arm_COPY.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (copy_core X w _ x12 ms HL XO HW HP HM). Qed.

Lemma arm_COPY__eq : forall s c r, arm_COPY_ (mkW s c r) = arm_COPY (mkW (iset_mode s COPY) c r).
Proof. intros s c r. unfold arm_COPY_. rewrite abind_run, set_mode_eq. reflexivity. Qed.

Lemma copy__core : forall X w x8 x12 ms,
  ILOOP X w PC_COPY_ x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = COPY_ ->
  evt psegs (fun ms' => IPOST X (arm_COPY_ w) ms' /\ PATG X (wof (arm_COPY_ w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. rewrite arm_COPY__eq.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & POB). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HISR : ISR s) by (split; assumption).
  set (w1 := mkW (iset_mode s COPY) c r).
  assert (HW1 : WINV w1).
  { unfold WINV, w1. cbn [w_s w_c w_r]. split; [exact HCORE|]. split; [exact HREGS|].
    rewrite HM in HMF, HWF. unfold MF, WF in *. cbn in HMF, HWF |- *. split; [exact HMF|]. split; [exact HWF| exact HWB]. }
  assert (HP1 : PATG X w1).
  { unfold w1. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold COPY, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact HISR. }
  eapply (evt_cut psegs (fun ms' => exists x12', ILOOP X w1 PC_COPY x8 x12' ms')).
  2:{ intros ms1 (x12' & H1). exact (copy_core X w1 x8 x12' ms1 H1 XO HW1 HP1 eq_refl). }
  clear RH HCORE HMF HWF HWB Rin Pfl PL PHD HREGS HW HW1 HP1. subst w1.
  iarm_open HL. ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  unfold PC_COPY_. do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. eapply ILOOP_intro; inorm; [ireg .. |].
  apply IMEM_intro; inorm.
  + exists jf. exact FRM.
  + exact STK.
  + exact ZS.
  + constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
  + exact IN.
  + unfold iout. exact OUT.
  + eassumption.
  + exact MU.
  + exact WM.
Qed.

Lemma copy__core_ok : copy__core_stmt.
Proof. exact copy__core. Qed.

Lemma arm_COPY__ok : forall flush, arm_stmtg flush COPY_ PC_COPY_ arm_COPY_.
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (copy__core X w _ x12 ms HL XO HW HP HM). Qed.
