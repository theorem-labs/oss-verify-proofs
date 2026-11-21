(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit Z_infl_iface Z_infl_c_pure Z_infl_c_tab Z_infl_t_iface Z_itab_kit Z_infl_a_dist1 Z_infl_a_lenlens1 Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1 RefInflateA_CODELENS1 RefInflateA_CODELENS11. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA5. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.
Definition PC_CL_B : Z := 0x1fc7c.
Definition PC_CL_J : Z := 0x1fd64.
Definition PC_CL_X : Z := 0x20014.
Definition CLK (X : ictx) (s : inflate_state) (q : iscrh) : Prop :=
  h11 q = wz (is_nlen s + is_ndist s) /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_lenbits s)
  /\ h14 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz (Z.ones (is_lenbits s)).
Definition CLB (X : ictx) (s : inflate_state) (r : iregs) (hv : Z) (q : iscrh) : Prop :=
  CLK X s q /\ h16 q = wz hv /\ h17 q = wz (il_NI (ix_L X) + ir_next r) /\ h31 q = wz (ir_have r) /\ HCC X r q.
Definition CLX (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop := h12 q = wz (is_nlen s) /\ HCC X r q.
Lemma cl_entry : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CODELENS_E q ms -> HCC X r q ->
  0 <= is_have s <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  evt usegs (fun ms' => exists q',
     if is_have s <? is_nlen s + is_ndist s
     then ILOOPh X (mkW s c r) PC_CL_B q' ms' /\ CLB X s r (is_have s) q'
     else ILOOPh X (mkW s c r) PC_CL_X q' ms' /\ CLX X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ Rh Rnl Rnd Rlb CPO.
  unfold HCC, HC in HQ. hred_in HQ. destruct HQ as ((E9 & E18 & E22 & E24 & E25) & E10).
  destruct HL as (m & -> & HMEM). hred. subst x9 x18 x22 x24 x25 x10.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_CODELENS_E.
  do 4 zs. zstep. br_cases K.
  - replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLX, HCC, HC. hred. repeat split; ireg.
  - replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    rd_sub GA 120%nat 0%nat 4%nat. do 7 zs. rewrite clang_mask32 by lia.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLB, CLK, HCC, HC. hred. repeat split; ireg.
Qed.
Definition cl_QJ (X : ictx) (s : inflate_state) (r r1 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  h23 q = wz (code_w e) /\ h30 q = wz (code_bits e) /\ h29 q = wz (code_w e ≫ 8)
  /\ h7 q = wz (ir_bits r1) /\ h5 q = wz (ir_bits r1) /\ h19 q = wz (- ir_bits r1) /\ h22 q = wz (ir_hold r1)
  /\ h6 q = wz (ir_have r1) /\ h24 q = wz (ir_have r1) /\ h25 q = wz (il_NI (ix_L X) + ir_next r1) /\ h28 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h16 q = wz (is_have s) /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r).
Lemma cl_dec : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATI X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dlvl c s (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits r ->
  evt usegs (DECJ X s c r r (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_CL_J (cl_QJ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP RN CPO DL.
  unfold CLB, CLK, HCC, HC in HQ. hred_in HQ.
  destruct HQ as ((E11 & E12 & E13 & E14 & E15) & E16 & E17 & E31 & (E9 & E18 & E22 & E24 & E25) & E10).
  destruct HL as (m & -> & HMEM). hred. subst x11 x12 x13 x14 x15 x16 x17 x31 x9 x18 x22 x24 x25 x10.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST.
  unfold PC_CL_B. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  zs. gT. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0. pose proof (cp_addr_rng (ix_L X) p i0 CPO RI0 ltac:(lia)) as CPR.
  zs. rewrite (Z.shiftl_mul_pow2 i0 2) by lia. change (2^2) with 4. zs. gT.
  do 3 zs. rewrite xor_guard by lia. gT.
  replace (0 <? cp_addr (ix_L X) p) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  do 9 zs. rewrite ?land_u32_small by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e0); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e0); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e0) as RW0. do 2 zs. rewrite code_w_bits.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold cl_QJ, CLK. hred. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    zstep. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gT. zs. gT.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      pose proof (cp_addr_rng (ix_L X) p i1 CPO RI1 ltac:(lia)) as CPR1.
      zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gT.
      do 6 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e1); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e1); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e1) as RW1. do 2 zs. rewrite code_w_bits.
      zstep. br_cases K3.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold cl_QJ, CLK. hred. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_false. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.
Lemma code_w_sh20 : forall v, code_w v ≫ 20 = code_val v ≫ 4.
Proof.
  intros v. unfold code_w. pose proof (code_lo_range v) as RL. pose proof (code_val_range v) as RV.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with (65536 * 16). change (2 ^ 4) with 16.
  rewrite <- Z.div_div by lia. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small (code_lo v)) by lia.
  rewrite Z.add_0_r. reflexivity.
Qed.
Lemma code_w_sl48 : forall v, Z.land (code_w v ≪ 48) 18446744073709551615 ≫ 56 = code_bits v.
Proof.
  intros v. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold code_w, code_lo. pose proof (code_op_range v) as RO. pose proof (code_bits_range v) as RB. pose proof (code_val_range v) as RV.
  replace ((code_op v + 256 * code_bits v + 65536 * code_val v) * 2 ^ 48) with ((code_op v + 256 * code_bits v) * 2 ^ 48 + code_val v * 2 ^ 64)
    by (change (2 ^ 64) with (65536 * 2 ^ 48); lia).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by (change (2 ^ 64) with (65536 * 2 ^ 48); lia).
  change (2 ^ 56) with (2 ^ 48 * 2 ^ 8). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. change (2 ^ 8) with 256.
  rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Local Ltac close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].
Lemma cl_litw : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) < 16 ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_nlen s + is_ndist s -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_have r1 -> 0 <= ir_next r1 ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let s' := cl_lit s (code_val here) in let r' := ddrop r1 (code_bits here) in
  evt usegs (fun ms' => exists q',
     if is_have s + 1 <? is_nlen s + is_ndist s
     then ILOOPh X (mkW s' c r') PC_CL_B q' ms' /\ CLB X s' r' (is_have s + 1) q'
     else ILOOPh X (mkW s' c r') PC_CL_X q' ms' /\ CLX X s' r' q') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EI EO ER EP EL RB RH RI CPO RN RV LL Rh Rnl Rnd RPUT Rh1 Rn1.
  unfold cl_QJ, CLK in HQ. hred_in HQ.
  destruct HQ as (E23 & E30 & E29 & E7 & E5 & E19 & E22 & E6 & E24 & E25 & E28 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RB1. pose proof (code_val_range e1) as RV1. pose proof (code_w_range e1) as RW1.
  cbv zeta.
  zs. rewrite code_w_sh20. rewrite (Z.shiftr_div_pow2 (code_val e1) 4) by lia. change (2 ^ 4) with 16. rewrite (Z.div_small (code_val e1) 16) by lia.
  zs. rewrite code_w_val.
  zstep. br_false.
  zs. gT.
  zs. zs. zs. itr_groups MUf WMf. clear MUf WMf.
  gT.
  zs. replace (is_have s ≪ 1) with (2 * is_have s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  zs. rewrite code_w_g63 by lia.
  zs. zs. rewrite subw_land64 by lia. replace (0 - - ir_bits r1) with (ir_bits r1) by lia.
  zs. zs. zs. rewrite code_w_sl48. zs.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv usegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl usegs m1) as WMf end.
  assert (EV : wrap16 (code_val e1) = code_val e1) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s) (wrap16 (code_val e1)) ltac:(rewrite EV; reflexivity).
  do 3 zs. itr_groups MUf WMf.
  zstep. br_cases K.
  - replace (is_have s + 1 <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
    + close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
    + unfold CLB, CLK, HCC, HC, cl_lit, ddrop. hred. ired. fold p n. repeat split; ireg.
  - zs. replace (is_have s + 1 <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
    + close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
    + unfold CLX, HCC, HC, cl_lit, ddrop. hred. ired. repeat split; ireg.
Qed.
Definition cl_pcx (val : Z) : Z := if val =? 16 then 0x1ff2c else if val =? 17 then 0x1fef8 else 0x1ff90.
Definition cl_QN (X : ictx) (s : inflate_state) (r r1 r2 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  h5 q = wz (ir_bits r2) /\ h7 q = wz (ir_bits r2) /\ h17 q = wz (il_NI (ix_L X) + ir_next r2) /\ h28 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h22 q = wz (ir_hold r2) /\ h24 q = wz (ir_have r2)
  /\ h30 q = wz (code_bits e) /\ h29 q = wz (code_w e ≫ 8) /\ h23 q = wz (code_w e)
  /\ h16 q = wz (is_have s) /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).
Definition NBJc (X : ictx) (s : inflate_state) (c : icall) (r r1 : iregs) (n pcx : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r2 q', NEEDBITS n (mkW s c r1) = ARun tt (mkW s c r2)
                   /\ ((r2 = r1 /\ n <= ir_bits r1) \/ (r2 = pullr c r1 /\ 0 < ir_have r1 /\ ir_bits r1 < n <= ir_bits r1 + 8))
                   /\ ILOOPh X (mkW s c r) pcx q' ms' /\ cl_QN X s r r1 r2 q')
    \/ (exists r2, NEEDBITS n (mkW s c r1) = ALeave (mkW s c r2) /\ (r2 = r1 \/ r2 = pullr c r1) /\ ILEAVE X (mkW s c r2) ms').
Local Ltac nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER :=
  let K := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in
  zs; zstep; br_cases K;
  [
    do 2 zs; apply evt_done; left; eexists r1, _; split; [apply nb_enough; lia|]; split; [left; split; [reflexivity| lia]|];
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
    unfold cl_QN, CLK; hred; repeat split; ireg
  | zs; zstep; br_cases K2;
    [
      let H1 := fresh "H1" in let NXT := fresh "NXT" in let RD := fresh "RD" in
      assert (H1 : ir_have r1 = 1) by lia;
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia);
      do 2 zs; gT; zs; gT;
      pose proof (u8ro_read usegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD;
      zs; clear RD; do 7 zs; rewrite <- Pin; rewrite !pull_shift by lia; zstep; br_cases K3;
      [
        zstep; br_false; do 7 zs; rewrite H1; change (Z.land 1 4294967295) with 1;
        apply evt_done; right; exists (pullr c r1); split; [apply nb_pull_dry; lia|]; split; [right; reflexivity|];
        unfold hide in RH; eapply ILEAVE_intro; pullr_rw c r1; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| rewrite ?pullr_in, ?pullr_out, ?pullr_put, ?pullr_left; assumption ..]
      | zs; apply evt_done; left; eexists (pullr c r1), _; split; [apply nb_pull_ok; lia|]; split; [right; split; [reflexivity| lia]|];
        split; [unfold hide in RH; eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
        unfold hide in RH; unfold cl_QN, CLK; hred; pullr_rw c r1;
        rewrite H1; change (Z.land 1 4294967295) with 1; repeat split; ireg ]
    |
      let H0 := fresh "H0" in assert (H0 : ir_have r1 = 0) by lia;
      do 7 zs; rewrite H0; apply evt_done; right; exists r1; split; [apply nb_dry; lia|]; split; [left; reflexivity|];
      eapply ILEAVE_intro; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| assumption ..] ] ].
Lemma cl_need : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> DREGS c r1 -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= 32 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  16 <= code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  evt usegs (NBJc X s c r r1 (code_bits here + cl_nb (code_val here)) (cl_pcx (code_val here))) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP EI EO ER EP EL RB RB32 RI CPO RN RV.
  unfold cl_QJ, CLK in HQ. hred_in HQ.
  destruct HQ as (E23 & E30 & E29 & E7 & E5 & E19 & E22 & E6 & E24 & E25 & E28 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18).
  destruct HL as (m & -> & HMEM). hred. subst.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB1 & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r1)) as RBy.
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_CL_J.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RBe. pose proof (code_val_range e1) as RVe. pose proof (code_w_range e1) as RWe.
  cbv zeta.
  zs. rewrite code_w_sh20.
  assert (V4 : 0 < code_val e1 ≫ 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; Z.div_mod_to_equations; lia).
  pose proof (shiftr_le (code_val e1) 4 ltac:(lia) ltac:(lia)) as V4'.
  zs. rewrite code_w_val.
  zstep. br_true.
  zs. zs. rewrite subw_land64 by lia. replace (0 - - ir_bits r1) with (ir_bits r1) by lia.
  zstep. br_cases K16.
  {  unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER. }
  zs. zstep. br_cases K17.
  {  unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (code_val e1 =? 17) with false by (symmetry; apply Z.eqb_neq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER. }
   unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (code_val e1 =? 17) with true by (symmetry; apply Z.eqb_eq; lia).
  nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER.
Qed.
Definition PC_CL_R : Z := 0x1ffd4.
Definition PC_CL_RX : Z := 0x20004.
Definition CLR (X : ictx) (s : inflate_state) (r : iregs) (i cnt v : Z) (q : iscrh) : Prop :=
  h16 q = wz i /\ h5 q = wz cnt /\ h6 q = wz v /\ h7 q = wz 320 /\ h17 q = wz (il_NI (ix_L X) + ir_next r)
  /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2)
  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h24 q = wz (ir_have r).
Local Ltac close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].
Local Ltac bad_stub MUf WMf := do 6 zs; itr_groups MUf WMf.
Lemma cl_rep_hd : forall X s c r r1 r2 q ms,
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let val := code_val here in let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  let len := (if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0) in
  let copy := cl_base val + BITSv (ir_hold r3) nb in
  let r4 := ddrop r3 nb in
  ILOOPh X (mkW s c r) (cl_pcx val) q ms -> cl_QN X s r r1 r2 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r2 = ir_in r -> ir_out r2 = ir_out r -> ir_ret r2 = ir_ret r -> ir_put r2 = ir_put r -> ir_left r2 = ir_left r ->
  code_bits here + nb <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_have r2 -> 16 <= val ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s <= is_nlen s + is_ndist s -> is_nlen s + is_ndist s <= 320 ->
  (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_next r2 ->
  evt usegs (fun ms' =>
    if (val =? 16) && (is_have s =? 0) then exists x26 x12, ILOOP X (cl_bad s c r3) PC_DISPATCH x26 x12 ms'
    else if is_nlen s + is_ndist s <? is_have s + copy then exists x26 x12, ILOOP X (cl_bad s c r4) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW s c r4) PC_CL_R q' ms' /\ CLR X s r4 (is_have s) copy len q') ms.
Proof.
  intros X s c r r1 r2 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms.
  intros here val nb r3 len copy r4 HL HQ XO HP EI EO ER EP EL RB RH RHV RV LL Rh Rnd HLs RPUT Rn2.
  unfold cl_QN, CLK in HQ. hred_in HQ.
  destruct HQ as (E5 & E7 & E17 & E28 & E22 & E24 & E30 & E29 & E23 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10).
  iarm_openh HL. subst x5 x7 x17 x28 x22 x24 x30 x29 x23 x16 x11 x12 x13 x14 x15 x9 x10.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  fold here. set (cb := code_bits here) in *. pose proof (code_bits_range here) as RCB. fold cb in RCB. pose proof (code_w_range here) as RW.
  assert (Rnb : 2 <= nb <= 7) by (subst nb; unfold cl_nb; destruct (val =? 16); [lia|]; destruct (val =? 17); lia).
  pose proof (shiftr_le (ir_hold r2) cb ltac:(lia) ltac:(lia)) as RH3.
  assert (EH3 : ir_hold r3 = ir_hold r2 ≫ cb) by reflexivity.
  pose proof (BITSv_land (ir_hold r3) nb ltac:(rewrite EH3; lia) ltac:(lia)) as EBV. pose proof (land_ones_rng (ir_hold r3) nb ltac:(lia)) as RBV. rewrite <- EBV in RBV.
  assert (Rcp : 3 <= copy <= 138).
  { subst copy. assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    unfold cl_base. destruct (val =? 16); [lia|]. destruct (val =? 17); lia. }
  unfold cl_pcx.
  destruct (Z.eqb_spec val 16) as [V16|NV16].
  -
    assert (Enb : nb = 2) by (subst nb; unfold cl_nb; rewrite V16; reflexivity).
    assert (Ecp : copy = 3 + Z.land (ir_hold r3) 3) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V16; reflexivity).
    zs. gT. zs. rewrite code_w_g63 by lia. fold cb. zs. zstep. br_cases K0.
    + replace (is_have s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (HLs (is_have s - 1) ltac:(lia)) as RLEN.
      zs. gT. zs. zs. replace ((is_have s + -1) ≪ 1) with (2 * (is_have s - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true. zs. zs.
      pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s - 1) ltac:(lia). clear Gl'.
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 2 ltac:(lia)) as R3. change (Z.ones 2) with 3 in R3. change (2 ^ 2) with 4 in R3.
      rewrite EH3 in Ecp.
      do 5 zs. zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    +
      replace (is_have s =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
      zs. do 2 zs. bad_stub MUf WMf.
      apply evt_done. eexists _, _. unfold cl_bad. subst r3. unfold ddrop. eapply ILOOP_intro; ired; [ireg .. |].
      close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
  - cbn [andb].
    destruct (Z.eqb_spec val 17) as [V17|NV17].
    + assert (Enb : nb = 3) by (subst nb; unfold cl_nb; rewrite V17; reflexivity).
      assert (Ecp : copy = 3 + Z.land (ir_hold r3) 7) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V17; reflexivity).
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 3 ltac:(lia)) as R3. change (Z.ones 3) with 7 in R3. change (2 ^ 3) with 8 in R3.
      rewrite EH3 in Ecp.
      zs. gT. zs. zs. rewrite code_w_g63 by lia. fold cb. do 6 zs.
      zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    + assert (Enb : nb = 7).
      { subst nb; unfold cl_nb. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      assert (Ecp : copy = 11 + Z.land (ir_hold r3) 127).
      { subst copy; rewrite EBV, Enb; unfold cl_base. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 7 ltac:(lia)) as R3. change (Z.ones 7) with 127 in R3. change (2 ^ 7) with 128 in R3.
      rewrite EH3 in Ecp.
      zs. gT. zs. zs. rewrite code_w_g63 by lia. fold cb. do 5 zs.
      zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
Qed.
