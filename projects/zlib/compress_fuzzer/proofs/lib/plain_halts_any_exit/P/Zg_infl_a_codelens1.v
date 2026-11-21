(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Zg_infl_t_iface Zg_infl_c_kit Zg_infl_a_lenlens1 Zg_infl_a_lenlens.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1 RefInflateA_CODELENS1 RefInflateA_CODELENS11 RefInflateSafeA5 RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeOK3 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.
Local Notation pullr := RefInflateArmLib.pullr.

Definition PC_CL_B : Z := 0x1d9c0.
Definition PC_CL_L : Z := 0x1d9e4.
Definition PC_CL_J : Z := 0x1da34.
Definition PC_CL_T : Z := 0x1dbdc.
Definition PC_CL_X : Z := 0x1dbe8.

Definition CLK (X : ictx) (s : inflate_state) (q : iscr) : Prop :=
  sc12 q = wz (is_nlen s) /\ sc14 q = wz (is_nlen s + is_ndist s) /\ sc15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ sc16 q = wz (Z.ones (is_lenbits s)).

Lemma cl_entry : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_CODELENS_E q ms -> sc13 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  0 <= is_have s <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  evt psegs (fun ms' => exists q',
     if is_have s <? is_nlen s + is_ndist s
     then ILOOPg X (mkW s c r) PC_CL_B q' ms' /\ CLK X s q' /\ sc13 q' = wz (is_have s) /\ sc6 q' = wz (ir_have r)
          /\ sc7 q' = wz (il_NI (ix_L X) + ir_next r) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     else ILOOPg X (mkW s c r) PC_CL_X q' ms' /\ sc12 q' = wz (is_nlen s) /\ sc13 q' = wz (is_have s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E26 Rh Rnl Rnd Rlb CPO.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_CODELENS_E.
  do 4 zs. br_cases K.
  - replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc12 sc13 sc26]. repeat split; ireg.
  - replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    rd_sub GA 136%nat 0%nat 4%nat. do 7 zs. rewrite clang_mask32 by lia.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLK. cbn [sc6 sc7 sc12 sc13 sc14 sc15 sc16 sc26]. repeat split; ireg.
Qed.

Definition cl_QJ (X : ictx) (s : inflate_state) (r r1 : iregs) (q : iscrh) : Prop :=
  h28 q = wz (dec_idx1 (is_lenbits s) (ir_hold r1)) /\ h5 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))
  /\ h17 q = wz (ir_bits r1) /\ h9 q = wz (ir_have r1) /\ h22 q = wz (ir_hold r1) /\ h26 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h23 q = wz (ir_bits r) /\ h29 q = wz 30 /\ h31 q = wz (-16180)
  /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_have s) /\ h14 q = wz (is_nlen s + is_ndist s)
  /\ h15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h16 q = wz (Z.ones (is_lenbits s)).

Lemma cl_loop1 : forall k X s c rb r rf q ms,
  ILOOPh X (mkW s c rb) PC_CL_L q ms ->
  h6 q = wz (ir_have rb) -> h7 q = wz (il_NI (ix_L X) + ir_next rb) -> h23 q = wz (ir_bits rb) ->
  h9 q = wz (ir_have r) -> h29 q = wz (ir_bits r) -> h17 q = wz (ir_bits r) -> h30 q = wz (il_NI (ix_L X) + ir_next r) -> h22 q = wz (ir_hold r) ->
  h12 q = wz (is_nlen s) -> h13 q = wz (is_have s) -> h14 q = wz (is_nlen s + is_ndist s) ->
  h15 q = wz (cp_addr (ix_L X) (is_lencode s)) -> h16 q = wz (Z.ones (is_lenbits s)) -> h31 q = wz (-16180) ->
  ix_ok X -> REGS c r -> pulled rb r -> 0 <= ir_bits rb -> 0 <= ir_have rb < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  ir_bits r < code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r))) ->
  dchk k c (dec_idx1 (is_lenbits s)) code_bits (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r = Some rf ->
  evt psegs (DECG X s c rb rb (DECODE_k k (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits (mkW s c r)) rf
               (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_CL_J (cl_QJ X s rb)) ms.
Proof.
  induction k as [|k IH]; intros X s c rb r rf [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms
    HL E6 E7 E23 E9 E29 E17 E30 E22 E12 E13 E14 E15 E16 E31 XO HREGS HPL HB0 HH0 Pin Pin1 RN CPO HB HD.
  { exfalso. exact (CK_short0 _ _ _ _ _ _ _ HD HB). }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
  subst x6 x7 x23 x9 x29 x17 x30 x22 x12 x13 x14 x15 x16 x31.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor rb r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs rb r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (ones_range15 n RN) as RMK.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0].
  unfold PC_CL_L. ix_open XO.
  zs. br_cases K.
  -
    pose proof (CK_pull _ _ _ _ _ _ _ _ HD HB ltac:(lia)) as HD'.
    rewrite (DC_pull k p (dec_idx1 n) code_bits s c r) by lia.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c rb r HREGS HB0 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7 & E8 & E9' & RH1).
    assert (RH1' : 0 <= ir_hold (pullr c r) < 2^64).
    { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
    apply (id : _ -> hide _) in RH1.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    replace (arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r) with (ir_hold (pullr c r)) by lia.
    pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
    zs. rewrite EI1.
    pose proof (code_bits_range (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) as RB1.
    destruct (CK_range _ _ _ _ _ _ _ _ HD') as [RI1 RN1].
    do 2 zs.
    pose proof (code_rd_bits m (ix_L X) s p (dec_idx1 n (ir_hold (pullr c r))) (wa (cp_addr (ix_L X) p + dec_idx1 n (ir_hold (pullr c r)) ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    zs. cbv beta. rewrite (bv8_small (code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))))) by exact RB1. clear RD.
    do 6 zs. br_cases K3.
    +
      eapply (IH X s c rb (pullr c r) rf);
        [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h29 h30 h31] ..
        | exact XO | exact HREGS1 | exact HPL1 | exact HB0 | exact HH0 | exact Pin | exact Pin1 | exact RN | exact CPO | rewrite E6'; exact K3 | exact HD' ];
        subst p n; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
    +
      rewrite (DC_found k p (dec_idx1 n) code_bits s c (pullr c r)) by lia.
      destruct (CK_found _ _ _ _ _ _ _ _ HD' ltac:(lia)) as [_ ->].
      do 2 zs. apply evt_done. left. eexists (pullr c r), _. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact RI1|].
      split; [exact HREGS1|]. split; [exact HPL1|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
      unfold cl_QJ. cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h28 h29 h31]. subst p n.
      repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (DC_dry k p (dec_idx1 n) code_bits s c r) by lia.
    do 8 zs. rewrite (zx32_small (ir_have rb)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply evt_done. right. exists r. split; [reflexivity|]. split; [exact HPL|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| first [assumption | symmetry; assumption | reflexivity]..].
Qed.

Lemma cl_dec : forall X s c r rf q ms,
  ILOOPg X (mkW s c r) PC_CL_B q ms -> CLK X s q -> sc13 q = wz (is_have s) -> sc6 q = wz (ir_have r) ->
  sc7 q = wz (il_NI (ix_L X) + ir_next r) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dchk 8 c (dec_idx1 (is_lenbits s)) code_bits (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r = Some rf ->
  evt psegs (DECG X s c r r (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits (mkW s c r)) rf
               (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_CL_J (cl_QJ X s r)) ms.
Proof.
  intros X s c r rf [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E14 & E15 & E16) E13 E6 E7 E26 XO HREGS HP RN CPO HD.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *.
  subst x12 x13 x14 x15 x16 x6 x7 x26.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  unfold PC_CL_B. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0]. pose proof (ones_range15 n RN) as RMK.
  zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0.
  do 2 zs.
  pose proof (code_rd_bits m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e0)) by exact RB0. clear RD.
  zs. br_cases K.
  -
    rewrite (DC_found 8 p (dec_idx1 n) code_bits s c r) by (fold i0; fold e0; lia).
    destruct (CK_found _ _ _ _ _ _ _ _ HD ltac:(fold i0; fold e0; lia)) as [_ ->].
    do 3 zs. apply evt_done. left. eexists r, _. split; [reflexivity|]. split; [reflexivity|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [exact HREGS|]. split; [apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)]|].
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold cl_QJ. cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h28 h29 h31]. fold p. fold n. fold i0. fold e0. repeat split; reflexivity.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    do 4 zs.
    eapply (cl_loop1 8%nat X s c r r rf);
      [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h29 h30 h31] ..
      | exact XO | exact HREGS | apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1 | exact RN | exact CPO | exact K' | exact HD ];
      subst e0 i0 p n; first [ reflexivity | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
Qed.

Local Ltac close_lit jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_litw : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> PATG X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) < 16 ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < 320 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q',
     ILOOPg X (mkW (cl_lit s (code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))) c
                 (ddrop r1 (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))))) PC_CL_T q' ms'
     /\ CLK X s q' /\ sc13 q' = wz (is_have s + 1) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r1)) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP EI EO ER EP EL RB RH RI CPO RN RV LL Rh RPUT.
  destruct HQ as (E28 & E5 & E17 & E9 & E22 & E26 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RB1. pose proof (code_val_range e1) as RV1. pose proof (dec_idx1_range n (ir_hold r1) ltac:(lia) RN) as RI1'. fold i1 in RI1'.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e1 in RD. zs. rewrite (zx16_small (code_val e1)) by lia. clear RD.
  do 2 zs. br_false.
  zs. rewrite land63_small by lia. do 4 zs. itr_groups MUf WMf. clear MUf WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv psegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl psegs m1) as WMf end.
  do 2 zs. rewrite zext32_x2 by lia.
  assert (EV : wrap16 (code_val e1) = code_val e1) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s) (wrap16 (code_val e1)) ltac:(rewrite EV; reflexivity).
  zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
  - close_lit jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
  - unfold CLK, cl_lit. cbn [sc12 sc13 sc14 sc15 sc16 sc26]. ired. fold p n. repeat split; ireg.
Qed.

Definition cl_pce (val : Z) : Z := if val =? 16 then 0x1dab8 else if val =? 17 then 0x1da7c else 0x1daf4.
Definition cl_pcx (val : Z) : Z := if val =? 16 then 0x1db58 else if val =? 17 then 0x1db34 else 0x1db94.

Definition cl_QN (X : ictx) (s : inflate_state) (r r1 r2 : iregs) (q : iscrh) : Prop :=
  h5 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))))
  /\ h17 q = wz (ir_bits r2) /\ h9 q = wz (ir_have r2) /\ h22 q = wz (ir_hold r2)
  /\ h26 q = wz (il_NI (ix_L X) + ir_next r2) /\ h27 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h23 q = wz (ir_bits r) /\ h29 q = wz 30 /\ h31 q = wz (-16180)
  /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_have s) /\ h14 q = wz (is_nlen s + is_ndist s)
  /\ h15 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h16 q = wz (Z.ones (is_lenbits s)).

Definition cl_site (pcl pcx : Z) : Prop :=
  (pcl = 0x1dac4 /\ pcx = 0x1db58) \/ (pcl = 0x1da88 /\ pcx = 0x1db34) \/ (pcl = 0x1db00 /\ pcx = 0x1db94).

Definition NBJcg (X : ictx) (s : inflate_state) (c : icall) (r r1 : iregs) (RES : ares unit) (pcx : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r2 q', RES = ARun tt (mkW s c r2) /\ ILOOPh X (mkW s c r) pcx q' ms' /\ cl_QN X s r r1 r2 q')
    \/ (exists r2, RES = ALeave (mkW s c r2) /\ ILEAVE X (mkW s c r2) ms').

Lemma cl_nloop : forall f X s c r r1 rc n pcl pcx q ms,
  cl_site pcl pcx ->
  ILOOPh X (mkW s c r) pcl q ms ->
  h5 q = wz (code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))) -> h6 q = wz n ->
  h7 q = wz (ir_bits rc) -> h17 q = wz (ir_bits rc) -> h9 q = wz (ir_have rc) -> h22 q = wz (ir_hold rc) ->
  h26 q = wz (il_NI (ix_L X) + ir_next rc) -> h23 q = wz (ir_bits r) -> h29 q = wz 30 -> h31 q = wz (-16180) ->
  h12 q = wz (is_nlen s) -> h13 q = wz (is_have s) -> h14 q = wz (is_nlen s + is_ndist s) ->
  h15 q = wz (cp_addr (ix_L X) (is_lencode s)) -> h16 q = wz (Z.ones (is_lenbits s)) ->
  ix_ok X -> REGS c rc -> pulled r rc -> 0 <= ir_bits r -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  0 <= n <= 40 -> ir_bits rc < n -> n <= ir_bits rc + 8 * Z.of_nat f ->
  evt psegs (NBJcg X s c r r1 (NEEDBITS_k f n (mkW s c rc)) pcx) ms.
Proof.
  induction f as [|f IH]; intros X s c r r1 rc n pcl pcx [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms
    SITE HL E5 E6 E7 E17 E9 E22 E26 E23 E29 E31 E12 E13 E14 E15 E16 XO HREGS HPL HB0 Pin Pin1 Hn HB Hf.
  { exfalso. cbn [Z.of_nat] in Hf. lia. }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
  subst x5 x6 x7 x17 x9 x22 x26 x23 x29 x31 x12 x13 x14 x15 x16.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next rc)) as RBy. pose proof (REGS_hold64 c rc HREGS) as RH64.
  pose proof (pulled_cursor r rc HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r rc HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have rc < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (code_bits_range (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))) as RB5.
  ix_open XO.
  destruct SITE as [[-> ->]|[[-> ->]|[-> ->]]].
  all: zs; br_cases K;
  [
    assert (NXT : 0 <= ir_next rc < arr_len (ix_input X)) by (rewrite <- Pin; lia);
    destruct (pull_step c r rc HREGS HB0 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7' & E8 & E9' & RH1);
    pose proof (u8ro_read psegs _ _ _ (ir_next rc) _ (wa (il_NI (ix_L X) + ir_next rc)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD;
    zs; clear RD; do 8 zs; rewrite <- Pin; rewrite !pull_shift by lia; br_cases K3;
    [
      rewrite (NB_pull f n s c rc) by lia;
      eapply (IH X s c r r1 (pullr c rc) n);
        [ first [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity]
        | eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
        | exact XO | exact HREGS1 | exact HPL1 | exact HB0 | exact Pin | exact Pin1 | exact Hn | rewrite E6'; lia | rewrite E6'; rewrite Nat2Z.inj_succ in Hf; lia ];
        first [ reflexivity | rewrite ?E1, ?E2, ?E5', ?E6'; ireg ]
    |
      rewrite (NB_pull f n s c rc) by lia; rewrite (NB_done f n s c (pullr c rc)) by (rewrite E6'; lia);
      zs; apply evt_done; left; eexists (pullr c rc), _; split; [reflexivity|]; split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
      unfold cl_QN; cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h29 h31]; rewrite E1, E2, E5', E6'; repeat split; ireg ]
  |
    assert (H0 : ir_have rc = 0) by lia;
    rewrite (NB_dry f n s c rc) by lia;
    do 4 zs; apply evt_done; right; exists rc; split; [reflexivity|];
    eapply ILEAVE_intro; ired; [ireg .. |];
    eapply IMEML_of_IMEM; [exact HMEM| first [assumption | symmetry; assumption | reflexivity]..] ].
Qed.

Lemma cl_need : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> REGS c r1 -> pulled r r1 -> 0 <= ir_bits r ->
  PATG X (mkW s c r) ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= 32 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  16 <= code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  evt psegs (NBJcg X s c r r1 (NEEDBITS (code_bits here + cl_nb (code_val here)) (mkW s c r1)) (cl_pcx (code_val here))) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HREGS HPL HB0 HP RB RB32 RI CPO RN RV.
  destruct HQ as (E28 & E5 & E17 & E9 & E22 & E26 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB1 RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (REGS_hold64 c r1 HREGS) as RH64.
  assert (HAV : ir_have r1 < 2^31) by (rewrite Pin in Rnh; lia).
  open_IST ST. ix_open XO. unfold PC_CL_J.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RBe. pose proof (code_val_range e1) as RVe. pose proof (dec_idx1_range n (ir_hold r1) ltac:(lia) RN) as RI1'. fold i1 in RI1'.
  cbv zeta. rewrite NB_top.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e1 in RD. zs. rewrite (zx16_small (code_val e1)) by lia. clear RD.
  do 2 zs. br_true.
  do 2 zs. br_cases K16; [| do 2 zs; br_cases K17]; unfold cl_nb, cl_pcx;
  [ replace (code_val e1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia)
  | replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia); replace (code_val e1 =? 17) with false by (symmetry; apply Z.eqb_neq; lia)
  | replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia); replace (code_val e1 =? 17) with true by (symmetry; apply Z.eqb_eq; lia) ].
  all: do 2 zs; br_cases K;
  [
    rewrite (NB_done 8 _ s c r1) by lia;
    zs; apply evt_done; left; eexists r1, _; split; [reflexivity|];
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
    unfold cl_QN; cbn [h5 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h29 h31]; subst e1 i1 p n; repeat split; reflexivity
  | zs ].
  - eapply (cl_nloop 8%nat X s c r r1 r1 _ 0x1dac4 0x1db58);
      [ left; split; reflexivity | eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
      | exact XO | exact HREGS | exact HPL | exact HB0 | exact Pin | exact Pin1 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ];
      subst e1 i1 p n; reflexivity.
  - eapply (cl_nloop 8%nat X s c r r1 r1 _ 0x1db00 0x1db94);
      [ right; right; split; reflexivity | eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
      | exact XO | exact HREGS | exact HPL | exact HB0 | exact Pin | exact Pin1 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ];
      subst e1 i1 p n; reflexivity.
  - eapply (cl_nloop 8%nat X s c r r1 r1 _ 0x1da88 0x1db34);
      [ right; left; split; reflexivity | eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
      | exact XO | exact HREGS | exact HPL | exact HB0 | exact Pin | exact Pin1 | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ];
      subst e1 i1 p n; reflexivity.
Qed.

Definition PC_CL_R : Z := 0x1dbbc.
Definition PC_CL_RX : Z := 0x1dbd4.

Local Ltac close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_hd : forall X s c r r1 r2 q ms,
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let val := code_val here in let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  let len := (if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0) in
  let copy := cl_base val + BITSv (ir_hold r3) nb in
  let r4 := ddrop r3 nb in
  ILOOPh X (mkW s c r) (cl_pcx val) q ms -> cl_QN X s r r1 r2 q -> ix_ok X -> PATG X (mkW s c r) ->
  ir_in r2 = ir_in r -> ir_out r2 = ir_out r -> ir_ret r2 = ir_ret r -> ir_put r2 = ir_put r -> ir_left r2 = ir_left r ->
  code_bits here + nb <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_have r2 -> 16 <= val ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s <= is_nlen s + is_ndist s -> is_nlen s + is_ndist s <= 320 ->
  (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if (val =? 16) && (is_have s =? 0) then exists x8, ILOOP X (cl_bad s c r3) PC_DISPATCH x8 (wz BAD) ms'
    else if is_nlen s + is_ndist s <? is_have s + copy then exists x8, ILOOP X (cl_bad s c r4) PC_DISPATCH x8 (wz BAD) ms'
    else exists q', ILOOPg X (mkW s c r4) PC_CL_R q' ms' /\ CLK X s q' /\ sc13 q' = wz (is_have s) /\ sc17 q' = wz (is_have s + copy)
                    /\ sc6 q' = wz len /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r2) /\ sc27 q' = wz (il_NI (ix_L X) + ir_next r2)) ms.
Proof.
  intros X s c r r1 r2 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms.
  intros here val nb r3 len copy r4 HL HQ XO HP EI EO ER EP EL RB RH RHV RV LL Rh Rnd HLs RPUT.
  destruct HQ as (E5 & E17 & E9 & E22 & E26 & E27 & E23 & E29 & E31 & E12 & E13 & E14 & E15 & E16).
  iarm_openh HL. subst x5 x17 x9 x22 x26 x27 x23 x29 x31 x12 x13 x14 x15 x16.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  fold here. set (cb := code_bits here) in *. pose proof (code_bits_range here) as RCB. fold cb in RCB.
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
    do 2 zs. rewrite land63_small by lia. zs. br_cases K0.
    + replace (is_have s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (HLs (is_have s - 1) ltac:(lia)) as RLEN.
      do 4 zs. rewrite zext32_x2 by lia.

      pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s - 1) ltac:(lia). clear Gl'.
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 2 ltac:(lia)) as R3. change (Z.ones 2) with 3 in R3. change (2 ^ 2) with 4 in R3.
      rewrite EH3 in Ecp.
      do 5 zs. do 2 zs. br_cases K1.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { apply IMEM_intro; inorm; [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
          | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin | unfold iarrs in *; inorm; exact ARRS| exact LAY]
          | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ]. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        apply IMEM_intro; inorm; [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
          | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin | unfold iarrs in *; inorm; exact ARRS| exact LAY]
          | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].
    +
      replace (is_have s =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
      do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
      apply evt_done. eexists. unfold cl_bad. subst r3. unfold ddrop. eapply ILOOP_intro; ired; [ireg .. |].
      close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
  -
    cbn [andb].
    destruct (Z.eqb_spec val 17) as [V17|NV17].
    + assert (Enb : nb = 3) by (subst nb; unfold cl_nb; rewrite V17; reflexivity).
      assert (Ecp : copy = 3 + Z.land (ir_hold r3) 7) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V17; reflexivity).
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 3 ltac:(lia)) as R3. change (Z.ones 3) with 7 in R3. change (2 ^ 3) with 8 in R3.
      rewrite EH3 in Ecp.
      do 2 zs. rewrite land63_small by lia. do 6 zs.
      do 2 zs. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    + assert (Enb : nb = 7).
      { subst nb; unfold cl_nb. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      assert (Ecp : copy = 11 + Z.land (ir_hold r3) 127).
      { subst copy; rewrite EBV, Enb; unfold cl_base. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 7 ltac:(lia)) as R3. change (Z.ones 7) with 127 in R3. change (2 ^ 7) with 128 in R3.
      rewrite EH3 in Ecp.
      do 2 zs. rewrite land63_small by lia. do 5 zs.
      do 2 zs. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done. eexists. split; [eapply ILOOPg_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLK. cbn [sc6 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27]. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. do 3 zs. do 2 zs. itr_groups MUf WMf.
        apply evt_done. eexists. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
Qed.
